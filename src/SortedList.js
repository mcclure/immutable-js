/**
 * Copyright (c) 2014-present, Facebook, Inc.
 * Additions copyright (c) 2020, Andi McClure.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

import {
  DELETE,
  SHIFT,
  SIZE,
  MASK,
  OwnerID,
  MakeRef,
  SetRef,
  wrapIndex,
  wholeSlice,
  resolveBegin,
  resolveEnd,
} from './TrieUtils';
import { IndexedCollection } from './Collection';
import { hasIterator, Iterator, iteratorValue, iteratorDone } from './Iterator';
import { setIn } from './methods/setIn';
import { deleteIn } from './methods/deleteIn';
import { update } from './methods/update';
import { updateIn } from './methods/updateIn';
import { mergeIn } from './methods/mergeIn';
import { mergeDeepIn } from './methods/mergeDeepIn';
import { withMutations } from './methods/withMutations';
import { asMutable } from './methods/asMutable';
import { asImmutable } from './methods/asImmutable';
import { wasAltered } from './methods/wasAltered';
import assertNotInfinite from './utils/assertNotInfinite';

const identity = x => x;
const lt = (x,y) => x < y;
const NODEMAX = 2 << SHIFT;
const NODEMID = NODEMAX / 2;

const IS_SORTED_LIST_SYMBOL = '@@__IMMUTABLE_SORTED_LIST__@@';

export function isSortedList(maybeList) {
  return Boolean(maybeList && maybeList[IS_SORTED_LIST_SYMBOL]);
}

// Invariants:
// - vnodes always contain at least one item
// - vnodes never contain more than NODEMAX (32) items
// - branch (non-leaf) vnodes always contain at least two items (THIS IS NOT A VALID ASSUMPTION)

export class SortedList extends IndexedCollection {
  // @pragma Construction

  constructor(value) {
    const empty = emptySortedList();
    if (value === null || value === undefined) {
      return empty;
    }
    if (isSortedList(value)) {
      return value;
    }
    const iter = IndexedCollection(value);
    const size = iter.size;
    if (size === 0) {
      return empty;
    }
    assertNotInfinite(size);
    return empty.withMutations(list => {
      iter.forEach((v) => list.add(v));
    });
  }

  static of(/*...values*/) {
    return this(arguments);
  }

  toString() {
    return this.__toString('SortedList [', ']');
  }

  _makeVnode(array) { // Note empty VNodes are not allowed
    return new VNode(array, this._key(array[0]), this._key(array[array.length-1]))
  }

  _nodeCmp(vnode, key) { // 0 if within range, -1 or 1 if outside // NOT USED
    if (this._lt(key, vnode.min))
      return -1;
    if (this._lt(vnode.max, key))
      return 1;
    return 0;
  }

  // Note: No attempt at sort stability is attempted
  add(value) {
    if (!this.root) {
      const root = this._makeVnode([value])
      return makeSortedList(1, 1, root, root, root, this._key, this._lt, this.__hash)
    }
    let maxLevel = this._level, head = null, tail = null;
    const key = this._key(value);
    const isMin = !this._lt(this._root.min, key); // Key will be inserted into current head vnode
    const isMax = !isHead || !this._lt(key, this._root.max); // Key will be inserted into current tail vnode
    const stack = [{ // : {node:VNode, isMin?:boolean, isMax?:boolean, index?:number}
      node:this._root,
      isMin:isMin, // Key is lte the vnode min-- don't have to find a position, just shove at beginning
      isMax:isMax  // Key is gte the vnode max-- don't have to find a position, just shove at end
    }];
    // First descend into the tree and find the insertion point
    for(let level = 0;; level++) {
      const top = stack[stack.length-1];
      const array = top.node.array
      if (level < maxLevel - 1) { // Branch nodes
        if (top.isMax) { // Pass through a previously figured out isMax (bias high)
          const index = array.length-1;
          top.index = index;
          stack.push({node:array[index], isMax:true})
        } else if (top.isMin) { // Pass through a previously figured out isMin
          top.index = 0;
          stack.push({node:array[0], isMin:true});
        } else { // Look within vnode to find best index
          let maxIndex = array.length-1
          if (!this._lt(key, array[maxIndex].max)) { // Identify an isMax (bias high)
            top.index = maxIndex;
            stack.push({node:array[maxIndex], isMax: true})
          } else if (!this._lt(array[0].min, key)) { // Identify an isMin (bias high)
            stack.push({node:array[0], isMin:true})
          } else { // Binary search within vnode to find best index
            let minIndex = 0; // Target node is now known to be somewhere between minIndex and maxIndex inclusive
            let isMax = false;
            if (!this._lt(key, array[maxIndex].min)) {
              minIndex = maxIndex; // Key is inside array[maxIndex]
            } else if (this._lt(array[0].max, key)) { // Skip search if key inside array[0]
              // Target node is now known to be somewhere between minIndex and maxIndex exclusive. We narrow the
              // range until either we happen on the cell containing key, or minIndex and maxIndex are exactly
              // 1 apart (in which case we've proven the key is in the gap between minIndex and maxIndex, at which
              // point we arbitrarily choose to descend into minIndex so we can add at the end of an array).
              isMax = true; // Setting on the assumption we'll stop on the "exactly 1 apart" condition.
              while (minIndex < maxIndex - 1) {
                let searchIndex = Math.ceil((minIndex+maxIndex)/2)
                if (this._lt(key, array[searchIndex].min)) {
                  maxIndex = searchIndex; // Target node now known to be between minIndex and searchIndex exclusive
                } else if (this._lt(array[searchIndex].max, key)) {
                  minIndex = searchIndex; // Target node now known to be between searchIndex and maxIndex exclusive
                } else { // Oh, we found it.
                  minIndex = searchIndex;
                  isMax = false; // Guess we aren't hitting "exactly 1 apart" after all
                  break;
                }
              }
            }
            top.index = minIndex; // Descend into min index so if we're adding "between" we still add at end of array
            stack.push({node:array[minIndex], isMax:isMax})
          }
        }
      } else { // We are now looking at a leaf node, and "stack" contains a complete route from the root to the leaf.
        const leafOverflow = array.length >= NODEMAX; // If leaf array is full we must split one or more nodes
        let leafNode;      // Leaf array we will be searching
        let lastNode;      // What is the last singular node we created?
        let lastNodeLevel; // At what level was the last singular node we created?
        let checkHeadTail = false; // Set true if the leaf node has a chance to change head/tail.

        let lastLeft, lastRight;

        // First thing to do is find the leaf node
        if (!leafOverflow) { // It's either the leaf we were already looking at
          leafNode = top.node;

          checkHeadTail = true; // When we insert our modified leaf node, maybe head or tail changes
        } else { // Or else we have to create it by splitting
          let lastLeft = new VNode(array.slice(0,NODEMID), top.node.min, this._key(array[NODEMID-1]));
          let lastRight = new VNode(array.slice(NODEMID), this._key(array[NODEMID]), top.node.max);
          leafNode = // Which of the two new nodes will we insert value into below?
            this._lt(key, this._key(right[0])) ? lastLeft : lastRight;

          // Head/tail can change when a leaf node splits
          if (stack.length <= 1) { // We split single node into a head and a tail
            head = lastLeft;
            tail = lastRight;
          } else { // The head or tail MAY or MAY NOT have changed.
            const preTop = stack[stack.length-2];
            if (preTop.index == 0) {
              head = lastLeft;
            } else if (preTop.index == preTop.node.array.length-1) {
              tail = lastRight;
            }
          }
        }

        // Now we know what node is the leaf node, figure out what index to insert into the leaf at
        let minIndex = 0;
        let maxIndex = leafNode.array.length;
        let maxKey = this._key(pusharray[maxIndex])
        let minKey = this._key(pushArray[0])

        if (top.isMax || !this._lt(key, maxKey)) { // We are off the bottom or equal to bottom
          maxIndex = minIndex = maxIndex + 1;
        } else if (top.isMin || !this._lt(minKey, key)) { // We are off the top or equal to top
          maxIndex = 0;
        } else { // Target node is somewhere between minIndex and maxIndex exclusive
          // We binary search until maxIndex is gte the key, minIndex is lt the key, and maxIndex-minIndex=1
          while (minIndex < maxIndex - 1) {
            let searchIndex = Math.ceil((minIndex+maxIndex)/2)
            let searchKey = this._key(pushArray[searchIndex])
            if (this._lt(key, searchKey)) {
              minIndex = searchIndex;
            } else {
              maxIndex = searchIndex;
            }
          }
        }

        // The search inside the leaf ends with maxIndex as the insert index:
        if (!leafOverflow) {
          lastNode = vnodeInsert(leafNode, maxIndex, value, key);

          lastNodeLevel = level;
        } else { // In the overflow case we own the only reference to (created) the node and can mutate it
          vnodeMutateInsert(leafNode, maxIndex, value, key);

          // The leaf is now dealt with, but since we're in the overflow path we have to handle splits.
          // We split the node above into lastLeft and lastRight. Now we need to put them in the tree, 
          // but that may trigger more splits. Walk backward up the tree until there are no more splits:
          for(lastNodeLevel = level-1; lastNodeLevel >= 0; lastNodeLevel--) {
            const top = stack[lastNodeLevel];
            let node = top.node;
            let index = top.index;
            const overflow = node.array.length >= NODEMAX;
            const left = lastLeft, right = lastRight;
            if (!overflow) { // Room for 1 more node. Do an insert of the left node:
              node = vnodeInsert(node, top.index, left);
            } else { // Need to do at least one more level of split:
              lastLeft = new VNode(node.array.slice(0,NODEMID), node.min, node.array[NODEMID-1].max);
              lastRight = new VNode(node.array.slice(NODEMID), node.array[NODEMID].min, node.max);
              if (top.index < NODEMID) {
                node = lastLeft;
              } else {
                index -= NODEMAX;
                node = lastRight;
              }
              vnodeMutateInsert(node, index, left); // Since we created this node, we can mutate it
            }
            vnodeMutateReplace(node, index+1, right); // The index we previously found has been moved over one by the insert
            if (!overflow) { // We are done splitting and can pass lastNode/lastNodeLevel to the final step
              lastNode = node;
              break;
            }
          }
          if (lastNodeLevel < 0) { // We split the entire tree, so we need to make a new root node.
            lastNode = new VNode([lastLeft, lastRight], lastLeft.min, lastRight.max);
            maxLevel++;
          }
        }

        // The leaf and the splits are dealt with, now it's just the rest of the tree. Walk backward
        // up the tree from just above our leaf (or, from just above the highest split point) to the root
        for(lastNodeLevel--; lastNodeLevel >= 0; lastNodeLevel--) {
          const top = stack[lastNodeLevel];

          if (checkHeadTail) { // We might have to adjust head/tail on the first pass of this loop.
            if (top.index == 0) {
              head = lastNode;
            } else if (top.index == top.node.array.length-1) {
              tail = lastNode;
            }
            checkHeadTail = false; 
          }

          lastNode = vnodeInsert(top.node, top.index, lastNode)
        }

        // We've walked all the way up to the top now, so lastNode is new root.
        return makeSortedList(this.size+1, maxLevel, lastNode, head || this._head, tail || this._tail,
                              this._key, this._lt, this.__hash)
      }
    }
  }

  clear() {
    if (this.size === 0) {
      return this;
    }
    return emptySortedList();
  }

  pop() { // Remove from right
    
    return setListBounds(this, 0, -1);
  }

  unshift(/*...values*/) {
    const values = arguments;
    return this.withMutations(list => {
      setListBounds(list, -values.length);
      for (let ii = 0; ii < values.length; ii++) {
        list.set(ii, values[ii]);
      }
    });
  }

  shift() {
    return setListBounds(this, 1);
  }

  // @pragma Composition

  concat(/*...collections*/) {
    const seqs = [];
    for (let i = 0; i < arguments.length; i++) {
      const argument = arguments[i];
      const seq = IndexedCollection(
        typeof argument !== 'string' && hasIterator(argument)
          ? argument
          : [argument]
      );
      if (seq.size !== 0) {
        seqs.push(seq);
      }
    }
    if (seqs.length === 0) {
      return this;
    }
    if (this.size === 0 && !this.__ownerID && seqs.length === 1) {
      return this.constructor(seqs[0]);
    }
    return this.withMutations(list => {
      seqs.forEach(seq => seq.forEach(value => list.push(value)));
    });
  }

  setSize(size) {
    return setListBounds(this, 0, size);
  }

  map(mapper, context) {
    return this.withMutations(list => {
      for (let i = 0; i < this.size; i++) {
        list.set(i, mapper.call(context, list.get(i), i, list));
      }
    });
  }

  // @pragma Iteration

  slice(begin, end) {
    const size = this.size;
    if (wholeSlice(begin, end, size)) {
      return this;
    }
    return setListBounds(
      this,
      resolveBegin(begin, size),
      resolveEnd(end, size)
    );
  }

  __iterator(type, reverse) {
    let index = reverse ? this.size : 0;
    const values = iterateList(this, reverse);
    return new Iterator(() => {
      const value = values();
      return value === DONE
        ? iteratorDone()
        : iteratorValue(type, reverse ? --index : index++, value);
    });
  }

  __iterate(fn, reverse) {
    let index = reverse ? this.size : 0;
    const values = iterateList(this, reverse);
    let value;
    while ((value = values()) !== DONE) {
      if (fn(value, reverse ? --index : index++, this) === false) {
        break;
      }
    }
    return index;
  }
}

SortedList.isSortedList = isSortedList;

export const SortedListPrototype = SortedList.prototype;
SortedListPrototype[IS_SORTED_LIST_SYMBOL] = true;
SortedListPrototype[DELETE] = SortedListPrototype.remove;
SortedListPrototype.merge = SortedListPrototype.concat;
SortedListPrototype.setIn = setIn;
SortedListPrototype.deleteIn = SortedListPrototype.removeIn = deleteIn;
SortedListPrototype.update = update;
SortedListPrototype.updateIn = updateIn;
SortedListPrototype.mergeIn = mergeIn;
SortedListPrototype.mergeDeepIn = mergeDeepIn;
SortedListPrototype.withMutations = withMutations;
SortedListPrototype.wasAltered = wasAltered;
SortedListPrototype.asImmutable = asImmutable;
SortedListPrototype['@@transducer/init'] = SortedListPrototype.asMutable = asMutable;
SortedListPrototype['@@transducer/step'] = function (result, arr) {
  return result.push(arr);
};
SortedListPrototype['@@transducer/result'] = function (obj) {
  return obj.asImmutable();
};

class VNode {
  constructor(array, min, max) {
    this.array = array;
    this.min = min;
    this.max = max;
  }
}

function vnodeReplace(node, index, value, key) { // key optional if value is node
  const array = [...node.array]; // Copy array
  array[index] = value;          // Replace index value
  const min = index == 0 ? (key || value.min) : node.min; // Adjust edges
  const max = index == array.length-1 ? (key || value.max) : node.max;
  return new VNode(array, min, max)
}

function vnodeInsert(node, index, value, key) { // key optional if value is node
  const oldArray = node.array;
  const array = [...oldArray.slice(0,index), value, ...oldArray.slice(index)]
  const min = index == 0 ? (key || value.min) : node.min;
  const max = index == oldArray.length ? (key || value.max) : node.max;
  return new VNode(array, min, max)
}

function vnodeMutateReplace(node, index, value, key) { // key optional if value is node
  node.array[index] = value;
  if (index == 0)
    node.min = key || value.min;
  if (index == array.length-1)
    node.max = key || value.max;
}

function vnodeMutateInsert(node, index, value, key) { // key optional if value is node
  array.splice(index, 0, value);
  if (index == 0)
    node.min = key || value.min;
  if (index == array.length-1)
    node.max = key || value.max;
}

function makeSortedList(size, level, root, head, tail, keyFn, ltFn, hash) {
  const list = Object.create(SortedListPrototype);
  list.size = size;
  list._level = level;
  list._root = root;
  list._head = head;
  list._tail = tail;
  list._key = keyFn || identity;
  list._lt = ltFn || lt;
  list.__hash = hash; // ENTIRELY UNCLEAR WHAT THIS DOES-- TODO-ANDI
  list.__altered = false;
  return list;
}

let EMPTY_SORTED_LIST;
export function emptySortedList() {
  return EMPTY_SORTED_LIST || (EMPTY_SORTED_LIST = makeSortedList(0, 0));
}
