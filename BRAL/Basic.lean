-- Based on Okasaki's Binary Random Access List
import Mathlib.Tactic
namespace BRAL
-- DEFINITIONS
-- Type
inductive Tree (α : Type) : Type
  | Leaf : α → Tree α
  | Node : ℕ → Tree α → Tree α → Tree α -- ℕ = Size of the tree
deriving Repr

abbrev RList (α : Type) := List (Tree α)


-- Tree size
def size {α : Type} : Tree α → ℕ
  | Tree.Leaf _       => 1
  | Tree.Node n _ _   => n

-- This invariant is preserved throughout the program by "link"
axiom size_n {α : Type} (n : ℕ) (t1 : Tree α) (t2 : Tree α) :
  size (Tree.Node n t1 t2) = (size t1) + (size t2)


-- Init: Empty list
def empty {α : Type} : RList α := []
def isEmpty {α : Type} : RList α → Bool
  | []  => true
  | _   => false


-- Cons
def link {α : Type} : Tree α → Tree α → Tree α :=
  fun t1 t2 ↦ Tree.Node (size t1 + size t2) t1 t2

def consTree {α : Type} : Tree α → RList α → RList α
  | t, []       => [t]
  | t, t' :: ts =>
        if size t = size t' then
          consTree (link t t') ts
        else
          t :: t' :: ts

def cons {α : Type} (x : α) (ts : RList α) : RList α :=
  consTree (Tree.Leaf x) ts


-- Lookup using index (in O(log n))
def lookupTree {α : Type} : ℕ → Tree α → Option α
  | 0, Tree.Leaf x        => some x
  | _, Tree.Leaf _        => none
  | i, Tree.Node _ t1 t2  =>
        if i < size t1 then
          lookupTree i t1
        else
          lookupTree (i - size t1) t2

def lookup {α : Type} : ℕ → RList α → Option α
  | _, []       => none
  | i, t :: ts  =>
        if i < size t then
          lookupTree i t
        else
          lookup (i - size t) ts


-- Update in-place (in O(log n))
def updateTree {α : Type} : ℕ → α → Tree α → Tree α
  | 0, y, Tree.Leaf _       => Tree.Leaf y
  | _, _, Tree.Leaf x       => Tree.Leaf x
  | i, y, Tree.Node n t1 t2 =>
        if i < size t1 then
          Tree.Node n (updateTree i y t1) t2
        else
          Tree.Node n t1 (updateTree (i - size t1) y t2)

def update {α : Type} : ℕ → α → RList α → RList α
  | _, _, []      => []
  | i, y, t :: ts =>
        if i < size t then
          (updateTree i y t) :: ts
        else
          t :: (update (i - size t) y ts)



-- CONVERSION
def treeToList {α : Type} : Tree α → List α
  | Tree.Leaf x       => [x]
  | Tree.Node _ t1 t2 => treeToList t1 ++ treeToList t2

def toList {α : Type} : RList α → List α
  | []        => []
  | t :: ts   => treeToList t ++ toList ts

def toRList {α : Type} : List α → RList α
  | []        => []
  | t :: ts   => cons t (toRList ts)



-- TESTING
#eval isEmpty (α := ℕ) empty
def one := (cons 1 empty)
def two := cons 2 one
def three := cons 3 two
def four := cons 4 three
def five := cons 5 four
def six := cons 6 five
def seven := cons 7 six

#eval one
#eval two
#eval three
#eval four
#eval five
#eval six
#eval seven

#eval lookup 0 seven
#eval lookup 1 seven
#eval lookup 2 seven
#eval lookup 3 seven
#eval lookup 4 seven
#eval lookup 5 seven
#eval lookup 6 seven
#eval lookup 7 seven

#eval lookup 0 (update 0 99 seven)
#eval lookup 1 (update 0 99 seven)
#eval lookup 2 (update 0 99 seven)
#eval lookup 3 (update 0 99 seven)
#eval lookup 4 (update 0 99 seven)
#eval lookup 5 (update 0 99 seven)
#eval lookup 6 (update 0 99 seven)
#eval lookup 7 (update 0 99 seven)

#eval lookup 0 (update 6 99 seven)
#eval lookup 1 (update 6 99 seven)
#eval lookup 2 (update 6 99 seven)
#eval lookup 3 (update 6 99 seven)
#eval lookup 4 (update 6 99 seven)
#eval lookup 5 (update 6 99 seven)
#eval lookup 6 (update 6 99 seven)
#eval lookup 7 (update 6 99 seven)

#eval lookup 0 (update 7 99 seven)
#eval lookup 1 (update 7 99 seven)
#eval lookup 2 (update 7 99 seven)
#eval lookup 3 (update 7 99 seven)
#eval lookup 4 (update 7 99 seven)
#eval lookup 5 (update 7 99 seven)
#eval lookup 6 (update 7 99 seven)
#eval lookup 7 (update 7 99 seven)


#eval toRList (α := ℕ) []
#eval toRList [1]
#eval toRList [1, 2]
#eval toRList [1, 2, 3]
#eval toRList [1, 2, 3, 4, 5, 6, 7]

#eval toList one
#eval toList two
#eval toList three
#eval toList four
#eval toList five
#eval toList six
#eval toList seven



-- VERIFICATION

-- Linking trees is equal to list concateℕion
lemma link_toList {α : Type} (t1 : Tree α) (t2 : Tree α) :
  treeToList (link t1 t2) = treeToList t1 ++ treeToList t2 :=
  by
    cases t1 <;> cases t2 <;> simp [link, treeToList]

-- Correctness of consTree
lemma consTree_toList {α : Type} (t : Tree α) (ts : RList α) :
  toList (consTree t ts) = treeToList t ++ (toList ts) :=
  by
    induction ts generalizing t with
      | nil           => simp [consTree, toList]
      | cons t' ts ih =>
          by_cases h : size t = size t'
          {
            simp [consTree, h, toList, ih, link_toList, List.append_assoc]
          }
          {
            simp [consTree, h, toList]
          }

-- Main result: Our implementation is equal to a cons-list
theorem cons_correct {α : Type} (x : α) (ts : RList α) :
  toList (cons x ts) = x :: toList ts :=
  by
    simp [cons, consTree_toList, treeToList]




-- helper-lemma for operations lookup/update
lemma length_eq {α : Type} (t : Tree α) :
  size t = (treeToList t).length :=
  by
    induction t with
      | Leaf x               =>
          simp [size, treeToList]
      | Node n t1 t2 ihl ihr =>
          simp [treeToList]
          rw [←ihl, ←ihr]
          apply size_n



-- Correctness lookup inside a single tree
lemma tree_lookup_correct {α : Type} (t : Tree α) (i : ℕ) :
  lookupTree i t = (treeToList t)[i]? :=
  by
    induction t generalizing i with
      | Leaf x                =>
          cases i <;> simp [lookupTree, treeToList]
      | Node n t1 t2 ihl ihr  =>
          by_cases h : i < size t1
          {
            simp [lookupTree, h, treeToList, ihl]
            rw [length_eq] at h
            set l_list := (treeToList t1)
            set r_list := (treeToList t2)
            simp [List.getElem?_append_left, h]
          }
          {
            simp [lookupTree, h, treeToList, ihr]
            rw [length_eq] at h
            rw [length_eq]
            set l_list := (treeToList t1)
            set r_list := (treeToList t2)
            simp [List.getElem?_append, h]
          }

-- Correctness lookup:
-- Proof of equality with List.getElem?
theorem lookup_correct {α : Type} (l : RList α) (i : ℕ) :
  lookup i l = (toList l)[i]? :=
  by
    induction l generalizing i with
      | nil           =>
          simp [lookup, toList]
      | cons t ts ih  =>
          by_cases h : i < size t
          {
            simp [lookup, h, toList, tree_lookup_correct]
            rw [length_eq] at h
            simp [List.getElem?_append_left, h]
          }
          {
            simp [lookup, h, toList, ih]
            rw [length_eq] at h
            rw [length_eq]
            simp [List.getElem?_append, h]
          }



-- Correctness update inside a single tree
lemma tree_update_correct {α : Type} (t : Tree α) (i : ℕ) (y : α) :
  treeToList (updateTree i y t) = List.set (treeToList t) i y :=
  by
    induction t generalizing i with
      | Leaf x                =>
          cases i <;> simp [updateTree, treeToList, List.set]
      | Node n t1 t2 ihl ihr  =>
          by_cases h : i < size t1
          {
            simp [updateTree, h, treeToList, ihl]
            rw [length_eq] at h
            set l_list := (treeToList t1)
            set r_list := (treeToList t2)
            simp [h]
          }
          {
            simp [updateTree, h, treeToList, ihr]
            rw [length_eq] at h
            rw [length_eq]
            set l_list := (treeToList t1)
            set r_list := (treeToList t2)
            simp [List.set_append, h]
          }

-- Correctness update:
-- Proof of equality with List.set
theorem update_correct {α : Type} (l : RList α) (i : ℕ) (y : α) :
  toList (update i y l) = List.set (toList l) i y :=
  by
    induction l generalizing i with
      | nil           =>
          simp [update, toList]
      | cons t ts ih  =>
          by_cases h : i < size t
          {
            simp [update, h, toList, tree_update_correct]
            rw [length_eq] at h
            simp [h]
          }
          {
            simp [update, h, toList, ih]
            rw [length_eq] at h
            rw [length_eq]
            set l_head := (treeToList t)
            set l_tail := (toList ts)
            simp [List.set_append, h]
          }


end BRAL
