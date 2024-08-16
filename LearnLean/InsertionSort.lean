import Mathlib.Tactic.Basic
import Mathlib.Order.Basic

def insert_sorted (x: Int) (xs: List Int): List Int := match xs with
  | [] => [x]
  | y :: ys => if x ≤ y then x :: xs else y :: insert_sorted x ys


#eval insert_sorted 3 [1, 2, 4, 5]

def sort : List Int → List Int
  | [] => []
  | x :: xs => insert_sorted x (sort xs)

#eval sort [5, 4, 3, 2, 1]

def sorted (x: List Int): Prop := match x with
 | [] => True
 | [_] => True
 | x :: y :: xs => (x ≤ y) ∧ sorted (y :: xs)


-- examples to make sure i didn't mess up `sorted`
example : sorted [1, 2, 3] := by
  apply And.intro
  . simp
  . apply And.intro
    . simp
    . apply True.intro

example : ¬ sorted [2, 1, 3] := by
  intro h
  cases h with
  | intro h1 _ =>
    contradiction


theorem sub_sorted (x: List Int): sorted x → sorted (x.tail) := by
  intro h_sorted
  cases x with
  | nil => trivial
  | cons x xs =>
    cases xs with
    | nil => trivial
    | cons y ys =>
      exact h_sorted.right


theorem insert_retains_sort (x: Int) (xs: List Int):
  sorted xs → sorted (insert_sorted x xs) := by
  intro h
  induction xs with
  | nil =>
    trivial
  | cons y ys ih =>
    unfold insert_sorted
    split
    . unfold sorted
      simp_all
    . next hnle =>
      have y_le_x : y ≤ x := by
        apply Int.le_of_not_le hnle
      cases ys with
      | nil =>
        unfold insert_sorted
        unfold sorted
        simp_all
        unfold sorted
        simp
      | cons z zs =>
        have y_le_z : y ≤ z := by
          unfold sorted at h
          simp_all
        have h0 : sorted (z :: zs) := by
          have h1 := sub_sorted (y :: z :: zs)
          simp [h] at h1
          exact h1
        have h1 : sorted (insert_sorted x (z :: zs)) := by
          apply ih
          exact h0
        have h2 : (insert_sorted x (z :: zs)) ≠ [] := by
          cases (z :: zs) with
          | nil => unfold insert_sorted; simp
          | cons _ _ =>
            unfold insert_sorted
            split
            . simp
            simp
        have h3 : y ≤ (insert_sorted x (z :: zs)).head h2 := by
          sorry
        unfold sorted
        unfold insert_sorted
        -- i give up at this point
        sorry
