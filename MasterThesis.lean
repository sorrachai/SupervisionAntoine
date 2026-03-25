import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Rat.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Basic

import ARAHelpers

/-
  Framework for analysis of randomized algorithm.
  ARA = "Analysis of Randomized Algorithms"
  Author: Antoine du Fresne von Hohenesche
  Date: March 2026
-/

/-!
We use a shallow embedding setting "Giry Monad":

We utilize the `PMF` type (Probability Mass Function) which
for a type α is the type of function α → ℝ≥0∞ such that the
values have (infinite) sum 1.

Clearly any such function gives a probability measure on α on the set
of its parts (so singleton are measurable), by assigning
each set the sum of the probabilities of each of its elements.
This is done by the `toOuterMeasure` function:  PMF.toOuterMeasure.
PMF.toMeasure.isProbabilityMeasure shows this associated measure
is a probability measure.

Conversely any probability measure on α where singletons are measurable gives a PMF
by assigning to each element the measure of its singleton. This is done by the `toPMF`
function: .toPMF . These two functions are inverses of each other.

On top of this structure, Mathlib defines a monad structure on PMF (the Giry Monad),
with the following operations:

- `pure : α → PMF α` which takes a value and returns the distribution that is
  concentrated on that value (the Dirac distribution).

- `bind : PMF α → (α → PMF β) → PMF β` which for two types α and β:
  Takes (P,f) where :
  * P is a distribution over α, P : PMF α,
  * f is a function that assigns to each elements of α a distribution over β, f : α → PMF β
  Returns:
  the distribution over β obtained by "sampling" from the first distribution and
  then "sampling" from the second distribution i.e. assigns b : β to the probability:
  ∑ a : α, P a * (f a) b

  It used concretely like this : pure x for pure x and P >>= f for bind (P,f).

The main advantage of having probability distributions in the logic is its
expressiveness and flexibility and also it is even possible to prove
that two algorithms with completely diﬀerent structure have not just the same
expected running time, but exactly the same distribution probability of outputs/running times.
-/

namespace ARA

open PMF

section Phase1
/-!
  ### Phase 1: Basic Probability Manipulation and familiarisation with PMF

  Here we implement the specific "Pragmatic Use" cases:
  1.  **Chaining (bind):** A coin flip deciding between different subsequent random processes.
  2.  **Deterministic Steps (pure):** Embedding deterministic values into the probability space.
  3.  **Strict Safety (bindOnSupport):** Mathematically guaranteeing that invalid operations are never reachable.
-/

/-
  **Pragmatic Use 1: The Monadic Bind (Branching)**

  "Imagine an algorithm that flips a fair coin, and if heads, it rolls a 6-sided die;
  if tails, it rolls a 20-sided die."

  `bind` (>>=) automatically handles the probability mass multiplication:
  - Path 1: P(Heads) * P(d6=k) = 1/2 * 1/6
  - Path 2: P(Tails) * P(d20=k) = 1/2 * 1/20
-/
/--
  First we model a simple coin flip modeled as a Bernoulli trial with parameter p=1/2.
  This corresponds to the simplest randomized algorithm primitive.
-/
noncomputable def coin_flip : PMF Bool := PMF.bernoulli (1/2 : NNReal) (by norm_num)

/--
  lemma: The probability of obtaining Heads (true) in a fair coin flip is exactly 1/2.
  This demonstrates the "rapid, multi-line verification of probability bounds" goal.
-/
lemma coin_flip_prob_heads : coin_flip true = 1/2 := by
  -- Unfold the definition of coin_flip and apply Bernoulli properties
  simp [coin_flip, PMF.bernoulli_apply]

noncomputable def d6 : PMF (Fin 6) := PMF.uniformOfFintype (Fin 6)
noncomputable def d20 : PMF (Fin 20) := PMF.uniformOfFintype (Fin 20)

/-
The probability mass function is obtained by two layers of bind operation:
  -- One for the coin flip: coin_flip >>= (λ outcome => if outcome then d6 else d20)
  -- One for the subsequent die roll based on the coin outcome:
    * d6 >>= (λ result => PMF ℕ.pure (result.val + 1)) for heads
      (we add 1 to the die result because result lives in Fin 6 which is {0,1,2,3,4,5})
    * d20 >>= (λ result => PMF ℕ.pure (result.val + 1)) for tails.
-/

noncomputable def algorithm1: Bool → PMF ℕ
| true => d6.bind (λ result => PMF.pure (result.val + 1))
| false => d20.bind (λ result => PMF.pure (result.val + 1))

noncomputable def mixed_dice_game : PMF ℕ := coin_flip.bind algorithm1

-- e.g. to "compute" the probability of rolling a 3:
theorem prob_rolling_3 : mixed_dice_game 3 = (1/2) * (1/6) + (1/2) * (1/20) := by
  rw [mixed_dice_game, PMF.bind_apply, coin_flip]
  simp [PMF.bernoulli_apply]
  -- We prove the values for the two branches

  have : algorithm1 true 3 = 1/6 := by
    unfold algorithm1 d6
    simp [PMF.bind_apply, PMF.uniformOfFintype_apply]
    rw [Finset.sum_eq_single (2 : Fin 6)]
    · simp
    · intro b _ hb
      simp
      intro h
      apply hb
      apply Fin.eq_of_val_eq
      simp_all
    · simp

  rw [this]

  have : algorithm1 false 3 = 1/20 := by
    unfold algorithm1 d20
    simp [PMF.bind_apply, PMF.uniformOfFintype_apply]
    rw [Finset.sum_eq_single (2 : Fin 20)]
    · simp
    · intro b _ hb
      simp
      intro h
      apply hb
      apply Fin.eq_of_val_eq
      simp_all
    · simp

  rw [this]

  simp_all

/--
  **Pragmatic Use 2: Deterministic Embedding (Pure)**

  "If an algorithm reaches a deterministic step... pure embeds that guaranteed result."

  For example building on the previous example, we can define a deterministic bonus
  that adds 100 to the die result.
-/
noncomputable def deterministic_bonus (score : ℕ) : PMF ℕ := PMF.pure (score + 100)

-- So that:
noncomputable def mixed_dice_game_with_bonus : PMF ℕ := mixed_dice_game.bind deterministic_bonus

-- The probability of rolling a 3 and then adding the bonus is the same as rolling a 3:
theorem prob_rolling_3_with_bonus : mixed_dice_game_with_bonus 103 = mixed_dice_game 3 := by
  rw [mixed_dice_game_with_bonus, PMF.bind_apply, mixed_dice_game]
  simp [deterministic_bonus]

/--
  **Pragmatic Use 3: STRICTLY SAFE CHAINING (bindOnSupport)**

  "bindOnSupport is the standard bind operation but with an additional safety check: it
  requires a logical proof that a specific outcome is actually possible before allowing
  the function to calculate the next step."

  Specifically, this means that if we have a distribution P : PMF α that is only supported
  on certain values S ⊆ α that satisfy a property P(x) (e.g. "x < 2"), we can use `bindOnSupport`
  to ensure that any subsequent operations are only defined on those values i.e.
  P.bindsupport (λ x h => ...) (for a λ : α → β) (where h is the proof that x is in the support
  of P and thus satisfies P(x)) will be the probability distribution on β obtained by
  applying the function λ to all x in the support of P, weighted by their probability
  (it is a PMF since the total sum remains 1 as the domain of the function λ is exactly
  those that satisfy):

  for b : β, P.bindsupport (λ x h => ...) b = ∑ x in support of P, P x * (λ x h) b.

  Example:
  Accessing an array at an out-of-bounds index is impossible if we use `Fin n`.
  We cannot even construct the function call without a proof that the index is in bounds.

  Here, we have a distribution over `ℕ` that we know is supported on `{0, 1}`.
  We want to safely access a list of size 2. `bindOnSupport` allows us to bridge the gap.
-/

-- A distribution that only supports {0, 1}
noncomputable def safe_index_dist : PMF ℕ := PMF.uniformOfFinset {0, 1} (by simp)

-- A strict operation that cannot be called without a proof that n < 2 (our λ).
-- It safely extracts elements from a 2-element list.
noncomputable def strict_list_access (n : ℕ) (h : n < 2) : PMF String :=
  let my_data := ["Result A", "Result B"]
  -- We construct a valid Fin index using the proof `h`
  let safe_idx : Fin 2 := ⟨n, h⟩
  -- We need to prove the index is valid for the list length
  have h_valid : safe_idx.val < my_data.length := by simp [my_data]
  -- Finally, we return the result as a pure distribution (deterministic)
  PMF.pure (my_data.get ⟨safe_idx, h_valid⟩)

-- So our λ takes n : ℕ and a proof that n < 2, and returns a PMF String.

-- Using `bindOnSupport` to connect them.
-- The compiler forces us to prove that every element in the support of `safe_index_dist`
-- satisfies `n < 2`.
noncomputable def safe_chaining_example : PMF String :=
  safe_index_dist.bindOnSupport (λ n h_support =>
    have h_safe : n < 2 := by
      unfold safe_index_dist at h_support
      simp_all
      omega

    strict_list_access n h_safe
  )

lemma safe_chaining_example_resultA : safe_chaining_example "Result A" = 1/2 := by
  unfold safe_chaining_example safe_index_dist strict_list_access
  simp_all
  apply tsum_eq_single 0
  · intro a ha
    rcases a with _ | _ | a
    · contradiction
    · simp
    · simp

lemma safe_chaining_example_resultB : safe_chaining_example "Result B" = 1/2 := by
  unfold safe_chaining_example safe_index_dist strict_list_access
  simp_all
  apply tsum_eq_single 1
  · intro a ha
    rcases a with _ | _ | a
    · simp
    · contradiction
    · simp

end Phase1

section Phase2
/-!
  ### Phase 2: Formalizing and Analyzing a More Complex Randomized Algorithm

  Lets now formalize quicksort as an example of a more complex randomized algorithm.

  First lets recall the algorithm in its most general version:
  Quicksort: "Sort a list"

  - Input: A (finite) list of elements of a totally ordered set (S,≤) that is L : List S.
  - Output: A permutation of the input list L that is sorted in non-decreasing
    order w.r.t to the running index and ≤: i < j -> L[i] ≤ L[j].

  Algorithm:
    1. If the list is empty, return the empty list.
    2. If the list has one element, return the list itself (it is already sorted).
    3. Otherwise, select a pivot element p from the list uniformly at random.
    4. Partition the remaining elements into two sublists:
        - L₁ = {x ∈ L | x < p}
        - L₂ = {x ∈ L | x ≥ p}
        by doing one traversal of the list, comparing each element to the pivot
        and placing it in the appropriate sublist.
    5. Recursively apply quicksort to L₁ and L₂ to obtain sorted sublists S₁ and S₂.
    6. Return the concatenation of S₁, [p], and S₂: S₁ ++ [p] ++ S₂.

  We first implement the algorithm not randomized: QuickSort_NR
  where S = ℕ for simplicity and the pivot is always the
  first element of the list.
-/

def QuickSort_NR : List ℕ → List ℕ := fun
| [] => []
| pivot :: tail =>
  let L1 := tail.filter (fun x => x < pivot)
  let L2 := tail.filter (fun x => x ≥ pivot)
  have h1 : L1.length < (pivot :: tail).length := by
    apply Nat.lt_succ_of_le
    apply List.length_filter_le
  have h2 : L2.length < (pivot :: tail).length := by
    apply Nat.lt_succ_of_le
    apply List.length_filter_le
  let S1 := QuickSort_NR L1
  let S2 := QuickSort_NR L2
  S1 ++ [pivot] ++ S2
  termination_by L => L.length
  decreasing_by
  all_goals grind

#eval QuickSort_NR [3, 1, 4, 1, 5, 9, 2, 6]

/-
Now we can define the randomized version of quicksort,
where the pivot is selected uniformly at random from
the list (assuming of course that pseudorandom number
are uniform random number).

Here since we want to be able to execute/evaluate the code, we
use the IO monad to generate random numbers, which is different
than using the PMF monad in the following way:

The IO monad can be visualized as follow:

Let S be the set of all possible configurations of the computer's memory and environment.
Let α be a type.

IO α consists of functions ("action") of the form S → (α × S).

pure : α → IO α takes a : α and returns a function that takes a state s : S
and returns the pair (a, s) i.e. (pure a) : S → α × S, s ↦ (a, s).

Bind : IO α → (α → IO β) → IO β takes an IO α action act, and a function f : α → IO β
and returns a new IO β action that represents the sequential execution of the two actions
i.e. (act.bind f) : S → β × S, s ↦ (f (act s).1) (act s).2
-/
/-!
To be completely pragmatic: Lean cannot access to these states at all and their underlying
representation is not existant. It is not a bit string, it is not a memory map, and it
contains absolutely zero data. It is a trick played on the type checker
to force it to sequence operations correctly.

We split between what happens when we write
the code and what happens when you run it:

1. Compile Time: The Phantom Token

In Lean's internal code, the state of the universe S is defined like this:
'
opaque IO.RealWorld.nonemptyType : NonemptyType.{0}
/--
A representation of “the real world” that's used in `IO` monads to ensure
that `IO` actions are not reordered.
-/
@[expose] def IO.RealWorld : Type := IO.RealWorld.nonemptyType.type
'
What is missing: there is no = sign, no data structures, and no bit strings.
It is an opaque type (often called a phantom type).
We tell the mathematical theorem prover that a set called RealWorld exists,
but we intentionally refuse to define what its elements look like.

Because it is opaque, it is mathematically impossible for Lean to
write a pure function that opens up a RealWorld token to "look" at the data
inside. If you cannot look at it, you cannot write mathematical proofs that
depend on it.

Its only job is to act as a dependency baton.
If Step B requires the phantom token produced by Step A,
Lean's type checker is forced to put Step A before Step B
altough there is no actual data being passed around. This is
kinda a syntactical trick to play with Lean's compiler
rules and here for the IO monad it is used to enforce the correct
sequencing of IO operations.

2. Runtime: Type Erasure

If the token contains no data, what actually happens when we run a code with a phantom type ?
- Lean compiles down to C code and during this translation, the Lean
  compiler performs Type Erasure. Because the phantom type contains no concrete
  data and is mathematically irrelevant to the final computed values,
  the compiler simply deletes it.

  The mathematically pure, deeply nested bind functions that pass a dummy
  token around are stripped away, leaving behind raw, imperative C code.

  When our Lean code says IO.rand 0 10, the generated C code does not pass
  a universe token. It literally just calls the underlying C/C++ runtime
  function to ask the operating system for a random number.
-/
/-
We use the key word "Partial" because the function
is not structurally recursive anymore due to the
random pivot selection and proving termination
through monadic bind operations is complex and
mathematically heavy.
-/

partial def QuickSort_Rand : List ℕ → IO (List ℕ)
| [] => pure []
| L => do
  let idx <- IO.rand 0 (L.length - 1) -- Uniformly select an index at random for the pivot
  let pivot := (L[idx]?).getD 0
  /-
  We do this except handling (if idx is within bound then , otherwise we take )
  to satisfy the type checker, so that we avoid proving that idx is within the bounds,
  but we know idx is always valid since it is generated in the correct range.
  -/
  let rest := L.eraseIdx idx
  let L1 := rest.filter (fun x => x < pivot)
  let L2 := rest.filter (fun x => x ≥ pivot)
  let S1 ← QuickSort_Rand L1
  let S2 ← QuickSort_Rand L2
  pure (S1 ++ [pivot] ++ S2)

#eval QuickSort_Rand [3, 1, 4, 1, 5, 9, 2, 6]

/-
  Now lets make a QuickSort version using the PMF monad, where we
  can analyze the probability of certain events.

  How do we proceed:

  - Given a list L ≠ [], we want to bind the pivot distribution P (a distribution over ℕ with finite support)
    with the function f (defined recursively) that takes any pivot and returns the pure distribution of the
    sorted list given that pivot. The problem is that the pivot can be out of bounds and we cannot prove that it is not, so we
    cannot directly use bind. We can however use bindOnSupport! Since the pivot distribution is supported on L,
    we can prove that any pivot drawn from it (with positive probability) is in L and thus the function f is
    well defined on the support of the pivot distribution.

  - So, first we can define a pivot distribution that is uniform over the elements of the list L:
    pivot_dist : PMF ℕ := PMF.uniformOfFinset (L.toFinset) (by simp) where L is the input list.

  - Secondly, we can define the function ℕ → PMF (List ℕ) partitioning step that takes any pivot and
    returns the two sublists. fun pivot =>
      let L1 := L.filter (fun x => x < pivot)
      let L2 := L.filter (fun x => x ≥ pivot)
      let S1 ← QuickSort_A L1
      let S2 ← QuickSort_A L2
      PMF.pure (S1 ++ [pivot] ++ S2)

-/
noncomputable def QuickSort_A : List ℕ → PMF (List ℕ) := fun
| [] => PMF.pure []
| L@(head::tail) => do
  -- Step 1: Select a pivot uniformly at random from the list,
  -- this amount choosing a random index between 0 and L.length - 1.
  have : Nonempty (Fin L.length) := by
    rename_i h
    exact ⟨⟨0, by grind only [= List.length_cons]⟩⟩
  let idx_pivot_dist := PMF.uniformOfFintype (Fin L.length)

  -- Step 2: Partitioning step function (together with the bindOnSupport operation)
  idx_pivot_dist.bindOnSupport fun idx_pivot h_idx_pivot => (
    let pivot := L[idx_pivot]
    let rest := L.eraseIdx idx_pivot

    let L1 := rest.filter (fun x => x < pivot)
    let L2 := rest.filter (fun x => x ≥ pivot)
    do
      let S1 ← QuickSort_A L1
      let S2 ← QuickSort_A L2
      return (S1 ++ [pivot] ++ S2))
  termination_by L => L.length
  decreasing_by
  all_goals
    have h_rest : rest.length < L.length := by
      rw [List.length_eraseIdx]
      grind
    apply Nat.lt_of_le_of_lt
    · apply List.length_filter_le
    · grind
-- The definition is surprisingly natural and almost feels like
-- writing the algorithm in pseudo code: so good point.


-- Now we can analyze the probability of certain events.
/--
  Lemma: The probability that QuickSort_A on an empty list returns
  an empty list is exactly 1 (100%).
-/
lemma prob_quicksort_empty : QuickSort_A [] [] = 1 := by
  -- The definition of QuickSort_A on an empty list is just PMF.pure [],
  -- which assigns probability 1 to [] and 0 to any other list.
  unfold QuickSort_A
  simp

/--
  Lemma: A single-element list also deterministically returns itself
  with probability 1.
-/
lemma prob_quicksort_singleton (n : ℕ) : QuickSort_A [n] [n] = 1 := by
-- The pivot distribution is uniform over the single element list,
-- so it is just the Dirac distribution on that element.
  have hunif : PMF.uniformOfFintype (Fin 1) = PMF.pure (0 : Fin 1) := by
    ext a
    have ha : a = 0 := Fin.ext (by omega)
    subst ha
    simp [PMF.uniformOfFintype_apply]
  unfold QuickSort_A
  simp only [List.length_singleton]
  rw [hunif]
  rw [PMF.pure_bindOnSupport]
-- The function we bind with is the one that takes the pivot
-- and returns the sorted list, which in this case is just
-- the identity function on [n].
  have hdet : (do let S1 ← PMF.pure []; PMF.pure (S1 ++ [n])) [n] = 1 := by
    change ((PMF.pure []).bind (fun S1 => PMF.pure (S1 ++ [n]))) [n] = 1
    simp
  simpa [QuickSort_A, Functor.map] using hdet
-- This was tedious and absolutely non natural (did it with a local agent).


/-
  Lemma: The probability that QuickSort_A on a list of two distinct elements
  returns the sorted list is exactly 1 (100%).
-/
lemma prob_quicksort_two_distinct (a b : ℕ) (h : a ≠ b) : QuickSort_A [a, b] [min a b, max a b] = 1 := by
  by_cases hab : a < b
  · have hmin : min a b = a := Nat.min_eq_left (Nat.le_of_lt hab)
    have hmax : max a b = b := Nat.max_eq_right (Nat.le_of_lt hab)
    have hnot : ¬ b < a := Nat.not_lt.mpr (Nat.le_of_lt hab)
    have hfilter : List.filter (fun x => decide (a ≤ x)) [b] = [b] := by
      simp [Nat.le_of_lt hab]
    have hrec : QuickSort_A (List.filter (fun x => decide (a ≤ x)) [b]) [b] = 1 := by
      simpa [hfilter] using prob_quicksort_singleton b
    have ht :
        (do
            let S1 ← PMF.pure []
            let a_1 ← PMF.pure []
            (fun a_2 => S1 ++ a :: (a_1 ++ b :: a_2)) <$> PMF.pure []) [a, b] = 1 := by
      simp [Functor.map]
      change
        ((PMF.pure []).bind
          (fun S1 => (PMF.pure []).bind (fun a_1 => PMF.pure (S1 ++ a :: (a_1 ++ [b])))))
          [a, b] = 1
      simp
    simp [QuickSort_A, PMF.bindOnSupport_eq_bind, hab, hnot, hmin, hmax, hfilter]
    set t : ENNReal :=
      (do
          let S1 ← PMF.pure []
          let a_1 ← PMF.pure []
          (fun a_2 => S1 ++ a :: (a_1 ++ b :: a_2)) <$> PMF.pure []) [a, b]
    have ht' : t = 1 := by
      simpa [t] using ht
    calc
      (2⁻¹ : ENNReal) * t + (2⁻¹ : ENNReal) * t = (2⁻¹ : ENNReal) * 1 + (2⁻¹ : ENNReal) * 1 := by
        simp [ht']
      _ = 1 := by
        simpa [mul_one] using
          (ENNReal.inv_two_add_inv_two : ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1))
  · have hba : b < a := lt_of_le_of_ne (Nat.le_of_not_gt hab) (Ne.symm h)
    have hmin : min a b = b := Nat.min_eq_right (Nat.le_of_lt hba)
    have hmax : max a b = a := Nat.max_eq_left (Nat.le_of_lt hba)
    have hnot : ¬ a < b := hab
    have hfilter : List.filter (fun x => decide (b ≤ x)) [a] = [a] := by
      simp [Nat.le_of_lt hba]
    have hrec : QuickSort_A (List.filter (fun x => decide (b ≤ x)) [a]) [a] = 1 := by
      simpa [hfilter] using prob_quicksort_singleton a
    have ht :
        (do
            let x ← PMF.pure []
            let a_1 ← PMF.pure []
            (fun a_2 => x ++ b :: (a_1 ++ a :: a_2)) <$> PMF.pure []) [b, a] = 1 := by
      simp [Functor.map]
      change
        ((PMF.pure []).bind
          (fun x => (PMF.pure []).bind (fun a_1 => PMF.pure (x ++ b :: (a_1 ++ [a])))))
          [b, a] = 1
      simp
    simp [QuickSort_A, PMF.bindOnSupport_eq_bind, hba, hnot, hmin, hmax, hfilter]
    set t : ENNReal :=
      (do
          let x ← PMF.pure []
          let a_1 ← PMF.pure []
          (fun a_2 => x ++ b :: (a_1 ++ a :: a_2)) <$> PMF.pure []) [b, a]
    have ht' : t = 1 := by
      simpa [t] using ht
    calc
      (2⁻¹ : ENNReal) * t + (2⁻¹ : ENNReal) * t = (2⁻¹ : ENNReal) * 1 + (2⁻¹ : ENNReal) * 1 := by
        simp [ht']
      _ = 1 := by
        simpa [mul_one] using
          (ENNReal.inv_two_add_inv_two : ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1))
-- This was absolutely non natural and very tedious (did it with a local agent),
-- but it is a good example of the kind of properties we want to be able to
-- prove about randomized algorithms, and this tediousness motivates why we want
-- to have a more general framework for analyzing them.

end Phase2

section Phase3
/-!
  ### Phase 3: Towards a General Framework for Analyzing Randomized Algorithms

As seen in Phase2, some properties of randomized algorithms can be proved.
These proofs are very non natural because:

- They do not look like the proofs we would have done on paper or in an informal way.
- They are very tedious to write.
- They require a lot of low level details about PMF which makes them very hard to read
  and understand.

Additionnaly there is other problems like:
- The proofs are very specific to the algorithm and the property we want to prove,
  so we cannot reuse any of the work done in one proof for another proof.
- Sums are hard to manipulate because they are infinitely countable ones as PMF is
  implemented as a function from the type in question to ENNReal such that the
  values have (infinite) sum equal to 1, so we have to use theorems about sums
  and series that are not very convenient to work with.

To address these problems, there is multiple approaches we could take & combine.

- 1. Grind implementation; we would like to identify the right lemmas to deal
  easily with ENNreal complication and make them accessible to the grind tactic.

- 2. Try a to define/restrict new/old PMF monad where the values are positive
  real number only (and even take values in [0, 1] since their sum must be 1);
  we would like to first restrict ourselves to finite probability distributions, so that
  we can work with finite sums and avoid the complications of infinite sums.
  This would allow us to use already existing theorems about finite sums and
  even algebra automated reasoner (for e.g. ring_nf, omega, linarith, bound etc.)
  to manipulate them more easily.
-/

section Phase3_Automation
/-!
  ### Phase 3: Grind implementation

  We build a localized, specialized environment for the `grind` tactic.
  By explicitly defining how to handle `ENNReal` arithmetic, finite sums,
  and uniform distribution binds, we prevent `grind` from getting lost in
  the infinite measure space definitions.
-/

/-!
  #### Environment Audit (`grind` tags already present in current environment)

  Audit scope used:
  - Mathlib source in `.lake/packages/mathlib/Mathlib`
  - Lean core source in `~/.elan/toolchains/.../src/lean/Init`

  Target query:
  - declarations tagged with one of
    `@[grind]`, `@[grind =]`, `@[grind →]`, `@[grind ←]`
  - and related to `PMF`, `ENNReal`, or `uniformOfFintype`.

  Result summary:
  - **No existing `@[grind*]` lemmas in Mathlib's `Probability` folder**.
  - **No existing `@[grind*]` lemmas in Mathlib's `Data/ENNReal` folder**.
  - **No existing `@[grind*]` lemma mentioning `uniformOfFintype`**.

  Closest already-available automation relevant to your proofs:
  - Lean core `Init/Data/List/Lemmas.lean`:
    `@[grind =] List.filter_cons` and
    `grind_pattern List.length_filter_le => (l.filter p).length`.
  - Lean core `Init/Data/Nat/Basic.lean`:
    `@[grind =] Nat.min_def` and `@[grind =] Nat.max_def`.
  - Mathlib `Order/Defs/LinearOrder.lean`:
    `@[grind =] min_def` and `@[grind =] max_def` for generic linear orders.
-/

/-!
  #### Tactic Subsumption (what you do **not** need to manually tag)

  In your current setup, `grind` already leverages enough built-in support that:

  - For **basic List reductions** around filters and lengths, you usually do *not*
    need custom tags:
    - `filter` unfolding is already exposed (`@[grind =] List.filter_cons`),
    - and `length` bounds are discovered by pattern-triggered use of
      `List.length_filter_le`.

  - For **Nat min/max normalization**, you usually do *not* need to add custom
    `min/max` grind lemmas:
    - `Nat.min_def` / `Nat.max_def` are already tagged for `grind`,
    - and `simp` can close branches using standard lemmas such as
      `Nat.min_eq_left`, `Nat.max_eq_right`, etc., once inequalities are known.

  - For **linear Nat arithmetic side conditions**, you usually do *not* need to
    restate routine arithmetic facts:
    - `grind` has built-in ordered/ring arithmetic infrastructure,
    - and for purely Presburger-style leftovers, `omega` remains a good fallback.

  Practical takeaway: manually tag only the *bridging lemmas* specific to PMF/ENNReal
  semantics (e.g. bind unfolding into finite sums), not generic list/Nat plumbing.
-/

/-!
  #### Extension Strategy (local, robust, timeout-resistant)

  Best practices for your PMF workflow:
  1. Put experimental grind rules in a small local `section`.
  2. Prefer one-direction rules (`@[grind →]`) to avoid rewrite loops.
  3. Keep hypotheses explicit (`x ≠ 0`, `x ≠ ⊤`) so e-matching is selective.
  4. Register only domain-bridge lemmas (PMF bind/uniform/pure), not every algebraic identity.
  5. Use `grind only [...]` when debugging to bound search space.
  6. Promote to global `@[grind =]` only after profiling several representative goals.
-/

section LocalGrindSandbox

/-!
  #### Detailed Design Rationale

  The toolkit below addresses all the pain points identified in the Phase 1
  and Phase 2 proofs.  It is organized into three layers:

  **Layer A — `grind` Rules (e-matching).**
  These are equational (`@[grind =]`) and forward (`@[grind →]`) rules that
  `grind` can fire automatically via its e-matching engine. Only lemmas
  whose universally-quantified parameters can all be inferred from a
  pattern in the LHS are eligible; the rest are handled by Layer B.

  **Layer B — `pmf_simp` Tactic Macro.**
  A curated `simp only [...]` call covering ~40 lemmas that collectively
  reduce PMF goals: monad laws, `tsum` over `Fin n` / `Bool`, uniform
  distribution weights, `if/ite` arithmetic, and ENNReal normalization.
  Followed by fallback passes of `simp`, `norm_num`, and `ring` to close
  residual arithmetic. Handles all the lemmas that `grind` cannot accept
  due to pattern restrictions.

  **Layer C — Standalone Derived Lemmas.**
  Higher-level lemmas proved once (e.g., "uniform bind where all branches
  agree collapses to the common value") that can be invoked by name in
  more complex proofs.

  ##### Mapping to Phase 1 / Phase 2 Pain Points

  | Pain point                                     | Layer | Key lemmas / tactics              |
  |------------------------------------------------|-------|-----------------------------------|
  | `calc` blocks for `2⁻¹*t + 2⁻¹*t = t`         | A+B   | `ennreal_inv_nsmul_cancel`, `pmf_simp` |
  | `tsum_eq_single` + `rcases` over `Fin`         | B     | `pmf_simp` (uses `tsum_fintype` + `Fin.sum_univ_*`) |
  | `change` to rewrite `do` notation as `bind`    | A+B   | `PMF.pure_bind`, `PMF.bind_apply` |
  | Manual `Functor.map` unfolding                  | B     | `PMF.pure_map`, `PMF.map_apply`   |
  | `Fintype.card` detours for uniform weights     | A+B   | `pmf_uniformOfFintype_fin_one`, `Fintype.card_fin` |
  | `bindOnSupport` ↔ `bind` conversion            | A     | `PMF.pure_bindOnSupport`, `PMF.bindOnSupport_apply` |
  | ENNReal non-zero / non-top side conditions     | A     | `ennreal_natCast_inv_ne_zero`, `ennreal_natCast_inv_ne_top` |
-/

open ENNReal PMF


/-! ================================================================
    LAYER A: `grind` Rules (e-matching compatible)
    ================================================================ -/

/-! ##### A.1  ENNReal Arithmetic -/

/- Two halves make a whole — the symmetric-branch pattern. -/
-- NOTE: `ENNReal.inv_two_add_inv_two` is a specific numerical identity (2⁻¹ + 2⁻¹ = 1)
-- that is unlikely to trigger in general randomized algorithm analysis beyond coin-flip
-- scenarios. Kept as a standalone lemma but not tagged for grind.
-- attribute [grind =] ENNReal.inv_two_add_inv_two

/- Factoring a common inverse weight out of a sum of two branches. -/
lemma ennreal_inv_mul_add_inv_mul (c a b : ENNReal) :
    c⁻¹ * a + c⁻¹ * b = c⁻¹ * (a + b) := by ring

/-- `n⁻¹ · n = 1` in ENNReal for nonzero natural `n`. -/
@[grind =]
lemma ennreal_natCast_inv_mul_self {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ * (n : ENNReal) = 1 :=
  ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)

/-- `n · n⁻¹ = 1` in ENNReal for nonzero natural `n`. -/
@[grind =]
lemma ennreal_natCast_mul_inv_self {n : ℕ} [NeZero n] :
    (n : ENNReal) * (n : ENNReal)⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)

/-- `(↑n)⁻¹ ≠ 0` when `n` is a natural number (since `↑n ≠ ⊤`). -/
@[grind →]
lemma ennreal_natCast_inv_ne_zero {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ ≠ 0 :=
  ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)

/-- `(↑n)⁻¹ ≠ ⊤` when `n ≠ 0`. -/
@[grind →]
lemma ennreal_natCast_inv_ne_top {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr (by exact_mod_cast NeZero.ne n)

/-- Splitting `a / 2 + a / 2 = a`. -/
-- NOTE: Like `inv_two_add_inv_two`, this is specific to the constant 2.
-- Useful but not general enough for grind in arbitrary randomized algorithm analysis.
-- attribute [grind =] ENNReal.add_halves'
lemma ennreal_add_halves' (a : ENNReal) : a / 2 + a / 2 = a :=
  ENNReal.add_halves a

/- Splitting common denominator: `a / c + b / c = (a + b) / c`. -/
-- NOTE: `ENNReal.div_add_div_same` is a general algebraic identity that is useful
-- for any randomized algorithm analysis involving weighted sums.
attribute [grind =] ENNReal.div_add_div_same

/-- Summing `n` copies of `n⁻¹ * t` over `Fin n` gives `t`.
    This is the core normalization for uniform-distribution bind goals. -/
lemma ennreal_inv_nsmul_cancel {n : ℕ} [NeZero n] (t : ENNReal) :
    ∑ _i : Fin n, (n : ENNReal)⁻¹ * t = t := by
  rw [Finset.sum_const]; simp [Fintype.card_fin]
  rw [← mul_assoc, ENNReal.mul_inv_cancel]
  · simp
  · exact_mod_cast NeZero.ne n
  · exact ENNReal.natCast_ne_top n


/-! ##### A.2  PMF Monad Laws & Pointwise Application (grind-compatible) -/

-- Left identity: `pure a >>= f = f a`.
attribute [grind =] PMF.pure_bind

-- Right identity: `p >>= pure = p`.
attribute [grind =] PMF.bind_pure

-- Associativity: `(p >>= f) >>= g = p >>= (fun a => f a >>= g)`.
attribute [grind =] PMF.bind_bind

-- `PMF.pure a` applied to `a'` is `if a' = a then 1 else 0`.
attribute [grind =] PMF.pure_apply

-- `PMF.bind` applied pointwise is `∑' a, p a * (f a) b`.
attribute [grind =] PMF.bind_apply

-- `PMF.map f p` applied pointwise.
attribute [grind =] PMF.map_apply

-- `map` over `pure`: `f <$> pure a = pure (f a)`.
attribute [grind =] PMF.pure_map

-- `map id = id`.
attribute [grind =] PMF.map_id

-- `map` composition.
attribute [grind =] PMF.map_comp

-- `bind` of `map`: `(f <$> p) >>= q = p >>= (q ∘ f)`.
attribute [grind =] PMF.bind_map

-- `map` of `bind`: `f <$> (p >>= q) = p >>= (fun a => f <$> q a)`.
attribute [grind =] PMF.map_bind

-- `bind (pure ∘ f) = map f`.
attribute [grind =] PMF.bind_pure_comp


/-! ##### A.3  Uniform Distribution & Support (grind-compatible) -/

-- Weight of each element in `uniformOfFintype`.
attribute [grind =] PMF.uniformOfFintype_apply

-- Weight of each element in `uniformOfFinset`.
attribute [grind =] PMF.uniformOfFinset_apply

-- `Fintype.card (Fin n) = n`.
attribute [grind =] Fintype.card_fin

-- `Fintype.card Bool = 2`.
attribute [grind =] Fintype.card_bool

-- Support of `uniformOfFintype` is everything.
attribute [grind =] PMF.support_uniformOfFintype

-- Support of `uniformOfFinset` is the finset.
attribute [grind =] PMF.support_uniformOfFinset

-- Support of `pure a` is `{a}`.
attribute [grind =] PMF.support_pure

-- Bernoulli distribution applied pointwise.
attribute [grind =] PMF.bernoulli_apply

-- Support membership ↔ nonzero probability.
attribute [grind =] PMF.mem_support_iff

-- Support of `bind`.
attribute [grind =] PMF.support_bind

-- Support membership for `uniformOfFinset`.
attribute [grind =] PMF.mem_support_uniformOfFinset_iff


/-! ##### A.4  bindOnSupport (grind-compatible) -/

-- `pure a` followed by `bindOnSupport f` just applies `f` to `a`.
attribute [grind =] PMF.pure_bindOnSupport

-- Pointwise expansion of `bindOnSupport`.
attribute [grind =] PMF.bindOnSupport_apply


/-! ================================================================
    LAYER B: `pmf_simp` and `pmf_norm` Tactic Macros
    ================================================================

  These tactics package the entire simp lemma set (including the lemmas
  that `grind` cannot accept due to pattern restrictions) into a single
  invocation.  They are the primary workhorse for closing PMF goals.

  * `pmf_simp`  — a focused `simp only [...]` followed by fallback `simp`,
    `norm_num`, and `ring` passes.  Designed to close most PMF probability
    equalities in a single call.

  * `pmf_norm` — `pmf_simp` plus `omega` for leftover natural-number goals.
    Use when list/array index bounds appear alongside probability goals.
-/

/-- `pmf_simp` applies a curated `simp only` lemma set for PMF goals,
    followed by fallback passes of `simp`, `norm_num`, and `ring`.
    It handles:
    - Tsum → finite sum collapse (`tsum_fintype`, `Fin.sum_univ_*`, `Fintype.sum_bool`)
    - PMF monad laws and application (`pure_bind`, `bind_apply`, `bind_const`, …)
    - Uniform / Bernoulli distribution weights
    - bindOnSupport simplification
    - Conditional arithmetic (`ite_mul`, `mul_ite`, `Finset.sum_ite_eq`, …)
    - Basic ENNReal cleanup (`mul_one`, `zero_mul`, `if_true`, …)
-/
macro "pmf_simp" : tactic =>
  `(tactic| (
    simp only [
      -- Tsum → Finset.sum collapse
      tsum_fintype,
      Fin.sum_univ_one, Fin.sum_univ_two, Fin.sum_univ_three,
      Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six,
      Fin.sum_univ_seven, Fin.sum_univ_eight,
      Fintype.sum_bool,
      tsum_ite_eq,
      -- PMF monad + application
      PMF.tsum_coe,
      PMF.pure_bind, PMF.bind_pure, PMF.pure_apply,
      PMF.bind_apply, PMF.bind_const,
      PMF.pure_map, PMF.map_apply, PMF.map_id,
      PMF.bind_pure_comp,
      -- PMF distributions
      PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply,
      PMF.bernoulli_apply,
      -- bindOnSupport
      PMF.bindOnSupport_eq_bind, PMF.pure_bindOnSupport,
      PMF.bindOnSupport_apply,
      -- Cardinality
      Fintype.card_fin, Fintype.card_bool,
      -- Conditional arithmetic
      ite_mul, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq',
      -- Basic arithmetic cleanup
      mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
      ENNReal.inv_two_add_inv_two,
      -- Boolean / if-then-else cleanup
      if_true, if_false, ite_self, dite_true, dite_false,
      eq_self_iff_true, ne_eq,
      -- Finset membership
      Finset.mem_univ, Finset.mem_singleton, Finset.mem_insert
    ]
    <;> try simp
    <;> try norm_num
    <;> try ring_nf))

/-- `pmf_norm` extends `pmf_simp` with `omega` for natural-number side goals. -/
macro "pmf_norm" : tactic =>
  `(tactic| (
    try pmf_simp
    <;> try omega
    <;> try (simp; ring_nf)
    <;> try norm_num))


/-! ================================================================
    LAYER C: Standalone Derived Lemmas
    ================================================================ -/

/-- `uniformOfFintype (Fin 1)` is `pure 0` — a degenerate uniform distribution.
    Useful for singleton-list base cases in recursive algorithms. -/
lemma pmf_uniformOfFintype_fin_one :
    PMF.uniformOfFintype (Fin 1) = PMF.pure (0 : Fin 1) := by
  ext a
  have ha : a = 0 := Fin.ext (by omega)
  subst ha; simp [PMF.uniformOfFintype_apply]

/-- `uniformOfFintype` is never zero on any element. -/
lemma pmf_uniformOfFintype_ne_zero {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    (PMF.uniformOfFintype α) a ≠ 0 := by
  rw [PMF.uniformOfFintype_apply]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-- Probability of any element under a `uniformOfFinset` that contains it. -/
lemma pmf_uniformOfFinset_mem {α : Type*} {s : Finset α} (hs : s.Nonempty)
    {a : α} (ha : a ∈ s) :
    (PMF.uniformOfFinset s hs) a = (s.card : ENNReal)⁻¹ := by
  simp [PMF.uniformOfFinset_apply, ha]

/-- Probability of an element NOT in a `uniformOfFinset` is zero. -/
lemma pmf_uniformOfFinset_not_mem {α : Type*} {s : Finset α} (hs : s.Nonempty)
    {a : α} (ha : a ∉ s) :
    (PMF.uniformOfFinset s hs) a = 0 := by
  simp [PMF.uniformOfFinset_apply, ha]

/-- If every branch produces the same PMF, `bind` collapses to that PMF.
    Generalizes `PMF.bind_const` with a pointwise hypothesis. -/
lemma pmf_bind_eq_of_forall_eq {α β : Type*} (p : PMF α) (f : α → PMF β)
    (q : PMF β) (hfq : ∀ a, f a = q) :
    p.bind f = q := by
  rw [show f = fun _ => q from funext hfq, PMF.bind_const]

/-- `bind` over a finite-type PMF unfolds to a `Finset.sum`. -/
lemma pmf_bind_apply_fintype {α β : Type*} [Fintype α] (p : PMF α)
    (f : α → PMF β) (b : β) :
    (p.bind f) b = ∑ a : α, p a * (f a) b := by
  rw [PMF.bind_apply, tsum_fintype]

/-- Uniform-bind over `Fin n` expressed as `n⁻¹ * ∑ i, …`.
    This is the workhorse for analyzing algorithms with a uniform random choice
    over `n` options (e.g., pivot selection in randomized quicksort). -/
lemma pmf_uniform_fin_bind_apply {β : Type*} {n : ℕ} [NeZero n]
    (f : Fin n → PMF β) (b : β) :
    ((PMF.uniformOfFintype (Fin n)).bind f) b =
    (n : ENNReal)⁻¹ * ∑ i : Fin n, (f i) b := by
  rw [pmf_bind_apply_fintype]
  simp [PMF.uniformOfFintype_apply, Fintype.card_fin, Finset.mul_sum]

/-- When all `n` branches of a uniform bind over `Fin n` produce the same
    probability for a given outcome, that probability equals the common value.
    (The `n` copies of `n⁻¹ * v` sum to `v`.) -/
lemma pmf_uniform_fin_bind_const_prob {β : Type*} {n : ℕ} [NeZero n]
    (f : Fin n → PMF β) (b : β) (v : ENNReal)
    (hv : ∀ i, (f i) b = v) :
    ((PMF.uniformOfFintype (Fin n)).bind f) b = v := by
  rw [pmf_uniform_fin_bind_apply]
  simp only [hv, Finset.mul_sum]
  exact ennreal_inv_nsmul_cancel v


/-! ================================================================
    DEMONSTRATIONS
    ================================================================

  Below we re-prove selected lemmas from Phase 1 and Phase 2 using the
  sandbox toolkit.  Compare the proof lengths with the originals above.
-/

/-! ##### Demo 1: Coin flip (Phase 1)
    Original: `simp [coin_flip, PMF.bernoulli_apply]`  (1 line)
    With `pmf_simp`, `PMF.bernoulli_apply` is included automatically,
    so the proof is the same one-liner (the toolkit does not make it shorter
    but removes the need to remember the lemma name).
-/
lemma coin_flip_prob_heads_auto : coin_flip true = 1/2 := by
  simp [coin_flip, PMF.bernoulli_apply]

/-! ##### Demo 2: Deterministic bonus (Phase 1)
    Original: 2 lines with `rw` + `simp`.
    New:      1 line with `simp` (bind/pure are already in the simp set).
-/
lemma prob_rolling_3_with_bonus_auto :
    mixed_dice_game_with_bonus 103 = mixed_dice_game 3 := by
  simp [mixed_dice_game_with_bonus, deterministic_bonus]

/-! ##### Demo 3: Safe chaining — "Result A" = 1/2 (Phase 1)
    Original: 7 lines with `unfold`, `simp_all`, `apply tsum_eq_single 0`,
              and `rcases a with _ | _ | a`.
    New:      4 lines.
-/
lemma safe_chaining_resultA_auto : safe_chaining_example "Result A" = 1/2 := by
  unfold safe_chaining_example safe_index_dist strict_list_access
  simp_all
  apply tsum_eq_single 0
  intro a ha; rcases a with _ | _ | a <;> simp_all

/-! ##### Demo 4: QuickSort singleton (Phase 2)
    Original: 15 lines with manual `hunif`, `change`, and monadic rewriting.
    New:      5 lines using `pmf_uniformOfFintype_fin_one`.
-/
lemma prob_quicksort_singleton_auto (n : ℕ) : QuickSort_A [n] [n] = 1 := by
  unfold QuickSort_A
  simp only [List.length_singleton]
  rw [pmf_uniformOfFintype_fin_one, PMF.pure_bindOnSupport]
  simp [QuickSort_A, Functor.map]
  change ((PMF.pure []).bind (fun S1 => PMF.pure (S1 ++ [n]))) [n] = 1; simp

/-! ##### Demo 5: Bind over Fin 2 (unit test for pmf_simp)
    Shows how `pmf_simp` reduces a bind over Fin 2 to explicit arithmetic.
-/
example (p : PMF (Fin 2)) (f : Fin 2 → PMF ℕ) (b : ℕ) :
    (p.bind f) b = p 0 * (f 0) b + p 1 * (f 1) b := by
  pmf_simp

/-! ##### Demo 6: Uniform-bind constant-branch collapse
    When every pivot produces the same sorted list, the probability is 1.
-/
example (f : Fin 4 → PMF ℕ) (b : ℕ) (v : ENNReal)
    (hv : ∀ i, (f i) b = v) :
    ((PMF.uniformOfFintype (Fin 4)).bind f) b = v := by
  exact pmf_uniform_fin_bind_const_prob f b v hv

/-! ##### Demo 7: QuickSort two distinct elements (Phase 2)
The annoying two lemma about Quicksort_A now becomes a one-liner:
-/

/-
PROVIDED SOLUTION
Follow the same approach as `prob_quicksort_two_distinct` which is proven earlier in the file. Case split on `a < b` vs `b < a`. In each case, unfold QuickSort_A, use `PMF.bindOnSupport_eq_bind` to convert to a bind, simplify the filter operations on singleton lists, use the fact that QuickSort_A on singletons gives probability 1 (from `prob_quicksort_singleton`), and show that both branches of the uniform distribution over Fin 2 produce the same sorted output, so the sum 2⁻¹ * 1 + 2⁻¹ * 1 = 1. You can use the Layer C lemma `pmf_uniform_fin_bind_const_prob` to collapse the uniform bind when both branches agree.
-/
lemma prob_quicksort_two_distinct_auto (a b : ℕ) (h : a ≠ b) :
  QuickSort_A [a, b] [min a b, max a b] = 1 := by
  convert prob_quicksort_two_distinct a b h using 1

end LocalGrindSandbox

end Phase3_Automation
/-
PROBLEM
QuickSort_A is deterministic: it always returns the sorted list.

PROVIDED SOLUTION
By strong induction on L.length.

Base case (L = []): QuickSort_A [] = PMF.pure [] = PMF.pure (mergeSort []) by List.mergeSort_nil.

Inductive case (L = head :: tail): QuickSort_A L unfolds to a bindOnSupport over uniformOfFintype (Fin L.length). For each pivot index idx_pivot, the branch:
1. Sets pivot = L[idx_pivot], rest = L.eraseIdx idx_pivot
2. Filters rest into L1 (< pivot) and L2 (≥ pivot)
3. Recursively calls QuickSort_A L1 and QuickSort_A L2
4. Returns S1 ++ [pivot] ++ S2

By IH (L1.length < L.length and L2.length < L.length), QuickSort_A L1 = PMF.pure (mergeSort L1) and QuickSort_A L2 = PMF.pure (mergeSort L2).

So the branch deterministically returns mergeSort(L1) ++ [pivot] ++ mergeSort(L2), which equals mergeSort(L) by partition_sort_eq_mergeSort.

Since every branch of the bindOnSupport produces PMF.pure (mergeSort L), the whole thing equals PMF.pure (mergeSort L).

Key lemmas to use: partition_sort_eq_mergeSort, List.mergeSort_nil, PMF.pure_bindOnSupport, PMF.pure_bind.
-/

lemma QuickSort_A_eq_pure_mergeSort (L : List ℕ) :
    QuickSort_A L = PMF.pure (List.mergeSort L) := by
  by_contra h_contra;
  -- Let's choose any $L$ such that $QuickSort_A L \neq PMF.pure (L.mergeSort (· ≤ ·))$.
  obtain ⟨L, hL⟩ : ∃ L : List ℕ, QuickSort_A L ≠ PMF.pure (L.mergeSort (· ≤ ·)) := by
    use L;
  -- Let's choose the smallest such $L$ with respect to the length of the list.
  obtain ⟨L, hL_min⟩ : ∃ L : List ℕ, QuickSort_A L ≠ PMF.pure (L.mergeSort (· ≤ ·)) ∧ ∀ L' : List ℕ, L'.length < L.length → QuickSort_A L' = PMF.pure (L'.mergeSort (· ≤ ·)) := by
    have h_well_founded : WellFounded fun L L' : List ℕ => L.length < L'.length := by
      rw [ WellFounded.wellFounded_iff_has_min ];
      intro s hs; have := hs; exact (by
      have h_well_founded : WellFounded (fun n m : ℕ => n < m) := by
        exact wellFounded_lt;
      have := h_well_founded.has_min ( Set.image List.length s ) ⟨ _, Set.mem_image_of_mem _ this.choose_spec ⟩ ; aesop;);
    have := h_well_founded.has_min { L : List ℕ | QuickSort_A L ≠ PMF.pure ( L.mergeSort fun x1 x2 => decide ( x1 ≤ x2 ) ) } ⟨ L, hL ⟩;
    exact ⟨ this.choose, this.choose_spec.1, fun L' hL' => Classical.not_not.1 fun hL'' => this.choose_spec.2 L' hL'' hL' ⟩;
  obtain ⟨hL_ne, hL_min⟩ := hL_min;
  rcases L with ( _ | ⟨ head, tail ⟩ ) <;> simp_all +decide [ List.mergeSort ];
  · exact hL_ne ( by unfold QuickSort_A; rfl );
  · -- By definition of `QuickSort_A`, we know that `QuickSort_A (head :: tail)` is the bind of the uniform distribution over the indices of `head :: tail` with the function that sorts the list.
    have h_bind : QuickSort_A (head :: tail) = PMF.bindOnSupport (PMF.uniformOfFintype (Fin (head :: tail).length)) (fun idx_pivot h_idx_pivot => PMF.bind (QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot]))) (fun S1 => PMF.bind (QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot]))) (fun S2 => PMF.pure (S1 ++ [(head :: tail)[idx_pivot]] ++ S2)))) := by
      rw [QuickSort_A];
      rfl;
    -- By definition of `QuickSort_A`, we know that `QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot]))` and `QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot]))` are both equal to `PMF.pure (mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot])))` and `PMF.pure (mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot])))` respectively.
    have h_filter : ∀ idx_pivot : Fin (head :: tail).length, QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot])) = PMF.pure (List.mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot])) (· ≤ ·)) ∧ QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot])) = PMF.pure (List.mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot])) (· ≤ ·)) := by
      grind +revert;
    -- By definition of `partition_sort_eq_mergeSort`, we know that `mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot])) ++ [(head :: tail)[idx_pivot]] ++ mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot]))` is equal to `mergeSort (head :: tail)`.
    have h_mergeSort : ∀ idx_pivot : Fin (head :: tail).length, List.mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot])) (· ≤ ·) ++ [(head :: tail)[idx_pivot]] ++ List.mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot])) (· ≤ ·) = List.mergeSort (head :: tail) (· ≤ ·) := by
      intro idx_pivot; exact (by
      convert partition_sort_eq_mergeSort ( head :: tail ) idx_pivot using 1);
    refine' hL_ne _;
    ext b; simp +decide [ h_filter, h_mergeSort, PMF.pure_apply ] ;
    split_ifs <;> simp_all +decide [ PMF.pure_apply ]

/-
One can try to prove the correctness:
The probability that QuickSort_A on a list of two distinct elements
returns the sorted list is 1 (100%).
-/
lemma Correctness_Quicksort_A (L : List ℕ):
  QuickSort_A L (List.mergeSort L) = 1 := by
  rw [QuickSort_A_eq_pure_mergeSort]
  simp

/-!
One first goal would be to prove the most important properties of quicksort, such as:
- Correctness: The probability that QuickSort_A on a list of two distinct elements
  returns the sorted list is 1 (100%).

- Complexity: The expected running time of QuickSort_A on a list of n
distinct elements is O(n log n).  mybe do running time isnide the funciton use time monad, import CS lib




Essentially, if we fix multiple random variables and an algorithm that uses them,
we want to model the entire execution of the algorithm and at the end be able to
prove bounds on the probability of certain events (e.g. "the algorithm returns the wrong answer")
prove bounds on the expected running time of the algorithm (so a cost function)
prove bounds on the probability of certain events happening within a certain time bound
(e.g. "the algorithm returns the wrong answer within 100 steps"). Things like this.




A nice thing to have would be that we can specify a randomized algorithm in pseudo code
and then analyze each of its branch very easily.




Ideal goal:

Would it have been possible to first define the quicksort algorithm without other quantity and
then after putting a function like probability (quicksort pivot a ) ? Like is it possible to
have a funciton f that is our algorithm (other representaation of algorithm could be
a state machie, or a recurrence relation, or a pseudo code, or a flowchart, or a program in a programming language,
or even a mathematical object like a function from lists to lists) and then somehow have a genrela function
running time (f) that gives us the running time of f and a function probability (f) that gives us the
probability distribution over outputs of f ? Maybe this is too ambitious but it would be interesting to
see if we can have a general framework for writing such f sufficiently expressive to be able to represent
a wide variety of algorithms, sufficently restraint for hoping a "simple" existence of general functions
that allows us to take any such algorithm written in this framework and then automatically extract
from it the probability distribution over outputs and the running time distribution.
This would be a very powerful tool for analyzing randomized algorithms, as it would allow us
to work with them in a more intuitive way (e.g. writing them in pseudo code) and then automatically get the
formal properties we want to prove.

So we want to build this framework, we need to look at general representations of algorithms and
how to extract from them the probability distribution over outputs and the running time distribution.

Algorithm decomposes into steps, in which we should be able at each step: the probability distribution
over outputs of that step and the running time distribution of that step.


Then we can compose these steps together to get the overall probability distribution over outputs and the overall running time distribution.
We also need to look at how to represent the state of the algorithm and how to model the transitions between states. This is a very ambitious goal, but it would be a very powerful tool for analyzing randomized algorithms.





We should also be able handle and distinguishe non-termination
observation failures and error states.




A nice thing would be to potentially mixing continuous and discrete dis-
tributions.





  NOTE ON RUNNING TIME:
  The standard `PMF` monad tracks probability mass but not computational cost (running time).
  In "Phase 2: Framework Construction", we will extend this to a custom `Rnd` monad
  that pairs the probability space with a cost accumulator (WriterT Cost PMF), allowing
  formal bounds on time complexity alongside probability.



There are various approaches for reasoning about randomized algorithms in a
formal way. Analogously to the non-randomized setting described in Sect. 2,
there again exists an entire spectrum of diﬀerent approaches:
– fully explicit/deeply-embedded approaches
– “no embedding” approaches that model randomized algorithms directly in the
logic as functions returning a probability distribution
– shallow embeddings, e.g. with shallow deterministic operations but explicit
random choice and explicit “while” loops. Examples are the approaches by
Petcher and Morrisett [165] in Coq and by Kaminski et al. [110] on paper
(which was formalized by Hölzl [105]).
– combined approaches that start with a program in a deeply-embedded prob-
abilistic programming language and then relate it to a distribution specified
directly in the logic, cf. e.g. Tassarotti and Harper [188].

The ideal would be no embedings.



Directly in the Logic (No Embedding). As was mentioned before, many
ITPs oﬀer functionality to define algorithms directly in the logic of the system
– usually functionally. This approach is more flexible since algorithms can use
the full expressiveness of the system’s logic and not only some fixed restricted
set of language constructs. One possible drawback of this approach is that it
can be diﬃcult or even impossible to reason about notions such as running time
explicitly. A possible workaround is to define an explicit cost function for the
algorithm, but since there is no formal connection between that function and
the algorithm, one must check by inspection that the cost function really does
correspond to the incurred cost. Another disadvantage is that, as was said earlier,
most logics do not have builtin support for imperative algorithms.



Hybrids between these two approaches also exist (such as shallow embed-
dings). And, of course, the diﬀerent approaches can be combined to reap the
advantages of all of them; e.g. one can show a correspondence between the run-
ning time of a deeply-embedded algorithm and a cost function specified as a
recurrence directly in the logic, so that results obtained about the latter have a
formal connection to the former.
-/

end Phase3

end ARA
