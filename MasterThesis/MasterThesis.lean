import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Rat.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Cslib.Algorithms.Lean.TimeM

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
theorem prob_rolling_3 : mixed_dice_game 3 = (1/2 : ENNReal) * (1/6 : ENNReal) + (1/2 : ENNReal) * (1/20 : ENNReal) := by
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


/-
Correctness: The probability that QuickSort_A on a list of two distinct elements
returns the sorted list is 1 (100%).
-/
lemma correctness_quicksort :
  ∀ (L : List ℕ), QuickSort_A L (List.sort L) = 1 := by
  sorry


/-
Complexity: The expected running time of QuickSort_A on a list of n
distinct elements is O(n log n).  mybe do running time isnide the funciton use time monad, import CS lib
-/
lemma complexity_quicksort :
  ∀ (L : List ℕ), -- QuickSort_A L has expected running time O(L.length * log L.length) := by
  sorry

end Phase2

section phase3
/-!
  ### Phase 3: Towards a General Framework for Analyzing Randomized Algorithms
As seen in phase2, some properties of randomized algorithms can be proved.
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

To address these problems, we would like to first restrict ourselves to finite
probability distributions, so that we can work with finite sums and avoid the
complications of infinite sums. This would allow us to use already existing
theorems about finite sums and even algebra automated reasoner
(for e.g. ring_nf, omega, etc.) to manipulate them more easily.
-/

/-
One first goal would be to prove the most important properties of quicksort, such as:
- Correctness: The probability that QuickSort_A on a list of two distinct elements
  returns the sorted list is 1 (100%).

- Complexity: The expected running time of QuickSort_A on a list of n
distinct elements is O(n log n).  mybe do running time isnide the funciton use time monad, import CS lib
-/




/-
Essentially, if we fix multiple random variables and an algorithm that uses them,
we want to model the entire execution of the algorithm and at the end be able to
prove bounds on the probability of certain events (e.g. "the algorithm returns the wrong answer")
prove bounds on the expected running time of the algorithm (so a cost function)
prove bounds on the probability of certain events happening within a certain time bound
(e.g. "the algorithm returns the wrong answer within 100 steps"). Things like this.
-/


/-
A nice thing to have would be that we can specify a randomized algorithm in pseudo code
and then analyze each of its branch very easily.
-/


/-

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

-/


/-
We should also be able handle and distinguishe non-termination
observation failures and error states.
-/

/-
A nice thing would be to potentially mixing continuous and discrete dis-
tributions.
-/


/-
  NOTE ON RUNNING TIME:
  The standard `PMF` monad tracks probability mass but not computational cost (running time).
  In "Phase 2: Framework Construction", we will extend this to a custom `Rnd` monad
  that pairs the probability space with a cost accumulator (WriterT Cost PMF), allowing
  formal bounds on time complexity alongside probability.
-/

/-
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
-/

/-
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
-/

/-
Hybrids between these two approaches also exist (such as shallow embed-
dings). And, of course, the diﬀerent approaches can be combined to reap the
advantages of all of them; e.g. one can show a correspondence between the run-
ning time of a deeply-embedded algorithm and a cost function specified as a
recurrence directly in the logic, so that results obtained about the latter have a
formal connection to the former.
-/
end phase3

end ARA
