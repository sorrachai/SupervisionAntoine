import ARA.Rnd
import ARA.Tactics

/-!
# Future-Proofing the Architecture: Extraction Framework

This module addresses the vision outlined in Phase 3 of the thesis:
the ability to write algorithms in a **pseudo-code style** and automatically
extract both the **running time distribution** and the **output probability distribution**.

## Architecture Overview

The `Rnd T α` monad (defined in `ARA.Rnd`) is the foundation. It represents a
joint distribution over `(output, cost)` pairs, combining the Giry monad (PMF)
with a cost accumulator (WriterT-style).

### The Three-Layer Extraction Pipeline

```
┌──────────────────────────────────────────────────┐
│  Layer 1: Algorithm Specification (Pseudo-code)  │
│  ─────────────────────────────────────────────── │
│  Write your algorithm using `do` notation in     │
│  the `Rnd T α` monad. Use:                      │
│  • `Rnd.uniformFin n` for uniform random choice  │
│  • `Rnd.coin p` for biased coin flips            │
│  • `Rnd.tick c` to charge cost                   │
│  • Standard `if/then/else`, `match`, recursion   │
├──────────────────────────────────────────────────┤
│  Layer 2: Property Extraction                    │
│  ─────────────────────────────────────────────── │
│  From any `m : Rnd T α`, automatically extract:  │
│  • `m.outputDist : PMF α` (output distribution)  │
│  • `m.costDist : PMF T` (cost distribution)      │
│  • `m.probOutput a` (prob of specific output)    │
│  • `m.probCost c` (prob of specific cost)        │
├──────────────────────────────────────────────────┤
│  Layer 3: Formal Verification                    │
│  ─────────────────────────────────────────────── │
│  Prove properties using `pmf_simp`, `grind`,     │
│  and the Layer C derived lemmas:                 │
│  • Correctness: `m.outputDist = PMF.pure answer` │
│  • Complexity: `𝔼[m.costDist] ≤ bound`          │
│  • Tail bounds: `P(cost > k) ≤ ε`               │
└──────────────────────────────────────────────────┘
```

## Design Decisions and Rationale

### Why `PMF (α × T)` and not `α → T → ℝ≥0∞`?

Using `PMF (α × T)` gives us:
1. **Automatic normalization**: The sum-to-1 constraint is enforced by `PMF`.
2. **Monad structure for free**: We inherit `bind` from `PMF` (with cost addition).
3. **Mathlib integration**: All existing PMF lemmas apply directly.
4. **Marginalization**: Output/cost distributions are just `PMF.map Prod.fst/snd`.

### Why not deeply embed a programming language?

A shallow embedding (algorithms as Lean functions returning `Rnd`) gives:
1. **Full expressiveness**: Use Lean's entire logic (pattern matching, recursion, etc.)
2. **Natural notation**: `do` blocks look like pseudo-code.
3. **Direct proofs**: Properties are stated about the same object, no translation.

The trade-off is that cost annotations are **trusted** (not automatically derived
from the code structure). This is the same trade-off as in `TimeM`. The user must
ensure that `tick` calls faithfully represent the cost model.

### Handling Non-Termination

For potentially non-terminating algorithms (e.g., Las Vegas algorithms):
- Use `partial` for executable versions.
- For formal analysis, define the algorithm with a fuel parameter `n : ℕ` and
  analyze the limit behavior.
- The `PMF` type naturally handles sub-distributions (measures with total mass ≤ 1)
  via `PMF.toOuterMeasure`, though `PMF` itself requires total mass = 1.

### Mixing Continuous and Discrete Distributions

The current `PMF`-based approach handles discrete distributions. For continuous
distributions (e.g., exponential waiting times), future work could:
1. Use `MeasureTheory.Measure` directly instead of `PMF`.
2. Define `RndC α := MeasureTheory.Measure (α × ℝ≥0)` with normalization.
3. Provide a coercion from `Rnd` (discrete) to `RndC` (continuous).
-/

/-!
## Preserved Comments from Original Phase 3

The following are the original architectural comments from the thesis,
preserved verbatim for reference.
-/

/-
One first goal would be to prove the most important properties of quicksort, such as:
- Correctness: The probability that QuickSort_A on any list
  returns the sorted list is 1 (100%).

- Complexity: The expected running time of QuickSort_A on a list of n
distinct elements is O(n log n).  mybe do running time isnide the funciton use time monad, import CS lib




- Essentially, if we fix multiple random variables and an algorithm that uses them,
we want to model the entire execution of the algorithm and at the end be able to
prove bounds on the probability of certain events (e.g. "the algorithm returns the wrong answer")
prove bounds on the expected running time of the algorithm (so a cost function)
prove bounds on the probability of certain events happening within a certain time bound
(e.g. "the algorithm returns the wrong answer within 100 steps"). Things like this.




- A nice thing to have would be that we can specify a randomized algorithm in pseudo code
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
– "no embedding" approaches that model randomized algorithms directly in the
logic as functions returning a probability distribution
– shallow embeddings, e.g. with shallow deterministic operations but explicit
random choice and explicit "while" loops. Examples are the approaches by
Petcher and Morrisett [165] in Coq and by Hölzl [105].
– combined approaches that start with a program in a deeply-embedded prob-
abilistic programming language and then relate it to a distribution specified
directly in the logic, cf. e.g. Tassarotti and Harper [188].

The ideal would be no embedings.



Directly in the Logic (No Embedding). As was mentioned before, many
ITPs oﬀer functionality to define algorithms directly in the logic of the system
– usually functionally. This approach is more flexible since algorithms can use
the full expressiveness of the system's logic and not only some fixed restricted
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

namespace ARA

open PMF ENNReal

/-! ## Demonstration: QuickSort with Cost Tracking

Below we show how the `Rnd` monad would be used to write QuickSort
with integrated cost tracking, enabling formal analysis of both
correctness and complexity.
-/

/-- QuickSort in the `Rnd ℕ` monad: tracks both probability and comparison count.
    Each comparison costs 1 unit. The pivot selection is uniform random. -/
noncomputable def QuickSort_Rnd : List ℕ → Rnd ℕ (List ℕ) := fun
| [] => pure []
| L@(head::tail) => do
  -- Uniform random pivot selection (zero cost — it's a random oracle call)
  have : Nonempty (Fin L.length) := ⟨⟨0, by grind only [= List.length_cons]⟩⟩
  let idx ← Rnd.uniformFintype (Fin L.length)
  let pivot := L[idx]
  let rest := L.eraseIdx idx
  -- Partition: each element comparison costs 1 tick
  -- (In a full implementation, we'd charge per-element; here we charge |rest| total)
  Rnd.tick rest.length
  let L1 := rest.filter (· < pivot)
  let L2 := rest.filter (· ≥ pivot)
  -- Recursive calls
  let S1 ← QuickSort_Rnd L1
  let S2 ← QuickSort_Rnd L2
  pure (S1 ++ [pivot] ++ S2)
termination_by L => L.length
decreasing_by
  all_goals
    have h_rest : (L.eraseIdx idx).length < L.length := by
      rw [List.length_eraseIdx]; grind
    apply Nat.lt_of_le_of_lt
    · apply List.length_filter_le
    · grind

/-- Extract the output distribution: should equal `PMF.pure (mergeSort L)`. -/
noncomputable def QuickSort_Rnd_outputDist (L : List ℕ) : PMF (List ℕ) :=
  (QuickSort_Rnd L).outputDist

/-- Extract the cost distribution: gives the distribution of comparison counts. -/
noncomputable def QuickSort_Rnd_costDist (L : List ℕ) : PMF ℕ :=
  (QuickSort_Rnd L).costDist

/-! ## Framework for Expected Cost Analysis

To prove expected running time bounds (e.g., E[comparisons] = O(n log n) for QuickSort),
the general approach is:

1. **Define expected cost**: `expectedCost m = ∑' (a, c), m.run (a, c) * c`
   (weighted sum of costs over the joint distribution).

2. **Set up a recurrence**: For recursive algorithms, express the expected cost
   as a recurrence relation: `E[T(n)] = 1/n * ∑ᵢ (n-1 + E[T(i)] + E[T(n-1-i)])`

3. **Solve the recurrence**: Use standard techniques (e.g., show it satisfies
   `E[T(n)] ≤ 2n ln n`) and prove the bound in Lean.

The `Rnd` monad makes step 1 automatic (via `costDist`), and the `pmf_simp`
toolkit helps with step 2. Step 3 requires mathematical analysis.
-/

/-- Expected cost of a `Rnd ℕ α` computation, defined as the expected value
    of the cost distribution. -/
noncomputable def expectedCostNat {α : Type*} (m : Rnd ℕ α) : ℝ≥0∞ :=
  ∑' (p : α × ℕ), m.run p * p.2

end ARA
