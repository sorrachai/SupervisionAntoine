import ARA.Basic

/-!
# The `Rnd` Monad: Combining Probability and Cost

This module defines the `Rnd` monad, which pairs the probability space (`PMF`)
with a cost accumulator, enabling formal analysis of **both** the output distribution
and the running time distribution of randomized algorithms.

## Design

The key insight is that a randomized computation with cost tracking is a
**joint distribution** over `(output, cost)` pairs:

```
Rnd T α ≅ PMF (α × T)
```

where `T` is the cost type (typically `ℕ` for counting operations).

This is equivalent to a `WriterT T PMF` monad transformer stack, where:
- `PMF` provides the probability backbone (Giry monad)
- `WriterT T` accumulates costs additively

### Monad Operations

- **`pure a`**: Returns `a` with zero cost and probability 1.
  Formally: `PMF.pure (a, 0)`

- **`bind m f`**: Samples `(a, c₁)` from `m`, then samples `(b, c₂)` from `f a`,
  and returns `(b, c₁ + c₂)`. Probabilities multiply (via PMF bind),
  costs add (via the writer).

### Extraction Functions

Given `m : Rnd T α`, we can extract:
- **Output distribution**: `m.outputDist : PMF α` — marginalizes over costs
- **Cost distribution**: `m.costDist : PMF T` — marginalizes over outputs
- **Joint distribution**: `m.run : PMF (α × T)` — the full joint distribution

### Primitives

- **`Rnd.coin p`**: Fair/biased coin flip (Bernoulli distribution), zero cost
- **`Rnd.uniformFin n`**: Uniform choice over `Fin n`, zero cost
- **`Rnd.uniformFintype α`**: Uniform choice over a finite type, zero cost
- **`Rnd.tick c`**: Deterministic unit computation that charges cost `c`
- **`Rnd.liftPMF p`**: Lift a pure PMF into the Rnd monad with zero cost

## Relationship to TimeM

`TimeM T α` from the companion module tracks cost deterministically (no probability).
`Rnd T α` generalizes this: a deterministic `TimeM` computation `⟨a, c⟩` corresponds
to the degenerate `Rnd` computation `PMF.pure (a, c)`.

The function `Rnd.fromTimeM` embeds any `TimeM` computation into `Rnd` as a
point-mass distribution.

## References

This design follows the "WriterT Cost PMF" approach mentioned in Phase 3 of the
thesis framework. It is a shallow embedding: algorithms are written directly in
Lean's logic using `do` notation, and properties are proved about the resulting
distributions.
-/

namespace ARA

open PMF ENNReal

/-! ## Core Definition -/

/-- `Rnd T α` represents a randomized computation that produces a value of type `α`
    and accumulates a cost of type `T`. It is implemented as `PMF (α × T)`:
    a probability distribution over `(output, cost)` pairs. -/
def Rnd (T : Type*) (α : Type*) := PMF (α × T)

namespace Rnd

variable {T : Type*} {α β γ : Type*}

/-- Access the underlying `PMF (α × T)` joint distribution. -/
def run (m : Rnd T α) : PMF (α × T) := m

/-! ## Monad Instance -/

/-- Lift a pure value into `Rnd` with zero cost. -/
noncomputable def pure' [Zero T] (a : α) : Rnd T α :=
  PMF.pure (a, 0)

/-- Sequentially compose two `Rnd` computations.
    Probabilities multiply (via PMF bind), costs add. -/
noncomputable def bind' [Add T] (m : Rnd T α) (f : α → Rnd T β) : Rnd T β :=
  m.bind (fun p => (f p.1).bind (fun q => PMF.pure (q.1, p.2 + q.2)))

/-- Map a function over the output, preserving cost and probability. -/
noncomputable def map' (f : α → β) (m : Rnd T α) : Rnd T β :=
  m.map (fun p => (f p.1, p.2))

noncomputable instance [Zero T] : Pure (Rnd T) where
  pure := Rnd.pure'

noncomputable instance [Add T] : Bind (Rnd T) where
  bind := Rnd.bind'

noncomputable instance : Functor (Rnd T) where
  map := Rnd.map'

/-! ## Primitive Operations -/

/-- Charge a cost of `c` units, returning `PUnit`. -/
noncomputable def tick [Zero T] (c : T) : Rnd T PUnit :=
  PMF.pure (PUnit.unit, c)

/-- A biased coin flip with probability `p` of `true`, zero cost. -/
noncomputable def coin [Zero T] (p : NNReal) (hp : p ≤ 1) : Rnd T Bool :=
  (PMF.bernoulli p hp).map (fun b => (b, (0 : T)))

/-- Uniform random choice over `Fin n`, zero cost. -/
noncomputable def uniformFin [Zero T] (n : ℕ) [NeZero n] : Rnd T (Fin n) :=
  (PMF.uniformOfFintype (Fin n)).map (fun i => (i, (0 : T)))

/-- Uniform random choice over a nonempty finite type, zero cost. -/
noncomputable def uniformFintype [Zero T] (α : Type*) [Fintype α] [Nonempty α] : Rnd T α :=
  (PMF.uniformOfFintype α).map (fun a => (a, (0 : T)))

/-- Uniform random choice over a nonempty finset, zero cost. -/
noncomputable def uniformFinset [Zero T] {α : Type*} (s : Finset α) (hs : s.Nonempty) : Rnd T α :=
  (PMF.uniformOfFinset s hs).map (fun a => (a, (0 : T)))

/-- Lift a pure PMF (no cost tracking) into `Rnd` with zero cost. -/
noncomputable def liftPMF [Zero T] (p : PMF α) : Rnd T α :=
  p.map (fun a => (a, (0 : T)))

/-- Embed a deterministic `TimeM`-style computation `(value, cost)` into `Rnd`
    as a point-mass distribution. -/
noncomputable def fromTimeM (ret : α) (time : T) : Rnd T α :=
  PMF.pure (ret, time)

/-! ## Extraction Functions -/

/-- Extract the **output distribution** by marginalizing over costs.
    `m.outputDist a = ∑' c, m.run (a, c)` -/
noncomputable def outputDist (m : Rnd T α) : PMF α :=
  m.map Prod.fst

/-- Extract the **cost distribution** by marginalizing over outputs.
    `m.costDist c = ∑' a, m.run (a, c)` -/
noncomputable def costDist (m : Rnd T α) : PMF T :=
  m.map Prod.snd

/-- The probability of a specific `(output, cost)` pair. -/
noncomputable def prob (m : Rnd T α) (a : α) (c : T) : ℝ≥0∞ :=
  m.run (a, c)

/-- The probability of a specific output (marginalizing over all costs). -/
noncomputable def probOutput (m : Rnd T α) (a : α) : ℝ≥0∞ :=
  m.outputDist a

/-- The probability of a specific cost (marginalizing over all outputs). -/
noncomputable def probCost (m : Rnd T α) (c : T) : ℝ≥0∞ :=
  m.costDist c

/-! ## Simp Lemmas -/

@[simp]
lemma run_pure [Zero T] (a : α) : (pure a : Rnd T α).run = PMF.pure (a, 0) := rfl

-- run_bind unfolds by definition (rfl)

@[simp]
lemma outputDist_pure [Zero T] (a : α) : (pure a : Rnd T α).outputDist = PMF.pure a := by
  show (PMF.pure (a, (0 : T))).map Prod.fst = PMF.pure a
  simp [PMF.pure_map]

@[simp]
lemma costDist_pure [Zero T] (a : α) : (pure a : Rnd T α).costDist = PMF.pure (0 : T) := by
  show (PMF.pure (a, (0 : T))).map Prod.snd = PMF.pure (0 : T)
  simp [PMF.pure_map]

@[simp]
lemma outputDist_liftPMF [Zero T] (p : PMF α) : (liftPMF p : Rnd T α).outputDist = p := by
  show (p.map (fun a => (a, (0 : T)))).map Prod.fst = p
  rw [PMF.map_comp]
  convert PMF.map_id p

@[simp]
lemma costDist_tick [Zero T] (c : T) : (tick c : Rnd T PUnit).costDist = PMF.pure c := by
  show (PMF.pure (PUnit.unit, c)).map Prod.snd = PMF.pure c
  simp [PMF.pure_map]

/-! ## Example: Coin flip with cost -/

/-- A fair coin flip that costs 1 unit. -/
noncomputable def fairCoinWithCost : Rnd ℕ Bool := do
  tick 1
  coin (1/2 : NNReal) (by norm_num)

end Rnd

end ARA
