import ARA.Tactics

class RandMonad (M : Type → Type) [Monad M] where
  -- Given a nonempty list, pick a random valid index
  randIdx {α} : (L : List α) → L ≠ [] → M (Fin L.length)

def QuickSort [Monad M] [RandMonad M] : List ℕ → M (List ℕ)
  | [] => return []
  | L@(_::_) => do
      let idx ← RandMonad.randIdx L (by grind)
      let pivot := L[idx]
      let rest := L.eraseIdx idx
      let L1 := rest.filter (· < pivot)
      let L2 := rest.filter (· ≥ pivot)
      let S1 ← QuickSort L1
      let S2 ← QuickSort L2
      return (S1 ++ [pivot] ++ S2)
  termination_by L => L.length
decreasing_by all_goals grind

instance : RandMonad IO where
  randIdx L hne := do
    let i ← IO.rand 0 (L.length - 1)
    return ⟨i % L.length, Nat.mod_lt i (List.length_pos_iff.mpr hne)⟩

noncomputable instance : RandMonad PMF where
  randIdx L hne :=
    have : Nonempty (Fin L.length) := ⟨⟨0, List.length_pos_iff.mpr hne⟩⟩
    PMF.uniformOfFintype (Fin L.length)

-- IO version (executable)
def QuickSort_Rand : List ℕ → IO (List ℕ) := QuickSort

#eval QuickSort_Rand [5,4,2,1]

-- PMF version (noncomputable specification)
noncomputable def QuickSort_A : List ℕ → PMF (List ℕ) := QuickSort
