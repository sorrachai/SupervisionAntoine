import ARA.Phase2
import ARA.Tactics

/-!
# QuickSort Correctness Proof

This module contains the full correctness proof for `QuickSort_A`.
The proof is somewhat natural once we understand the PMF operations,
although long and technical. It cwould be nice to improve it.
-/

namespace ARA

open PMF List

/-! ### Permutation lemma: eraseIdx gives back a permutation -/

lemma perm_getElem_cons_eraseIdx (L : List ℕ) (i : Fin L.length) :
    L.Perm (L[i] :: L.eraseIdx i) := by
  induction' i with i ih;
  induction' L with hd tl ih generalizing i ; aesop;
  rcases i with ( _ | i ) <;> simp_all +decide [ List.eraseIdx ];
  exact List.Perm.trans
    (List.Perm.cons _ ( ih _ <| by simpa using ‹i + 1 < List.length ( hd :: tl ) › ) )
    ( List.Perm.swap .. )

lemma Correctness_Quicksort_A: ∀ L : List ℕ, ∃ Output : List ℕ,
  QuickSort_A L = PMF.pure Output ∧ Output.SortedLE ∧ Output.Perm L := by
  intro L
  induction' hn : L.length using Nat.strong_induction_on with n ih generalizing L
  by_cases h : n = 0
  · simp only [h, length_eq_zero_iff] at hn
    simp only [hn, perm_nil, exists_eq_right_right]
    unfold QuickSort_A
    grind only [= sortedLE_iff_pairwise, ← Pairwise.nil]
  · have h_nonempty : L ≠ [] := by grind only [= length_nil]
    match L with
    | [] => contradiction
    | head::tail =>
      let L := head :: tail
      have h_nonempty : Nonempty (Fin L.length) := ⟨0, by grind only⟩
      have idx_pivot_dist := PMF.uniformOfFintype (Fin L.length)

      have h_partition : ∀ idx_pivot : Fin L.length,
        let pivot := L[idx_pivot]
        let rest := L.eraseIdx idx_pivot
        let L1 := rest.filter (fun x => decide (x < pivot))
        let L2 := rest.filter (fun x => decide (x ≥ pivot))
        ∃ Output : List ℕ,
        PMF.bind (QuickSort_A L1)
        (fun S1 =>
        PMF.bind (QuickSort_A L2) (fun S2 => PMF.pure (S1 ++ [pivot] ++ S2))) = PMF.pure Output
        ∧ Output.SortedLE ∧ Output.Perm L := by
        intro idx_pivot
        let pivot := L[idx_pivot]
        let rest := L.eraseIdx idx_pivot
        let L1 := rest.filter (fun x => decide (x < pivot))
        let L2 := rest.filter (fun x => decide (x ≥ pivot))
        /- By ih, since L1.length < L.length and L2.length < L.length,
        we know that QuickSort_A L1 and QuickSort_A L2 are Pure PMF's
        on certain respective outputs: Output1 and Output2 that are
        sorted and are permutations of L1 and L2 respectively.-/
        obtain ⟨Output1, ⟨EqPure1, ⟨Sorted1, Perm1⟩⟩⟩ := by
          apply ih L1.length
          grind only [→ Fin.pos', usr length_filter_le, usr Fin.isLt, = length_eraseIdx]
          rfl
        obtain ⟨Output2, ⟨EqPure2, ⟨Sorted2, Perm2⟩⟩⟩ := by
          apply ih L2.length
          grind only [→ Fin.pos', usr length_filter_le, usr Fin.isLt, = length_eraseIdx]
          rfl
        use Output1 ++ [pivot] ++ Output2
        constructor
        · -- the multiple bind operations in the recursive call result in a
          -- PMF.pure (Output1 ++ [pivot] ++ Output2). This is nicely done
          -- by our extended grind! (Check by removing the 'import ARA.Tactics').
          grind only [= PMF.pure_bind, #43c4]
        · constructor
          · -- Output1 ++ [pivot] ++ Output2 is sorted
            -- 1. Extract the upper bound for Output1
            have h_out1_bound : ∀ x ∈ Output1, x < pivot := by
              intro x hx
              have hx_in_L1 : x ∈ L1 := Perm1.subset hx
              simp only [L1, List.mem_filter, decide_eq_true_eq] at hx_in_L1
              omega
            -- 2. Extract the lower bound for Output2
            have h_out2_bound : ∀ x ∈ Output2, pivot ≤ x := by
              intro x hx
              have hx_in_L2 : x ∈ L2 := Perm2.subset hx
              simp only [L2, List.mem_filter, decide_eq_true_eq] at hx_in_L2
              omega
            -- 3. Combine Sorted1, Sorted2, and the bounds.
            -- First, prove the right side (pivot :: Output2) is sorted.
            have h_right_sorted : (Output1 ++ [pivot]).SortedLE := by
              rw [List.sortedLE_iff_pairwise]
              grind
            -- Second, establish that every element in the left side is ≤ every element in the right side.
            have h_cross_bound : ∀ x ∈ Output1 ++ [pivot], ∀ y ∈ Output2, x ≤ y := by
              intro x hx y hy
              grind
            rw [List.sortedLE_iff_pairwise]
            apply List.pairwise_append.mpr
            grind
          · -- Output1 ++ [pivot] ++ Output2 is a permutation of L.
            have h_perm_concat : (Output1 ++ [pivot] ++ Output2).Perm (L1 ++ [pivot] ++ L2) := by
              exact List.Perm.append (List.Perm.append Perm1 (List.Perm.refl [pivot])) Perm2
            have h_partition_sort : (L1 ++ [pivot] ++ L2).Perm L := by
              have h_perm_middle : (L1 ++ [pivot] ++ L2).Perm ([pivot] ++ (L1 ++ L2)) := by
                simp only [List.append_assoc]
                grind
              have h_filter_perm : ([pivot] ++ (L1 ++ L2)).Perm (pivot :: rest) := by
                apply List.Perm.cons
                have h_append := List.filter_append_perm (fun x => decide (x < pivot)) rest
                have h_equiv : List.filter (fun x => !(decide (x < pivot))) rest = L2 := by
                  grind
                rwa [h_equiv] at h_append
              have h_rest_perm : (pivot :: rest).Perm L := by
                apply List.Perm.symm
                apply (perm_getElem_cons_eraseIdx)
              exact List.Perm.trans h_perm_middle (List.Perm.trans h_filter_perm h_rest_perm)
            exact List.Perm.trans h_perm_concat h_partition_sort

      have h_partition_refined : ∃ Output : List ℕ, ∀ idx_pivot : Fin L.length,
        let pivot := L[idx_pivot]
        let rest := L.eraseIdx idx_pivot
        let L1 := rest.filter (fun x => decide (x < pivot))
        let L2 := rest.filter (fun x => decide (x ≥ pivot))
        PMF.bind (QuickSort_A L1)
        (fun S1 =>
        PMF.bind (QuickSort_A L2) (fun S2 => PMF.pure (S1 ++ [pivot] ++ S2))) = PMF.pure Output
        ∧ Output.SortedLE ∧ Output.Perm L := by
          -- We get an Output from h_partition by using the index 0 (possible as the list is nonempty)
          -- Then we introduce any index and get for free the right of the constructor, for the left of
          -- it we get the output from h_partition, then show that it must be the same as the first output
          -- so we are done
          obtain ⟨Output0, hPure0, hSorted0, hPerm0⟩ := h_partition ⟨0, by simp [L]⟩
          use Output0
          intro idx_pivot
          obtain ⟨Output_i, hPure_i, hSorted_i, hPerm_i⟩ := h_partition idx_pivot
          -- Both Output0 and Output_i are sorted permutations of L, so they must be equal
          have h_eq : Output_i = Output0 := by
            apply List.Perm.eq_of_pairwise
            · exact fun _ _ _ _ hab hba => Nat.le_antisymm hab hba
            · exact List.sortedLE_iff_pairwise.mp hSorted_i
            · exact List.sortedLE_iff_pairwise.mp hSorted0
            · exact hPerm_i.trans hPerm0.symm
          rw [h_eq] at hPure_i
          exact ⟨hPure_i, hSorted0, hPerm0⟩

      -- Now use h_partition_refined to prove the main goal
      obtain ⟨Output, hOutput⟩ := h_partition_refined
      obtain ⟨hPure, hSorted, hPerm⟩ := hOutput ⟨0, by simp [L]⟩
      use Output
      constructor
      · -- Show QuickSort_A L = PMF.pure Output
        have h_const : ∀ idx : Fin L.length,
          (let pivot := L[idx]
           let rest := L.eraseIdx idx
           let L1 := rest.filter (fun x => decide (x < pivot))
           let L2 := rest.filter (fun x => decide (x ≥ pivot))
           PMF.bind (QuickSort_A L1) fun S1 =>
           PMF.bind (QuickSort_A L2) fun S2 => PMF.pure (S1 ++ [pivot] ++ S2)) =
          PMF.pure Output := fun idx => (hOutput idx).1
        calc QuickSort_A L
            = (PMF.uniformOfFintype (Fin L.length)).bind fun idx =>
                let pivot := L[idx]
                let rest := L.eraseIdx idx
                let L1 := rest.filter (fun x => decide (x < pivot))
                let L2 := rest.filter (fun x => decide (x ≥ pivot))
                PMF.bind (QuickSort_A L1) fun S1 =>
                PMF.bind (QuickSort_A L2) fun S2 => PMF.pure (S1 ++ [pivot] ++ S2) := by
              rw [QuickSort_A]; rfl
          _ = (PMF.uniformOfFintype (Fin L.length)).bind fun _ => PMF.pure Output := by
              congr 1; funext idx; exact h_const idx
          _ = PMF.pure Output := PMF.bind_const _ _
      · exact ⟨hSorted, hPerm⟩

end ARA
