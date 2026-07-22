/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Counterexample to Written on the Wall II — Conjecture 59

This file is intentionally separate from the authoritative open-conjecture source.
It defines an explicit connected graph on `Fin 18` and proves that the exact
Conjecture 59 inequality fails.

Construction: take `K_{5,5}` on `{0,...,4}` and `{5,...,9}`, delete
`(0,5)`, `(0,6)`, `(0,7)`, `(1,5)`, add seven isolated vertices
`10,...,16`, and finally add a universal vertex `17`.
-/

namespace WrittenOnTheWallII.GraphConjecture59Counterexample

open Classical SimpleGraph Finset

private def coreForward (u v : Fin 18) : Prop :=
  u.val < 5 ∧ 5 ≤ v.val ∧ v.val < 10 ∧
    ¬ ((u.val = 0 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7)) ∨
       (u.val = 1 ∧ v.val = 5))

private def counterG : SimpleGraph (Fin 18) where
  Adj u v :=
    u ≠ v ∧
      (u.val = 17 ∨ v.val = 17 ∨ coreForward u v ∨ coreForward v u)
  symm u v h := by
    rcases h with ⟨hne, hcases⟩
    exact ⟨hne.symm, by tauto⟩
  loopless u h := h.1 rfl

private instance counterG_decidable : DecidableRel counterG.Adj := fun u v => by
  unfold counterG coreForward
  infer_instance

private lemma counterG_adj (u v : Fin 18) :
    counterG.Adj u v ↔
      u ≠ v ∧
        (u.val = 17 ∨ v.val = 17 ∨ coreForward u v ∨ coreForward v u) :=
  Iff.rfl

private lemma counterG_center_adj (v : Fin 18) (hv : v ≠ 17) : counterG.Adj 17 v := by
  rw [counterG_adj]
  exact ⟨hv.symm, Or.inl rfl⟩

private lemma counterG_reachable_from_center (v : Fin 18) : counterG.Reachable 17 v := by
  by_cases hv : v = 17
  · subst hv
    exact Reachable.refl _
  · exact (counterG_center_adj v hv).reachable

private lemma counterG_connected : counterG.Connected := by
  constructor
  intro u v
  exact (counterG_reachable_from_center u).symm.trans
    (counterG_reachable_from_center v)

/-- The expected degree of each labelled vertex in the explicit graph. -/
private def expectedDegree (v : Fin 18) : ℕ :=
  if v.val = 0 then 3
  else if v.val = 1 then 5
  else if v.val = 2 then 6
  else if v.val = 3 then 6
  else if v.val = 4 then 6
  else if v.val = 5 then 4
  else if v.val = 6 then 5
  else if v.val = 7 then 5
  else if v.val = 8 then 6
  else if v.val = 9 then 6
  else if v.val = 10 then 1
  else if v.val = 11 then 1
  else if v.val = 12 then 1
  else if v.val = 13 then 1
  else if v.val = 14 then 1
  else if v.val = 15 then 1
  else if v.val = 16 then 1
  else 17

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private lemma counterG_degree_eq_expected (v : Fin 18) :
    counterG.degree v = expectedDegree v := by
  fin_cases v <;> decide

/-- The degree multiset before sorting. -/
private lemma expectedDegreeMultiset :
    Finset.univ.val.map expectedDegree =
      (↑([3, 5, 6, 6, 6, 4, 5, 5, 6, 6, 1, 1, 1, 1, 1, 1, 1, 17] : List ℕ) :
        Multiset ℕ) := by
  rw [Fin.univ_val_map]
  norm_num [List.ofFn_succ, expectedDegree]
private lemma counterG_degreeSequence :
    ((Finset.univ.val.map fun v => counterG.degree v).sort (· ≥ ·)) =
      [17, 6, 6, 6, 6, 6, 5, 5, 5, 4, 3, 1, 1, 1, 1, 1, 1, 1] := by
  simp_rw [counterG_degree_eq_expected]
  rw [expectedDegreeMultiset]
  change List.mergeSort [3, 5, 6, 6, 6, 4, 5, 5, 6, 6, 1, 1, 1, 1, 1, 1, 1, 17]
      (fun x y => decide (x ≥ y)) =
    [17, 6, 6, 6, 6, 6, 5, 5, 5, 4, 3, 1, 1, 1, 1, 1, 1, 1]
  rw [List.mergeSort_eq_insertionSort]
  rfl

private lemma hhStep0 :
    havelHakimiStep [17, 6, 6, 6, 6, 6, 5, 5, 5, 4, 3, 1, 1, 1, 1, 1, 1, 1] =
      [5, 5, 5, 5, 5, 4, 4, 4, 3, 2, 0, 0, 0, 0, 0, 0, 0] := by
  change List.mergeSort [5, 5, 5, 5, 5, 4, 4, 4, 3, 2, 0, 0, 0, 0, 0, 0, 0]
      (fun x y => decide (x ≥ y)) =
    [5, 5, 5, 5, 5, 4, 4, 4, 3, 2, 0, 0, 0, 0, 0, 0, 0]
  rw [List.mergeSort_eq_insertionSort]
  rfl

private lemma hhStep1 :
    havelHakimiStep [5, 5, 5, 5, 5, 4, 4, 4, 3, 2, 0, 0, 0, 0, 0, 0, 0] =
      [4, 4, 4, 4, 4, 4, 3, 3, 2, 0, 0, 0, 0, 0, 0, 0] := by
  change List.mergeSort [4, 4, 4, 4, 3, 4, 4, 3, 2, 0, 0, 0, 0, 0, 0, 0]
      (fun x y => decide (x ≥ y)) =
    [4, 4, 4, 4, 4, 4, 3, 3, 2, 0, 0, 0, 0, 0, 0, 0]
  rw [List.mergeSort_eq_insertionSort]
  rfl

private lemma hhStep2 :
    havelHakimiStep [4, 4, 4, 4, 4, 4, 3, 3, 2, 0, 0, 0, 0, 0, 0, 0] =
      [4, 3, 3, 3, 3, 3, 3, 2, 0, 0, 0, 0, 0, 0, 0] := by
  change List.mergeSort [3, 3, 3, 3, 4, 3, 3, 2, 0, 0, 0, 0, 0, 0, 0]
      (fun x y => decide (x ≥ y)) =
    [4, 3, 3, 3, 3, 3, 3, 2, 0, 0, 0, 0, 0, 0, 0]
  rw [List.mergeSort_eq_insertionSort]
  rfl

private lemma hhStep3 :
    havelHakimiStep [4, 3, 3, 3, 3, 3, 3, 2, 0, 0, 0, 0, 0, 0, 0] =
      [3, 3, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] := by
  change List.mergeSort [2, 2, 2, 2, 3, 3, 2, 0, 0, 0, 0, 0, 0, 0]
      (fun x y => decide (x ≥ y)) =
    [3, 3, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0]
  rw [List.mergeSort_eq_insertionSort]
  rfl

private lemma hhStep4 :
    havelHakimiStep [3, 3, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0] =
      [2, 2, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] := by
  change List.mergeSort [2, 1, 1, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0]
      (fun x y => decide (x ≥ y)) =
    [2, 2, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0]
  rw [List.mergeSort_eq_insertionSort]
  rfl

private lemma hhStep5 :
    havelHakimiStep [2, 2, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] =
      [2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0] := by
  change List.mergeSort [1, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0]
      (fun x y => decide (x ≥ y)) =
    [2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]
  rw [List.mergeSort_eq_insertionSort]
  rfl

private lemma hhStep6 :
    havelHakimiStep [2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0] =
      [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  change List.mergeSort [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
      (fun x y => decide (x ≥ y)) =
    [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  rw [List.mergeSort_eq_insertionSort]
  rfl

private lemma hhStep7 :
    havelHakimiStep [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] =
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  change List.mergeSort [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      (fun x y => decide (x ≥ y)) =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  rw [List.mergeSort_eq_insertionSort]
  rfl

/-- Exact Havel--Hakimi residue certificate, expanded into eight verified transitions. -/
private lemma counterG_residue : residue counterG = 10 := by
  unfold residue
  rw [counterG_degreeSequence]
  rw [residueAux, hhStep0, residueAux, hhStep1, residueAux, hhStep2,
    residueAux, hhStep3, residueAux, hhStep4, residueAux, hhStep5,
    residueAux, hhStep6, residueAux, hhStep7, residueAux]
  norm_num
private lemma counterG_b_ge : (17 : ℝ) ≤ counterG.b := by
  unfold b
  suffices h : 17 ≤ largestInducedBipartiteSubgraphSize counterG by
    exact_mod_cast h
  apply le_csSup
  · exact ⟨18, fun n ⟨s, _, hs⟩ => hs ▸ s.card_le_univ⟩
  · refine ⟨Finset.univ.erase (17 : Fin 18), ?_, by decide⟩
    refine ⟨SimpleGraph.Coloring.mk
      (fun ⟨v, _⟩ => if v.val < 5 then (0 : Fin 2) else 1) ?_⟩
    intro ⟨u, hu⟩ ⟨v, hv⟩ hadj
    have hu_mem : u ∈ Finset.univ.erase (17 : Fin 18) := Finset.mem_coe.mp hu
    have hv_mem : v ∈ Finset.univ.erase (17 : Fin 18) := Finset.mem_coe.mp hv
    have hu_ne_center : u ≠ 17 := (Finset.mem_erase.mp hu_mem).1
    have hv_ne_center : v ≠ 17 := (Finset.mem_erase.mp hv_mem).1
    have hadj' : counterG.Adj u v := hadj
    rw [counterG_adj] at hadj'
    rcases hadj'.2 with hu17 | hv17 | huv | hvu
    · exact (hu_ne_center (Fin.ext hu17)).elim
    · exact (hv_ne_center (Fin.ext hv17)).elim
    · unfold coreForward at huv
      rcases huv with ⟨hu5, hv5, _hv10, _hdeleted⟩
      have hvNot5 : ¬v.val < 5 := Nat.not_lt.mpr hv5
      simp [hu5, hvNot5]
    · unfold coreForward at hvu
      rcases hvu with ⟨hv5, hu5, _hu10, _hdeleted⟩
      have huNot5 : ¬u.val < 5 := Nat.not_lt.mpr hu5
      simp [hv5, huNot5]

private lemma isCycle_triangle {α : Type*} {G : SimpleGraph α} {u v w : α}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwu : G.Adj w u)
    (hne1 : u ≠ v) (hne2 : v ≠ w) (hne3 : w ≠ u) :
    ∃ (p : G.Walk u u), p.IsCycle := by
  let p : G.Walk u u := Walk.cons huv (Walk.cons hvw (Walk.cons hwu Walk.nil))
  refine ⟨p, ?_⟩
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.cons_isPath_iff]
    constructor
    · rw [Walk.cons_isPath_iff]
      constructor
      · exact Walk.IsPath.nil
      · simp [hne3]
    · simp [hne1.symm, hne2]
  · simp [SimpleGraph.Walk.edges]
    tauto

private lemma isCycle_quad {α : Type*} {G : SimpleGraph α} {a b c d : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hne_ab : a ≠ b) (hne_bc : b ≠ c) (hne_cd : c ≠ d) (hne_da : d ≠ a)
    (hne_ac : a ≠ c) (hne_bd : b ≠ d) :
    ∃ (p : G.Walk a a), p.IsCycle := by
  let p : G.Walk a a :=
    Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil)))
  refine ⟨p, ?_⟩
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.cons_isPath_iff]
    constructor
    · rw [Walk.cons_isPath_iff]
      constructor
      · rw [Walk.cons_isPath_iff]
        constructor
        · exact Walk.IsPath.nil
        · simp [hne_da]
      · simp [hne_cd, hne_ac.symm]
    · simp [hne_bc, hne_bd, hne_ab.symm]
  · simp [SimpleGraph.Walk.edges]
    tauto

/-- Embed the ten-vertex bipartite core into the full graph. -/
private def coreEmbed : Fin 10 ↪ Fin 18 where
  toFun v := ⟨v.val, by omega⟩
  inj' := by
    intro u v h
    apply Fin.ext
    simpa using congrArg Fin.val h

private def selectedCore (s : Finset (Fin 18)) : Finset (Fin 10) :=
  Finset.univ.filter fun v => coreEmbed v ∈ s

private def coreAdj (u v : Fin 10) : Prop :=
  counterG.Adj (coreEmbed u) (coreEmbed v)

private instance coreAdj_decidable : DecidableRel coreAdj := fun u v => by
  unfold coreAdj counterG coreEmbed coreForward
  infer_instance

/-- Vertices `10,...,17`. -/
private def upperVertices : Finset (Fin 18) :=
  Finset.univ.filter fun v => 10 ≤ v.val

/-- Vertices `10,...,16`. -/
private def leaves : Finset (Fin 18) :=
  Finset.univ.filter fun v => 10 ≤ v.val ∧ v.val < 17

private lemma upperVertices_card : upperVertices.card = 8 := by
  decide

private lemma leaves_card : leaves.card = 7 := by
  decide

private lemma selected_subset_core_union_upper (s : Finset (Fin 18)) :
    s ⊆ (selectedCore s).map coreEmbed ∪ upperVertices := by
  intro v hv
  by_cases hv10 : v.val < 10
  · apply Finset.mem_union_left upperVertices
    let u : Fin 10 := ⟨v.val, hv10⟩
    have heq : coreEmbed u = v := by
      apply Fin.ext
      rfl
    have hu : u ∈ selectedCore s := by
      simp [selectedCore, heq, hv]
    exact Finset.mem_map.mpr ⟨u, hu, heq⟩
  · apply Finset.mem_union_right ((selectedCore s).map coreEmbed)
    simp [upperVertices, Nat.le_of_not_gt hv10]

private lemma selected_subset_core_union_leaves (s : Finset (Fin 18))
    (hc : (17 : Fin 18) ∉ s) :
    s ⊆ (selectedCore s).map coreEmbed ∪ leaves := by
  intro v hv
  by_cases hv10 : v.val < 10
  · apply Finset.mem_union_left leaves
    let u : Fin 10 := ⟨v.val, hv10⟩
    have heq : coreEmbed u = v := by
      apply Fin.ext
      rfl
    have hu : u ∈ selectedCore s := by
      simp [selectedCore, heq, hv]
    exact Finset.mem_map.mpr ⟨u, hu, heq⟩
  · apply Finset.mem_union_right ((selectedCore s).map coreEmbed)
    have hv_ne_center : v ≠ (17 : Fin 18) := by
      intro h
      subst v
      exact hc hv
    have hv_val_ne : v.val ≠ 17 := by
      intro h
      apply hv_ne_center
      apply Fin.ext
      simpa using h
    have hv_lt18 : v.val < 18 := v.isLt
    have hv17 : v.val < 17 := by omega
    simp [leaves, Nat.le_of_not_gt hv10, hv17]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Any six selected vertices of the ten-vertex core contain an edge. -/
private lemma six_core_has_edge :
    ∀ t : Finset (Fin 10), 6 ≤ t.card →
      ∃ u ∈ t, ∃ v ∈ t, u ≠ v ∧ coreAdj u v := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Any seven selected vertices of the ten-vertex core contain a 4-cycle. -/
private lemma seven_core_has_quad :
    ∀ t : Finset (Fin 10), 7 ≤ t.card →
      ∃ a ∈ t, ∃ b ∈ t, ∃ c ∈ t, ∃ d ∈ t,
        a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
          coreAdj a b ∧ coreAdj b c ∧ coreAdj c d ∧ coreAdj d a := by
  decide +kernel

private lemma large_with_center_has_edge :
    ∀ s : Finset (Fin 18), (17 : Fin 18) ∈ s → 14 ≤ s.card →
      ∃ u ∈ s, ∃ v ∈ s,
        u ≠ v ∧ u ≠ 17 ∧ v ≠ 17 ∧ counterG.Adj u v := by
  intro s _hc hs14
  have ht6 : 6 ≤ (selectedCore s).card := by
    have hcard := Finset.card_le_card (selected_subset_core_union_upper s)
    have hunion :=
      Finset.card_union_le ((selectedCore s).map coreEmbed) upperVertices
    rw [Finset.card_map, upperVertices_card] at hunion
    omega
  obtain ⟨u, hu, v, hv, huv, hadj⟩ := six_core_has_edge (selectedCore s) ht6
  have huS : coreEmbed u ∈ s := by simpa [selectedCore] using hu
  have hvS : coreEmbed v ∈ s := by simpa [selectedCore] using hv
  refine ⟨coreEmbed u, huS, coreEmbed v, hvS, ?_, ?_, ?_, ?_⟩
  · exact fun h => huv (coreEmbed.injective h)
  · intro h
    have hval : u.val = 17 := by simpa [coreEmbed] using congrArg Fin.val h
    have hlt : u.val < 10 := u.isLt
    omega
  · intro h
    have hval : v.val = 17 := by simpa [coreEmbed] using congrArg Fin.val h
    have hlt : v.val < 10 := v.isLt
    omega
  · simpa [coreAdj] using hadj

private lemma large_without_center_has_quad :
    ∀ s : Finset (Fin 18), (17 : Fin 18) ∉ s → 14 ≤ s.card →
      ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s,
        a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
          counterG.Adj a b ∧ counterG.Adj b c ∧
          counterG.Adj c d ∧ counterG.Adj d a := by
  intro s hc hs14
  have ht7 : 7 ≤ (selectedCore s).card := by
    have hcard := Finset.card_le_card (selected_subset_core_union_leaves s hc)
    have hunion := Finset.card_union_le ((selectedCore s).map coreEmbed) leaves
    rw [Finset.card_map, leaves_card] at hunion
    omega
  obtain ⟨a, ha, b, hb, c, hc', d, hd,
      hab_ne, hbc_ne, hcd_ne, hda_ne, hac_ne, hbd_ne,
      hab, hbc, hcd, hda⟩ := seven_core_has_quad (selectedCore s) ht7
  have haS : coreEmbed a ∈ s := by simpa [selectedCore] using ha
  have hbS : coreEmbed b ∈ s := by simpa [selectedCore] using hb
  have hcS : coreEmbed c ∈ s := by simpa [selectedCore] using hc'
  have hdS : coreEmbed d ∈ s := by simpa [selectedCore] using hd
  refine ⟨coreEmbed a, haS, coreEmbed b, hbS, coreEmbed c, hcS,
    coreEmbed d, hdS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hab_ne (coreEmbed.injective h)
  · exact fun h => hbc_ne (coreEmbed.injective h)
  · exact fun h => hcd_ne (coreEmbed.injective h)
  · exact fun h => hda_ne (coreEmbed.injective h)
  · exact fun h => hac_ne (coreEmbed.injective h)
  · exact fun h => hbd_ne (coreEmbed.injective h)
  · simpa [coreAdj] using hab
  · simpa [coreAdj] using hbc
  · simpa [coreAdj] using hcd
  · simpa [coreAdj] using hda

private lemma counterG_forest_le : counterG.largestInducedForestSize ≤ 13 := by
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    intro ⟨v, hv⟩
    simp at hv
  · intro n ⟨s, hacyclic, hcard⟩
    by_contra hnot
    have hs14 : 14 ≤ s.card := by omega
    by_cases hc : (17 : Fin 18) ∈ s
    · obtain ⟨u, hu, v, hv, huv, hu17, hv17, hadj⟩ :=
        large_with_center_has_edge s hc hs14
      let vc : s := ⟨17, hc⟩
      let vu : s := ⟨u, hu⟩
      let vv : s := ⟨v, hv⟩
      have hcu : (counterG.induce s).Adj vc vu := counterG_center_adj u hu17
      have huv' : (counterG.induce s).Adj vu vv := hadj
      have hvc : (counterG.induce s).Adj vv vc := (counterG_center_adj v hv17).symm
      have hc_ne_u : vc ≠ vu := by
        intro h
        exact hu17 (Subtype.ext_iff.mp h).symm
      have hu_ne_v : vu ≠ vv := fun h => huv (Subtype.ext_iff.mp h)
      have hv_ne_c : vv ≠ vc := by
        intro h
        exact hv17 (Subtype.ext_iff.mp h)
      obtain ⟨p, hp⟩ := isCycle_triangle hcu huv' hvc hc_ne_u hu_ne_v hv_ne_c
      exact hacyclic p hp
    · obtain ⟨a, ha, b, hb, c, hc', d, hd,
          hab_ne, hbc_ne, hcd_ne, hda_ne, hac_ne, hbd_ne,
          hab, hbc, hcd, hda⟩ := large_without_center_has_quad s hc hs14
      let va : s := ⟨a, ha⟩
      let vb : s := ⟨b, hb⟩
      let vc : s := ⟨c, hc'⟩
      let vd : s := ⟨d, hd⟩
      have hab' : (counterG.induce s).Adj va vb := hab
      have hbc' : (counterG.induce s).Adj vb vc := hbc
      have hcd' : (counterG.induce s).Adj vc vd := hcd
      have hda' : (counterG.induce s).Adj vd va := hda
      have hab_ne' : va ≠ vb := fun h => hab_ne (Subtype.ext_iff.mp h)
      have hbc_ne' : vb ≠ vc := fun h => hbc_ne (Subtype.ext_iff.mp h)
      have hcd_ne' : vc ≠ vd := fun h => hcd_ne (Subtype.ext_iff.mp h)
      have hda_ne' : vd ≠ va := fun h => hda_ne (Subtype.ext_iff.mp h)
      have hac_ne' : va ≠ vc := fun h => hac_ne (Subtype.ext_iff.mp h)
      have hbd_ne' : vb ≠ vd := fun h => hbd_ne (Subtype.ext_iff.mp h)
      obtain ⟨p, hp⟩ :=
        isCycle_quad hab' hbc' hcd' hda'
          hab_ne' hbc_ne' hcd_ne' hda_ne' hac_ne' hbd_ne'
      exact hacyclic p hp

@[category test, AMS 5]
theorem counterexample_conjecture59 :
    ¬ (⌈Real.sqrt ((residue counterG : ℝ) * b counterG)⌉ ≤
         (counterG.largestInducedForestSize : ℝ)) := by
  intro hconj
  have hprod :
      (169 : ℝ) < (residue counterG : ℝ) * b counterG := by
    rw [counterG_residue]
    calc
      (169 : ℝ) < 10 * 17 := by norm_num
      _ ≤ 10 * counterG.b :=
        mul_le_mul_of_nonneg_left counterG_b_ge (by norm_num)
  have hsqrt :
      (13 : ℝ) < Real.sqrt ((residue counterG : ℝ) * b counterG) := by
    calc
      (13 : ℝ) = Real.sqrt 169 := by norm_num
      _ < Real.sqrt ((residue counterG : ℝ) * b counterG) :=
        Real.sqrt_lt_sqrt (by norm_num) hprod
  have hsqrt_le_ceil :
      Real.sqrt ((residue counterG : ℝ) * b counterG) ≤
        (⌈Real.sqrt ((residue counterG : ℝ) * b counterG)⌉ : ℝ) := by
    exact Int.le_ceil _
  have hforest : (counterG.largestInducedForestSize : ℝ) ≤ 13 := by
    exact_mod_cast counterG_forest_le
  linarith

/-- Written on the Wall II Conjecture 59 is false, witnessed by `counterG`. -/
@[category research solved, AMS 5]
theorem conjecture59_false : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected),
      ⌈Real.sqrt ((residue G : ℝ) * b G)⌉ ≤
        (G.largestInducedForestSize : ℝ) := by
  constructor
  · intro h
    exact h.elim
  · intro hP
    exact counterexample_conjecture59 (hP (Fin 18) counterG counterG_connected)

end WrittenOnTheWallII.GraphConjecture59Counterexample
