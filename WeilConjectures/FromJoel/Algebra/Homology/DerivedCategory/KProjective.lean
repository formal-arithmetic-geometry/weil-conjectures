/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Morphisms from K-projective complexes in the derived category

Supplement to `Mathlib.Algebra.Homology.DerivedCategory.KProjective`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.32.0`.

-/

@[expose] public section

open CategoryTheory Localization DerivedCategory

variable {C : Type*} [Category C] [Abelian C]

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard in
lemma IsKProjective.isIso_quotient_map_iff_quasiIso
    {K L : CochainComplex C ℤ} [K.IsKProjective] [L.IsKProjective]
    (f : K ⟶ L) :
    IsIso ((HomotopyCategory.quotient _ _).map f) ↔ QuasiIso f := by
  trans IsIso (Qh.map ((HomotopyCategory.quotient _ _).map f))
  · refine ⟨fun _ ↦ inferInstance, fun _ ↦ ?_⟩
    let φ := Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f)
    obtain ⟨ψ, hψ⟩ := (IsKProjective.Qh_map_bijective _ _).2 (inv φ)
    refine ⟨ψ, ?_, ?_⟩
    all_goals exact (IsKProjective.Qh_map_bijective _ _).1 (by cat_disch)
  · rw [← isIso_Q_map_iff_quasiIso]
    apply (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    exact Arrow.isoMk ((quotientCompQhIso C).app _) ((quotientCompQhIso C).app _)

open HomologicalComplex in
lemma quasiIso_iff_homotopyEquivalences_of_isKProjective {K L : CochainComplex C ℤ}
    (f : K ⟶ L) [K.IsKProjective] [L.IsKProjective] :
    QuasiIso f ↔ homotopyEquivalences _ _ f := by
  rw [← isIso_quotient_map_iff_homotopyEquivalences,
    IsKProjective.isIso_quotient_map_iff_quasiIso]

end CochainComplex
