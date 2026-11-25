/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.SixFunctors.ProEtale.InternalPrincipalConeHomReflection
import WeilConjectures.SixFunctors.ProEtale.InternalQuotientPrincipalConeComparison

/-! # Completeness of the internal quotient Roos completion

## References

* [Stacks, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.AdicCompletion

/-- The actual Roos completion of a K-flat representative is itself complete. -/
theorem isDerivedComplete_roos
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (P : CochainComplex (Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P) :
    IsDerivedComplete l E X (DerivedCategory.Q.obj (roos l E X P)) := by
  obtain ⟨d, hd, _⟩ := DerivedNakayama.derived_nakayama_resolution l E
  obtain ⟨cP, _⟩ := internal_quotient_principal_cone_comparison l E X d hd P hP
  obtain ⟨R, q, hq, _, hR⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (roos l E X P)
  have := hq
  let eR := asIso (DerivedCategory.Q.map q)
  let e := eR ≪≫ cP.symm
  obtain ⟨cR, hcR⟩ := internal_quotient_principal_cone_comparison l E X d hd R hR
  let v := DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit
    (End.of (DerivedNakayama.scalarOnComplex l E X d R)))
  obtain ⟨r, hr⟩ :=
    (internal_principal_cone_hom_reflection l E X d hd R P).surjective e.hom
  change v ≫ r = e.hom at hr
  let s := r ≫ e.inv
  have hs : v ≫ s = 𝟙 _ := by
    dsimp only [s]
    rw [← Category.assoc, hr, Iso.hom_inv_id]
  have hright : s ≫ v = 𝟙 _ := by
    apply (internal_principal_cone_hom_reflection l E X d hd R R).injective
    change v ≫ (s ≫ v) = v ≫ 𝟙 _
    rw [← Category.assoc, hs, Category.id_comp, Category.comp_id]
  have : IsIso v := ⟨⟨s, hs, hright⟩⟩
  have : IsIso (DerivedCategory.Q.map (augmentation l E X R)) := by
    rw [← hcR]
    exact inferInstanceAs (IsIso (v ≫ cR.hom))
  exact ⟨R, hR, ⟨eR⟩, inferInstance⟩

end AlgebraicGeometry.ProEtale.AdicCompletion
