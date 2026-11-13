/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.FreeCechComplexExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Abelian sheaf cohomology of injective module sheaves

## References

* Stacks Project, Tag 03FD.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- The underlying abelian sheaf of an injective module sheaf is acyclic for H.
This concerns an injective on its own site, without a closed immersion or torsion.
(Stacks, Tag 03FD.) -/
theorem Etale.subsingleton_H_underlying_of_injective_module
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Injective J] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J) q) := by
  let R : Sheaf X.smallEtaleTopology RingCat.{u + 1} :=
    (sheafCompose X.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ))
  obtain ⟨e, he⟩ := moduleSheaf_constantRing_equivalence Λ X
  let I : SheafOfModules.{u + 1} R := e.functor.obj J
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  have hI : Injective I := by infer_instance
  have htop : X.smallEtaleTopology.toPrecoverage.toGrothendieck =
      X.smallEtaleTopology := by
    apply le_antisymm
    · exact X.smallEtaleTopology.toGrothendieck_toPrecoverage_le
    · intro U S hS
      simpa only [Sieve.generate_sieve] using
        Precoverage.generate_mem_toGrothendieck
          ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ S).mpr hS)
  let P := X.smallEtaleTopology.toPrecoverage
  have hcech (U : X.Etale) (T : Type (u + 1)) (V : T → X.Etale)
      (f : ∀ t : T, V t ⟶ U) (hf : Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
      (p : ℕ) (hp : 0 < p) :
      IsZero (((cechComplexFunctor fun t : T ↦ Over.mk (f t)).obj
        ((Over.forget U).op ⋙ ((SheafOfModules.toSheaf R).obj I).obj)).homology p) := by
    have hcover : Presieve.ofArrows V f ∈ P U := hf
    obtain ⟨S⟩ := SiteCechComplex.exists_of_covering P hcover
    have hzero : IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
      have : Injective I.val := injective_module_sheaf_injective_presheaf R I
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
      change IsZero ((S.complex I.val.presheaf).homology (q + 1))
      apply HomologicalComplex.ExactAt.isZero_homology
      apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
        q (q + 1) (q + 2) (by simp) (by simp)).2
      rw [ShortComplex.ab_exact_iff]
      intro c hc
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
      rw [CochainComplex.of_d] at hc
      obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
        R.obj I.val V f S q c hc
      refine ⟨b, ?_⟩
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) q (q + 1)) b = c
      rw [CochainComplex.of_d]
      exact hb
    obtain ⟨e⟩ := Scheme.nonempty_etale_siteCech_complex_iso X U V f S I.val.presheaf
    exact hzero.of_iso ((HomologicalComplex.homologyFunctor _ _ p).mapIso e.symm)
  have hzero := Scheme.isZero_rightDerived_etale_of_cech_vanishing X Set.univ
    (fun U _ V f ↦ Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
    ((SheafOfModules.toSheaf R).obj I)
    (fun _ _ _ _ h ↦ h)
    (fun _ _ _ _ _ ↦ ⟨Set.mem_univ _, fun _ ↦ Set.mem_univ _,
      fun _ _ ↦ Set.mem_univ _⟩)
    (fun _ _ T V f hf ↦ ⟨T, V, f, hf, fun t ↦ ⟨t, 𝟙 _, by simp⟩⟩)
    hcech T (Set.mem_univ _) q hq
  let G := (SheafOfModules.toSheaf R).obj I
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ X
  let eΓ := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1} hT
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op T)).Additive :=
    Functor.additive_of_iso eΓ
  let eD : Γ.rightDerived q ≅
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (Opposite.op T)).rightDerived q :=
    ⟨eΓ.hom.rightDerived q, eΓ.inv.rightDerived q, by
      rw [← NatTrans.rightDerived_comp, eΓ.hom_inv_id, NatTrans.rightDerived_id], by
      rw [← NatTrans.rightDerived_comp, eΓ.inv_hom_id, NatTrans.rightDerived_id]⟩
  have hΓ : IsZero ((Γ.rightDerived q).obj G) := hzero.of_iso (eD.app G)
  let eSingle := Γ.homologyRightDerivedFunctorObjSingleFunctorIso G q
  obtain ⟨eH⟩ := Scheme.nonempty_sheafH_extDerivedIso X q
  have hHG : IsZero ((Sheaf.functorH X.smallEtaleTopology q).obj G) :=
    (hΓ.of_iso eSingle).of_iso (eH.app G)
  obtain ⟨eF⟩ := he
  have hHF := hHG.of_iso ((Sheaf.functorH X.smallEtaleTopology q).mapIso (eF.app J).symm)
  exact AddCommGrpCat.subsingleton_of_isZero hHF

end AlgebraicGeometry
