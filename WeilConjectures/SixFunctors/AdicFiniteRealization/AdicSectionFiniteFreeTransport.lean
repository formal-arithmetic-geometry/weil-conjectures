/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationData
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicSectionLocalFreeness
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicSectionInverseImageComparison
import all WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteFreeScalarTransport
import WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement
import WeilConjectures.Mathlib.Topology.Constructible

/-! # Finite-free targets under section encoding

Section encoding preserves and reflects the stratified finite-free target.

## Implementation details

The section equivalence preserves and reflects the standard degree bounds and identifies each
homology module with the section encoding of internal homology; on each stratum, the section
inverse-image comparison and local finite-freeness detection give the same criterion. For the
reverse direction, the constructibility fields of a stratification are restored using that
every locally closed subset of a noetherian space is constructible.

## References

- Stacks Project, Tags 00YV, 03D2, 03DM and 03DO.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures.AdicFiniteRealization

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private theorem stratum_sections (T : Scheme.{u})
    (A : Sheaf (ProEt.topology T) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) A)
    (X : Scheme.{u}) (f : X ⟶ T) :
    (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ j : C.I₀,
      Mod.IsFree ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (C.f j)).obj
          ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).obj A))
        (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (C.f j)).mapMod _).obj
          (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).mapMod A).obj M))) ↔
      ((proEtaleModuleInverseImage f
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (ProEt.topology T) A)).obj
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (ProEt.topology T) A).functor.obj M)).IsFiniteLocallyFree := by
  obtain ⟨c, ⟨e⟩⟩ := sectionModule_inverseImage X T f A M
  exact (sectionModule_locallyFree_iff X _ _).trans
    ((lf_iso e).trans (lf_restrict c _))

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Section encoding preserves and reflects the stratified finite-free target. -/
theorem section_finiteFreeTarget (T : Scheme.{u}) [IsNoetherian T]
    (A : Sheaf (ProEt.topology T) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) A)) :
    internalFiniteFreeTarget T A K ↔
      finiteFreeTarget T
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (ProEt.topology T) A) ((sectionDerived T A).obj K) := by
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T) A
  let := Functor.additive_of_preserves_binary_products E.functor
  let := Functor.additive_of_preserves_binary_products E.inverse
  have hD : sectionDerived T A = E.mapDerivedCategory.functor := by
    unfold sectionDerived
    rfl
  have hq (q : ℤ) (X : Scheme.{u}) (f : X ⟶ T) :
      ((proEtaleModuleInverseImage f
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (ProEt.topology T) A)).obj
        (E.functor.obj ((DerivedCategory.homologyFunctor _ q).obj K))).IsFiniteLocallyFree ↔
      ((proEtaleModuleInverseImage f
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (ProEt.topology T) A)).obj
        ((DerivedCategory.homologyFunctor _ q).obj
          ((sectionDerived T A).obj K))).IsFiniteLocallyFree := by
    rw [hD]
    exact lf_iso ((proEtaleModuleInverseImage f _).mapIso
      ((E.functor.mapDerivedCategoryHomologyFunctorIso q).app K))
  constructor
  · rintro ⟨⟨a, b, hab, ha, hb⟩, hs⟩
    let := ha
    let := hb
    refine ⟨⟨a, b, hab, ?_, ?_⟩, fun q ↦ ?_⟩
    · rw [hD]
      exact E.functor.isGE_mapDerivedCategory_obj K a
    · rw [hD]
      exact E.functor.isLE_mapDerivedCategory_obj K b
    · obtain ⟨S, hS⟩ := hs q
      exact ⟨S.toFiniteLocallyClosed, fun i ↦ (hq q _ _).mp
        ((stratum_sections T A _ _ _).mp (hS i))⟩
  · rintro ⟨⟨a, b, hab, ha, hb⟩, hs⟩
    rw [hD] at ha hb
    have h := E.functor.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
      (X := K) (a := a) (b := b) ⟨ha, hb⟩
    refine ⟨⟨a, b, hab, h.1, h.2⟩, fun q ↦ ?_⟩
    obtain ⟨S, hS⟩ := hs q
    have hc (i : Fin S.n) : Topology.IsConstructible (S.stratum i) :=
      (S.isLocallyClosed_stratum i).isConstructible_of_noetherianSpace
    exact ⟨S.withConstructibleStrata hc, fun i ↦ (stratum_sections T A _ _ _).mpr
      ((hq q _ _).mpr (hS i))⟩

end WeilConjectures.AdicFiniteRealization
