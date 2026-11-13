/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.AffineOpenPerfectSourceModel
import WeilConjectures.AlgebraicGeometry.AffineOpenSupportedTargetModel
import WeilConjectures.AlgebraicGeometry.AffineOpenRealizationScalar
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Affine module models with supported cohomology

## References

* Stacks Project, Tags 08EJ, 08EB and 06Z0.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem affineSheafification_preservesFiniteLimits
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) :
    PreservesFiniteLimits (affinePerfectSheafification X U hU) := by
  let : (Modules.restrictFunctor hU.isoSpec.hom).Additive :=
    Functor.additive_of_preserves_binary_products _
  let A := X.presheaf.obj (op U)
  let T := tilde.functor A
  let : T.PreservesMonomorphisms := ⟨by
    intro M N g hg
    let : Mono g := hg
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro V s t h
    apply Subtype.ext
    funext x
    apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N)
      g.hom ((ModuleCat.mono_iff_injective g).mp inferInstance)
    exact congrArg (fun z ↦ z.val x) h⟩
  let : T.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels T
  let : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  unfold affinePerfectSheafification
  exact comp_preservesFiniteLimits _ _

set_option maxHeartbeats 500000 in
-- Elaborating the two derived localization comparisons and the model witnesses needs this limit.
set_option linter.unusedVariables false in
/-- Affine restriction admits a bounded finite-projective source model and a target
whose cohomology is elementwise power torsion. The comparison is full and additive
and intertwines the scalar identity of the source with restriction of global scalars.
(Stacks, Tags 08EJ, 08EB, 06Z0) -/
theorem perfect_support_affine_module_model
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E E' : schemeDerivedQCohCategory X)
    (hE : X.IsPerfect E.obj)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x)))
    (U : X.Opens) (hU : IsAffineOpen U) (k : ℤ) :
    let A := ↑(X.sheaf.obj.obj (op U))
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ)
      (M : DerivedCategory (ModuleCat.{u} A))
      (F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))),
      F.Full ∧ F.Additive ∧
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Finite A (P.X i)) ∧
      (∀ i : ℤ, Module.Projective A (P.X i)) ∧
      (∀ (i : ℤ) (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M),
        ∃ n : ℕ, (f.val (op U)) ^ n • m = 0) ∧
      ∃ (eP : F.obj (DerivedCategory.Q.obj P) ≅ R.obj E.obj)
        (eM : F.obj M ≅ R.obj (E'.obj⟦k⟧)),
        ∀ a : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}),
          F.map ((show A from a.val (op U)) • 𝟙 (DerivedCategory.Q.obj P)) ≫ eP.hom =
            eP.hom ≫ R.map (schemeDerivedScalar X a (𝟙 E.obj)) := by
  let A := ↑(X.presheaf.obj (op U))
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  let H := affinePerfectSheafification X U hU
  let : PreservesFiniteLimits H := affineSheafification_preservesFiniteLimits X U hU
  let : H.Additive := Functor.additive_of_preserves_binary_products H
  let : PreservesFiniteColimits H := by
    dsimp [H, affinePerfectSheafification]
    exact comp_preservesFiniteColimits _ _
  let F : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    H.mapDerivedCategory.{u + 1, w}
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings (Spec (X.presheaf.obj (op U))).toRingedSpace)) :=
    HasDerivedCategory.standard _
  obtain ⟨e, ⟨ce⟩, _, _⟩ := exists_affineQCohDerivedEquivalence.{u, u + 1, u + 1}
      (X.presheaf.obj (op U))
  obtain ⟨t, ⟨ct⟩⟩ := affine_localized_site_derived_transport.{u, u + 1, w} X U hU
  let G := e.functor ⋙
    (schemeDerivedQCohProperty (Spec (X.presheaf.obj (op U)))).ι ⋙ t.functor
  let : G.Full := inferInstance
  let c : DerivedCategory.Q ⋙ G ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight ce t.functor ≪≫ ct
  let d : G ≅ F := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ))
    (DerivedCategory.Q ⋙ G) (H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    G F c
  let : F.Full := Functor.Full.of_iso d
  have hF : Nonempty (DerivedCategory.Q ⋙ F ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
    ⟨H.mapDerivedCategoryFactors⟩
  obtain ⟨P, hb, hf, hp, ⟨eP⟩⟩ :=
    affine_open_perfect_source_model X E hE U hU F hF
  obtain ⟨M, htors, ⟨eM⟩⟩ :=
    affine_open_supported_target_model X f E' hSupport U hU k F hF
  refine ⟨P, M, F, inferInstance, inferInstance, hb, hf, hp, htors, eP, eM, ?_⟩
  intro a
  exact affine_open_realization_scalar X U hU F hF P E.obj eP a

end AlgebraicGeometry.Scheme
