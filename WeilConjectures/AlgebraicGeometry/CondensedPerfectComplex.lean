/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
public import WeilConjectures.Compactification.FiniteFieldDatum.GeometricHypotheses
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeSitePerfectDual
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Topology.Irreducible
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.CondensedComponentScalarModel.CondensedComponentGenericScalarModels
import WeilConjectures.AlgebraicGeometry.CondensedComponentScalarModel.CondensedComponentScalarModelData
import WeilConjectures.AlgebraicGeometry.CondensedComponentScalarModel.CondensedClosedComponentCover
import WeilConjectures.AlgebraicGeometry.CondensedFiniteClopenModelGluing
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedPullbackSquare
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.CondensedScalarModelIntersection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationUnderivedModelData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationDerivedComparison
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldComplexCohomologySplitting
import WeilConjectures.CategoryTheory.DerivedCategory.ZetaWeil.RingDerivedDualizablePerfect

/-! # Perfect point and condensed coefficient complexes

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-global-duality-and-the-poincare-pairing/sk-thm-derived-duality/sk-def-perfect/_section.md,
order 3598 (blueprint: sk-def-perfect).

The point category is the ordinary module derived category of the singleton section ring.
The scheme category is the ordinary unbounded derived category of modules over p_X^Λ.
Its tensor is the published K-flat relative derived tensor, with the native Koszul symmetry.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w v t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The existence predicate is precisely the two triangle identities, with composition
written in Lean's left-to-right order. It does not choose a dual.
Source: blueprint order 3598, displayed duality identities (blueprint: sk-def-perfect).
Proof: unpack HasRightDual into its object and ExactPairing. The two ExactPairing
identities become the displayed identities by inserting the inverse source unitor and
cancelling the target unitor. Conversely cancel those unitors and construct ExactPairing,
then HasRightDual, from the evaluation and coevaluation. -/
theorem dualizable_iff_triangle_identities {C : Type t} [Category.{v} C]
    [MonoidalCategory C] (K : C) :
    IsDualizable K ↔
      ∃ (D : C) (e : D ⊗ K ⟶ 𝟙_ C) (c : 𝟙_ C ⟶ K ⊗ D),
        (λ_ K).inv ≫ c ▷ K ≫ (α_ K D K).hom ≫ K ◁ e ≫ (ρ_ K).hom = 𝟙 K ∧
        (ρ_ D).inv ≫ D ◁ c ≫ (α_ D K D).inv ≫ e ▷ D ≫ (λ_ D).hom = 𝟙 D := by
  constructor
  · rintro ⟨hK⟩
    let := hK
    refine ⟨Kᘁ, ε_ K Kᘁ, η_ K Kᘁ, ?_, ?_⟩ <;> simp
  · rintro ⟨D, e, c, hK, hD⟩
    refine ⟨{ rightDual := D, exact := {
      coevaluation' := c
      evaluation' := e
      coevaluation_evaluation' := ?_
      evaluation_coevaluation' := ?_ } }⟩
    · rw [← cancel_epi (ρ_ D).inv, ← cancel_mono (λ_ D).hom]
      simpa using hD
    · rw [← cancel_epi (λ_ K).inv, ← cancel_mono (ρ_ K).hom]
      simpa using hK

open TopologicalSpace

private theorem connected_affine_cover (X : Scheme.{u}) [IsLocallyNoetherian X] :
    ∃ C : Scheme.OpenCover.{u} X,
      ∀ i : C.I₀, IsAffine (C.X i) ∧ ConnectedSpace (C.X i) ∧
        (irreducibleComponents (C.X i)).Finite := by
  classical
  let A := X.affineCover
  let U (i : A.I₀) (x : A.X i) : (A.X i).Opens :=
    ⟨connectedComponent x, isOpen_connectedComponent⟩
  have hA (i : A.I₀) : IsLocallyNoetherian (A.X i) := inferInstance
  have hU (i : A.I₀) (x : A.X i) : IsAffineOpen (U i x) := by
    have : IsClosedImmersion (U i x).ι :=
      IsClosedImmersion.of_isPreimmersion (U i x).ι (by
        rw [Scheme.Opens.range_ι]
        change IsClosed (connectedComponent x)
        exact isClosed_connectedComponent)
    exact isAffine_of_isAffineHom (U i x).ι
  let C : Scheme.OpenCover.{u} X := Scheme.Cover.mkOfCovers
    (Σ i : A.I₀, A.X i) (fun j ↦ (U j.1 j.2).toScheme)
    (fun j ↦ (U j.1 j.2).ι ≫ A.f j.1)
    (fun x ↦ by
      obtain ⟨i, y, hy⟩ := A.exists_eq x
      exact ⟨⟨i, y⟩, ⟨y, mem_connectedComponent⟩, hy⟩)
    (fun _ ↦ inferInstance)
  refine ⟨C, fun j ↦ ?_⟩
  change IsAffine (U j.1 j.2).toScheme ∧ ConnectedSpace (U j.1 j.2).toScheme ∧
    (irreducibleComponents (U j.1 j.2).toScheme).Finite
  have : IsAffine (U j.1 j.2).toScheme := hU j.1 j.2
  have : IsLocallyNoetherian (U j.1 j.2).toScheme := inferInstance
  have : IsNoetherianRing Γ((U j.1 j.2).toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : NoetherianSpace (U j.1 j.2).toScheme := noetherianSpace_of_isAffine
  exact ⟨inferInstance, isConnected_iff_connectedSpace.mp isConnected_connectedComponent,
    NoetherianSpace.finite_irreducibleComponents⟩

open CondensedRing.Evaluation

private theorem scalar_finite_projective_map
    {R : Type (u + 1)} [CommRing R] (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (G : ModuleCat.{u + 1} R ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    [G.Additive] [G.Monoidal]
    (M : ModuleCat.{u + 1} R) [Module.Projective R M] [Module.Finite R M] :
    CondensedRing.IsFiniteProjectiveOnCoefficientSite Λ X (G.obj M) := by
  obtain ⟨n, ξ, m, hm⟩ := ModuleCat.exists_sum_comp_eq_id_of_projective M
  let e : G.obj (ModuleCat.of R R) ≅ Mod.regular (condensedRingObj Λ X) :=
    (Functor.Monoidal.εIso G).symm
  refine ⟨n, ⟨{
    i := biproduct.lift (fun j ↦ G.map (ξ j) ≫ e.hom)
    r := biproduct.desc (fun j ↦ e.inv ≫ G.map (m j))
    retract := ?_ }⟩⟩
  rw [biproduct.lift_desc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp, ← G.map_sum, hm,
    G.map_id]

private theorem scalar_perfect_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (K : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)))
    (hK : DerivedCategory.IsPerfectRingComplex K) :
    ∃ (P : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, CondensedRing.IsFiniteProjectiveOnCoefficientSite Λ X (P.X i)) ∧
      Nonempty ((condensedScalarRealization Λ X).obj K ≅ DerivedCategory.Q.obj P) := by
  classical
  let J := coherentTopology Profinite.{u}
  let L := terminalScalarRealization J Λ (⊤_ Profinite.{u}) terminalIsTerminal
  obtain ⟨hf, hb, hadj⟩ :=
    contractible_realization_underived_data J Λ (⊤_ Profinite.{u}) terminalIsTerminal
  let := hf
  let := hb
  let : L.Monoidal := hb.toMonoidal
  obtain ⟨ed⟩ := contractible_realization_derived_comparison J Λ
    (⊤_ Profinite.{u}) terminalIsTerminal L hadj
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    let : pointUpperStar.{u}.IsLeftAdjoint :=
      pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  let : (upperStarFromPoint X).Braided :=
    { toMonoidal := inferInstance, braided := Functor.LaxBraided.braided }
  let q := (upperStarFromPoint X).mapMod Λ
  have : q.Additive := Functor.additive_of_preserves_binary_products q
  let : q.Monoidal := by dsimp only [q]; infer_instance
  let G := L ⋙ q
  let : G.Monoidal := inferInstanceAs (L ⋙ q).Monoidal
  obtain ⟨P, a, b, ha, hbb, hp, ⟨eP⟩⟩ := hK
  let := ha
  let := hbb
  let H := (G.mapHomologicalComplex (.up ℤ)).obj P
  refine ⟨H, a, b, inferInstance, inferInstance, fun i ↦ ?_, ?_⟩
  · have := (hp i).1
    have := (hp i).2
    exact scalar_finite_projective_map X Λ G (P.X i)
  · have hkf : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P :=
      CochainComplex.kFlat_of_bounded_of_flat P a b (fun i ↦ by
        have := (hp i).1
        exact (ModuleCat.flat_iff_flat _).mpr inferInstance)
    have := L.isIso_leftDerivedFunctorCounit_app_of_kFlat P hkf
    let eL : L.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P) :=
      L.leftDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
        asIso (L.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
        DerivedCategory.Qh.mapIso ((L.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
        (DerivedCategory.quotientCompQhIso _).app
          ((L.mapHomologicalComplex (.up ℤ)).obj P)
    let eR : L.leftDerivedFunctor ⋙ q.mapDerivedCategory ≅ condensedScalarRealization Λ X :=
      Functor.isoWhiskerRight ed q.mapDerivedCategory ≪≫
        Functor.associator _ _ _
    refine ⟨(eR.app K).symm ≪≫
      (L.leftDerivedFunctor ⋙ q.mapDerivedCategory).mapIso eP ≪≫
      q.mapDerivedCategory.mapIso eL ≪≫ q.mapDerivedCategoryFactors.app _ ≪≫ ?_⟩
    exact DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl G) (.up ℤ)).app P)

private theorem dualizable_site_model
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (hK : IsDualizable K) : CondensedRing.IsPerfectOnCoefficientSite Λ.X X K := by
  classical
  obtain ⟨C, hC⟩ := connected_affine_cover X
  let C' := C.weaken
    (Scheme.zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))
  choose I W f hf hw using fun i : C.I₀ ↦
    Scheme.ProEt.exists_wContractible_affine_cover (C.X i) (Scheme.ProEt.mk (𝟙 (C.X i)))
  let B (i : C.I₀) : Scheme.Cover.{u} Scheme.proetalePrecoverage (C.X i) :=
    { I₀ := I i
      X := fun j ↦ (W i j).left
      f := fun j ↦ (f i j).left
      mem₀ := by
        have hh := hf i
        change (Presieve.ofArrows (W i) (f i)).map
          (Scheme.ProEt.forget (C.X i) ⋙ Over.forget (C.X i)) ∈
            Scheme.proetalePrecoverage (C.X i) at hh
        rw [Presieve.map_ofArrows] at hh
        exact hh }
  refine ⟨C'.bind B, ?_⟩
  rintro ⟨i, j⟩
  have : IsAffine (C.X i) := (hC i).1
  have : ConnectedSpace (C.X i) := (hC i).2.1
  let L := (CondensedRing.upperStar Λ.X (C.f i)).mapDerivedCategory.obj K
  have hL : IsDualizable L :=
    condensed_derivedPullback_preserves_dualizable Λ (C.f i) K hK
  obtain ⟨P, hP, hm⟩ := condensed_connected_contractible_model Λ
    (C.X i) (hC i).2.2 L hL
  obtain ⟨R, hR, e, S, φ, g, hg, hff, het, he⟩ := hw i j
  let := hR
  have haff : IsAffine (W i j).left := (IsAffine.iff_of_isIso e.hom).mp inferInstance
  have hwc : IsWContractibleRing Γ((W i j).left, ⊤) :=
    wContractible_of_ringEquiv
      ((Scheme.Γ.mapIso e.op) ≪≫ Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
  obtain ⟨em⟩ := hm (W i j) haff hwc
  obtain ⟨Q, a, b, ha, hb, hQ, ⟨eQ⟩⟩ := scalar_perfect_model Λ.X (W i j).left P hP
  refine ⟨Q, a, b, ha, hb, hQ, ⟨?_⟩⟩
  let F := CondensedRing.upperStar Λ.X (C.f i)
  let G := CondensedRing.upperStar Λ.X (W i j).hom
  have eqf : (f i j).left = (W i j).hom := by
    have h := (f i j).w
    change (f i j).left ≫ 𝟙 (C.X i) = (W i j).hom at h
    exact (Category.comp_id (f i j).left).symm.trans h
  change (CondensedRing.upperStar Λ.X ((f i j).left ≫ C.f i)).mapDerivedCategory.obj K ≅ _
  rw [eqf]
  exact (Functor.mapDerivedCategoryNatIso
    (CondensedRing.upperStarComp Λ.X (W i j).hom (C.f i))).app K ≪≫
      (Functor.mapDerivedCategoryCompIso F G).app K ≪≫ em ≪≫ eQ

private theorem site_model_dualizable
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : CondensedRing.IsPerfectOnCoefficientSite Λ X K) : IsDualizable K := by
  obtain ⟨_, ep, _⟩ := CondensedRing.native_sitePerfect_dual Λ X K hK
  let := ep
  let := condensedDerivedBraiding (Mon.mk Λ) X
  exact ⟨{ rightDual := (ihom K).obj (𝟙_ _)
           exact := BraidedCategory.exactPairing_swap _ _ }⟩

namespace CondensedRing

end CondensedRing
end AlgebraicGeometry.ProEtale
