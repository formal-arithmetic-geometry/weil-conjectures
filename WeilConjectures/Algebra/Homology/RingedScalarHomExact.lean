/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
public import WeilConjectures.Algebra.Homology.ScalarInternalHomDataSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientSystemScalarCalculus
public import WeilConjectures.CategoryTheory.SignedDerivedInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import WeilConjectures.SixFunctors.EvaluationShiftTransport
import WeilConjectures.CategoryTheory.ContravariantIsoLocus
import WeilConjectures.Algebra.Homology.RingedSignedHomEvaluation
import WeilConjectures.Algebra.Homology.RingedScalarTensorCancellation
import all WeilConjectures.Algebra.Homology.ScalarHomComparisonTower
import WeilConjectures.Algebra.Homology.DerivedScalarExtensionCounitShift
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift

/-! # Exactness of the evaluation-defined ringed scalar Hom comparison

Source: blueprint det-prop-scalar-six-tensor-hom, proof (2) Reduction;
Stacks Project, sites-cohomology.tex, Tags 08J9 and 08JC.
(blueprint: lem-sfb-ringed-scalar-hom-exact).

The scalar and tensor data below are the already recorded normalized models.
The comparison is the existing evaluation transpose `coefficientBaseChangeHom`.
The scalar shift is fixed by its universal counit, and the two Hom shifts by
both signed source-shift normalizations. No invertibility of the Hom comparison
is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
-- The four instance binders are fixed parts of the existing public statement.
set_option linter.unusedVariables false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)]
  (A : ScalarHomModels.{c, v, r, w} J)
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

/-- Scalar extension after contravariant derived Hom, with its target fixed.
Source: blueprint det-prop-scalar-six-tensor-hom, (2) Reduction; Stacks 08JC.
(blueprint: lem-sfb-ringed-scalar-hom-exact). -/
abbrev ringedScalarHomLeft (M : DerivedCategory (scalarModules J R)) :=
  (Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R) ⋙
    (A.scalar a).derived

/-- Contravariant derived Hom after scalar extension, with the extended target fixed.
Source: blueprint det-prop-scalar-six-tensor-hom, (2) Reduction; Stacks 08JC.
(blueprint: lem-sfb-ringed-scalar-hom-exact). -/
abbrev ringedScalarHomRight (M : DerivedCategory (scalarModules J R)) :=
  (A.scalar a).derived.op ⋙
    (Prod.sectL _ ((A.scalar a).derived.obj M) ⋙
      derivedInternalHomOfUniverses.{c, v, r, w} J S)

set_option maxHeartbeats 2000000 in
-- The normalized scalar and Hom comparisons elaborate large derived-category instances.
/-- The evaluation transpose is an exact natural comparison of contravariant functors.
The three shift witnesses are normalized, rather than arbitrary exact structures:
the scalar counit commutes with all integer shifts, and the two Hom shifts have
the degree-one negative and degree-minus-one positive representative normalization.
The functor shifts in the conclusion are their composite comparisons, including
the canonical opposite comparison on scalar extension.

Source: blueprint det-prop-scalar-six-tensor-hom, proof (2) Reduction;
Stacks sites-cohomology.tex, Tags 06YY, 07A4, 08J9, 08JC and 0A8X.
(blueprint: lem-sfb-ringed-scalar-hom-exact).

Proof:
1. Descend the coherent scalar shift through the universal right Kan extension
counit. Its degree-one normalization identifies it with the exact scalar shift.
2. Use signed derived-Hom exactness and native signed evaluation over each ring.
Transport the evaluation identity to the supplied closed tensor presentations;
composition gives the two exact contravariant functors in the statement.
3. Take beta to be the existing evaluation transpose coefficientBaseChangeHom.
Its naturality and defining evaluation equation are the scalar Hom comparison
identities. Permuting the product tensor arguments puts the source first and
uses no symmetric-monoidal coherence identification.
4. For every integer apply evaluation shift transport to the two signed Hom
evaluation identities, cancellation naturality and normalized scalar tensor
cancellation. Injectivity of transposition detects equality. The resulting
reindexed equations give CommShift for beta with the actual composite shifts.
5. Naturality supplies the first two triangle squares. In the third, move
beta[1] through the source shift comparison using its shift square and apply
naturality to the connecting map. This writes a morphism of image triangles.
6. The contravariant comparison lemma proves triangulated and retract closure
of the isomorphism locus. Naturality along an isomorphism proves isomorphism
closure. The argument never assumes every beta component is invertible.
-/
theorem ringedScalarHom_exact (μ : ScalarHomTensorComparison A a)
    (M : DerivedCategory (scalarModules J R)) :
    ∃ (sF : (A.scalar a).derived.CommShift ℤ)
      (sR : (Prod.sectL _ M ⋙
        derivedInternalHomOfUniverses.{c, v, r, w} J R).CommShift ℤ)
      (sS : (Prod.sectL _ ((A.scalar a).derived.obj M) ⋙
        derivedInternalHomOfUniverses.{c, v, r, w} J S).CommShift ℤ),
      (fun [ordinaryAdditive : (A.scalar a).extension.Additive]
        [scalarShift : (A.scalar a).derived.CommShift ℤ]
        [sourceHomShift : (Prod.sectL _ M ⋙
          derivedInternalHomOfUniverses.{c, v, r, w} J R).CommShift ℤ]
        [targetHomShift : (Prod.sectL _ ((A.scalar a).derived.obj M) ⋙
          derivedInternalHomOfUniverses.{c, v, r, w} J S).CommShift ℤ] ↦
        (∀ (n : ℤ) (P : HomotopyCategory (scalarModules J R) (.up ℤ)),
          (A.scalar a).derived.map ((DerivedCategory.Qh.commShiftIso n).hom.app P) ≫
              ((A.scalar a).derived.commShiftIso n).hom.app (DerivedCategory.Qh.obj P) ≫
              ((A.scalar a).counit.app P)⟦n⟧' =
            (A.scalar a).counit.app (P⟦n⟧) ≫
              DerivedCategory.Qh.map
                ((((A.scalar a).extension.mapHomotopyCategory (.up ℤ)).commShiftIso n).hom.app P) ≫
              (DerivedCategory.Qh.commShiftIso n).hom.app
                (((A.scalar a).extension.mapHomotopyCategory (.up ℤ)).obj P)) ∧
        (A.scalar a).derived.IsTriangulated ∧
        (Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R).IsTriangulated ∧
        (Prod.sectL _ ((A.scalar a).derived.obj M) ⋙
          derivedInternalHomOfUniverses.{c, v, r, w} J S).IsTriangulated ∧
        (∀ K : DerivedCategory (scalarModules J R),
          ((Prod.sectL _ M ⋙
            derivedInternalHomOfUniverses.{c, v, r, w} J R).commShiftIso (1 : ℤ)).hom.app (op K) =
              -(RingedHomUniverses.sourceShift.{c, v, r, w} J R K (-1)).inv.app M) ∧
        (∀ K : DerivedCategory (scalarModules J R),
          ((Prod.sectL _ M ⋙
            derivedInternalHomOfUniverses.{c, v, r, w} J R).commShiftIso (-1 : ℤ)).inv.app (op K) =
              (RingedHomUniverses.sourceShift.{c, v, r, w} J R K 1).hom.app M) ∧
        (∀ K : DerivedCategory (scalarModules J S),
          ((Prod.sectL _ ((A.scalar a).derived.obj M) ⋙
            derivedInternalHomOfUniverses.{c, v, r, w} J S).commShiftIso (1 : ℤ)).hom.app (op K) =
            -(RingedHomUniverses.sourceShift.{c, v, r, w} J S K (-1)).inv.app
              ((A.scalar a).derived.obj M)) ∧
        (∀ K : DerivedCategory (scalarModules J S),
          ((Prod.sectL _ ((A.scalar a).derived.obj M) ⋙
            derivedInternalHomOfUniverses.{c, v, r, w} J S).commShiftIso (-1 : ℤ)).inv.app (op K) =
            (RingedHomUniverses.sourceShift.{c, v, r, w} J S K 1).hom.app
              ((A.scalar a).derived.obj M)) ∧
        (ringedScalarHomLeft J A a M).IsTriangulated ∧
        (ringedScalarHomRight J A a M).IsTriangulated ∧
        ∃ β : ringedScalarHomLeft J A a M ⟶ ringedScalarHomRight J A a M,
          (∀ K : DerivedCategory (scalarModules J R), β.app (op K) =
            coefficientBaseChangeHom (A.closed R) (A.closed S)
              (A.scalar a).derived μ.iso K M) ∧
          NatTrans.CommShift β ℤ ∧
          (∀ T : Triangle (DerivedCategory (scalarModules J R))ᵒᵖ,
            T ∈ distTriang _ →
              ∃ f : (ringedScalarHomLeft J A a M).mapTriangle.obj T ⟶
                (ringedScalarHomRight J A a M).mapTriangle.obj T,
                f.hom₁ = β.app T.obj₁ ∧ f.hom₂ = β.app T.obj₂ ∧ f.hom₃ = β.app T.obj₃) ∧
          ObjectProperty.IsTriangulated (fun K ↦ IsIso (β.app (op K))) ∧
          ObjectProperty.IsClosedUnderIsomorphisms (fun K ↦ IsIso (β.app (op K))) ∧
          ObjectProperty.IsStableUnderRetracts (fun K ↦ IsIso (β.app (op K))))
        (ordinaryAdditive := (A.scalar a).extension_additive)
        (scalarShift := sF) (sourceHomShift := sR) (targetHomShift := sS) := by
  classical
  let F := (A.scalar a).derived
  let E := (A.scalar a).extension
  letI : E.Additive := (A.scalar a).extension_additive
  let ε : DerivedCategory.Qh ⋙ F ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := (A.scalar a).counit
  have hkan : F.IsRightKanExtension ε :=
    (A.scalar a).isLeftDerived.isRightKanExtension
  obtain ⟨sF, hε⟩ := Functor.rightKanExtension_coherentShift
    (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) DerivedCategory.Qh F ε hkan
  letI := sF
  letI := hε
  have hcounit (n : ℤ) (P : HomotopyCategory (scalarModules J R) (.up ℤ)) :
      F.map ((DerivedCategory.Qh.commShiftIso n).hom.app P) ≫
          (F.commShiftIso n).hom.app (DerivedCategory.Qh.obj P) ≫ (ε.app P)⟦n⟧' =
        ε.app (P⟦n⟧) ≫ DerivedCategory.Qh.map
            (((E.mapHomotopyCategory (.up ℤ)).commShiftIso n).hom.app P) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app
            ((E.mapHomotopyCategory (.up ℤ)).obj P) := by
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm ε n P
  letI := (A.scalar a).isLeftDerived
  obtain ⟨σ, _, huniq, _, htri⟩ := derivedScalarExtension_counitShift.{c, v, max c v r, w, w} a E
    (A.scalar a).extension_obj (A.scalar a).extension_map F ε
  have hσ : F.commShiftIso (1 : ℤ) = σ := huniq _ (hcounit 1)
  have hF : F.IsTriangulated := by
    constructor
    intro T hT
    change Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
      (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈ distTriang _
    rw [hσ]
    exact htri T hT
  letI := hF
  obtain ⟨sR, hR, hR₁, hR₂, hRev⟩ :=
    ringedSignedHom_evaluation.{c, v, r, w} J R (A.closed R) M
  obtain ⟨sS, hS, hS₁, hS₂, hSev⟩ :=
    ringedSignedHom_evaluation.{c, v, r, w} J S (A.closed S) (F.obj M)
  letI := sR
  letI := sS
  letI := hR
  letI := hS
  refine ⟨sF, sR, sS, hcounit, hF, hR, hS, hR₁, hR₂, hS₁, hS₂,
    inferInstance, inferInstance, ?_⟩
  let β : ringedScalarHomLeft J A a M ⟶ ringedScalarHomRight J A a M :=
    { app K := coefficientBaseChangeHom (A.closed R) (A.closed S) F μ.iso K.unop M
      naturality K L f := by
        simpa only [ringedScalarHomLeft, ringedScalarHomRight, Functor.comp_map,
          Prod.sectL, Functor.op_map, Quiver.Hom.op_unop, F.map_id] using
          scalarBaseChangeHom_naturality
          (A.closed R) (A.closed S) F μ.iso K.unop M L.unop M f.unop (𝟙 M) }
  let d := Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R
  let e := Prod.sectL _ (F.obj M) ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J S
  let B := Prod.swap _ _ ⋙ (A.closed R).tensor
  let U := Prod.swap _ _ ⋙ (A.closed S).tensor
  let μ' : B ⋙ F ≅ F.prod F ⋙ U := Functor.isoWhiskerLeft (Prod.swap _ _) μ.iso
  have detect (K P : DerivedCategory (scalarModules J S))
      (f g : P ⟶ e.obj (op K))
      (h : U.map (Prod.mkHom (𝟙 K) f) ≫ (A.closed S).evaluation K (F.obj M) =
        U.map (Prod.mkHom (𝟙 K) g) ≫ (A.closed S).evaluation K (F.obj M)) : f = g := by
    apply ((A.closed S).transpose P K (F.obj M)).symm.injective
    simpa only [scalarUncurry, U, Functor.comp_map, Prod.swap] using h
  have ewnat {K L : DerivedCategory (scalarModules J S)} (f : K ⟶ L) :
      U.map (Prod.mkHom f (𝟙 _)) ≫ (A.closed S).evaluation L (F.obj M) =
        U.map (Prod.mkHom (𝟙 K) (e.map f.op)) ≫
          (A.closed S).evaluation K (F.obj M) := by
    simpa only [U, e, Functor.comp_map, Prod.swap, Prod.sectL,
      Category.comp_id] using
      (scalarEvaluation_naturality (A.closed S) L (F.obj M) K (F.obj M) f (𝟙 _)).symm
  have hβ : NatTrans.CommShift β ℤ := by
    apply commShift_of_reindexed_components F d e β
    intro n K
    refine evaluation_shift_transport B U F d e M (F.obj M)
      (fun K ↦ (A.closed R).evaluation K M)
      (fun K ↦ (A.closed S).evaluation K (F.obj M)) detect (fun f ↦ ewnat f)
      μ' (𝟙 _) β ?_ n (reindexedDualShift d n) (reindexedDualShift e n)
      (fun K P ↦ RingedSignedTensor.cancellation.{c, v, r, w} J R (A.closed R) K P n)
      (fun K P ↦ RingedSignedTensor.cancellation.{c, v, r, w} J S (A.closed S) K P n)
      ?_ ?_ ?_ ?_ K
    · intro K
      simpa only [Category.comp_id, scalarUncurry, U, μ', β,
        d, Functor.comp_obj, Functor.comp_map, Prod.sectL, Prod.swap,
        Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app] using
        scalarBaseChangeHom_beta (A.closed R) (A.closed S) F μ.iso K M
    · intro K P Q f
      exact RingedSignedTensor.cancellation_natural.{c, v, r, w}
        J S (A.closed S) K f n
    · exact fun K ↦ hRev K n
    · exact fun K ↦ hSev K n
    · intro K P
      simpa only [U, μ', Functor.comp_map, Prod.swap,
        Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app] using
        ringedScalarTensor_cancellation.{c, v, r, w} J A a μ hcounit K P n
  letI := hβ
  obtain ⟨hlocus, hretract⟩ := contravariantComparison_isoLocus β
  refine ⟨β, fun _ ↦ rfl, hβ, ?_, hlocus, ?_, hretract⟩
  · intro T _
    refine ⟨{ hom₁ := β.app T.obj₁, hom₂ := β.app T.obj₂, hom₃ := β.app T.obj₃
              comm₁ := β.naturality T.mor₁
              comm₂ := β.naturality T.mor₂
              comm₃ := ?_ }, rfl, rfl, rfl⟩
    change ((ringedScalarHomLeft J A a M).map T.mor₃ ≫
      ((ringedScalarHomLeft J A a M).commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        (β.app T.obj₁)⟦(1 : ℤ)⟧' = β.app T.obj₃ ≫
      ((ringedScalarHomRight J A a M).map T.mor₃ ≫
        ((ringedScalarHomRight J A a M).commShiftIso (1 : ℤ)).hom.app T.obj₁)
    rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc, β.naturality]
    exact Category.assoc _ _ _
  · constructor
    intro K L e hK
    letI := hK
    exact (NatTrans.isIso_app_iff_of_iso β e.op).mpr inferInstance

end CategoryTheory
