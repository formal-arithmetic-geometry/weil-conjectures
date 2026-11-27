/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportClauses
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.CategoryTheory.StageSystem.Functor
import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportShiftDescent
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportEpsilonNaturality

/-! # A step of normalized isomorphism transport

The finite-field transport clauses for pullback along an isomorphism descend to the common
algebraically closed coefficient stage.

## Implementation details

The stage comparisons come from the normalized descent of common-stage pullback, so the object
and arrow clauses are the descended formulas and each stage comparison is the identity. The
scalar inverse squares make the finite-stage counits a compatible family, which descends to the
common-stage counit; applying the same argument to `inv g` gives the equivalence. The
finite-stage shifts descend, and exactness holds because every distinguished triangle is
represented at a finite stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option linter.privateModule false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients (ofHom inclusion)
open CategoryTheory.Pretriangulated

section Descent
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

attribute [local irreducible] rationalDerivedPullback commonStagePullbackComparison
  ObjectProperty.FullSubcategory.category

private theorem pullback_stage_comparison :
    ∃ c : ∀ E : Index l Ω,
      inclusion (Y := Y) E ⋙ commonStageDerivedPullback l Ω g ≅
        rationalDerivedPullback l (Coefficient.{u} l Ω E) g ⋙ inclusion (Y := X) E,
      ∀ (E : Index l Ω)
        (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
        HEq ((c E).hom.app K) (𝟙 (commonStagePullbackObject l Ω g
          ((inclusion (Y := Y) E).obj K))) := by
  obtain ⟨hcoh, hM⟩ := commonStagePullbackNormalizedDescent l Ω g
  rw [hM]
  exact ⟨fun E ↦ StageSystem.Morphism.ιCompFunctorIso _ E, fun E K ↦ HEq.rfl⟩

private theorem pullback_object (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω g).obj P = commonStagePullbackObject l Ω g P :=
  (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1 P

end Descent

section Inverse
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
  (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
  (S : ∀ E : Index l Ω,
    IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY)

attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback
  ObjectProperty.FullSubcategory.category

private def epsilon_component (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω (inv g)).obj P ≅ P :=
  eqToIso (congrArg (commonStageDerivedPullback l Ω (inv g)).obj
      (pullback_object l Ω g P)) ≪≫
    eqToIso (pullback_object l Ω (inv g) (commonStagePullbackObject l Ω g P)) ≪≫
      (inclusion (Y := Y) P.stage).mapIso ((S P.stage).rationalEpsilon.app P.obj)

private theorem epsilon_component_formula
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    HEq (epsilon_component l Ω g hX hY S P).hom
      ((inclusion (Y := Y) P.stage).map ((S P.stage).rationalEpsilon.hom.app P.obj)) := by
  simp only [epsilon_component, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Iso.app_hom]
  exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _)

private theorem pullback_epsilon
    (hS : ∀ (E L : Index l Ω) (h : E ≤ L),
      isomorphismFieldTransportRationalScalarLaw l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) g hX hY (S E) (S L)) :
    ∃ ε : commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω (inv g) ≅
        𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω Y),
      ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
        HEq (ε.hom.app P)
          ((inclusion (Y := Y) P.stage).map ((S P.stage).rationalEpsilon.hom.app P.obj)) := by
  let e := epsilon_component l Ω g hX hY S
  have he := epsilon_component_formula l Ω g hX hY S
  refine ⟨NatIso.ofComponents e (fun {P Q} f ↦ ?_), he⟩
  exact isomorphismFieldTransportEpsilonNaturality l Ω g hX hY S hS e he P Q f

end Inverse

attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback
  ObjectProperty.FullSubcategory.category

/-- If pullback along an isomorphism `g` and along `inv g` satisfy the finite-field clauses
`S`, `R` at every stage, compatibly with rational scalar extension, then common-stage pullback
along `g` satisfies the common-stage clauses `IsomorphismFieldTransportCommon`. -/
theorem isomorphismFieldTransportCommonStage
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [IsNoetherian X] [IsNoetherian Y]
    (_hDimX : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hDimY : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY)
    (R : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) (inv g) hY hX)
    (hS : ∀ (E L : Index l Ω) (h : E ≤ L),
      isomorphismFieldTransportRationalScalarLaw l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) g hX hY (S E) (S L))
    (hR : ∀ (E L : Index l Ω) (h : E ≤ L),
      isomorphismFieldTransportRationalScalarLaw l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) (inv g) hY hX (R E) (R L)) :
    Nonempty (IsomorphismFieldTransportCommon l Ω g hX hY S) := by
  obtain ⟨c, hc⟩ := pullback_stage_comparison l Ω g
  obtain ⟨q, hq⟩ := isomorphismFieldTransportShiftDescent l Ω g hX hY S c hc
  let : (commonStageDerivedPullback l Ω g).CommShift ℤ := q
  have hExact : (commonStageDerivedPullback l Ω g).IsTriangulated := by
    constructor
    intro T hT
    obtain ⟨E, U, hU, ⟨e⟩⟩ :=
      (GeneralAlgebraicallyClosedCoefficients.distinguished_iff T).1 hT
    let : (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ :=
      (S E).rationalShift
    let : (inclusion (Y := X) E).CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E
    let : (inclusion (Y := Y) E).CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E
    have : (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).IsTriangulated :=
      (S E).rationalExact
    have : NatTrans.CommShift (c E).hom ℤ := hq E
    have : (inclusion (Y := X) E).IsTriangulated :=
      GeneralAlgebraicallyClosedCoefficients.inclusion_exact E
    have : (rationalDerivedPullback l (Coefficient.{u} l Ω E) g ⋙
        inclusion (Y := X) E).IsTriangulated := inferInstance
    have : (inclusion (Y := Y) E ⋙ commonStageDerivedPullback l Ω g).IsTriangulated :=
      Functor.isTriangulated_of_iso (c E).symm
    exact isomorphic_distinguished _
      ((inclusion (Y := Y) E ⋙ commonStageDerivedPullback l Ω g).map_distinguished U hU) _
      ((commonStageDerivedPullback l Ω g).mapTriangle.mapIso e ≪≫
        (Functor.mapTriangleCompIso (inclusion (Y := Y) E)
          (commonStageDerivedPullback l Ω g)).symm.app U)
  have : (commonStageDerivedPullback l Ω g).IsTriangulated := hExact
  obtain ⟨ε, hε⟩ := pullback_epsilon l Ω g hX hY S hS
  obtain ⟨ε', _⟩ := pullback_epsilon l Ω (inv g) hY hX R hR
  have eInv : inv (inv g) = g := by simp
  rw [eInv] at ε'
  let e := CategoryTheory.Equivalence.mk (commonStageDerivedPullback l Ω g)
    (commonStageDerivedPullback l Ω (inv g)) ε.symm ε'
  have hEquiv : (commonStageDerivedPullback l Ω g).IsEquivalence :=
    e.isEquivalence_functor
  exact ⟨{
    equivalence := hEquiv
    shift := q
    exact := hExact
    additive := inferInstance
    stageComparison := c
    stage_comparison_formula := hc
    stage_shift := hq
    object_formula := pullback_object l Ω g
    arrow_formula := by
      unfold commonStageDerivedPullback
      exact (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.2
    epsilon := ε
    epsilon_formula := hε }⟩

end WeilConjectures
