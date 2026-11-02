/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.CategoryTheory.RingedSignedTensor.RingedTensorSignedCancellation
public import WeilConjectures.CategoryTheory.Site.SitePerfectScalarHomComparison
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.ProjectiveHomEvaluationModel
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.LinearAlgebra.Contraction
public import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingClassicalGenerator
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.ZetaWeil.RingDerivedDualizablePerfect
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperExchangeComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperCompactificationCoincidence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily

/-!
# The native scalar cup product

Source: current `sk-cor-trace.proof.md`, Complement (iii), ordinary cup and removal
of the degree-zero Tate line (blueprint: lem-pd-cup-graded-commutativity).

All maps below are built from the recorded ordinary module adjunction, its K-flat
tensorator, terminal sections, and the compactification projection. No new tensor,
sections functor, constructibility predicate, or proper comparison is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CupGradedCommutativity

open CompactificationReindexing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Use the published small derived category for scalar modules.
Source: ordinary scalar module derived category in Complement (iii)
(blueprint: lem-pd-cup-graded-commutativity). -/
local instance scalarHasDerivedCategory :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (Γ Λ)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The native ordinary cup is the adjunct of the K-flat pullback tensorator followed
by the tensor of the two specified counits.
Source: current sk-cor-trace Complement (iii), ordinary cup construction
(blueprint: lem-pd-cup-graded-commutativity). -/
def siteCup {X Y : Scheme.{u}} (a : X ⟶ Y) (K L : D Λ X) :
    (R Λ a).obj K ⊗ (R Λ a).obj L ⟶ (R Λ a).obj (K ⊗ L) :=
  (derivedUpperStarLowerStarAdjunction Λ a).homEquiv _ _
    (((leftDerivedUpperStarTensor Λ a).app ((R Λ a).obj K)).app ((R Λ a).obj L) ≫
      ((derivedUpperStarLowerStarAdjunction Λ a).counit.app K ⊗ₘ
        (derivedUpperStarLowerStarAdjunction Λ a).counit.app L))

/-- Terminal sections of the tensor-of-counits cup, preceded by the normalized point
section tensor comparison. Only the comparison map is used, not an ambient equivalence.
Source: current sk-cor-trace Complement (iii), scalar realization
(blueprint: lem-pd-cup-graded-commutativity). -/
def scalarCup (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) (K L : D Λ X) :
    (condensedRingOrdinaryCoefficientComplex Λ a).obj K ⊗
        (condensedRingOrdinaryCoefficientComplex Λ a).obj L ⟶
      (condensedRingOrdinaryCoefficientComplex Λ a).obj (K ⊗ L) :=
  TraceCupPoint.tensor Λ k ((R Λ a).obj K) ((R Λ a).obj L) ≫
    (TraceCupPoint.fiber Λ k).map (siteCup Λ a K L)

/-- The site cup is the module projection/counit product, and both the site and scalar
equations express agreement with the compact projection/counit product. The module
projection is the recorded `moduleObjectProjectionMap`; the scalar equation uses exactly
the same point tensor.
Source: current sk-cor-trace Complement (iii), mixed-support product
(blueprint: lem-pd-cup-graded-commutativity). -/
def ProperProductComparison (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsProper a] (K L : D Λ X) : Prop :=
  siteCup Λ a K L =
      (moduleObjectProjectionMap Λ a K ((R Λ a).obj L) :
        (R Λ a).obj K ⊗ (R Λ a).obj L ⟶ (R Λ a).obj (K ⊗ (P Λ a).obj ((R Λ a).obj L))) ≫
        (R Λ a).map (K ◁ (derivedUpperStarLowerStarAdjunction Λ a).counit.app L) ∧
  ∀ c : Compactification a,
    let κ := properComparison Λ c
    let mixed := (derivedUpperStarLowerStarAdjunction Λ a).cupProductOfProjection
      (F Λ c) (exceptionalProjectionMorphismOfCompactification Λ c) K L
    (κ.app K ▷ (R Λ a).obj L ≫ siteCup Λ a K L = mixed ≫ κ.app (K ⊗ L)) ∧
    (TraceCupPoint.tensor Λ k ((F Λ c).obj K) ((R Λ a).obj L) ≫
        (TraceCupPoint.fiber Λ k).map mixed ≫
        (TraceCupPoint.fiber Λ k).map (κ.app (K ⊗ L)) =
      ((TraceCupPoint.fiber Λ k).map (κ.app K) ⊗ₘ 𝟙 _) ≫ scalarCup Λ k a K L)

/-- Multiplication of the coefficient unit after the ordinary scalar lax tensor map.
Source: current sk-cor-trace Complement (iii), ordinary cup on B_X
(blueprint: lem-pd-cup-graded-commutativity). -/
def multiplication (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) :
    (condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ (D Λ X)) ⊗
        (condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ (D Λ X)) ⟶
      (condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ (D Λ X)) :=
  scalarCup Λ k a (𝟙_ _) (𝟙_ _) ≫
    (condensedRingOrdinaryCoefficientComplex Λ a).map (λ_ (𝟙_ (D Λ X))).hom

set_option maxHeartbeats 1600000 in
-- The projective scalar-unit comparison elaborates large derived-category instances.
/-- The standard projective-unit representative identification, evaluated at one.
This is the generic module-derived comparison, independent of coefficient models.
Source: current sk-cor-trace Complement (iii), scalar cohomology representatives
(blueprint: lem-pd-cup-graded-commutativity). -/
def cohomologyClassEquiv (M : DerivedCategory (ModuleCat.{u + 1} (Γ Λ))) (i : ℤ) :
    ((𝟙_ (DerivedCategory (ModuleCat.{u + 1} (Γ Λ)))) ⟶ M⟦i⟧) ≃
      ↥((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M) :=
  ((DerivedCategory.singleFunctorObjUnitIso _).symm.homCongr (Iso.refl _)).trans
    (((DerivedCategory.shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso
      (ModuleCat.of.{u + 1} (Γ Λ) (Γ Λ)) i).app M).addCommGroupIsoToAddEquiv.toEquiv.trans
        ((ModuleCat.homLinearEquiv (R := Γ Λ) (S := ℤ)
          (M := ModuleCat.of.{u + 1} (Γ Λ) (Γ Λ))
          (N := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M)).toEquiv.trans
          (LinearMap.ringLmapEquivSelf (Γ Λ) ℤ
            ↥((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M)).toEquiv))

set_option maxHeartbeats 1600000 in
-- Give the scalar complex explicitly to avoid metavariable-driven instance search.
/-- Ordinary cup on the actual scalar cohomology modules, formed by tensoring unit-map
representatives, extracting their shifts, and applying coefficient multiplication.
Source: current sk-cor-trace Complement (iii), homogeneous classes
(blueprint: lem-pd-cup-graded-commutativity). -/
def cup (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) (i j : ℤ)
    (x : (condensedRingOrdinaryCohomology Λ a i).obj (𝟙_ (D Λ X)))
    (y : (condensedRingOrdinaryCohomology Λ a j).obj (𝟙_ (D Λ X))) :
    (condensedRingOrdinaryCohomology Λ a (i + j)).obj (𝟙_ (D Λ X)) :=
  let M := (condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ (D Λ X))
  let x' := (cohomologyClassEquiv Λ M i).symm x
  let y' := (cohomologyClassEquiv Λ M j).symm y
  let mulMap := multiplication Λ k a
  cohomologyClassEquiv Λ M (i + j)
    ((λ_ _).inv ≫ (x' ⊗ₘ y') ≫
      (DerivedCategory.shiftTensorShiftIso _ M M i j).hom ≫
        mulMap⟦i + j⟧')

/-- Untwisting a pulled-back degree-zero line using any of its bases. A line is
represented invariantly by a point complex isomorphic to the coefficient unit.
Source: current sk-cor-trace Complement (iii), free rank-one degree-zero line
(blueprint: lem-pd-cup-graded-commutativity). -/
def untwist {X Y : Scheme.{u}} (a : X ⟶ Y) (V : D Λ Y)
    (basis : V ≅ 𝟙_ (D Λ Y)) (K : D Λ X) : K ⊗ (P Λ a).obj V ⟶ K :=
  K ◁ ((P Λ a).map basis.hom ≫ (leftDerivedUpperStarUnitIso Λ a).hom) ≫ (ρ_ K).hom

/-- Both product comparisons for a pulled-back free line, and the naturality squares
which remove its basis in either factor. The assertion quantifies over every basis.
Source: current sk-cor-trace Complement (iii), tensoring and untwisting
(blueprint: lem-pd-cup-graded-commutativity). -/
def LineCompatibility (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsProper a] (K L : D Λ X) : Prop :=
  ∀ (V : D Λ (Spec (.of k))) (basis : V ≅ 𝟙_ (D Λ (Spec (.of k)))),
    ProperProductComparison Λ k a (K ⊗ (P Λ a).obj V) L ∧
    ProperProductComparison Λ k a K (L ⊗ (P Λ a).obj V) ∧
    (((condensedRingOrdinaryCoefficientComplex Λ a).map (untwist Λ a V basis K) ⊗ₘ
        𝟙 _) ≫ scalarCup Λ k a K L =
      scalarCup Λ k a (K ⊗ (P Λ a).obj V) L ≫
        (condensedRingOrdinaryCoefficientComplex Λ a).map
          (untwist Λ a V basis K ⊗ₘ 𝟙 L)) ∧
    ((𝟙 _ ⊗ₘ (condensedRingOrdinaryCoefficientComplex Λ a).map
        (untwist Λ a V basis L)) ≫ scalarCup Λ k a K L =
      scalarCup Λ k a K (L ⊗ (P Λ a).obj V) ≫
        (condensedRingOrdinaryCoefficientComplex Λ a).map
          (𝟙 K ⊗ₘ untwist Λ a V basis L))

set_option maxHeartbeats 1600000 in
-- The statement compares several fully specified derived functor composites.
/-- The canonical scalar lax cup for smooth proper X over Fbar_q is Koszul symmetric,
equals the proper mixed-support projection/counit cup, is graded commutative on all
integer scalar cohomology groups, and is unchanged by a degree-zero scalar line.

The coefficient hypothesis is precisely the continuous E or finite-subextension-valued
Qbar_l case of def-pur-admissible-condensed-ring. No model over the finite field or
pure-dimension assumption is supplied.

Source: current sk-cor-trace.proof.md, Complement (iii)
(blueprint: lem-pd-cup-graded-commutativity).

Proof in words: compute the pullback tensorator on balanced K-flat generators. The
Koszul swap gives the same signed generator on both paths. Transpose under the native
adjunction: the two symmetry composites have identical tensors of counits, so are equal.
The proper identity-open compactification reduces its projection to the module
projection; the canonical refinement transports this equality to any compactification.
Projection followed by the second counit has the same transpose as siteCup. Apply exact
point sections and their normalized tensor comparison. Multiplication of the coefficient
unit is commutative; signed shift-tensor representatives give (-1)^(ij), hence the same
formula on actual cohomology through classEquiv. For any degree-zero line, choose a
basis, use tensor and counit naturality, and cancel it. A change of basis multiplies both
paths by the same unit, so the two untwisting squares are independent of that choice. -/
theorem native_cup_graded_commutativity
    (d : WeilConjectures.FiniteFieldDatum.{u}) (c : d.CoefficientDatum)
    (E : PadicAlgCl.FiniteIntermediateField c.l)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} c.l)))
    {X : Scheme.{u}} (a : X ⟶ Spec (.of d.k)) [Smooth a] [IsProper a] :
    (∀ K L : CondensedConstructibleFiniteTor Λ X,
      (siteCup Λ a K.obj L.obj ≫ (R Λ a).map
          ((TraceCupPoint.siteBraiding Λ X).braiding K.obj L.obj).hom =
        ((TraceCupPoint.siteBraiding Λ (Spec (.of d.k))).braiding
          ((R Λ a).obj K.obj) ((R Λ a).obj L.obj)).hom ≫ siteCup Λ a L.obj K.obj) ∧
      (scalarCup Λ d.k a K.obj L.obj ≫ (condensedRingOrdinaryCoefficientComplex Λ a).map
          ((TraceCupPoint.siteBraiding Λ X).braiding K.obj L.obj).hom =
        ((TraceCupPoint.scalarBraiding Λ).braiding
          ((condensedRingOrdinaryCoefficientComplex Λ a).obj K.obj)
          ((condensedRingOrdinaryCoefficientComplex Λ a).obj L.obj)).hom ≫
            scalarCup Λ d.k a L.obj K.obj) ∧
      ProperProductComparison Λ d.k a K.obj L.obj ∧
      LineCompatibility Λ d.k a K.obj L.obj) ∧
    (∀ (i j : ℤ)
      (x : (condensedRingOrdinaryCohomology Λ a i).obj (𝟙_ (D Λ X)))
      (y : (condensedRingOrdinaryCohomology Λ a j).obj (𝟙_ (D Λ X))),
      cup Λ d.k a i j x y = (i * j).negOnePow •
        (eqToHom (by rw [add_comm]) :
          (condensedRingOrdinaryCohomology Λ a (j + i)).obj (𝟙_ (D Λ X)) ⟶
            (condensedRingOrdinaryCohomology Λ a (i + j)).obj (𝟙_ (D Λ X)))
              (cup Λ d.k a j i y x)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CupGradedCommutativity
