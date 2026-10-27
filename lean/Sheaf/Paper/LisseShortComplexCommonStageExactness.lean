/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.LisseRationalRealization
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.FiniteCoefficientPoint
public import Mathlib.Algebra.Homology.ExactSequence
public import Sheaf.Paper.CoefficientCohomologyModules
public import Sheaf.Paper.DlLocallyConstructibleAdicHeart
public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.LocalizedTStructure
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import Sheaf.Paper.DlConstructibleFibresExact
import Sheaf.Paper.ScalarExtensionExactIntrinsic
import Sheaf.Paper.ConstructibleTruncations
import Sheaf.Paper.IntegralTStructure
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-! # Simultaneous exact finite-stage representatives of lisse short complexes

Source: Bhatt--Scholze, Corollary 6.8.5, Lemma 6.8.7, Proposition 6.8.14(2);
blueprint real-mixed-by-curves, paragraph 1, finite common-stage assembly
(blueprint: lem-zl-lisse-short-complex-common-stage-exactness).

The quiver is a finite presentation, rather than a category with finitely many morphisms.
Path equations include inverse identities; `none` denotes the zero arrow. The literal
coefficient stage and integral object of every vertex are its prescribed model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u v w z t
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.LisseShortComplex
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

/-- Evaluate a path or the zero arrow in a presented diagram.
Source: finite Hom-colimit diagram assembly, proof step 3
(blueprint: lem-zl-lisse-short-complex-common-stage-exactness). -/
def pathValue {V : Type v} [Quiver.{w} V] {C : Type z} [Category.{t} C]
    [HasZeroMorphisms C] (F : V ⥤q C) {i j : V} (p : Option (Quiver.Path i j)) :
    F.obj i ⟶ F.obj j :=
  match p with
  | none => 0
  | some p => (Paths.lift F).map p

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (V : Type v) [Quiver.{w} V]

/-- A finite list of equations and short complexes in the given diagram. Inverses are
arrows with the corresponding two path equations. Optional Weil maps use exactly the
recorded geometric-Frobenius pullback, without a k-linearity assumption.
Source: finite common-stage assembly, proof steps 1, 3 and 7
(blueprint: lem-zl-lisse-short-complex-common-stage-exactness). -/
structure Presentation (F : V ⥤q sfCommonStageHeart c.l (D.geometricFiber Y₀).left c.Qbar)
    (Q : Type z) (J : Type z) where
  eqSource : Q → V
  eqTarget : Q → V
  lhs : ∀ q, Option (Quiver.Path (eqSource q) (eqTarget q))
  rhs : ∀ q, Option (Quiver.Path (eqSource q) (eqTarget q))
  equations : ∀ q, pathValue F (lhs q) = pathValue F (rhs q)
  first : J → V
  middle : J → V
  last : J → V
  f : ∀ j, first j ⟶ middle j
  g : ∀ j, middle j ⟶ last j
  zero : ∀ j, F.map (f j) ≫ F.map (g j) = 0
  weil : Option (∀ i : V,
    (sfCommonStageWeilFrobeniusPullback D c.l c.different Y₀ c.Qbar).obj (F.obj i).obj ≅
      (F.obj i).obj)
  equivariant : ∀ θ, weil = some θ → ∀ (i j : V) (a : i ⟶ j),
    (sfCommonStageWeilFrobeniusPullback D c.l c.different Y₀ c.Qbar).map (F.map a).hom ≫
      (θ j).hom = (θ i).hom ≫ (F.map a).hom

variable {D c Y₀ V}

/-- The displayed short complex in the common-stage heart.
Source: the displayed sequence of the node
(blueprint: lem-zl-lisse-short-complex-common-stage-exactness). -/
def Presentation.complex {F : V ⥤q sfCommonStageHeart c.l (D.geometricFiber Y₀).left c.Qbar}
    {Q J : Type z} (P : Presentation D c Y₀ V F Q J) (j : J) :
    ShortComplex (sfCommonStageHeart c.l (D.geometricFiber Y₀).left c.Qbar) :=
  ShortComplex.mk (F.map (P.f j)) (F.map (P.g j)) (P.zero j)

/-- The original finite-stage model extended to a common overfield, literally, without
replacing any vertex. Source: proof step 3
(blueprint: lem-zl-lisse-short-complex-common-stage-exactness). -/
abbrev model (K : sfCommonStageHeart c.l (D.geometricFiber Y₀).left c.Qbar)
    (E : Index c.l c.Qbar) (h : K.obj.stage ≤ E) := K.obj.toStage h

/-- The normalized scalar/pullback comparison on a finite-stage object, using the
recorded tensor comparison and the equality identifying stage transitions.
Source: proof steps 3 and 7, scalar-compatible lisse pullback normalization
(blueprint: lem-zl-lisse-short-complex-common-stage-exactness). -/
def frobeniusScalar {E L : Index c.l c.Qbar} (k : E ≤ L)
    (M : Stage c.l c.Qbar (D.geometricFiber Y₀).left E) :
    ((stageSystem c.l c.Qbar (D.geometricFiber Y₀).left).T k).obj
        ((sfWeilFrobeniusPullback D c.l c.different Y₀
          (Coefficient.{u} c.l c.Qbar E)).obj M) ≅
      (sfWeilFrobeniusPullback D c.l c.different Y₀
        (Coefficient.{u} c.l c.Qbar L)).obj
          (((stageSystem c.l c.Qbar (D.geometricFiber Y₀).left).T k).obj M) :=
  (operationStageTransitionIso c.l c.Qbar (D.geometricFiber Y₀).left E L k).app _ ≪≫
    (@rationalPullbackScalarComparison c.l _ (Coefficient.{u} c.l c.Qbar E) _ _ _
      (Coefficient.{u} c.l c.Qbar L) _ _ _
      (AlgebraicallyClosedCoefficients.coefficientInclusion c.l c.Qbar E L k) _ _
      (D.geometricFrobenius Y₀).hom (sfWeilPrimeInvertible D c.l c.different Y₀)
      (sfWeilPrimeInvertible D c.l c.different Y₀)).app M ≪≫
    (sfWeilFrobeniusPullback D c.l c.different Y₀ (Coefficient.{u} c.l c.Qbar L)).mapIso
      ((operationStageTransitionIso c.l c.Qbar (D.geometricFiber Y₀).left E L k).app M).symm

/-- Extend a Weil isomorphism and conjugate by the specified scalar associators,
keeping the vertex literally its original model extended to the new field.
Source: proof steps 3, 6 and 7
(blueprint: lem-zl-lisse-short-complex-common-stage-exactness). -/
def extendWeil (K : generalAlgebraicallyClosedConstructibleCategory c.l c.Qbar
      (D.geometricFiber Y₀).left) {E L : Index c.l c.Qbar}
    (h : K.stage ≤ E) (k : E ≤ L)
    (θ : (sfWeilFrobeniusPullback D c.l c.different Y₀
      (Coefficient.{u} c.l c.Qbar E)).obj (K.toStage h) ≅ K.toStage h) :
    (sfWeilFrobeniusPullback D c.l c.different Y₀
      (Coefficient.{u} c.l c.Qbar L)).obj (K.toStage (h.trans k)) ≅
        K.toStage (h.trans k) :=
  (sfWeilFrobeniusPullback D c.l c.different Y₀ (Coefficient.{u} c.l c.Qbar L)).mapIso
      (((stageSystem c.l c.Qbar (D.geometricFiber Y₀).left).assoc h k).app K.obj).symm ≪≫
    (frobeniusScalar (D := D) (c := c) (Y₀ := Y₀) k (K.toStage h)).symm ≪≫
    ((stageSystem c.l c.Qbar (D.geometricFiber Y₀).left).T k).mapIso θ ≪≫
    ((stageSystem c.l c.Qbar (D.geometricFiber Y₀).left).assoc h k).app K.obj

/-- The specified finite-stage Weil isomorphisms intertwine all arrows and realize to
the original common-stage structures, under the canonical stage isomorphisms.
Source: proof step 7
(blueprint: lem-zl-lisse-short-complex-common-stage-exactness). -/
def WeilAt
    {F : V ⥤q sfCommonStageHeart c.l (D.geometricFiber Y₀).left c.Qbar}
    (θ : ∀ i : V,
      (sfCommonStageWeilFrobeniusPullback D c.l c.different Y₀ c.Qbar).obj (F.obj i).obj ≅
        (F.obj i).obj)
    (E : Index c.l c.Qbar) (h : ∀ i, (F.obj i).obj.stage ≤ E)
    (A : ∀ {i j : V}, (i ⟶ j) → (model (F.obj i) E (h i) ⟶ model (F.obj j) E (h j)))
    (θE : ∀ i : V,
      (sfWeilFrobeniusPullback D c.l c.different Y₀
        (Coefficient.{u} c.l c.Qbar E)).obj (model (F.obj i) E (h i)) ≅
          model (F.obj i) E (h i)) : Prop :=
  (∀ (i j : V) (a : i ⟶ j),
    (sfWeilFrobeniusPullback D c.l c.different Y₀
      (Coefficient.{u} c.l c.Qbar E)).map (A a) ≫ (θE j).hom =
        (θE i).hom ≫ A a) ∧
  ∀ i : V,
    (sfCommonStageWeilFrobeniusPullback D c.l c.different Y₀ c.Qbar).map
        ((stageSystem c.l c.Qbar (D.geometricFiber Y₀).left).isoToStage
          (F.obj i).obj (h i)).hom ≫
      (sfWeilStagePullbackIdentification D c.l c.different Y₀ c.Qbar E
        (model (F.obj i) E (h i))).hom ≫
      (inclusion E).map (θE i).hom =
    (θ i).hom ≫ ((stageSystem c.l c.Qbar (D.geometricFiber Y₀).left).isoToStage
      (F.obj i).obj (h i)).hom

/-- Finite-stage assertions for the specified arrows: lisse heart membership, original
Hom classes, all path equations, sf/PBC short exactness, and the same realized Weil maps.
The PBC clause is quantified over the normalized comparison data, so no arbitrary
comparison or exactness assumption is substituted.
Source: proof steps 3--7
(blueprint: lem-zl-lisse-short-complex-common-stage-exactness). -/
def StageAssertions
    {F : V ⥤q sfCommonStageHeart c.l (D.geometricFiber Y₀).left c.Qbar}
    {Q J : Type z} (P : Presentation D c Y₀ V F Q J)
    (E : Index c.l c.Qbar) (h : ∀ i, (F.obj i).obj.stage ≤ E)
    (A : ∀ {i j : V}, (i ⟶ j) → (model (F.obj i) E (h i) ⟶ model (F.obj j) E (h j))) :
    Prop :=
  (∀ i, @rationalLisseHeartProperty c.l _ (Coefficient.{u} c.l c.Qbar E) _ _ _
    (D.geometricFiber Y₀).left
      (sfWeilPrimeInvertible D c.l c.different Y₀) (model (F.obj i) E (h i))) ∧
  (∀ (i j : V) (a : i ⟶ j),
    ofHom (F.obj i).obj (F.obj j).obj E (h i) (h j) (A a) = (F.map a).hom) ∧
  (∀ q, pathValue (⟨fun i ↦ model (F.obj i) E (h i), fun a ↦ A a⟩)
      (P.lhs q) = pathValue (⟨fun i ↦ model (F.obj i) E (h i), fun a ↦ A a⟩) (P.rhs q)) ∧
  (∃ H : ∀ i, sfRationalHeartProperty c.l (Coefficient.{u} c.l c.Qbar E)
      (D.geometricFiber Y₀).left (model (F.obj i) E (h i)),
    ∀ j : J, ∃ S : ShortComplex
        (sfRationalHeart c.l (Coefficient.{u} c.l c.Qbar E) (D.geometricFiber Y₀).left),
      S.X₁ = ⟨model (F.obj (P.first j)) E (h _), H _⟩ ∧
      S.X₂ = ⟨model (F.obj (P.middle j)) E (h _), H _⟩ ∧
      S.X₃ = ⟨model (F.obj (P.last j)) E (h _), H _⟩ ∧
      HEq S.f.hom (A (P.f j)) ∧ HEq S.g.hom (A (P.g j)) ∧ S.ShortExact) ∧
  (∀ [IsNoetherian (D.geometricFiber Y₀).left]
    [Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber Y₀).left ≤ n)]
    [Fact (∀ x : (D.geometricFiber Y₀).left,
      IsUnit (c.l : (D.geometricFiber Y₀).left.presheaf.stalk x))]
    (C : FdCoefficientComparisonSystem.{u} c.l c.Qbar),
    ∀ j : J, ∃ S : ShortComplex
        (pbc_localized_tstructure (D.geometricFiber Y₀).left c.l
          (Coefficient.{u} c.l c.Qbar E)).choose.heart.FullSubcategory,
      HEq S.X₁.obj (((C.coefficients (D.geometricFiber Y₀).left).family.Φ E).obj
        (model (F.obj (P.first j)) E (h _))) ∧
      HEq S.X₂.obj (((C.coefficients (D.geometricFiber Y₀).left).family.Φ E).obj
        (model (F.obj (P.middle j)) E (h _))) ∧
      HEq S.X₃.obj (((C.coefficients (D.geometricFiber Y₀).left).family.Φ E).obj
        (model (F.obj (P.last j)) E (h _))) ∧
      HEq S.f.hom (((C.coefficients (D.geometricFiber Y₀).left).family.Φ E).map (A (P.f j))) ∧
      HEq S.g.hom (((C.coefficients (D.geometricFiber Y₀).left).family.Φ E).map (A (P.g j))) ∧
      S.ShortExact) ∧
  (∀ θ, P.weil = some θ → ∃ θE : ∀ i : V,
      (sfWeilFrobeniusPullback D c.l c.different Y₀
        (Coefficient.{u} c.l c.Qbar E)).obj (model (F.obj i) E (h i)) ≅
          model (F.obj i) E (h i),
    WeilAt θ E h A θE ∧
    ∀ (L : Index c.l c.Qbar) (k : E ≤ L),
      WeilAt θ L (fun i ↦ (h i).trans k)
        (fun a ↦ (stageSystem c.l c.Qbar (D.geometricFiber Y₀).left).tr k (A a))
        (fun i ↦ extendWeil (D := D) (c := c) (Y₀ := Y₀) (F.obj i).obj (h i) k (θE i)))

/-- Simultaneous exact descent with the prescribed lisse vertex models and all relations.
Source: BS Corollary 6.8.5, Lemma 6.8.7, Proposition 6.8.14(2);
blueprint real-mixed-by-curves, paragraph 1
(blueprint: lem-zl-lisse-short-complex-common-stage-exactness).

Proof:
1. Apply lem-dl-a1-constructible-fibres-exact to each short complex, using precisely
H^0 Fib_s Ly* on the heart, to obtain common-stage short exactness.
2. By lem-weil-heart-short-exact-triangles choose a connecting map for each sequence.
Each distinguished triangle has a finite-stage distinguished representative by
 def-weil-algebraically-closed-coefficients. Include its isomorphism and inverse.
3. Represent the original arrows, inverse arrows, connecting maps and triangle
isomorphisms in the Hom colimits. Take one upper coefficient field for these and the
prescribed models. Each equation has an eventual-equality witness; take an upper
field for the finitely many witnesses. Keep every vertex literally its prescribed
model extended to this field. Include Weil maps, their inverses and equivariance
squares, using the scalar-normalized pullback comparisons of
 def-weil-weil-sheaf-complex and lem-tw-lisse-rational-realization.
4. By lem-weil-scalar-extension-exact-triangulated the auxiliary triangles stay
distinguished. The descended inverse identities and squares identify them with the
triangles on our prescribed vertices and arrows. By prop-constructible-truncations
and lem-tw-lisse-rational-realization these vertices remain in the lisse heart.
The heart-triangle criterion makes all descended complexes short exact.
5. The comparison lem-fd-rational-coefficient-category-comparison is the identity on
the common integral category and pure localized tensors. By
 lem-weil-pbc-integral-stratified-perfect-characterization the ambient cohomology and
completed coefficient ring agree. Thus both standard halves agree, using
 def-weil-constructible-standard-tstructure, prop-weil-pbc-integral-tstructure and
 prop-weil-localized-tstructure. The comparison is t-exact in both directions and
carries these distinguished triangles to short exact sequences in the PBC heart.
6. Every further finite extension preserves the triangles, hearts and equations.
The scalar associators identify the transported arrows with their specified models;
normalized lisse realization and the scalar-compatible comparison preserve all data.
7. Include the Weil isomorphisms and inverse identities in step 3. Their squares
are exactly equivariance and the displayed equality retains the same realized
structures. The zero triangle covers zero complexes. Empty complex families need
no triangles, and an empty diagram starts at Q_l. No integral lattice exactness
is used, and the empty scheme needs no geometric points. -/
theorem simultaneous_exactness
    [Finite V] [∀ i j : V, Finite (i ⟶ j)]
    {Q J : Type z} [Finite Q] [Finite J]
    (F : V ⥤q sfCommonStageHeart c.l (D.geometricFiber Y₀).left c.Qbar)
    (P : Presentation D c Y₀ V F Q J)
    (_models : ∀ i, @rationalLisseHeartProperty c.l _
      (Coefficient.{u} c.l c.Qbar (F.obj i).obj.stage) _ _ _ (D.geometricFiber Y₀).left
      (sfWeilPrimeInvertible D c.l c.different Y₀) (F.obj i).obj.obj)
    (_fibres : ∀ (j : J) (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
      Function.Injective (((sfCommonStageHeartProperty c.l (D.geometricFiber Y₀).left c.Qbar).ι ⋙
        @commonStageDerivedPullback c.l _ c.Qbar _ _ _ _ _ x
          (dlAdicGeometricResidueInvertible D c (Spec (.of D.k)))
          (dlAdicGeometricResidueInvertible D c (D.geometricFiber Y₀).left) ⋙
        pointQbarFibre D c.l c.different c.Qbar ⋙
        DerivedCategory.coefficientQbarCohomology c.l c.Qbar 0).map
        (F.map (P.f j))) ∧
      Function.Exact (((sfCommonStageHeartProperty c.l (D.geometricFiber Y₀).left c.Qbar).ι ⋙
        @commonStageDerivedPullback c.l _ c.Qbar _ _ _ _ _ x
          (dlAdicGeometricResidueInvertible D c (Spec (.of D.k)))
          (dlAdicGeometricResidueInvertible D c (D.geometricFiber Y₀).left) ⋙
        pointQbarFibre D c.l c.different c.Qbar ⋙
        DerivedCategory.coefficientQbarCohomology c.l c.Qbar 0).map
        (F.map (P.f j))) (((sfCommonStageHeartProperty c.l (D.geometricFiber Y₀).left c.Qbar).ι ⋙
        @commonStageDerivedPullback c.l _ c.Qbar _ _ _ _ _ x
          (dlAdicGeometricResidueInvertible D c (Spec (.of D.k)))
          (dlAdicGeometricResidueInvertible D c (D.geometricFiber Y₀).left) ⋙
        pointQbarFibre D c.l c.different c.Qbar ⋙
        DerivedCategory.coefficientQbarCohomology c.l c.Qbar 0).map
          (F.map (P.g j))) ∧
      Function.Surjective (((sfCommonStageHeartProperty c.l (D.geometricFiber Y₀).left c.Qbar).ι ⋙
        @commonStageDerivedPullback c.l _ c.Qbar _ _ _ _ _ x
          (dlAdicGeometricResidueInvertible D c (Spec (.of D.k)))
          (dlAdicGeometricResidueInvertible D c (D.geometricFiber Y₀).left) ⋙
        pointQbarFibre D c.l c.different c.Qbar ⋙
        DerivedCategory.coefficientQbarCohomology c.l c.Qbar 0).map
        (F.map (P.g j)))) :
    (∀ j : J, (P.complex j).ShortExact) ∧
    ∃ (E : Index c.l c.Qbar) (h : ∀ i, (F.obj i).obj.stage ≤ E)
      (A : ∀ {i j : V}, (i ⟶ j) → (model (F.obj i) E (h i) ⟶ model (F.obj j) E (h j))),
      StageAssertions P E h A ∧
      ∀ (L : Index c.l c.Qbar) (k : E ≤ L),
        StageAssertions P L (fun i ↦ (h i).trans k)
          (fun a ↦ (stageSystem c.l c.Qbar (D.geometricFiber Y₀).left).tr k (A a)) := by
  sorry

end WeilConjectures.LisseShortComplex
