/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfConstructibleHeart
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.ProperSectionsSemilinearGerms
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.AlgebraicGeometry.ResidueField
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.ZetaSeries
public import Mathlib.Algebra.DirectSum.Module
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.SystemOperationExchangeRealization
import Sheaf.Paper.AdicCompactificationSectionRealization
import Sheaf.Paper.RationalDirectImageRealization
import Sheaf.Paper.ContinuousRationalDerivedRealization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.TopInvariance
import Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RingTheory.QuasiFinite.Basic

/-! # Finite geometric sections and closed-point Frobenius orbits

Source: Stacks, Tag 03QP (1); Deligne, Weil II (1.1.3), (1.1.7), pp. 150--151
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits).
The geometric points are actual sections of the geometric structure morphism.
The section decomposition uses degree zero of the recorded compact counit germs.
The common-stage clause retains both specified comparison maps at every larger stage.
-/

@[expose] public noncomputable section
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped DirectSum
namespace WeilConjectures
namespace FiniteGeometricSections

variable (D : FiniteFieldDatum.{u}) (Z₀ : Over (Spec (.of D.k₀))) [IsFinite Z₀.hom]

/-- The k-points of the geometric fibre, with their structure equation.
Source: Stacks 03QP (1)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
abbrev Points := {z : Spec (.of D.k) ⟶ (D.geometricFiber Z₀).left //
  z ≫ (D.geometricFiber Z₀).hom = 𝟙 _}

/-- Projection of a geometric point to the underlying point of the finite model.
Source: Stacks 03QP (1)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
def projection (z : Points D Z₀) : Z₀.left :=
  (z.val ≫ pullback.fst Z₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) (IsLocalRing.closedPoint D.k)

/-- The fibre P_x of the projection, without a reducedness assumption.
Source: Stacks 03QP (1)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
abbrev PointsOver (x : closedPoints Z₀.left) :=
  {z : Points D Z₀ // projection D Z₀ z = x.val}

/-- The k₀-embeddings of the actual residue field into the fixed closure.
Source: Stacks 03QP (1); Deligne (1.1.7)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
abbrev Embeddings (x : closedPoints Z₀.left) :=
  {ι : Z₀.left.residueField x.val →+* D.k //
    ι.comp (Z₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k}

/-- The canonical model-valued point attached to a residue-field embedding.
Source: Mathlib's SpecToEquivOfField; Stacks 03QP (1)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
def embeddingPoint (x : closedPoints Z₀.left) (ι : Embeddings D Z₀ x) :=
  Spec.map (CommRingCat.ofHom ι.val) ≫ Z₀.left.fromSpecResidueField x.val

/-- The arithmetic q-power automorphism of the fixed closure.
Source: Deligne (1.1.7)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
def arithmeticFrobenius : D.k →+* D.k :=
  letI := Fintype.ofFinite D.k₀
  (FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingHom

/-- Exact geometric orbit assertions; the permutation is fixed by its formula,
and the embedding equivalence is fixed by its model-valued point.
Source: Deligne (1.1.7); Stacks 03QP (1)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
structure PointOrbits where
  finite_points : Finite (Points D Z₀)
  finite_closedPoints : Finite (closedPoints Z₀.left)
  projection_closed : ∀ z : Points D Z₀, projection D Z₀ z ∈ closedPoints Z₀.left
  projection_surjective : ∀ x : closedPoints Z₀.left, Nonempty (PointsOver D Z₀ x)
  embeddings : ∀ x : closedPoints Z₀.left, PointsOver D Z₀ x ≃ Embeddings D Z₀ x
  embeddings_spec : ∀ (x : closedPoints Z₀.left) (z : PointsOver D Z₀ x),
    z.val.val ≫ pullback.fst Z₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      embeddingPoint D Z₀ x (embeddings x z)
  cardinality : ∀ x : closedPoints Z₀.left,
    Nat.card (PointsOver D Z₀ x) = Z₀.hom.degreeOver x.val
  degree_pos : ∀ x : closedPoints Z₀.left, 1 ≤ Z₀.hom.degreeOver x.val
  permutation : Equiv.Perm (Points D Z₀)
  permutation_spec : ∀ z : Points D Z₀,
    (permutation z).val = (frobeniusPointIso D).inv ≫ z.val ≫ (D.geometricFrobenius Z₀).hom
  preserves_projection : ∀ z : Points D Z₀,
    projection D Z₀ (permutation z) = projection D Z₀ z
  embedding_frobenius : ∀ (x : closedPoints Z₀.left) (z z' : PointsOver D Z₀ x),
    z'.val = permutation z.val →
      (embeddings x z').val =
        (arithmeticFrobenius D).comp
          (embeddings x z).val
  single_cycle : ∀ (x : closedPoints Z₀.left) (z z' : PointsOver D Z₀ x),
    ∃! j : Fin (Z₀.hom.degreeOver x.val), (permutation ^ j.val) z.val = z'.val
  period_square : ∀ (x : closedPoints Z₀.left) (z : PointsOver D Z₀ x),
    z.val.val ≫ ((D.geometricFrobenius Z₀) ^ Z₀.hom.degreeOver x.val).hom =
      (CategoryTheory.End.asHom
        (CategoryTheory.End.of (frobeniusPointIso D).hom ^ Z₀.hom.degreeOver x.val)) ≫ z.val.val

variable (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- H_c^0 at the identity compactification, restricted to the constructible heart.
Source: Stacks 03QP (1); Deligne (1.1.3)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
abbrev sections :=
  (sfRationalHeartProperty l E (D.geometricFiber Z₀).left).ι ⋙
    ProperSemilinearGerms.rationalSections D Z₀ l E ⋙
      DerivedCategory.coefficientFdCohomology E 0

/-- H^0 Fib_s Lz*, restricted to the same heart, with all its morphisms.
Source: Stacks 03QP (1); Deligne (1.1.3)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
abbrev fibre (z : Points D Z₀) :=
  (sfRationalHeartProperty l E (D.geometricFiber Z₀).left).ι ⋙
    ProperSemilinearGerms.rationalFibre D Z₀ l E z.val ⋙
      DerivedCategory.coefficientFdCohomology E 0

/-- Degree zero of the actual compact rational counit germ e_z.
Source: Stacks 03QP (1); Deligne (1.1.3)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
def evaluation (M : sfRationalHeart l E (D.geometricFiber Z₀).left) (z : Points D Z₀) :
    (sections D Z₀ l E).obj M ⟶ (fibre D Z₀ l E z).obj M :=
  (DerivedCategory.coefficientFdCohomology E 0).map
    (ProperSemilinearGerms.rationalGerm D Z₀ l E z.val z.property M.obj)

open Classical in
/-- The finite double direct sum in the node's evaluation display.
Source: Stacks 03QP (1)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
abbrev StalkSum (M : sfRationalHeart l E (D.geometricFiber Z₀).left) :=
  ⨁ x : closedPoints Z₀.left, ⨁ z : PointsOver D Z₀ x, (fibre D Z₀ l E z.val).obj M

open Classical in
/-- The finite-coefficient assertions, including specified components and naturality
for every heart arrow. No Weil structure is a parameter.
Source: Stacks 03QP (1); Deligne (1.1.3)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
structure RationalEvaluation where
  iso : ∀ M : sfRationalHeart l E (D.geometricFiber Z₀).left,
    (sections D Z₀ l E).obj M ≃ₗ[E] StalkSum D Z₀ l E M
  component : ∀ (M : sfRationalHeart l E (D.geometricFiber Z₀).left)
    (t : (sections D Z₀ l E).obj M) (x : closedPoints Z₀.left) (z : PointsOver D Z₀ x),
    (iso M t) x z = evaluation D Z₀ l E M z.val t
  naturality : ∀ (M N : sfRationalHeart l E (D.geometricFiber Z₀).left) (f : M ⟶ N)
    (t : (sections D Z₀ l E).obj M) (z : Points D Z₀),
    evaluation D Z₀ l E N z ((sections D Z₀ l E).map f t) =
      (fibre D Z₀ l E z).map f (evaluation D Z₀ l E M z t)
  finite_sections : ∀ M : sfRationalHeart l E (D.geometricFiber Z₀).left,
    FiniteDimensional E ((sections D Z₀ l E).obj M)
  finite_fibres : ∀ (M : sfRationalHeart l E (D.geometricFiber Z₀).left) (z : Points D Z₀),
    FiniteDimensional E ((fibre D Z₀ l E z).obj M)

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- H^0 of the actual derived scalar realization, allowing independent universes.
Source: Deligne (1.1.3)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
abbrev realizedH0 :=
  @DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) _ _
    (HasDerivedCategory.standard _) 0

/-- Realized compact sections at any chosen finite coefficient field.
Source: Deligne (1.1.3)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
abbrev realizedSections (F : AlgebraicallyClosedCoefficients.Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber Z₀).left F ⥤
      ModuleCat.{max u v} Ω := by
  letI : Algebra ℚ_[l] (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) :=
    inferInstanceAs (Algebra ℚ_[l] (Shrink.{u} F.val))
  exact ProperSemilinearGerms.rationalSections D Z₀ l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) ⋙
    ProperSemilinearGerms.stageRealization l Ω F ⋙ realizedH0.{u, v} Ω

/-- Realized point fibres at a chosen finite coefficient field.
Source: Deligne (1.1.3)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
abbrev realizedFibre (F : AlgebraicallyClosedCoefficients.Index l Ω) (z : Points D Z₀) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber Z₀).left F ⥤
      ModuleCat.{max u v} Ω := by
  letI : Algebra ℚ_[l] (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) :=
    inferInstanceAs (Algebra ℚ_[l] (Shrink.{u} F.val))
  exact ProperSemilinearGerms.rationalFibre D Z₀ l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) z.val ⋙
    ProperSemilinearGerms.stageRealization l Ω F ⋙ realizedH0.{u, v} Ω

/-- Scalar extension of the specified germ, before taking degree zero.
Source: Deligne (1.1.3)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
def realizedEvaluation (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber Z₀).left F)
    (z : Points D Z₀) :
    (realizedSections D Z₀ l Ω F).obj M ⟶ (realizedFibre D Z₀ l Ω F z).obj M :=
  (realizedH0.{u, v} Ω).map ((ProperSemilinearGerms.stageRealization l Ω F).map
    (ProperSemilinearGerms.rationalGerm D Z₀ l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) z.val z.property M))

/-- The specified comparison for a realized point fibre from its own field to L.
Source: Deligne (1.1.3); recorded point and pullback scalar comparisons
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
def fibreStageComparison
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Z₀).left)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : M.stage ≤ L) (z : Points D Z₀) :
    (realizedFibre D Z₀ l Ω M.stage z).obj M.obj ≅
      (realizedFibre D Z₀ l Ω L z).obj (M.toStage h) :=
  (realizedH0.{u, v} Ω).mapIso
    (ProperSemilinearGerms.realizedPointComparison D l Ω
        (commonStagePullbackObject l Ω z.val M) L h ≪≫
      (ProperSemilinearGerms.stageRealization l Ω L).mapIso
        ((pointRationalFibre D l Fact.out
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).mapIso
            (commonStagePullbackComparison l Ω z.val M L h)))

/-- The specified comparison on compact sections, followed by H^0.
Source: Deligne (1.1.3); identity compactification
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
def sectionsStageComparison
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Z₀).left)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : M.stage ≤ L) :
    (realizedSections D Z₀ l Ω M.stage).obj M.obj ≅
      (realizedSections D Z₀ l Ω L).obj (M.toStage h) :=
  (realizedH0.{u, v} Ω).mapIso
    (ProperSemilinearGerms.realizedSourceComparison D Z₀ l Ω M L h)

open Classical in
/-- Algebraically closed coefficients: the evaluation is scalar extension at every
finite stage, natural on all stage arrows, and compatible with the actual source
and point comparisons for every enlargement. Thus it descends on every common-stage
morphism representative, not merely on arrows already defined at the object's field.
Source: Deligne (1.1.3); Stacks 03QP (1)
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits). -/
structure CommonEvaluation where
  common_iso : ∀ M : sfCommonStageHeart l (D.geometricFiber Z₀).left Ω,
    (realizedSections D Z₀ l Ω M.obj.stage).obj M.obj.obj ≃ₗ[Ω]
      (⨁ x : closedPoints Z₀.left, ⨁ z : PointsOver D Z₀ x,
        (realizedFibre D Z₀ l Ω M.obj.stage z.val).obj M.obj.obj)
  common_component : ∀ (M : sfCommonStageHeart l (D.geometricFiber Z₀).left Ω)
    (t : (realizedSections D Z₀ l Ω M.obj.stage).obj M.obj.obj)
    (x : closedPoints Z₀.left) (z : PointsOver D Z₀ x),
    (common_iso M t) x z = realizedEvaluation D Z₀ l Ω M.obj.stage M.obj.obj z.val t
  common_finite_sections : ∀ M : sfCommonStageHeart l (D.geometricFiber Z₀).left Ω,
    FiniteDimensional Ω ((realizedSections D Z₀ l Ω M.obj.stage).obj M.obj.obj)
  common_finite_fibres : ∀ (M : sfCommonStageHeart l (D.geometricFiber Z₀).left Ω)
    (z : Points D Z₀),
    FiniteDimensional Ω ((realizedFibre D Z₀ l Ω M.obj.stage z).obj M.obj.obj)
  iso : ∀ (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber Z₀).left F),
    sfRationalHeartProperty l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
        (D.geometricFiber Z₀).left M →
      (realizedSections D Z₀ l Ω F).obj M ≃ₗ[Ω]
        (⨁ x : closedPoints Z₀.left, ⨁ z : PointsOver D Z₀ x,
          (realizedFibre D Z₀ l Ω F z.val).obj M)
  component : ∀ (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber Z₀).left F)
    (hM : sfRationalHeartProperty l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
      (D.geometricFiber Z₀).left M)
    (t : (realizedSections D Z₀ l Ω F).obj M)
    (x : closedPoints Z₀.left) (z : PointsOver D Z₀ x),
    (iso F M hM t) x z = realizedEvaluation D Z₀ l Ω F M z.val t
  naturality : ∀ (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (M N : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber Z₀).left F)
    (_hM : sfRationalHeartProperty l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
      (D.geometricFiber Z₀).left M)
    (_hN : sfRationalHeartProperty l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
      (D.geometricFiber Z₀).left N)
    (f : M ⟶ N) (z : Points D Z₀),
    (realizedSections D Z₀ l Ω F).map f ≫ realizedEvaluation D Z₀ l Ω F N z =
      realizedEvaluation D Z₀ l Ω F M z ≫ (realizedFibre D Z₀ l Ω F z).map f
  changeStage : ∀
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Z₀).left)
    (_hM : sfCommonStageHeartProperty l (D.geometricFiber Z₀).left Ω M)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : M.stage ≤ L) (z : Points D Z₀),
    (sectionsStageComparison D Z₀ l Ω M L h).hom ≫
        realizedEvaluation D Z₀ l Ω L (M.toStage h) z =
      realizedEvaluation D Z₀ l Ω M.stage M.obj z ≫
        (fibreStageComparison D Z₀ l Ω M L h z).hom
  common_naturality : ∀
    (M N : sfCommonStageHeart l (D.geometricFiber Z₀).left Ω)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hM : M.obj.stage ≤ L) (hN : N.obj.stage ≤ L)
    (f : M.obj.toStage hM ⟶ N.obj.toStage hN) (z : Points D Z₀),
    (sectionsStageComparison D Z₀ l Ω M.obj L hM).hom ≫
        (realizedSections D Z₀ l Ω L).map f ≫
        (sectionsStageComparison D Z₀ l Ω N.obj L hN).inv ≫
        realizedEvaluation D Z₀ l Ω N.obj.stage N.obj.obj z =
      realizedEvaluation D Z₀ l Ω M.obj.stage M.obj.obj z ≫
        (fibreStageComparison D Z₀ l Ω M.obj L hM z).hom ≫
        (realizedFibre D Z₀ l Ω L z).map f ≫
        (fibreStageComparison D Z₀ l Ω N.obj L hN z).inv
  finite_sections : ∀ (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber Z₀).left F),
    sfRationalHeartProperty l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
      (D.geometricFiber Z₀).left M →
        FiniteDimensional Ω ((realizedSections D Z₀ l Ω F).obj M)
  finite_fibres : ∀ (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber Z₀).left F),
    sfRationalHeartProperty l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
      (D.geometricFiber Z₀).left M → ∀ z : Points D Z₀,
        FiniteDimensional Ω ((realizedFibre D Z₀ l Ω F z).obj M)

end FiniteGeometricSections

/-- Finite geometric sections decompose canonically by closed-point Frobenius orbits,
with finite-dimensional factors, arbitrary-heart-arrow naturality, and common-stage
scalar compatibility. The finite model may be nonreduced or empty.
Source: Stacks 03QP (1); Deligne, Weil II (1.1.3), (1.1.7), pp. 150--151
(blueprint: lem-a1-finite-geometric-sections-and-point-orbits).
Proof:
1. A finite scheme over k₀ is affine with a finite-dimensional coordinate algebra
(lem-weil-pbc-finite-over-field-affine-finite-dim). Its spectrum is finite discrete,
all points are closed, and each residue field is finite of positive degree
(lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum). Finite implies proper.
2. The pullback universal property and Scheme.SpecToEquivOfField identify P_x
with the k₀-embeddings of κ(x) into k. Algebraic extensions embed in an algebraic
closure. Finite-field Galois Frobenius and transitivity of normal embeddings give
exactly d_x embeddings (lem-sfb-finite-field-galois-frobenius and
lem-sfb-normal-embeddings-automorphism-transitive).
3. On affine tensors the moving point sends b tensor c to γ⁻¹(ι(b)γ(c)), hence
its embedding is γ⁻¹ι. It rotates the d_x embeddings in a single cycle.
Iteration gives g^d z=z h^d, with the composition order recorded above.
4. After base change the finite algebra has residue fields k. Chinese remainders
identify its reduced quotient with the product of k over all geometric points
(lem-pc-crt-ideal-quotient-product, lem-weil-pbc-alg-closed-finite-extension-trivial).
5. Spec of this quotient is the coproduct of the geometric points. Its inclusion
is a surjective closed immersion and therefore a universal homeomorphism. Both
schemes are Noetherian of dimension zero when nonempty; nilpotents cause no change.
6. The sf/PBC normalized heart model identifies the heart object with a continuous
coefficient module sheaf in degree zero. Pro-étale topological invariance makes
restriction to the reduction an equivalence; its unit on sections is restriction.
7. Pro-étale finite-coproduct evaluation identifies these sections with the product
of their point sections, with the actual restriction components.
8. Adic compactification section realization at the identity compactifications of
Z and s identifies the source with H_c^0 and each factor with H^0 Fib_s Lz*.
The point realization comparison identifies the same standard degree zero.
9. System-operation exchange realization and rational-direct-image realization
carry the specified adjunction counit to restriction of module sections. Thus
the composite's components are precisely evaluation, with no scalar ambiguity.
Reindex the finite product by the fibres P_x and identify it with the double sum.
10. Point fibres have finite-dimensional cohomology, hence so does the finite sum.
Restriction commutes with every sheaf arrow. The normalized compact-section,
point, and rational adjunction comparisons commute with scalar extension. Apply
these at any stage and any common stage of an arrow, obtaining changeStage and
naturality independently of the representative. The empty-cover axiom gives
zero sections for the empty scheme and the empty direct sum. -/
theorem finiteGeometricSectionsAndPointOrbits
    (D : FiniteFieldDatum.{u}) (Z₀ : Over (Spec (.of D.k₀))) [IsFinite Z₀.hom]
    (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    Nonempty (FiniteGeometricSections.PointOrbits D Z₀) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
        Nonempty (FiniteGeometricSections.RationalEvaluation D Z₀ l E)) ∧
      Nonempty (FiniteGeometricSections.CommonEvaluation D Z₀ l Ω) := by
  sorry

end WeilConjectures
