/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.DiagonalProjectiveAction
public import Sheaf.AlgebraicGeometry.FixedPointTangentWeights
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis
import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Projective attracting cells for the multiplicative group

Source: Milne, Algebraic Groups (2017), Theorem 13.47, Corollaries 13.48--13.49,
pp.272--274; Remark 13.57 and Proposition 13.58, pp.277--278; properness erratum.
(blueprint: lem-sfb-projective-attracting-cells).

A weight basis presents the given finite-dimensional projective representation using
`DiagonalProjectiveAction.IsDiagonal`. This is a choice of coordinates on the given
linear representation, not a condition on the signs or multiplicities of its weights.
Orbit extensions use Remark 13.57's equivalent description of equivariant maps: their
restriction to G_m is the orbit of their value at one. Separatedness makes the extension
unique, including over nonreduced algebras. The arbitrary-algebra characterization also
specifies the cells after scalar extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.ProjectiveAttractingCells

/-- The constant a on the affine line, as a section over F.
Source: Milne, Remark 13.57, p.277 (blueprint: lem-sfb-projective-attracting-cells). -/
def linePoint {F : Type u} [Field F] (a : F) :
    𝟙_ (Over (Spec (.of F))) ⟶ StandardGroupSchemes.additive F :=
  StandardGroupSchemes.identitySection F (Polynomial.aeval a)

/-- An orbit extension over A with prescribed value x at zero. A map to X over F from
Spec A times A1 is the same as an A-map to X_A. The restriction equality says it extends
its evaluation-at-one orbit; by Milne Remark 13.57 this is precisely equivariance for
multiplication on A1. Source: Milne, Definition 13.55 and Remark 13.57, pp.276--277
(blueprint: lem-sfb-projective-attracting-cells). -/
def IsExtension {F : Type u} [Field F] {X : Over (Spec (.of F))}
    (a : ModObj (StandardGroupSchemes.multiplicative F) X)
    (x : 𝟙_ (Over (Spec (.of F))) ⟶ X) (A : CommAlgCat.{u} F)
    (q : StandardGroupSchemes.affine F A ⊗ StandardGroupSchemes.additive F ⟶ X) : Prop :=
  (𝟙 (StandardGroupSchemes.affine F A) ⊗ₘ
      StandardGroupSchemes.map F (Polynomial.toLaurentAlg (R := F))) ≫ q =
    lift (snd _ _) (fst _ _ ≫
      lift (𝟙 _) (toUnit _ ≫ linePoint 1) ≫ q) ≫ a.smul ∧
    lift (𝟙 _) (toUnit _ ≫ linePoint 0) ≫ q = toUnit _ ≫ x

/-- The all-algebra attracting-point predicate, with evaluation at one specified.
Source: Milne, Remark 13.57, p.277 (blueprint: lem-sfb-projective-attracting-cells). -/
def Attracts {F : Type u} [Field F] {X : Over (Spec (.of F))}
    (a : ModObj (StandardGroupSchemes.multiplicative F) X)
    (x : 𝟙_ (Over (Spec (.of F))) ⟶ X) (A : CommAlgCat.{u} F)
    (y : StandardGroupSchemes.affine F A ⟶ X) : Prop :=
  ∃ q, IsExtension a x A q ∧ lift (𝟙 _) (toUnit _ ≫ linePoint 1) ≫ q = y

/-- Smooth affine attracting cells, their all-algebra representing property, geometric
uniqueness, finite partition, and unique open dense cell. The fixed scheme is presented
as a finite coproduct of rational reduced points. The fixed-functor condition is tested
after all changes of test scheme, so it is scheme-theoretic rather than pointwise.
The projective embedding is written in a weight basis, using the already defined
finite-rank split torus, a group isomorphism from G_m, and its diagonal projective action.

Source: Milne, Theorem 13.47, Corollaries 13.48--13.49, pp.272--274, paragraph after
Lemma 13.51, p.275, Remark 13.57 and Proposition 13.58, pp.277--278; properness erratum.
(blueprint: lem-sfb-projective-attracting-cells).

Proof, following the eight steps of the DAG node:
1. Choose a weight basis (lem-sfb-gm-representation-weight-basis). Standard projective
   charts are affine (lemma-nagata-relative-affine-space-open-immersion), invariant,
   and their intersections with X are smooth affine. At x set the negative-weight
   ratios to zero and the zero-weight ratios to their values at x, obtaining Y_x.
2. Over every A these equations are exactly polynomial extendibility of the orbit
   with limit x. A[t] injects into A[t,t^-1], even with nilpotents. An equivariant map
   with value x at zero stays in this chart: its closed invariant complement misses
   zero in every geometric fibre and must be empty. Use the open-factorization lemma
   and lem-sfb-smooth-affine-concentrator. This proves the all-algebra property.
3. The positively graded coordinate algebra B has B_0=F and is regular at its
   augmentation ideal by lem-weil-pbc-smooth-scheme-over-field-regular. Apply
   lem-sfb-positive-graded-regular-polynomial to homogeneous cotangent basis lifts;
   Y_x is affine d-space, smooth and reduced.
4. In dual numbers, the chart equations kill precisely nonpositive-weight tangent
   directions. The weight decomposition identifies T_x Y_x with the positive part
   of T_x X. The polynomial presentation computes its dimension as d.
5. For a geometric point [v], its least nonzero weight component gives the extension
   [sum t^(a-w) v_a] and its unique fixed limit. Hence the cells are disjoint and
   exhaust X. These equations and the all-algebra functor commute with scalar change.
6. Geometric points determine the supports. The uniqueness of the reduced induced
   closed structure on chart opens (lem-weil-pbc-reduced-induced-closed-subscheme)
   gives the unique isomorphism of any other reduced immersed cell over X.
7. Smooth connected nonempty X is integral (IsRegular.of_smooth and
   IsRegular.isIntegral). A finite locally closed partition of an irreducible space
   has one dense member; it is open, and two nonempty opens intersect. Its tangent
   space is the full tangent space. For Spec F the tangent is zero and the cell A0.
8. Conversely, all-positive tangent weights give a cell with equal tangent space.
   Both local rings are regular. The regular-local-quotient independent-generators
   lemma forces its defining ideal to vanish near x. The cell therefore contains
   a nonempty open and must be the unique open dense member from step 7.
-/
theorem exists_projective_attracting_cells
    (F : Type u) [Field F] [IsAlgClosed F]
    (X : Over (Spec (.of F))) [Smooth X.hom] [IsProjective X.hom]
    [Nonempty X.left] [ConnectedSpace X.left]
    (a : ModObj (StandardGroupSchemes.multiplicative F) X)
    (hlinear : ∃ (n : ℕ) (w : ULift.{u} (Fin (n + 1)) → Fin 1 → ℤ)
      (b : ModObj (DiagonalProjectiveAction.torus F 1).X
        (DiagonalProjectiveAction.space F n))
      (e : Grp.mk (StandardGroupSchemes.multiplicative F) ≅
        DiagonalProjectiveAction.torus F 1)
      (j : X ⟶ DiagonalProjectiveAction.space F n),
      DiagonalProjectiveAction.IsDiagonal F 1 n w b ∧ IsClosedImmersion j.left ∧
        a.smul ≫ j = (e.hom.hom.hom ⊗ₘ j) ≫ b.smul)
    (m : ℕ) (Z : Over (Spec (.of F))) (z : Fin m → (𝟙_ (Over (Spec (.of F))) ⟶ Z))
    (hz : IsColimit (Cofan.mk Z z)) (jZ : Z ⟶ X) [IsClosedImmersion jZ.left]
    (hfixed : ∀ (T : Over (Spec (.of F))) (y : T ⟶ X),
      (∃ s : T ⟶ Z, s ≫ jZ = y) ↔
        ∀ (W : Over (Spec (.of F))) (f : W ⟶ T)
          (t : W ⟶ StandardGroupSchemes.multiplicative F),
          lift t (f ≫ y) ≫ a.smul = f ≫ y) :
    ∃ (C : Fin m → Over (Spec (.of F))) (i : ∀ r : Fin m, C r ⟶ X) (d : Fin m → ℕ),
      (∀ r : Fin m, IsImmersion (i r).left ∧ Smooth (C r).hom ∧ IsReduced (C r).left) ∧
      (∀ (r : Fin m) (A : CommAlgCat.{u} F)
        (y : StandardGroupSchemes.affine F A ⟶ X),
        (∃ p, p ≫ i r = y) ↔ Attracts a (z r ≫ jZ) A y) ∧
      (∀ (r : Fin m) (A : CommAlgCat.{u} F)
        (q : StandardGroupSchemes.affine F A ⊗ StandardGroupSchemes.additive F ⟶ X),
        IsExtension a (z r ≫ jZ) A q →
          ∃! p : StandardGroupSchemes.affine F A ⟶ C r,
            p ≫ i r = lift (𝟙 _) (toUnit _ ≫ linePoint 1) ≫ q) ∧
      (∀ (r : Fin m) (A : CommAlgCat.{u} F)
        (p : StandardGroupSchemes.affine F A ⟶ C r),
        ∃! q : StandardGroupSchemes.affine F A ⊗ StandardGroupSchemes.additive F ⟶ X,
          IsExtension a (z r ≫ jZ) A q ∧
            lift (𝟙 _) (toUnit _ ≫ linePoint 1) ≫ q = p ≫ i r) ∧
      (∀ r : Fin m, Nonempty (C r ≅
        Over.mk (AffineSpace (ULift.{u} (Fin (d r))) (Spec (.of F)) ↘ Spec (.of F))) ∧
        d r = Module.finrank (X.left.residueField
          ((z r ≫ jZ).left (IsLocalRing.closedPoint F)))
          (positiveSpace a ((z r ≫ jZ).left (IsLocalRing.closedPoint F)))) ∧
      (∀ p : X.left, ∃! r : Fin m, p ∈ Set.range (i r).left) ∧
      (∀ (r : Fin m) (K : Type u) [Field K] [IsAlgClosed K] [Algebra F K]
        (y : StandardGroupSchemes.affine F K ⟶ X),
        (∃ p, p ≫ i r = y) ↔ Attracts a (z r ≫ jZ) (.of F K) y) ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra F K]
        (p : ((Over.pullback (Spec.map
          (CommRingCat.ofHom (algebraMap F K)))).obj X).left),
        ∃! r : Fin m, p ∈ Set.range
          (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F K)))).map
            (i r)).left)) ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra F K] (r : Fin m),
        Nonempty (((Over.pullback (Spec.map
          (CommRingCat.ofHom (algebraMap F K)))).obj (C r)) ≅
            Over.mk (AffineSpace (ULift.{u} (Fin (d r))) (Spec (.of K)) ↘ Spec (.of K)))) ∧
      (∀ (r : Fin m) (Y : Over (Spec (.of F))) (jY : Y ⟶ X)
        [IsImmersion jY.left] [IsReduced Y.left] [Smooth Y.hom],
        (∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra F K]
          (y : StandardGroupSchemes.affine F K ⟶ X),
          (∃ p, p ≫ jY = y) ↔ Attracts a (z r ≫ jZ) (.of F K) y) →
        ∃! e : Y ≅ C r, e.hom ≫ i r = jY) ∧
      (∃! r : Fin m, IsOpenImmersion (i r).left ∧ DenseRange (i r).left) ∧
      (∀ r : Fin m,
        (IsOpenImmersion (i r).left ∧ DenseRange (i r).left) ↔
          positiveSpace a ((z r ≫ jZ).left (IsLocalRing.closedPoint F)) = ⊤) ∧
      (IsIso X.hom → Nonempty (Unique (Fin m)) ∧ ∀ r : Fin m, d r = 0) := by
  sorry

end AlgebraicGeometry.ProjectiveAttractingCells
