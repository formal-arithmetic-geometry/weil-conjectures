/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.AlgebraicGeometry.ProjectivizedGmRepresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis
import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.LfpSmoothFlatBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Rational projective attracting cells over an arbitrary field

Source: Milne, Algebraic Groups (2017), Theorem 13.47, Corollary 13.49,
pp.272--274, the linear-action application p.275, and Section 13g, pp.276--278.
(blueprint: lem-sfb-rational-projective-attracting-cells).

A map A¹_A → X_A is written as the equivalent F-map Spec A × A¹_F → X.
Its equivariance is tested after every A-algebra map, at every unit and every scalar.
The pullbacks in the scalar-extension conclusion are the actual library pullbacks.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.RationalProjectiveAttractingCells

/-- The scalar u as an A-valued point of the affine line, by polynomial evaluation.
Source: Milne Section 13g (blueprint: lem-sfb-rational-projective-attracting-cells). -/
def linePoint (F : Type u) [Field F] (A : CommAlgCat.{u} F) (u : A) :
    StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.additive F :=
  StandardGroupSchemes.map F (Polynomial.aeval u)

/-- The multiplicative scalar t as a point of Gm, by Laurent evaluation.
Source: Milne Section 13g (blueprint: lem-sfb-rational-projective-attracting-cells). -/
def unitPoint (F : Type u) [Field F] (A : CommAlgCat.{u} F) (t : Aˣ) :
    StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.multiplicative F :=
  StandardGroupSchemes.map F
    { LaurentPolynomial.eval₂ (algebraMap F A) t with
      commutes' := LaurentPolynomial.eval₂_C (algebraMap F A) t }

/-- Fixedness after every algebra extension, including nonreduced test algebras.
Source: Milne Section 13f (blueprint: lem-sfb-rational-projective-attracting-cells). -/
def IsFixed {F : Type u} [Field F] {X : Over (Spec (.of F))}
    (a : ModObj (StandardGroupSchemes.multiplicative F) X)
    (A : CommAlgCat.{u} F) (y : StandardGroupSchemes.affine F A ⟶ X) : Prop :=
  ∀ (B : CommAlgCat.{u} F) (f : A ⟶ B) (t : Bˣ),
    lift (unitPoint F B t) (StandardGroupSchemes.map F f.hom ≫ y) ≫ a.smul =
      StandardGroupSchemes.map F f.hom ≫ y

/-- The finite coproduct of rational points represents exactly the fixed subfunctor.
Injectivity is stated separately, so duplicate nonfixed sections cannot masquerade
as a representing family. Source: Milne Corollary 13.49
(blueprint: lem-sfb-rational-projective-attracting-cells). -/
def RepresentsFixed {F : Type u} [Field F] {X : Over (Spec (.of F))}
    (a : ModObj (StandardGroupSchemes.multiplicative F) X)
    (I : Type u) [Finite I] (x : I → (𝟙_ (Over (Spec (.of F))) ⟶ X))
    (A : CommAlgCat.{u} F) : Prop :=
  Function.Injective (fun z : StandardGroupSchemes.affine F A ⟶
    ∐ (fun _ : I ↦ 𝟙_ (Over (Spec (.of F)))) ↦ z ≫ Sigma.desc x) ∧
  ∀ y : StandardGroupSchemes.affine F A ⟶ X,
    IsFixed a A y ↔ ∃ z : StandardGroupSchemes.affine F A ⟶
      ∐ (fun _ : I ↦ 𝟙_ (Over (Spec (.of F)))), z ≫ Sigma.desc x = y

/-- Equivariant maps from A¹_A to X_A with the prescribed value at zero.
Source: Milne Definition 13.55, Remark 13.57
(blueprint: lem-sfb-rational-projective-attracting-cells). -/
def IsAttractorMap {F : Type u} [Field F] {X : Over (Spec (.of F))}
    (a : ModObj (StandardGroupSchemes.multiplicative F) X)
    (x : 𝟙_ (Over (Spec (.of F))) ⟶ X) (A : CommAlgCat.{u} F)
    (q : StandardGroupSchemes.affine F A ⊗ StandardGroupSchemes.additive F ⟶ X) : Prop :=
  lift (𝟙 _) (linePoint F A 0) ≫ q = toUnit _ ≫ x ∧
  ∀ (B : CommAlgCat.{u} F) (f : A ⟶ B) (t : Bˣ) (v : B),
    lift (StandardGroupSchemes.map F f.hom) (linePoint F B ((t : B) * v)) ≫ q =
      lift (unitPoint F B t)
        (lift (StandardGroupSchemes.map F f.hom) (linePoint F B v) ≫ q) ≫ a.smul

/-- Representation by evaluation at one, stated as a unique factorization in both
 directions. Each attractor map is uniquely the map corresponding to a cell point,
 and each cell point has exactly one attractor map. These formulas make the
 bijections natural by composition, rather than choosing arbitrary bijections.
Source: Milne Remark 13.57 and Proposition 13.58
(blueprint: lem-sfb-rational-projective-attracting-cells). -/
def RepresentsAttractor {F : Type u} [Field F] {X : Over (Spec (.of F))}
    (a : ModObj (StandardGroupSchemes.multiplicative F) X)
    (x : 𝟙_ (Over (Spec (.of F))) ⟶ X)
    (C : Over (Spec (.of F))) (j : C ⟶ X) (A : CommAlgCat.{u} F) : Prop :=
  (∀ q, IsAttractorMap a x A q →
    ∃! z : StandardGroupSchemes.affine F A ⟶ C,
      z ≫ j = lift (𝟙 _) (linePoint F A 1) ≫ q) ∧
  ∀ z : StandardGroupSchemes.affine F A ⟶ C,
    ∃! q : StandardGroupSchemes.affine F A ⊗ StandardGroupSchemes.additive F ⟶ X,
      IsAttractorMap a x A q ∧ lift (𝟙 _) (linePoint F A 1) ≫ q = z ≫ j

/-- The rational isolated-fixed-point projective attracting-cell theorem.
Source: Milne Theorem 13.47 and Corollary 13.49, pp.272--274; linear application
p.275; concentrators in Section 13g, pp.276--278.
(blueprint: lem-sfb-rational-projective-attracting-cells).

Proof plan, following the seven steps of the DAG:
1. Use lem-sfb-gm-representation-weight-basis to diagonalize rho. In the invariant
   chart z_i ≠ 0 use ratios u_j with weights a_j-a_i. The standard-chart theorem
   lemma-nagata-relative-affine-space-open-immersion and closedness of X make
   its intersection affine; lem-pc-open-immersion-smooth-composition makes it smooth.
   At x impose u_j=0 for negative weights and u_j=u_j(x) for zero weights.
2. The remaining positive coordinates extend by u_j ↦ t^(a_j-a_i)u_j. Polynomial
   to Laurent polynomial localization is injective even with nilpotent coefficients.
   Thus the extension stays in X, is equivariant, and is the affine concentrator.
   Apply lem-sfb-smooth-affine-concentrator with the smooth closed rational point.
3. Every equivariant map with that value at zero stays in this chart: on a geometric
   fibre an invariant closed complement missing zero cannot contain a nonzero orbit.
   Apply lem-weil-pbc-morphism-factors-through-open-subscheme. Equivariance fixes
   the map on Gm, and polynomial localization fixes it everywhere. Evaluation at one
   therefore represents the identical functor in every chart, on every test algebra.
4. The cell algebra is positively graded with degree-zero part F. Smoothness gives
   regularity at its vertex by lem-weil-pbc-smooth-scheme-over-field-regular.
   Apply lem-sfb-positive-graded-regular-polynomial to homogeneous cotangent lifts;
   def-sbc-affine-space gives the claimed affine-space isomorphism.
5. For a geometric point [v], let w be its least nonzero weight. The polynomial
   expression [sum_b t^(b-w)v_b] extends the orbit inside X with unique fixed limit.
   Every scheme point lifts to a geometric point, proving exhaustion and disjointness.
6. Smoothness gives regularity; geometric connectedness and nonemptiness give
   integrality by lem-sc-regular-connected-integral. Finitely many cell closures cover,
   so one is dense and locally closed, hence open. Irreducibility gives uniqueness.
   Use lem-weil-pbc-reduced-induced-closed-subscheme to identify its open structure.
7. The same functor on L-algebras is the base-changed functor. Base change its
   affine-space isomorphisms. The minimum-weight argument gives the partition.
   Use lem-sfb-scheme-lfp-smooth-flat-base-change and lem-pc-field-extension-flat
   to retain smoothness; geometric connectedness retains irreducibility, so the
   same nonempty open cell remains dense and unique. For Spec F the functor has
   exactly one element and its representing scheme is affine zero-space. -/
theorem rational_projective_attracting_cells
    {F : Type u} [Field F]
    (X : Over (Spec (.of F))) [Nonempty X.left] [Smooth X.hom]
    [IsProjective X.hom] [GeometricallyConnected X.hom]
    (a : ModObj (StandardGroupSchemes.multiplicative F) X)
    (n : ℕ) (rho : StandardGroupSchemes.multiplicative F ⟶
      GeneralLinearGroup (ULift.{u} (Fin (n + 1))) F) [IsMonHom rho]
    (p : ModObj (StandardGroupSchemes.multiplicative F)
      (DiagonalProjectiveAction.space F n))
    (hp : ProjectivizedGmRepresentation.IsProjectivization rho p)
    (i : X ⟶ DiagonalProjectiveAction.space F n) [IsClosedImmersion i.left]
    (hi : a.smul ≫ i = (𝟙 _ ⊗ₘ i) ≫ p.smul)
    (I : Type u) [Finite I]
    (x : I → (𝟙_ (Over (Spec (.of F))) ⟶ X))
    (hfixed : ∀ A : CommAlgCat.{u} F, RepresentsFixed a I x A) :
    ∃ (C : I → Over (Spec (.of F))) (j : ∀ b, C b ⟶ X) (d : I → ℕ),
      (∀ b, Smooth (C b).hom ∧ IsImmersion (j b).left ∧
        Nonempty (C b ≅ Over.mk
          (AffineSpace (ULift.{u} (Fin (d b))) (Spec (.of F)) ↘ Spec (.of F))) ∧
        ∀ A : CommAlgCat.{u} F, RepresentsAttractor a (x b) (C b) (j b) A) ∧
      (∀ y : X.left, ∃! b, y ∈ Set.range (j b).left) ∧
      ∃ b₀ : I, IsOpenImmersion (j b₀).left ∧ DenseRange (j b₀).left ∧
        (∀ b, closure (Set.range (j b).left) = Set.univ ↔ b = b₀) ∧
        (∀ (L : Type u) [Field L] [Algebra F L],
          (∀ (A : CommAlgCat.{u} F) [Algebra L A] [IsScalarTower F L A],
            RepresentsFixed a I x A ∧
            ∀ b, RepresentsAttractor a (x b) (C b) (j b) A) ∧
          (∀ b, Smooth (((Over.pullback
                (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (C b)).hom) ∧
            IsImmersion (((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map (j b)).left) ∧
            Nonempty (((Over.pullback
                (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (C b)) ≅
              Over.mk (AffineSpace (ULift.{u} (Fin (d b))) (Spec (.of L)) ↘ Spec (.of L)))) ∧
          (∀ y : ((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj X).left,
            ∃! b, y ∈ Set.range (((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map (j b)).left)) ∧
          IsOpenImmersion (((Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map (j b₀)).left) ∧
          (∀ b, closure (Set.range (((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map (j b)).left)) =
            Set.univ ↔ b = b₀)) ∧
        (Nonempty (X ≅ 𝟙_ (Over (Spec (.of F)))) →
          Nonempty (Unique I) ∧ ∀ b, d b = 0) := by
  sorry

end AlgebraicGeometry.RationalProjectiveAttractingCells
