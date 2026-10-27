/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q14
-/
module

public import Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality
public import Sheaf.AlgebraicGeometry.ProjectiveCoordinateRingEulerPolynomial
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.RingTheory.CoordinateQuotientGrading
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeAffineCovers
import WeilConjectures.AlgebraicGeometry.DimensionBaseChange
import WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts

/-! # An affine numerical cover for isomorphism graphs of projective curves

Source: Stacks Project, Tags 0DSQ, 0B9T, 0AYX, 01WD, 0AG7 and 08AE.
(blueprint: lem-sfb-curve-graph-fixed-polynomial-cover)

The helper predicates only expand the clauses of this theorem. The graph is represented
by its source X_t with its canonical closed graph immersion. All field actions in Euler
characteristics are supplied by the displayed structural morphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.CurveGraphFixedPolynomial

/-- Euler characteristic of the nth tensor power on a field-valued fibre. The zeroth
power is the structure module, including for the empty fibre.
Source: Stacks, Tags 0B9T, 0AYR
(blueprint: lem-sfb-curve-graph-fixed-polynomial-cover). -/
def fibreEuler {S X : Scheme.{u}} (f : X ⟶ S) (K : Type u) [Field K]
    (t : Spec (.of K) ⟶ S) (L : X.Modules) (n : ℕ) : ℤ :=
  @Scheme.Modules.eulerChar K _ (pullback f t)
    (OverClass.ofHom (pullback.snd f t))
    (((Scheme.Modules.tensorPullback (pullback.fst f t)).obj L).tensorPow n)

/-- The two constant Euler values, their linear polynomial for all nonnegative powers,
and its zero value on empty fibres. No geometric-point restriction is imposed here.
Source: Stacks, Tags 0B9T, 0AYX
(blueprint: lem-sfb-curve-graph-fixed-polynomial-cover). -/
def HasFibreValues {S X : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    (c l : ℤ) (P : Polynomial ℚ) : Prop :=
  P = Polynomial.C ((l - c : ℤ) : ℚ) * Polynomial.X + Polynomial.C (c : ℚ) ∧
    ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ S),
      fibreEuler f K t L 0 = c ∧ fibreEuler f K t L 1 = l ∧
      (∀ n : ℕ, fibreEuler f K t L n = (n : ℤ) * (l - c) + c ∧
        P.eval (n : ℚ) = (fibreEuler f K t L n : ℚ)) ∧
      (IsEmpty ↥(pullback f t : Scheme.{u}) → c = 0 ∧ l = 0 ∧ P = 0)

/-- Graph Euler and coordinate assertions for one embedding of the product. The graph
map is fixed by both factor projections and its field projection. A polynomial-ring Proj
model q identifies the coordinate presentation with projective space over the field;
the over-field equation prevents an unrelated field action. Every homogeneous ideal
presentation is quantified, without saturation or nonemptiness assumptions.
Source: Stacks, Tags 0DSQ, 0AG7, 08AE
(blueprint: lem-sfb-curve-graph-fixed-polynomial-cover). -/
def HasGraphValues {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (r : ℕ)
    (j : pullback f g ⟶ ℙ(ULift.{u} (Fin (r + 1)); S))
    (M : (pullback f g).Modules) (cX lX cY lY : ℤ) (PX PY R : Polynomial ℚ) : Prop :=
  R = Polynomial.C (((lX - cX) + (lY - cY) : ℤ) : ℚ) * Polynomial.X +
      Polynomial.C (cX : ℚ) ∧
    R = PX + PY - Polynomial.C (PY.eval 0) ∧
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      ∃ q : Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) K ≅
          ℙ(ULift.{u} (Fin (r + 1)); Spec (.of K)),
        q.hom ≫ (ℙ(ULift.{u} (Fin (r + 1)); Spec (.of K)) ↘ Spec (.of K)) =
          Proj.projectiveSpaceOverAffineToSpec _ K ∧
        ∀ e : Over.mk (pullback.snd f t) ≅ Over.mk (pullback.snd g t),
          cX = cY ∧
          ∃ γ : pullback f t ⟶
              pullback (j ≫ (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S)) t,
            IsClosedImmersion γ ∧
            γ ≫ pullback.snd _ t = pullback.snd f t ∧
            γ ≫ pullback.fst _ t ≫ pullback.fst f g = pullback.fst f t ∧
            γ ≫ pullback.fst _ t ≫ pullback.snd f g = e.hom.left ≫ pullback.fst g t ∧
            (∀ n : ℕ,
              @Scheme.Modules.eulerChar K _ (pullback f t)
                (OverClass.ofHom (pullback.snd f t))
                ((Scheme.Modules.tensorPullback γ).obj
                  (((Scheme.Modules.tensorPullback (pullback.fst _ t)).obj M).tensorPow n)) =
                  (n : ℤ) * ((lX - cX) + (lY - cY)) + cX) ∧
            ProjectiveHilbertPolynomial.IsCoordinatePolynomial K r
              (γ ≫ ProjectiveHilbertPolynomial.baseChangeEmbedding r j t) R ∧
            (∀ J : @HomogeneousIdeal _ _ _ _ _ _
                (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) K)
                _ _ MvPolynomial.gradedAlgebra,
              ∀ d : Proj (coordinateQuotientPiece J) ≅ pullback f t,
                d.hom ≫ γ ≫ ProjectiveHilbertPolynomial.baseChangeEmbedding r j t =
                  coordinateQuotientImmersion J ≫ q.hom →
                ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
                  (Module.finrank K (coordinateQuotientPiece J n) : ℚ) = R.eval (n : ℚ)) ∧
            (IsEmpty ↥(pullback f t : Scheme.{u}) → R = 0)

/-- All numerical and product-embedding clauses over one base open, with the given
restricted polarizations. Proper, flat, finitely presented includes qc and qs explicitly.
Source: Stacks, Tags 0DSQ, 01WD
(blueprint: lem-sfb-curve-graph-fixed-polynomial-cover). -/
def HasLocalValues {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (L : X.Modules) (N : Y.Modules) (a b : ℕ) : Prop :=
  IsProper f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
  IsProper g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g ∧
  ∃ (cX lX cY lY : ℤ) (PX PY R : Polynomial ℚ),
    HasFibreValues f L cX lX PX ∧ HasFibreValues g N cY lY PY ∧
    ∃ j : pullback f g ⟶ ℙ(ULift.{u} (Fin (((a + 1) * (b + 1) - 1) + 1)); S),
      IsClosedImmersion j ∧
      j ≫ (ℙ(ULift.{u} (Fin (((a + 1) * (b + 1) - 1) + 1)); S) ↘ S) =
        pullback.fst f g ≫ f ∧
      Nonempty ((Scheme.Modules.tensorPullback j).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (((a + 1) * (b + 1) - 1) + 1))) S 1) ≅
          (Scheme.Modules.tensorPullback (pullback.fst f g)).obj L ⊗
          (Scheme.Modules.tensorPullback (pullback.snd f g)).obj N) ∧
      HasGraphValues f g ((a + 1) * (b + 1) - 1) j
        ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj L ⊗
          (Scheme.Modules.tensorPullback (pullback.snd f g)).obj N) cX lX cY lY PX PY R

/-- Affine Noetherian numerical cover and the fixed graph coordinate polynomial, allowing
empty, nonreduced, disconnected and mixed zero/one-dimensional fibres.
Source: Stacks, Tag 0DSQ (lemma-curves-diagonal-separated-fp), Tags 0B9T, 0AYX, 01WD,
0AG7 and 08AE (blueprint: lem-sfb-curve-graph-fixed-polynomial-cover).

Proof (the seven steps of the DAG node):
1. Apply lem-sfb-flat-projective-twist-base-change-data to both embeddings for properness
   and the finite presentation and relative flatness of twists zero and one. Apply
   lem-sfb-hilbert-graph-family-base-change in both orders for all restrictions and fibres.
2. Apply lem-sfb-proper-flat-sheaf-euler-local-constancy to the four modules; intersect the
   four constancy neighbourhoods and refine by affine Noetherian opens (pqf-def-locnoeth,
   lem-weil-pbc-noetherian-open-subscheme-noetherian). Its base-change clause gives the
   same four integers at every field-valued point, not just residue-field points.
3. Use lem-pc-dim-base-change-affine-covers, lem-pc-dim-base-change,
   lem-pc-dimension-affine-open-cover and lem-pc-scheme-dimension-local-rings to compare
   all field fibres with geometric fibres, treating the empty scheme separately.
4. Degree is chi(L)-chi(O) (def-pc-degree-line-bundle). Induction using
   lem-trf-curve-degree-tensor-additive gives chi(L^n)=n*degree(L)+chi(O) for n>=0.
   This includes n=0, zero-dimensional and empty fibres, and gives PX and PY.
5. Compose the product closed immersion with Segre (lem-chow-segre, def-chow-segre,
   lem-weil-pbc-closed-immersion-products). The transition ratios multiply, identifying
   the pulled-back O(1) with prX^*L tensor prY^*N.
6. The graph-family lemma makes the graph closed. Pullback tensor compatibility
   (lem-weil-pbc-invertible-pullback-tensor) identifies its polarization with L tensor
   e^*N. The isomorphism preserves cohomology, hence cX=cY, and degree additivity gives
   n*(dX+dY)+cX = PX(n)+PY(n)-PY(0).
7. Base change j and compose with the graph. Identify the polynomial Proj model with
   projective space by the same standard coordinate charts (q). For every homogeneous
   ideal presentation, lem-sfb-projective-coordinate-ring-euler-polynomial identifies
   the high coordinate dimensions with twist Euler characteristics. The twist transition
   rule and tensor pullback identify these with step 6. Empty fibres give zero throughout.
-/
theorem exists_affine_numerical_cover {S X Y : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) (g : Y ⟶ S) [IsHProjective f] [IsHProjective g] [Flat f] [Flat g]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (a b : ℕ) (iX : X ⟶ ℙ(ULift.{u} (Fin (a + 1)); S))
    (iY : Y ⟶ ℙ(ULift.{u} (Fin (b + 1)); S))
    [IsClosedImmersion iX] [IsClosedImmersion iY]
    (hiX : iX ≫ (ℙ(ULift.{u} (Fin (a + 1)); S) ↘ S) = f)
    (hiY : iY ≫ (ℙ(ULift.{u} (Fin (b + 1)); S) ↘ S) = g)
    (hX : ∀ s : S,
      topologicalKrullDim ↥(pullback f (ProjectiveHilbertPolynomial.geometricPoint S s) :
        Scheme.{u}) ≤ 1)
    (hY : ∀ s : S,
      topologicalKrullDim ↥(pullback g (ProjectiveHilbertPolynomial.geometricPoint S s) :
        Scheme.{u}) ≤ 1) :
    ∃ (I : Type u) (U : I → S.Opens), (⨆ i, U i) = ⊤ ∧
      ∀ i : I, IsAffineOpen (U i) ∧ IsNoetherian (U i).toScheme ∧
        HasLocalValues (pullback.snd f (U i).ι) (pullback.snd g (U i).ι)
          ((Scheme.Modules.tensorPullback (pullback.fst f (U i).ι ≫ iX)).obj
            (ProjectiveSpace.twist (ULift.{u} (Fin (a + 1))) S 1))
          ((Scheme.Modules.tensorPullback (pullback.fst g (U i).ι ≫ iY)).obj
            (ProjectiveSpace.twist (ULift.{u} (Fin (b + 1))) S 1)) a b := by
  sorry

end AlgebraicGeometry.CurveGraphFixedPolynomial
