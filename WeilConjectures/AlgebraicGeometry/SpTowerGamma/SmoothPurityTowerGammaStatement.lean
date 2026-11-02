/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates

/-! # Statement of tower orientation and purity

This module records the corrected stage-2 interface for the tower-geometric
gamma proposition.  The field is allowed to be finite or algebraically closed;
the positive-characteristic parameter and the smooth separated factorisation
are explicit.  The data in `SpTowerGamma.Purity` expands the three clauses of
the blueprint statement: the diagonal orientation and its finite evaluations,
the counit-transpose purity map and its naturality, and preservation of
normalized towers by both adjoints.

The theorem is named `tower_gamma_statement`: the landed, invalidated finite-field
theorem `SpTowerGamma.tower_gamma` of `Sheaf.Paper.SmoothPurityTowerGamma` keeps its
name for its importers, and a second public declaration of that full name would make
the two modules impossible to import together.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.md`, clauses (1)--(3)
(blueprint: det-sp-tower-gamma).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
  WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerGamma

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/--
For a finite or algebraically closed field of positive characteristic, a
separated finite-type smooth factorisation admits the tower orientation, the
natural tower purity isomorphism, and preservation of normalized towers by
compact support and exceptional pullback.

The witness `Purity` contains, clause by clause, the orientation
`orderedLine ≅ exceptional (unit)`, the actual tensor/counit transpose and
its finite-level smooth-purity evaluations, and the two normalization
preservation assertions.  Its `FiniteLevels` field records every positive
coefficient level and the prescribed comparison squares.  Level `n` here is the
coefficient ring `O_E / ell ^ (n + 1)`.

Proof (the node's six steps; `R_n = O_E / ell ^ n`, `m ≤ n`):
1. Reduction compatibility of the finite orientations: the comparison `c` of
   det-sp-reduction-exceptional is the mate of `b⁻¹`; lem-weil-pbc-mate-pasting(1)
   applied to the cocycle of `b` (det-sp-reduction-direct-image, scalar associators of
   det-sp-scalar-extension-functor) gives `c_{A,B} (c_{R,A})_B = c_{R,B}`.  With
   det-sp-finite-general-ring(1) `a_A = c_{R,A} (a_R)_A` this gives
   `c_{A,B} (a_A)_B = a_B`, which by det-sp-tower-gluing(3) is compatibility with the
   actual reduction of `omega = G 1_Y`.  No flatness of `B` over `A` is used.
2. By det-sp-tower-gluing(1), `omega[-2d]` is locally a degree-zero rank-one Tate
   tower; det-sp-finite-general-ring(2) identifies the step-1 orientations with the
   direct diagonal/DNC ones.  lem-sp-strict-line-heart-assembly, applied to
   `L = (R_{n,X}(d))_n`, `V = omega`, `s = 2d` and the squares of step 1, gives the
   tower isomorphism `a : L[2d] ≅ omega` with exactly those finite levels (clause (1)).
3. For `P_K = f^* K (d)[2d]` and `Q_K = f^* K ⊗ omega`,
   lem-coef-semilinear-derived-sections gives the finite evaluations;
   det-sp-finite-general-ring(3) identifies `(P_K)_n` with `(G K)_n`, transferring the
   uniform constructible finite-Tor bounds of `G K` (gluing) to `P_K`, and the
   isomorphism of step 2 to `Q_K`.  lem-sp-tower-compact-support-projection-formula
   for `(omega, K)` gives the projection isomorphism; `h_K` is its inverse followed
   by `1 ⊗ ε`, and `t_K = G(h_K) η`.  Naturality of projection, tensor and unit makes
   `gamma_K = t_K (1 ⊗ a) τ_K` natural, and the finite projection evaluations with
   gluing's finite units and counits give `(gamma_K)_n = gamma_{f,R_n}(K_n)`.
4. Each `gamma_{f,R_n}(K_n)` is invertible by det-sp-finite-general-ring(3); the
   conservativity of det-sp-tower-shriek-levels(3) makes `gamma_K` invertible, and the
   inverse lies in the full uniform constructible finite-Tor subcategory (clause (2)).
5. For normalized `C`, lem-sp-coefficient-tower-shriek-calculus(3) writes the
   reduction of `F C` as `F_m(r^C) ∘ b(C_n)`; both factors are invertible
   (det-sp-reduction-direct-image), and gluing gives the uniform bounds: `F`
   preserves normalized towers.
6. For normalized `K`, lem-weil-pbc-ringed-topoi-derived-tensor-pullback and the
   Tate-line comparison of det-sp-scalar-extension-functor(3) make the reductions of
   `P = f^* K (d)[2d]` invertible.  Naturality of reduction
   (det-sp-coefficient-towers-abelian(3)) applied to the tower map `gamma_K` gives
   `r^{GK} (gamma_{K,n})_m = gamma_{K,m} r^P`, with the left reduction identified by
   det-sp-tower-gluing(3); the other three factors are invertible, so `G` preserves
   normalized towers (clause (3)).

Source: latest blueprint, tower-geometric gamma, clauses (1)--(3) and their proof
(blueprint: det-sp-tower-gamma).
-/
theorem tower_gamma_statement
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (pchar : ℕ) (_hp : 0 < pchar) [CharP k pchar] (hne : l ≠ pchar)
    {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of k))]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (w : SpChartAdmissibility.Twists l E X)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (factorization j p) hF G adj) :
    Nonempty (Purity l E b o q j p d w hF G adj lv) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerGamma
