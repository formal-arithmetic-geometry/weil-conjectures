/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.CondensedTateRealizationData
import Sheaf.Paper.CondensedTateAugmentation
import Sheaf.Paper.CondensedTateScalarPower

/-! # Assembly of the normalized condensed Tate realization

The derived-limit comparison and the scalar-extension comparison are combined by
adjunction, then transported through the prescribed realization and shift comparisons.
(blueprint: lem-pur-condensed-tate-realization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures WeilConjectures.CondensedERealization

namespace AlgebraicGeometry.ProEtale.CondensedTateRealization

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

private theorem normalized_iso_of_transpose
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {P M : C} {N : D} (a : P ⟶ M) [IsIso a]
    (b : P ⟶ G.obj N) [IsIso ((adj.homEquiv P N).symm b)] :
    ∃! e : F.obj M ≅ N, a ≫ adj.unit.app M ≫ G.map e.hom = b := by
  let q := (adj.homEquiv P N).symm b
  let e : F.obj M ≅ N := (F.mapIso (asIso a)).symm ≪≫ asIso q
  have he : F.map a ≫ e.hom = q := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_hom, asIso_inv]
    rw [← F.map_comp_assoc, IsIso.hom_inv_id, F.map_id, Category.id_comp]
  have hnorm : a ≫ adj.unit.app M ≫ G.map e.hom = b := by
    have h := congrArg (adj.homEquiv P N) he
    rw [adj.homEquiv_naturality_left, adj.homEquiv_unit] at h
    exact h.trans ((adj.homEquiv P N).apply_symm_apply b)
  refine ⟨e, hnorm, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (cancel_epi (F.map a)).1
  apply (adj.homEquiv P N).injective
  simpa only [adj.homEquiv_naturality_left, adj.homEquiv_unit] using he'.trans hnorm.symm

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The reconstructed positive Tate tower realizes canonically as the actual condensed
derived Tate twist, including the unit in tensor degree zero.
Source: main-20261015, smooth purity, rational-and-qbar-purity proof Step 2;
Bhatt--Scholze 3.1.10, 6.8.2 and 6.8.4; Stacks 03EK, 06YU, 0941
(blueprint: lem-pur-condensed-tate-realization).

Proof:
1. completedCondensedIntegral and the finite-quotient and completed-constant comparisons
identify R with the completed coefficient ring, with every finite projection unchanged
[sk-prop-sfb-qlbar-colimit-x, lem-pur-condensed-zl-reduction-mod-ell-power,
lem-weil-pbc-completed-constant-sheaf-reduction].
The finite root sheaf is killed by ell^n, so r tensor z maps to rho_n(r) z, with inverse
z maps to 1 tensor z. The two composites are identities by locally lifting rho_n(r)
to an integer. These maps commute with root-power transitions. The n=0 root sheaf
mu_1 is zero; removing it preserves the limit and every positive projection.
2. The internal/sectionwise equivalence retains underlying sheaves. The locally-free
Tate-line theorem identifies the limit with a rank-one R-module. Repleteness makes
each limit projection epic. Its induced finite quotient map is an epimorphism between
locally rank-one free modules, hence invertible. Tensoring gives exactly powerProjection
and the strict finite tower, including quotient coefficients at d=0
[lem-pur-twist-sheaf-locally-free, det-pe-replete-epimorphism,
def-weil-pbc-internal-abelian-sheaf-module-equivalence].
3. Trivializing the line identifies its tensor powers with R. They are flat and their
single complexes K-flat. The tower is epimorphic. Its degree-zero limit is integralPower.
Compare its Roos triangle with the K-injective Rlim triangle using the same projections.
The levelwise-isomorphism theorem gives invertibility of derivedAugmentation;
negative Ext vanishing gives uniqueness of this projection-normalized map
[lem-pc-kflat-closure, lem-weil-proetale-surjective-tower-derived-limit,
lemma-weil-pbc-r-lim-levelwise-isomorphism,
lem-weil-pbc-ringed-strict-tower-homotopy-limit].
4. J's recorded scalarExtension computes realization on the integral object. The
canonical lift/down coefficient transport identifies the rational field with Q_l.
The K-flat line computes both scalar extensions. The actual derived adjunction unit
identifies the adjoint of the ordinary balancedPower map with its scalar-extension map.
Monoidality of ringed derived tensor pullback makes this an isomorphism to tateTwistNat
[lem-weil-pbc-condensed-e-realization, lem-pur-derived-change-of-rings,
lem-pur-kflat-change-of-rings, lem-weil-pbc-ringed-topoi-derived-tensor-pullback].
5. Invert derivedAugmentation to obtain the unique e0 satisfying the displayed equation.
The recorded realization and canonical shift comparisons give shiftedComparison, hence
the requested ambient isomorphism. At d=0 the balanced map is precisely integralToQbar,
so this is the canonical identification of the realized unit with B. The same construction
works on the empty scheme and at ell=2; no primitive root or global trivialization is chosen. -/
theorem condensed_tate_realization (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] (T : Base k)
    (r : At l (LiftedQ.{u} l) T.scheme) (d : ℕ)
    (hM : PbcIsBoundedConstructibleComplete T.scheme
      (pbcIntegralDatum l (LiftedQ.{u} l)) (shiftedReconstructed T.scheme l r d))
    (_hred : HasCanonicalReductions T.scheme l r d) :
    ∃! e : realized T.scheme l r ⟨shiftedReconstructed T.scheme l r d, hM⟩ ≅
        (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived T.scheme l (d : ℤ)),
      ∃ e0 : (ambientRealization T.scheme l r).obj (reconstructed T.scheme l r d) ≅
          tateTwistDerived T.scheme l (d : ℤ),
        derivedAugmentation T.scheme l r d ≫
            (scalarAdjunction T.scheme l r).unit.app (reconstructed T.scheme l r d) ≫
            (ambientRestriction T.scheme l r).map e0.hom =
              derivedBalancedPower T.scheme l r d ∧
          e = shiftedComparison T.scheme l r d hM e0 := by
  let := derivedAugmentation_isIso l k T r d
  let := scalarBalancedPower_isIso l k T r d
  obtain ⟨e0, he0, huniq⟩ := normalized_iso_of_transpose
    (scalarAdjunction T.scheme l r) (derivedAugmentation T.scheme l r d)
    (derivedBalancedPower T.scheme l r d)
  refine ⟨shiftedComparison T.scheme l r d hM e0, ⟨e0, he0, rfl⟩, ?_⟩
  rintro e ⟨e0', he0', rfl⟩
  exact congrArg (shiftedComparison T.scheme l r d hM) (huniq e0' he0')

end AlgebraicGeometry.ProEtale.CondensedTateRealization
