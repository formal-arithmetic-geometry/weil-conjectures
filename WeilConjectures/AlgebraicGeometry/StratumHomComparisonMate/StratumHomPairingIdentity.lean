/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StratumHomComparisonMate.Etale.StratumHomComparisonData

/-! # Comparison of the normalized stratum evaluation pairings

Source: Weil blueprint, latest, finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-pairing-identity).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor MonoidalCategory
namespace AlgebraicGeometry.StratumHomComparisonMate

/-- The evaluation pairings of the two normalized stratum isomorphisms agree.
Source: Weil blueprint, latest, sec-smooth-purity/sk-lem-sp-tower,
lem-weil-finite-duality-site-comparison.proof.md, second paragraph
(blueprint: lem-sf-stratum-hom-pairing-identity).

Proof: Let K = H_e(P,J_e M) and h = chi_e(P,M). Its ordinary adjunct is
u = s_e^*(h) followed by the ordinary counit on K. Write t for evaluation
following u tensor the identity of P. The inverse normalization equation for chi_e,
together with naturality of projection and chi_e followed by its inverse, identifies
ambient evaluation with projection, then Q_e(t), then the exceptional counit.
Put d = H_p(1,gamma) beta_(P,J_e M). The ordinary adjunct of
R s_p(d) b_s C_X(h) is d C_S(u) followed by the inverse pullback comparison: this
is the counit equation for the fixed mate b_s, transported from D+ by its canonical
compatibility maps. Evaluation of this adjunct is gamma C_S(t), because beta is
by definition the transpose of pulled-back evaluation and the tensor comparison is
natural. Now apply the inverse normalization equation for chi_p to that composite.
Precompose its tensor transpose with the extension comparison Delta. The canonical
projection-comparison square, transported by the exact/derived extension isomorphisms,
replaces its projection by Delta C_X(projection_e). Naturality of Delta at t moves
Delta past the evaluation arrow. The counit compatibility equation supplied by z
then replaces Q_p(gamma), Delta and the pro-etale exceptional counit by comparison
of the etale exceptional counit. The resulting pairing is comparison of ambient
etale evaluation. Injectivity of the tensor-Hom adjunction proves equality with the
ambient beta, after Hom of Delta inverse. Finally postcompose by chi_p. This gives
exactly the displayed equality. No existence or choice of chi, boundedness theorem,
or conditional invertibility assertion is part of this lemma.
-/
theorem normalizedComparisonIdentity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)]
    (z : AlgebraicGeometry.ProEtale.LocallyClosedExceptionalComparison A c v)
    (P : Etale.D A S) (M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X)
    (χe : Etale.HomIso A c v z.adjoints) (χp : ProEtale.HomIso A c v z.adjoints)
    (he : Etale.Normalized A c v z.adjoints χe)
    (hp : ProEtale.Normalized A c v z.adjoints χp)
    (hK : DerivedCategory.TStructure.t.plus
      (Etale.hom A S P ((z.adjoints.etaleRight v).obj M.obj))) :
    AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) M.obj ≫
      homChange A c v P M.obj ≫
      χp.hom.app (op ((ImmersionProjectionComparison.comparison A S).obj P),
        (ImmersionProjectionComparison.comparison A X).obj M.obj) =
      (ImmersionProjectionComparison.comparison A X).map (χe.hom.app (op P, M.obj)) ≫
        directImageMate A (c ≫ v) ⟨_, hK⟩ ≫
        (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
          ).rightDerivedFunctor.map (stratumMap A c v z P M) := by sorry

end AlgebraicGeometry.StratumHomComparisonMate
