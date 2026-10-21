/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.SixFunctors.EtaleOpenTensor
public import Sheaf.Paper.ProperOpenCoefficientRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import Sheaf.Paper.ScalarPullbackComposition

/-! # Scalar extension respects ordinary étale open base change

Source: Stacks Project, etale-cohomology.tex, Tag 03S6,
`lemma-shriek-base-change`, with the coefficient/unit calculation in the DAG
(blueprint: lem-pur-etale-open-scalar-exchange).

All functors act on the ordinary unbounded small étale derived categories.
The open coefficient map is the existing balancing isomorphism `openScalarExtension`.
The exact pullback comparison is `properOpenCoefficientPullbackIso`, and the open
base-change map is the inverse of the published degreewise-derived isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Scalar balancing commutes with ordinary étale open base change, naturally on
all unbounded derived objects. Here the pullback is `T' ×_T U`, with open projection
`pullback.fst g j` and other projection `pullback.snd g j`.
Source: Stacks Project, etale-cohomology.tex, Tag 03S6, `lemma-shriek-base-change`
(blueprint: lem-pur-etale-open-scalar-exchange).

Proof:
1. Write L, J for open extension and restriction, G, H for pullback along g, h,
and Q, Q', S, S' for scalar extension on T, T', U, U'. Write i and i' for the
inverses of the open balancing maps, d_R for the inverse open base-change maps,
and c_R : H_R J_R ≅ J'_R G_R for the canonical square comparison. The prescribed
open-unit transpose formulas give J_B(i) eta_B = lambda_j inverse S(eta_A),
and J'_R(d_R) eta'_R = c_R H_R(eta_R). These are the degreewise-normalized open
adjunctions and comparisons of lem-coef-etale-open-tensor,
def-pur-open-coefficient-normalizations and lem-cbc-extension-zero-base-change.
2. Apply lem-sf-scalar-pullback-composition to (j,h) and (g,j'). Their composite
scheme maps agree. Eliminate the common scalar comparison for that composite.
After multiplying by inverse scalar comparisons, the resulting square identity is
J'_B(lambda_g inverse) lambda_j' inverse S'(c_A) =
c_B H_B(lambda_j inverse) lambda_h inverse.
3. Invert both composites in the asserted equality. The resulting maps are
x = G_B(i) d_B L'_B(lambda_h inverse) and
y = lambda_g inverse Q'(d_A) i', both out of L'_B S' H_A M.
It suffices to compare their transposes under L'_B adjoint to J'_B.
4. Naturality of the open unit, the formula for d_B, naturality of c_B, the formula
for i, and naturality of lambda_h inverse give the transpose of x as
c_B H_B(lambda_j inverse) lambda_h inverse S'H_A(eta_A).
5. The formula for i', naturality of lambda_j' inverse, and the formula for d_A
give the transpose of y as
J'_B(lambda_g inverse) lambda_j' inverse S'(c_A) S'H_A(eta_A).
6. Apply the square identity of step 2 at L_A M and precompose with S'H_A(eta_A).
The transposes coincide, so injectivity of the adjunction bijection gives x = y.
Taking inverses proves the displayed equality. Every factor is natural in M.
The argument uses no boundedness, coefficient flatness, or quasi-compactness. -/
theorem etaleOpenScalarExchange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U T T' : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (g : T' ⟶ T) (M : DerivedCategoryModule A U) :
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.map
        ((openScalarExtension φ j).hom.app M) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} B) (IsPullback.of_hasPullback g j).flip).inv.app
          ((scalarExtension φ U).obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B)
        (pullback.fst g j)).mapDerivedCategory.map
          ((properOpenCoefficientPullbackIso φ (pullback.snd g j)).hom.app M) =
    (properOpenCoefficientPullbackIso φ g).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      (scalarExtension φ T').map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} A) (IsPullback.of_hasPullback g j).flip).inv.app M) ≫
      (openScalarExtension φ (pullback.fst g j)).hom.app
        ((upperStar (ModuleCat.{u + 1} A) (pullback.snd g j)).mapDerivedCategory.obj M) := by
  sorry

end AlgebraicGeometry.Etale
