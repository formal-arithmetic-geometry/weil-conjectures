/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.CategoryTheory.DerivedBaseChangeMap
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.SixFunctors.RingedDerivedAdjointLift
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.SixFunctors.RingedDerivedCompositionComparison
import Sheaf.SixFunctors.RingedDerivedTwoIsoComparison
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Resolution-unit normalization of flat ringed exchange

Source: Stacks Project, Cohomology on Sites, Tags 0736 and 07A7
(blueprint: lem-sfb-flat-ringed-exchange-resolution-unit).

The ordinary exchange is the mate of the specified geometric square. The theorem
compares it with the existing derived exchange, retaining the canonical termwise
comparison maps on both sides of the equality.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.RingedDerivedComparisons

/-- The ordinary exchange for the very square used by `derivedBaseChangeMap`.
The three ordinary comparisons are the normalized scalar-extension comparisons
of the two paths and the specified ring-compatible geometric two-isomorphism.
Source: Stacks Project, Cohomology on Sites, Tags 0736 and 07A7
(blueprint: lem-sfb-flat-ringed-exchange-resolution-unit). -/
def ordinaryBaseChangeMap {E E' F F' : Site.{u, w}}
    (S : DerivedBaseChangeSquare E E' F F') :
    S.lf.edge.pushforward ⋙ S.lg.edge.pullback ⟶
      S.lg'.edge.pullback ⋙ S.lf'.edge.pushforward :=
  CategoryTheory.mateEquiv S.lf.edge.moduleAdjunction S.lf'.edge.moduleAdjunction
    (TwoSquare.mk _ _ _ _
      (((S.firstComposition.ordinary.symm ≪≫ S.squareComparison.ordinary) ≪≫
        S.secondComposition.ordinary).hom))

/-- Flat horizontal module pullbacks identify the derived exchange, composed with
its right-derived resolution unit, with the termwise ordinary exchange followed
by the other resolution unit. The maps `Lift.alpha` are the canonical comparisons
`Lg* Q → Q g*`; under the two exactness hypotheses they are the termwise
identifications. Keeping them in the equation avoids any choice of inverses.
Only the horizontal pullbacks are exact. The bounded below complex has arbitrary
terms, and neither resolution unit nor the exchange is assumed invertible.
Source: Stacks Project, Cohomology on Sites, Tags 0736 and 07A7
(blueprint: lem-sfb-flat-ringed-exchange-resolution-unit).

Proof:
1. Write A = g*, B = g'*, a = g_*, b = g'_*, R = f_* and T = f'_*.
   The exact-functor derived theorem (lem-weil-pbc-exact-functor-derived-functor)
   identifies the horizontal left derived functors with their termwise functors.
   Apply lem-sfb-resolving-derived-adjunction-normalization to every complex,
   since A and B are exact. Its Hom formula gives the horizontal derived unit
   as Q of the ordinary unit followed by eta_b, and the derived counit after
   A(eta_a) as Q of the ordinary counit. These are the lift's adjunctions:
   lem-sfb-ringed-derived-adjoint-lift fixes the same Hom formula on flat-term
   K-flat and K-injective representatives. Every derived object is QI for a
   K-injective I (prop-pur-kinjective-resolutions-exist). A flat-term K-flat
   quasi-isomorphism P' → bI (lem-pc-kflat-resolution) gives an invertible map
   QP' → Rb(QI). The two Hom formulas agree there, forcing the automorphism
   comparing the two right adjoints to be the identity; likewise for a.
2. The every-complex right-derived-unit equations of the two path composition
   comparisons (lem-sfb-ringed-derived-composition-comparison) and the specified
   two-isomorphism (lem-sfb-ringed-derived-two-iso-comparison) identify the right
   derived square tau at QW with the ordinary right square t at W, with both
   path resolution units inserted. No resolution unit is canceled.
3. Rotate the specified derived mate by the horizontal adjunctions using
   lem-weil-pbc-mate-pasting. It is the horizontal derived counit after A(tau)
   after A Rf_*(the horizontal derived unit). The same rotation expresses
   ordinaryBaseChangeMap by the ordinary horizontal counit, A(t), and AR(unit).
4. At W = BP, insert the unit formula from step 1 and move eta_R across the
   ordinary unit using naturality. Step 2 replaces the resulting tau and its
   two path resolution units by the other path through Q(t).
5. Naturality moves eta_T past the horizontal derived counit. The counit
   formula of step 1 replaces the remaining counit and eta_a by Q(counit).
   Functoriality and step 3 now identify the remaining composite with Q(e_P).
   Restoring the two canonical alpha maps yields the displayed equation.
   The argument never uses injectivity or acyclicity of P or BP.
-/
theorem flat_ringed_exchange_resolution_unit {E E' F F' : Site.{u, w}}
    (S : DerivedBaseChangeSquare E E' F F')
    (_hg : exactFunctor F.modules F'.modules S.lg.edge.pullback)
    (_hg' : exactFunctor E.modules E'.modules S.lg'.edge.pullback)
    (P : CochainComplex E.modules ℤ) (n : ℤ) (_hP : P.IsStrictlyGE n) :
    S.lg.edge.left.map (S.lf.eta.app P) ≫
        derivedBaseChangeMap S (DerivedCategory.Q.obj P) ≫
        S.lf'.edge.right.map (S.lg'.alpha P) =
      S.lg.alpha ((S.lf.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (ordinaryBaseChangeMap S) (.up ℤ)).app P) ≫
        S.lf'.eta.app ((S.lg'.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

end CategoryTheory.RingedDerivedComparisons
