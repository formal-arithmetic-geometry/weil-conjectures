/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Comma.Arrow
import Sheaf.AlgebraicGeometry.DerivedDirectImageComposition
import WeilConjectures.SixFunctors.Integral.BaseChange
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Paper.ExchangeIdentityPasting
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Sheaf.AlgebraicGeometry.IntegralEtaleDirectImageExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Integral pushforward and the base-change arrow

Source: Stacks Project, Tag 0F05, lemma-base-change-q-integral-bottom, proof;
Tag 04C2, lemma-what-integral; Tag 0E46, remark-compose-base-change
(blueprint: lem-sbc-integral-pushforward-base-change-arrow).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Integral pushforward identifies the two degreewise base-change arrows, naturally in
an abelian etale sheaf. An isomorphism in the arrow category of the functor category
includes both natural endpoint isomorphisms and their compatibility with the arrows.
The degreewise arrows below are the cohomology of the recorded bounded-below exchange,
restricted to sheaves in degree zero; this is the abelian-sheaf clause of the base-change
map. Source: Stacks Project, Tags 0F05 (proof), 04C2 and 0E46
(blueprint: lem-sbc-integral-pushforward-base-change-arrow).

Proof plan:
1. The base change of the integral map is integral
   (lem-sbc-integral-morphism-base-change). Its pushforward and that of the original
   integral map are exact (sbc-lem-integral-etale-direct-image-exact); inverse images
   are exact (prop-weil-pbc-inverse-image-exact).
2. The underived integral exchange (lem-sbc-integral-underived-exchange) extends
   termwise to complexes. Exact functors compute their own derived functors
   (lem-weil-pbc-exact-functor-derived-functor), and localization descends the comparison
   (lem-weil-pbc-localization-universal-property). The resolution formula
   (lem-weil-pbc-derived-exchange-termwise) identifies it with the canonical exchange:
   the extra resolution map stays a quasi-isomorphism under exact pushforward, by
   lem-weil-pbc-exact-functor-complex-cohomology.
3. Insert the derived composition comparisons
   (def-weil-pbc-derived-direct-image-composition) into the vertical pasting identity
   (lem-weil-pbc-exchange-identity-pasting). The resulting equality identifies the pasted
   exchange with integral pushforward of the inner exchange, conjugated by these
   comparisons and the integral exchange from step 2.
4. Apply degree-q cohomology. The natural exact-functor cohomology comparisons
   (lem-weil-pbc-exact-functor-complex-cohomology) give the two endpoint isomorphisms.
5. Naturality gives the commuting arrow square. Functors preserve inverses, so if the
   inner base-change arrow is invertible, its pushforward and the conjugate pasted
   arrow are invertible as well. -/
theorem integralPushforward_baseChange_arrow
    {X' S' S'' X'' T Y : Scheme.{u}}
    {f' : X' ⟶ S'} {f'' : X'' ⟶ S''} {π' : X'' ⟶ X'}
    {g' : T ⟶ S''} {h' : Y ⟶ X''} {e : Y ⟶ T}
    (π : S'' ⟶ S') [IsIntegralHom π] [QuasiCompact g'] [QuasiSeparated g']
    (sqπ : ChosenCartesianSquare π' f'' f' π)
    (sq : ChosenCartesianSquare h' e f'' g') (q : ℕ) :
    Nonempty
      (Arrow.mk
        (Functor.whiskerRight
          (Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
            (Functor.whiskerRight
              (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq.flip)
              (DerivedCategory.Plus.homologyFunctor _ (q : ℤ))))
          (lowerStar AddCommGrpCat.{u + 1} π')) ≅
        Arrow.mk
          (Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
            (Functor.whiskerRight
              (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
                (sq.toCommSq.flip.vert_comp sqπ.toCommSq.flip))
              (DerivedCategory.Plus.homologyFunctor _ (q : ℤ))))) ∧
    ∀ (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsIso
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq.flip).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) →
      IsIso
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
            (sq.toCommSq.flip.vert_comp sqπ.toCommSq.flip)).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
