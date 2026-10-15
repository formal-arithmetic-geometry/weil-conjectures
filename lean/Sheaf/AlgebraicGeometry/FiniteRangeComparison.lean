/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.AlgebraicGeometry.TruncationExchangeCouple
public import Sheaf.AlgebraicGeometry.HypercohomologyFiltrations
public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.ExactCoupleMorphism
import Sheaf.CategoryTheory.SpectralSequencePageInduction
import Sheaf.CategoryTheory.FiniteFiltrationInduction
import Sheaf.AlgebraicGeometry.TruncationExchangeAbutment
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative

/-!
# Finite-range comparison

Source: literature/blueprint/master/blueprint/sec-smooth-base-change/sk-rem-rest/
sbc-lem-finite-range-comparison.md, statement and proof, order 1436
(blueprint: sbc-lem-finite-range-comparison).

The existential exact couples have exactly the recorded truncation data. The limiting
comparison is specified by its restriction to limiting cycles and its quotient square,
so it is the map induced by exchange, rather than an unrelated isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.TruncationExchange
open CategoryTheory.BigradedExactCouple

namespace AlgebraicGeometry.Etale

/-- If exchange is an isomorphism on every E₂ term and K has cohomology in [a,b],
then its induced infinite-page maps, all its cohomology maps, and exchange itself
are isomorphisms.

Proof:
1. Apply lem-weil-pbc-truncation-couple-morphism to form the two exact couples
   and their exchange morphism. Its page identifications identify tE with the
   degree-p exchange on H^q(K). Apply lem-sp-couple-morphism for the induced maps.
2. The lower bound a permits lemma-weil-pbc-exact-couple-abutment: its half-plane
   bounds give limiting pages, finite filtrations, and the canonical identifications
   of the abutments with H^n(Phi K) and H^n(Psi K). Only q in [a,b] contributes.
3. By lem-sp-page-induction, the E₂ isomorphisms induce isomorphisms on all pages
   and on limiting cycles modulo limiting boundaries. These are the z/tInf squares below.
4. Under the canonical abutment identifications, the graded maps are those same
   infinite-page maps. Apply lem-sp-finite-filtration-induction to each finite
   filtered abutment to obtain the isomorphism on H^n(exchange), for every n.
5. Geometric stalks preserve these isomorphisms; lem-weil-pbc-derived-stalk-conservative
   implies exchange is an isomorphism in D+.
Source: blueprint sec-smooth-base-change/sk-rem-rest, order 1436, proof
(blueprint: sbc-lem-finite-range-comparison). -/
theorem finite_range_exchange_comparison
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (a b : ℤ) (_hab : a ≤ b)
    (_hK : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (_h₂ : ∀ p q : ℤ,
      IsIso (tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q)) :
    (∃ P Q : BigradedExactCouple (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0,
      P.D = D (truncationPhi f g) K ∧
      Q.D = D (truncationPsi g' f') K ∧
      ∃ hPE : P.E = E (truncationPhi f g) K,
      ∃ hQE : Q.E = E (truncationPsi g' f') K,
      HEq P.alpha (alpha (truncationPhi f g) K) ∧
      HEq Q.alpha (alpha (truncationPsi g' f') K) ∧
      HEq P.f (CategoryTheory.TruncationExchange.f (truncationPhi f g) K) ∧
      HEq Q.f (CategoryTheory.TruncationExchange.f (truncationPsi g' f') K) ∧
      HEq P.g (CategoryTheory.TruncationExchange.g (truncationPhi f g) K) ∧
      HEq Q.g (CategoryTheory.TruncationExchange.g (truncationPsi g' f') K) ∧
      ∃ L : LimitSubobjects P, ∃ M : LimitSubobjects Q,
      ∃ z : ∀ p q : ℤ,
        (L.Z p q : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) ⟶
          (M.Z p q : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}),
      ∃ tInf : ∀ p q : ℤ, P.pageInfinity L p q ⟶ Q.pageInfinity M p q,
        (∀ p q : ℤ,
          z p q ≫ (M.Z p q).arrow = (L.Z p q).arrow ≫
            eqToHom (congrFun (congrFun hPE p) q) ≫
            tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
            eqToHom (congrFun (congrFun hQE p) q).symm) ∧
        (∀ p q : ℤ,
          cokernel.π (Subobject.ofLE _ _ (limitBoundary_le_cycle P L p q)) ≫ tInf p q =
            z p q ≫ cokernel.π (Subobject.ofLE _ _ (limitBoundary_le_cycle Q M p q))) ∧
        (∀ p q : ℤ, IsIso (tInf p q))) ∧
    (∀ n : ℤ, IsIso ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K))) ∧
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K) := by
  sorry

end AlgebraicGeometry.Etale
