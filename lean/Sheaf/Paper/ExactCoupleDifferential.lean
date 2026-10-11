/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.TruncationExchangeCouple
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Compatibility of the exact-couple differential

Source: Stacks Project, Etale Cohomology, Tag 0DDE, proof; Homology, Tags 011Q–011S;
blueprint sec-proper-base-change/sk-thm-properbasechange.
(blueprint: lem-weil-pbc-exact-couple-differential)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale
open CategoryTheory.TruncationExchange

/-- The exchanged truncation couples are exact, their exchange maps commute with the
connecting maps and every page differential, and their E₂ map is degree-p exchange.

Proof:
1. Apply exact inverse image to the truncation couple of K for the first couple.
   For the second, exact inverse image commutes with canonical truncation and cohomology,
   so it is the truncation couple of g' inverse image of K. Both are exact by
   lem-sp-truncation-couple-exact and lem-weil-pbc-exact-functor-bounded-below.
2. Apply lem-weil-pbc-derived-exchange-triangulated to each truncation triangle.
   Naturality gives the inclusion and projection squares; compatibility with the
   composite shift isomorphisms gives the connecting-arrow square.
3. Apply H^{p+q} to these three squares. The cohomology shift identification converts
   the third into the displayed square at (p+2,q-1). Thus tD and tE form a couple morphism
   in the convention of def-sp-exact-couple.
4. Use lem-sp-couple-morphism: differential commutation preserves kernels and boundaries,
   so tE induces the quotient map on the derived E term. Repeat on derived couples;
   this gives the maps on all pages, commuting with each differential. Page n here is
   the actual page n+2. The kernel/quotient squares specify the induced successor maps.
5. At E₂ the map is H^{p+q}(Ex on H^q(K)[-q]). Apply shift compatibility for -q and
   H^{p+q}(N[-q]) = H^p(N). Through pageIso, truncationSourceIso and truncationTargetIso,
   it is H^p(Ex on H^q(K)), as asserted; exact inverse image identifies the source with
   g inverse image of R^p f_* H^q(K).
Source: Stacks Project, Tag 0DDE, proof; Tags 011Q, 011R and 011S.
(blueprint: lem-weil-pbc-exact-couple-differential).
-/
theorem exact_couple_differential
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (a : ℤ)
    (_hT : ∀ q : ℤ, ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K).IsTorsion)
    (_hbelow : ∀ q : ℤ, q < a →
      IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∃ P Q : BigradedExactCouple (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0,
    ∃ hPE : P.E = E (truncationPhi f g) K,
    ∃ hQE : Q.E = E (truncationPsi g' f') K,
      P.D = D (truncationPhi f g) K ∧ Q.D = D (truncationPsi g' f') K ∧
      HEq P.alpha (alpha (truncationPhi f g) K) ∧
      HEq Q.alpha (alpha (truncationPsi g' f') K) ∧
      HEq P.f (CategoryTheory.TruncationExchange.f (truncationPhi f g) K) ∧
      HEq Q.f (CategoryTheory.TruncationExchange.f (truncationPsi g' f') K) ∧
      HEq P.g (CategoryTheory.TruncationExchange.g (truncationPhi f g) K) ∧
      HEq Q.g (CategoryTheory.TruncationExchange.g (truncationPsi g' f') K) ∧
    (∀ p q : ℤ,
      alpha (truncationPhi f g) K p q ≫
          tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq)
            K (p - 1) (q + 1) =
        tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          alpha (truncationPsi g' f') K p q) ∧
    (∀ p q : ℤ,
      CategoryTheory.TruncationExchange.g (truncationPhi f g) K p q ≫
          tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q =
        tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          CategoryTheory.TruncationExchange.g (truncationPsi g' f') K p q) ∧
    (∀ p q : ℤ,
      CategoryTheory.TruncationExchange.f (truncationPhi f g) K p q ≫
          tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq)
            K (p + 2) (q - 1) =
        tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          CategoryTheory.TruncationExchange.f (truncationPsi g' f') K p q) ∧
    (∃ t : ∀ (n : ℕ) (p q : ℤ), (P.pageCouple n).E p q ⟶ (Q.pageCouple n).E p q,
      (∀ p q : ℤ, t 0 p q =
        eqToHom (congrFun (congrFun hPE p) q) ≫
          tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          eqToHom (congrFun (congrFun hQE p) q).symm) ∧
      (∀ (n : ℕ) (p q : ℤ),
        (P.pageCouple n).d p q ≫ t n (p + 2 + n) (q - 1 - n) =
          t n p q ≫ (Q.pageCouple n).d p q) ∧
      (∀ (n : ℕ) (p q : ℤ),
        ∃ k : kernel ((P.pageCouple n).d p q) ⟶ kernel ((Q.pageCouple n).d p q),
          k ≫ kernel.ι ((Q.pageCouple n).d p q) =
            kernel.ι ((P.pageCouple n).d p q) ≫ t n p q ∧
          (P.pageCouple n).derivedEProjection p q ≫ t (n + 1) p q =
            k ≫ (Q.pageCouple n).derivedEProjection p q)) ∧
    (∀ p q : ℤ,
      tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          (pageIso (truncationPsi g' f') K p q ≪≫
            truncationTargetIso g' f'
              ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom =
        (pageIso (truncationPhi f g) K p q ≪≫
          truncationSourceIso f g
            ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom ≫
        (truncationSourceIso f g
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).inv ≫
        (_root_.DerivedCategory.Plus.homologyFunctor
          (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).map
            ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app (sheaf K q)) ≫
        (truncationTargetIso g' f'
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom) := by
  sorry

end AlgebraicGeometry.Etale
