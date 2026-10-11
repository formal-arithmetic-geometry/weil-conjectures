/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.TruncationExchangeCouple
public import Sheaf.CategoryTheory.ExactCoupleMorphism
public import Sheaf.CategoryTheory.ImageFiltration

/-!
# The abutment of the truncation exchange couples

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
lemma-weil-pbc-exact-couple-abutment, Detailed form; Stacks Tags 0DDE and 05TC
(blueprint: lemma-weil-pbc-exact-couple-abutment).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.TruncationExchange
open CategoryTheory.BigradedExactCouple

namespace AlgebraicGeometry.Etale

/-- The two truncation couples converge with finite image filtrations, their canonical
abutments identify with the cohomology of the whole complexes, and their induced map is
cohomology of exchange, including on associated graded objects.
The parameters P and Q, with the ten data identifications, specify the two exact couples
of def-weil-pbc-truncation-exact-couples; they impose no additional geometric hypothesis.

Proof, Step 1: For q < a, upper truncation and the q-th layer vanish. Negative derived
functor vanishing (lem-weil-pbc-derived-functor-negative-vanishing) and exact inverse
image (lem-weil-pbc-exact-functor-bounded-below) give E = 0 for p < 0. Apply
thm-sp-half-plane-convergence to obtain canonical diagonal colimits, finite exhaustive
separated filtrations, and the canonical infinite-page comparisons.
Step 2: The canonical truncation inclusion is a cohomology isomorphism through n and
mono in degree n+1. Apply lem-weil-pbc-derived-functor-truncation-iso, and commute exact
inverse image with cohomology, to get the two canonical abutment isomorphisms.
Step 3: Composing the diagonal cocone maps with these isomorphisms gives the maps from
truncation at n-p into K. Their images are precisely the transported image filtrations
(def-sp-image-filtration). Naturality of cohomology/inverse-image comparison and exact
preservation of images identify the first filtration with g inverse image of the
filtration on H^n(Rf_*K) (def-weil-pbc-hypercohomology-filtrations).
Step 4: Naturality of derived exchange at truncLEι gives the displayed abutment square.
Step 5: Apply lem-sp-couple-morphism to the exchange morphism of couples. It preserves
filtrations and induces the quotient map on limiting cycles modulo boundaries.
Transport its canonical graded comparison square along the abutment isomorphisms;
the induced graded map is characterized by the cokernel square for the step maps.
Source: blueprint lemma-weil-pbc-exact-couple-abutment, Detailed form, Proof;
Stacks Tags 0DDE, 05TC and 011Q
(blueprint: lemma-weil-pbc-exact-couple-abutment). -/
theorem truncation_exchange_exact_couple_abutment
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (a n : ℤ)
    (hK : ∀ q : ℤ, q < a → IsZero
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (P Q : BigradedExactCouple (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0)
    (hPD : P.D = D (truncationPhi f g) K)
    (hPE : P.E = E (truncationPhi f g) K)
    (_hPalpha : HEq P.alpha (alpha (truncationPhi f g) K))
    (_hPf : HEq P.f (CategoryTheory.TruncationExchange.f (truncationPhi f g) K))
    (_hPg : HEq P.g (CategoryTheory.TruncationExchange.g (truncationPhi f g) K))
    (hQD : Q.D = D (truncationPsi g' f') K)
    (hQE : Q.E = E (truncationPsi g' f') K)
    (_hQalpha : HEq Q.alpha (alpha (truncationPsi g' f') K))
    (_hQf : HEq Q.f (CategoryTheory.TruncationExchange.f (truncationPsi g' f') K))
    (_hQg : HEq Q.g (CategoryTheory.TruncationExchange.g (truncationPsi g' f') K)) :
    (∀ p q : ℤ, q < a → IsZero (P.D p q)) ∧
    (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (P.E p q)) ∧
    (∀ p q : ℤ, q < a → IsZero (Q.D p q)) ∧
    (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (Q.E p q)) ∧
    ∃ L : LimitSubobjects P, ∃ M : LimitSubobjects Q,
    ∃ A : ∀ m : ℤ, AlphaColimit P m, ∃ B : ∀ m : ℤ, AlphaColimit Q m,
    ∃ hA : ∀ m : ℤ, (A m).obj = P.D 0 m,
    ∃ hB : ∀ m : ℤ, (B m).obj = Q.D 0 m,
      (∀ m : ℤ, (A m).ι 0 ≫ eqToHom (hA m) = eqToHom (by congr 1; omega)) ∧
      (∀ m : ℤ, (B m).ι 0 ≫ eqToHom (hB m) = eqToHom (by congr 1; omega)) ∧
      P.ConvergesTo L A ∧ Q.ConvergesTo M B ∧
      (∀ m : ℤ, (P.imageFiltration m (A m)).IsFinite ∧
        (P.imageFiltration m (A m)).IsExhaustive ∧
        (P.imageFiltration m (A m)).IsSeparated) ∧
      (∀ m : ℤ, (Q.imageFiltration m (B m)).IsFinite ∧
        (Q.imageFiltration m (B m)).IsExhaustive ∧
        (Q.imageFiltration m (B m)).IsSeparated) ∧
      (∀ p q : ℤ, ∃ e : P.pageInfinity L p q ≅
        (P.imageFiltration (p + q) (A (p + q))).gradedPiece p,
        P.toPageInfinity L p q ≫ e.hom = P.toGradedPiece A p q) ∧
      (∀ p q : ℤ, ∃ e : Q.pageInfinity M p q ≅
        (Q.imageFiltration (p + q) (B (p + q))).gradedPiece p,
        Q.toPageInfinity M p q ≫ e.hom = Q.toGradedPiece B p q) ∧
      ∃ i : (A n).obj ≅ (_root_.DerivedCategory.Plus.homologyFunctor _ n).obj ((truncationPhi f
        g).obj K),
      ∃ j : (B n).obj ≅ (_root_.DerivedCategory.Plus.homologyFunctor _ n).obj ((truncationPsi g'
        f').obj K),
      HEq i.hom ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map ((truncationPhi f g).map
        ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n)).app K))) ∧
      HEq j.hom ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map ((truncationPsi g' f').map
        ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n)).app K))) ∧
      ∃ U : DecreasingFiltration ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj
        ((truncationPhi f g).obj K)),
      ∃ V : DecreasingFiltration ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj
        ((truncationPsi g' f').obj K)),
      U = (P.imageFiltration n (A n)).image i.hom ∧
      V = (Q.imageFiltration n (B n)).image j.hom ∧
      (∀ p : ℤ, U.step p = imageSubobject ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
        ((truncationPhi f g).map ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n - p)).app
        K)))) ∧
      (∀ p : ℤ, V.step p = imageSubobject ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
        ((truncationPsi g' f').map ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n -
        p)).app K)))) ∧
      (∀ p : ℤ, (Subobject.«exists» (((upperStar AddCommGrpCat.{u + 1}
        g).mapDerivedCategoryPlusHomologyFunctorIso n).symm.app ((lowerStar AddCommGrpCat.{u + 1}
        f).rightDerivedFunctorPlus.obj K)).hom).obj (U.step p) =
        imageSubobject ((upperStar AddCommGrpCat.{u + 1} g).map
          (imageSubobject ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map ((lowerStar
            AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.map
            ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n - p)).app K)))).arrow)) ∧
      ∃ t : P.D 0 n ⟶ Q.D 0 n, HEq t (tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        sq.toCommSq) K 0 n) ∧
      eqToHom (hA n) ≫ t ≫ eqToHom (hB n).symm ≫ j.hom =
        i.hom ≫ (_root_.DerivedCategory.Plus.homologyFunctor _ n).map ((derivedBaseChangeMapPlus
          AddCommGrpCat.{u + 1} sq.toCommSq).app K) ∧
      ∃ lift : ∀ p : ℤ, (U.step p : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) ⟶ (V.step p
        : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ p : ℤ, lift p ≫ (V.step p).arrow =
        (U.step p).arrow ≫ (_root_.DerivedCategory.Plus.homologyFunctor _ n).map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)) ∧
      ∃ gr : ∀ p : ℤ, U.gradedPiece p ⟶ V.gradedPiece p,
      (∀ p : ℤ,
        cokernel.π (Subobject.ofLE _ _ (U.antitone_step (by omega : p ≤ p + 1))) ≫
          gr p = lift p ≫
            cokernel.π (Subobject.ofLE _ _ (V.antitone_step (by omega : p ≤ p + 1)))) ∧
      ∃ z : ∀ p : ℤ, (L.Z p (n - p) : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) ⟶ (M.Z p
        (n - p) : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}),
      ∃ tInf : ∀ p : ℤ, P.pageInfinity L p (n - p) ⟶ Q.pageInfinity M p (n - p),
      (∀ p : ℤ, HEq (z p ≫ (M.Z p (n - p)).arrow)
        ((L.Z p (n - p)).arrow ≫
          eqToHom (congrFun (congrFun hPE p) (n - p)) ≫
          tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p (n - p))) ∧
      (∀ p : ℤ,
        cokernel.π (Subobject.ofLE _ _ (limitBoundary_le_cycle P L p (n - p))) ≫
          tInf p = z p ≫
            cokernel.π (Subobject.ofLE _ _ (limitBoundary_le_cycle Q M p (n - p)))) ∧
      ∃ e : ∀ p : ℤ, P.pageInfinity L p (n - p) ≅ U.gradedPiece p,
      ∃ e' : ∀ p : ℤ, Q.pageInfinity M p (n - p) ≅ V.gradedPiece p,
      ∃ hU : ∀ p : ℤ, U.step p = imageSubobject ((A n).ι p ≫ i.hom),
      ∃ hV : ∀ p : ℤ, V.step p = imageSubobject ((B n).ι p ≫ j.hom),
      (∀ p : ℤ, P.toPageInfinity L p (n - p) ≫ (e p).hom =
        factorThruImageSubobject ((A n).ι p ≫ i.hom) ≫
        eqToHom (congrArg (fun S : Subobject _ ↦ (S : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u
          + 1})) (hU p).symm) ≫
        cokernel.π (Subobject.ofLE _ _ (U.antitone_step (by omega : p ≤ p + 1)))) ∧
      (∀ p : ℤ, Q.toPageInfinity M p (n - p) ≫ (e' p).hom =
        factorThruImageSubobject ((B n).ι p ≫ j.hom) ≫
        eqToHom (congrArg (fun S : Subobject _ ↦ (S : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u
          + 1})) (hV p).symm) ≫
        cokernel.π (Subobject.ofLE _ _ (V.antitone_step (by omega : p ≤ p + 1)))) ∧
      (∀ p : ℤ, (e p).hom ≫ gr p = tInf p ≫ (e' p).hom) := by
  sorry

end AlgebraicGeometry.Etale
