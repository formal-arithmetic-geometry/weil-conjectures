/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.HypercohomologyFiltrations
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.Filtration
import Sheaf.CategoryTheory.HalfPlaneConvergence
import Sheaf.CategoryTheory.ImageFiltration
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso
import Sheaf.CategoryTheory.TruncationCouple
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Half-plane convergence of the three hypercohomology couples

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1316;
Stacks Project, Tags 0DDE, 015J, 0132, 012W, 0BDV
(blueprint: lemma-weil-pbc-hypercohomology-convergence).

Natural-number
page index `r` in `pageCouple` and the cycle/boundary tower means actual page `r + 2`.
Thus the first available stabilized index is `(max (q-a) (p-1)).toNat`.
-/

@[expose] public section

set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Half-plane convergence for Rf_*.
Source: blueprint order 1316; Stacks Tags 0DDE, 015J, 0132, 012W, 0BDV
(blueprint: lemma-weil-pbc-hypercohomology-convergence).

Proof: (1) For the first and third couples, the truncation and cohomology complex vanish
below a. Right-derived negative vanishing gives D = 0 below a and E = 0 also for p < 0
(lem-weil-pbc-derived-functor-negative-vanishing, lem-sp-shift-identification).
(2) Exact inverse image commutes with cohomology and preserves zero objects, transferring
these bounds to the middle couple (prop-weil-pbc-inverse-image-exact,
lem-weil-pbc-exact-functor-bounded-below).
(3) Every later page and the infinite page are subquotients of E₂, so the quadrant persists.
On p+q=n the support is contained in 0≤p≤n-a, giving the displayed finite cardinal bound.
(4) The outgoing target has q-r+1<a and the incoming source has p-r<0 past the stated
bound. Thus both differentials vanish and the cycles and boundaries stabilize; their
intersection and union give the infinite page (def-sp-exact-couple, def-sp-convergence,
thm-sp-half-plane-convergence).
(5) The half-plane convergence theorem gives regularity, completeness, the diagonal
colimit and the canonical associated-graded comparison. The filtration is whole for p≤0
and zero for p≥n-a+1, hence finite, exhaustive, separated and its quotient system has the
abutment as inverse limit (def-sp-filtration, def-sp-convergence).
(6) The canonical map Hⁿ(Rv τ≤n K) → Hⁿ(Rv K) is an isomorphism by
lem-weil-pbc-derived-functor-truncation-iso. Functoriality identifies the diagonal cocone
maps with hypercohomologyAbutmentMap, so the image filtration is exactly that of
def-weil-pbc-hypercohomology-filtrations. For the middle couple apply exact inverse image
to this identification (lem-weil-pbc-exact-functor-bounded-below). -/
theorem hypercohomology_convergence_first
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Q.obj K.obj ≅ L.obj)
    (hT : ∀ q : ℤ, CategoryTheory.Sheaf.IsTorsion
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (a : ℤ) (ha : ∀ q : ℤ, q < a → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (hterms : ∀ i : ℤ, i < a → IsZero (K.obj.X i)) :
    (∀ p q : ℤ, q < a → IsZero ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).D p q)) ∧
    (∀ (r : ℕ) (p q : ℤ), (p < 0 ∨ q < a) → IsZero (((hypercohomologyCouple
        (hypercohomologyFirstFunctor f) K).pageCouple r).E p q)) ∧
    (∀ (r : ℕ) (n p q : ℤ), p + q = n → ¬ IsZero (((hypercohomologyCouple
        (hypercohomologyFirstFunctor f) K).pageCouple r).E p q) →
      a ≤ q ∧ q ≤ n ∧ 0 ≤ p ∧ p ≤ n - a) ∧
    (∀ (r : ℕ) (n : ℤ),
      Set.Finite {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero (((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).pageCouple r).E pq.1 pq.2)} ∧
      Set.ncard {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero (((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).pageCouple r).E pq.1 pq.2)} ≤
        (n - a + 1).toNat) ∧
    (∀ (r : ℕ) (n p q : ℤ), p + q = n → n < a → IsZero (((hypercohomologyCouple
        (hypercohomologyFirstFunctor f) K).pageCouple r).E p q)) ∧
    (∀ (r : ℕ) (p q : ℤ), max (q - a + 1) p < (r : ℤ) + 2 →
      ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).pageCouple r).d p q = 0 ∧
          ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).pageCouple r).dInto p q = 0) ∧
    (∀ (r : ℕ) (p q : ℤ), max (q - a + 1) p < (r : ℤ) + 2 →
      (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).cycleBoundaryTower.Z r p q =
        (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).cycleBoundaryTower.Z (max (q -
            a) (p - 1)).toNat p q ∧
      (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).cycleBoundaryTower.B r p q =
        (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).cycleBoundaryTower.B (max (q -
            a) (p - 1)).toNat p q) ∧
    (∀ n : ℤ,
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p = ⊤)
        ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p).arrow = 0) ∧
      (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).IsFinite ∧
      (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).IsExhaustive ∧
      (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).IsSeparated ∧
      BigradedExactCouple.IsInverseLimit (hypercohomologyFiltration (hypercohomologyFirstFunctor f)
        K n)) ∧
    (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).IsRegular ∧ (hypercohomologyCouple
        (hypercohomologyFirstFunctor f) K).IsComplete ∧
    ∃ Z : (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).LimitSubobjects, ∃ A : ∀ n :
        ℤ, (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).AlphaColimit n,
      ∃ hA : ∀ n : ℤ, (A n).obj =
        (DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj)),
      (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).ConvergesTo Z A ∧
      (∀ n p : ℤ, (A n).ι p ≫ eqToHom (hA n) =
        eqToHom (congrArg (fun m : ℤ ↦
          (DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
            m).obj
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K (n - p)).obj)))
            (by omega : p + (n - p) = n)) ≫
          hypercohomologyAbutmentMap (hypercohomologyFirstFunctor f) K n (n - p)) ∧
      (∀ n p : ℤ,
        (Subobject.«exists» (eqToHom (hA n))).obj
          (((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).imageFiltration n (A
              n)).step p) =
            (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p) ∧
      (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero ((hypercohomologyCouple (hypercohomologyFirstFunctor f)
          K).pageInfinity Z p q)) ∧
      (∀ p q : ℤ, Nonempty ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).pageInfinity
          Z p q ≅
        ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).pageCouple (max (q - a) (p -
            1)).toNat).E p q)) ∧
      (∀ (r : ℕ) (n p q : ℤ), p + q = n → n - a + 2 ≤ (r : ℤ) + 2 →
        Nonempty (((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).pageCouple r).E p q ≅
            (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).pageInfinity Z p q)) ∧
      (∀ p q : ℤ, Nonempty ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).pageInfinity
          Z p q ≅
        (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K (p + q)).gradedPiece p)) := by
  sorry

/-- Half-plane convergence for g⁻¹Rf_*.
Source: blueprint order 1316; Stacks Tags 0DDE, 015J, 0132, 012W, 0BDV
(blueprint: lemma-weil-pbc-hypercohomology-convergence).

Proof: (1) For the first and third couples, the truncation and cohomology complex vanish
below a. Right-derived negative vanishing gives D = 0 below a and E = 0 also for p < 0
(lem-weil-pbc-derived-functor-negative-vanishing, lem-sp-shift-identification).
(2) Exact inverse image commutes with cohomology and preserves zero objects, transferring
these bounds to the middle couple (prop-weil-pbc-inverse-image-exact,
lem-weil-pbc-exact-functor-bounded-below).
(3) Every later page and the infinite page are subquotients of E₂, so the quadrant persists.
On p+q=n the support is contained in 0≤p≤n-a, giving the displayed finite cardinal bound.
(4) The outgoing target has q-r+1<a and the incoming source has p-r<0 past the stated
bound. Thus both differentials vanish and the cycles and boundaries stabilize; their
intersection and union give the infinite page (def-sp-exact-couple, def-sp-convergence,
thm-sp-half-plane-convergence).
(5) The half-plane convergence theorem gives regularity, completeness, the diagonal
colimit and the canonical associated-graded comparison. The filtration is whole for p≤0
and zero for p≥n-a+1, hence finite, exhaustive, separated and its quotient system has the
abutment as inverse limit (def-sp-filtration, def-sp-convergence).
(6) The canonical map Hⁿ(Rv τ≤n K) → Hⁿ(Rv K) is an isomorphism by
lem-weil-pbc-derived-functor-truncation-iso. Functoriality identifies the diagonal cocone
maps with hypercohomologyAbutmentMap, so the image filtration is exactly that of
def-weil-pbc-hypercohomology-filtrations. For the middle couple apply exact inverse image
to this identification (lem-weil-pbc-exact-functor-bounded-below). -/
theorem hypercohomology_convergence_baseChange
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Q.obj K.obj ≅ L.obj)
    (hT : ∀ q : ℤ, CategoryTheory.Sheaf.IsTorsion
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (a : ℤ) (ha : ∀ q : ℤ, q < a → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (hterms : ∀ i : ℤ, i < a → IsZero (K.obj.X i)) :
    (∀ p q : ℤ, q < a → IsZero ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).D
        p q)) ∧
    (∀ (r : ℕ) (p q : ℤ), (p < 0 ∨ q < a) → IsZero (((hypercohomologyCouple
        (hypercohomologyBaseChangeFunctor f g) K).pageCouple r).E p q)) ∧
    (∀ (r : ℕ) (n p q : ℤ), p + q = n → ¬ IsZero (((hypercohomologyCouple
        (hypercohomologyBaseChangeFunctor f g) K).pageCouple r).E p q) →
      a ≤ q ∧ q ≤ n ∧ 0 ≤ p ∧ p ≤ n - a) ∧
    (∀ (r : ℕ) (n : ℤ),
      Set.Finite {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero (((hypercohomologyCouple
          (hypercohomologyBaseChangeFunctor f g) K).pageCouple r).E pq.1 pq.2)} ∧
      Set.ncard {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero (((hypercohomologyCouple
          (hypercohomologyBaseChangeFunctor f g) K).pageCouple r).E pq.1 pq.2)} ≤
        (n - a + 1).toNat) ∧
    (∀ (r : ℕ) (n p q : ℤ), p + q = n → n < a → IsZero (((hypercohomologyCouple
        (hypercohomologyBaseChangeFunctor f g) K).pageCouple r).E p q)) ∧
    (∀ (r : ℕ) (p q : ℤ), max (q - a + 1) p < (r : ℤ) + 2 →
      ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).pageCouple r).d p q = 0 ∧
          ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).pageCouple r).dInto p
              q = 0) ∧
    (∀ (r : ℕ) (p q : ℤ), max (q - a + 1) p < (r : ℤ) + 2 →
      (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).cycleBoundaryTower.Z r p q =
        (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).cycleBoundaryTower.Z (max
            (q - a) (p - 1)).toNat p q ∧
      (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).cycleBoundaryTower.B r p q =
        (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).cycleBoundaryTower.B (max
            (q - a) (p - 1)).toNat p q) ∧
    (∀ n : ℤ,
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step
        p = ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step p).arrow = 0) ∧
      (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).IsFinite ∧
      (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).IsExhaustive ∧
      (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).IsSeparated ∧
      BigradedExactCouple.IsInverseLimit (hypercohomologyFiltration
        (hypercohomologyBaseChangeFunctor f g) K n)) ∧
    (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).IsRegular ∧
        (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).IsComplete ∧
    ∃ Z : (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).LimitSubobjects, ∃ A :
        ∀ n : ℤ, (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).AlphaColimit n,
      ∃ hA : ∀ n : ℤ, (A n).obj =
        (DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj K.obj)),
      (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).ConvergesTo Z A ∧
      (∀ n p : ℤ, (A n).ι p ≫ eqToHom (hA n) =
        eqToHom (congrArg (fun m : ℤ ↦
          (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
            m).obj
            ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K (n - p)).obj)))
            (by omega : p + (n - p) = n)) ≫
          hypercohomologyAbutmentMap (hypercohomologyBaseChangeFunctor f g) K n (n - p)) ∧
      (∀ n p : ℤ,
        (Subobject.«exists» (eqToHom (hA n))).obj
          (((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).imageFiltration n (A
              n)).step p) =
            (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step p) ∧
      (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero ((hypercohomologyCouple
          (hypercohomologyBaseChangeFunctor f g) K).pageInfinity Z p q)) ∧
      (∀ p q : ℤ, Nonempty ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g)
          K).pageInfinity Z p q ≅
        ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).pageCouple (max (q - a)
            (p - 1)).toNat).E p q)) ∧
      (∀ (r : ℕ) (n p q : ℤ), p + q = n → n - a + 2 ≤ (r : ℤ) + 2 →
        Nonempty (((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).pageCouple
            r).E p q ≅ (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g)
                K).pageInfinity Z p q)) ∧
      (∀ p q : ℤ, Nonempty ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g)
          K).pageInfinity Z p q ≅
        (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K (p + q)).gradedPiece p))
          := by
  sorry

/-- Half-plane convergence for Rf′_*(g′)⁻¹.
Source: blueprint order 1316; Stacks Tags 0DDE, 015J, 0132, 012W, 0BDV
(blueprint: lemma-weil-pbc-hypercohomology-convergence).

Proof: (1) For the first and third couples, the truncation and cohomology complex vanish
below a. Right-derived negative vanishing gives D = 0 below a and E = 0 also for p < 0
(lem-weil-pbc-derived-functor-negative-vanishing, lem-sp-shift-identification).
(2) Exact inverse image commutes with cohomology and preserves zero objects, transferring
these bounds to the middle couple (prop-weil-pbc-inverse-image-exact,
lem-weil-pbc-exact-functor-bounded-below).
(3) Every later page and the infinite page are subquotients of E₂, so the quadrant persists.
On p+q=n the support is contained in 0≤p≤n-a, giving the displayed finite cardinal bound.
(4) The outgoing target has q-r+1<a and the incoming source has p-r<0 past the stated
bound. Thus both differentials vanish and the cycles and boundaries stabilize; their
intersection and union give the infinite page (def-sp-exact-couple, def-sp-convergence,
thm-sp-half-plane-convergence).
(5) The half-plane convergence theorem gives regularity, completeness, the diagonal
colimit and the canonical associated-graded comparison. The filtration is whole for p≤0
and zero for p≥n-a+1, hence finite, exhaustive, separated and its quotient system has the
abutment as inverse limit (def-sp-filtration, def-sp-convergence).
(6) The canonical map Hⁿ(Rv τ≤n K) → Hⁿ(Rv K) is an isomorphism by
lem-weil-pbc-derived-functor-truncation-iso. Functoriality identifies the diagonal cocone
maps with hypercohomologyAbutmentMap, so the image filtration is exactly that of
def-weil-pbc-hypercohomology-filtrations. For the middle couple apply exact inverse image
to this identification (lem-weil-pbc-exact-functor-bounded-below). -/
theorem hypercohomology_convergence_second
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Q.obj K.obj ≅ L.obj)
    (hT : ∀ q : ℤ, CategoryTheory.Sheaf.IsTorsion
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (a : ℤ) (ha : ∀ q : ℤ, q < a → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (hterms : ∀ i : ℤ, i < a → IsZero (K.obj.X i)) :
    (∀ p q : ℤ, q < a → IsZero ((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).D p
        q)) ∧
    (∀ (r : ℕ) (p q : ℤ), (p < 0 ∨ q < a) → IsZero (((hypercohomologyCouple
        (hypercohomologySecondFunctor f' g') K).pageCouple r).E p q)) ∧
    (∀ (r : ℕ) (n p q : ℤ), p + q = n → ¬ IsZero (((hypercohomologyCouple
        (hypercohomologySecondFunctor f' g') K).pageCouple r).E p q) →
      a ≤ q ∧ q ≤ n ∧ 0 ≤ p ∧ p ≤ n - a) ∧
    (∀ (r : ℕ) (n : ℤ),
      Set.Finite {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero (((hypercohomologyCouple
          (hypercohomologySecondFunctor f' g') K).pageCouple r).E pq.1 pq.2)} ∧
      Set.ncard {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero (((hypercohomologyCouple
          (hypercohomologySecondFunctor f' g') K).pageCouple r).E pq.1 pq.2)} ≤
        (n - a + 1).toNat) ∧
    (∀ (r : ℕ) (n p q : ℤ), p + q = n → n < a → IsZero (((hypercohomologyCouple
        (hypercohomologySecondFunctor f' g') K).pageCouple r).E p q)) ∧
    (∀ (r : ℕ) (p q : ℤ), max (q - a + 1) p < (r : ℤ) + 2 →
      ((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).pageCouple r).d p q = 0 ∧
          ((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).pageCouple r).dInto p q
              = 0) ∧
    (∀ (r : ℕ) (p q : ℤ), max (q - a + 1) p < (r : ℤ) + 2 →
      (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).cycleBoundaryTower.Z r p q =
        (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).cycleBoundaryTower.Z (max
            (q - a) (p - 1)).toNat p q ∧
      (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).cycleBoundaryTower.B r p q =
        (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).cycleBoundaryTower.B (max
            (q - a) (p - 1)).toNat p q) ∧
    (∀ n : ℤ,
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step p
        = ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step p).arrow = 0) ∧
      (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).IsFinite ∧
      (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).IsExhaustive ∧
      (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).IsSeparated ∧
      BigradedExactCouple.IsInverseLimit (hypercohomologyFiltration (hypercohomologySecondFunctor f'
        g') K n)) ∧
    (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).IsRegular ∧
        (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).IsComplete ∧
    ∃ Z : (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).LimitSubobjects, ∃ A : ∀
        n : ℤ, (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).AlphaColimit n,
      ∃ hA : ∀ n : ℤ, (A n).obj =
        (DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj K.obj)),
      (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).ConvergesTo Z A ∧
      (∀ n p : ℤ, (A n).ι p ≫ eqToHom (hA n) =
        eqToHom (congrArg (fun m : ℤ ↦
          (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
            m).obj
            ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K (n - p)).obj)))
            (by omega : p + (n - p) = n)) ≫
          hypercohomologyAbutmentMap (hypercohomologySecondFunctor f' g') K n (n - p)) ∧
      (∀ n p : ℤ,
        (Subobject.«exists» (eqToHom (hA n))).obj
          (((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).imageFiltration n (A
              n)).step p) =
            (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step p) ∧
      (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero ((hypercohomologyCouple (hypercohomologySecondFunctor
          f' g') K).pageInfinity Z p q)) ∧
      (∀ p q : ℤ, Nonempty ((hypercohomologyCouple (hypercohomologySecondFunctor f' g')
          K).pageInfinity Z p q ≅
        ((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).pageCouple (max (q - a) (p
            - 1)).toNat).E p q)) ∧
      (∀ (r : ℕ) (n p q : ℤ), p + q = n → n - a + 2 ≤ (r : ℤ) + 2 →
        Nonempty (((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).pageCouple r).E
            p q ≅ (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).pageInfinity Z p
                q)) ∧
      (∀ p q : ℤ, Nonempty ((hypercohomologyCouple (hypercohomologySecondFunctor f' g')
          K).pageInfinity Z p q ≅
        (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K (p + q)).gradedPiece p))
          := by
  sorry

end AlgebraicGeometry.Etale
