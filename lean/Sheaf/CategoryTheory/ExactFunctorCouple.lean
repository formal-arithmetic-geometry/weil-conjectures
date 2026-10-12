/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.CategoryTheory.HalfPlaneConvergence
import Sheaf.CategoryTheory.DerivedCoupleExact
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.ExactCoupleMorphism
import Sheaf.CategoryTheory.Filtration

/-!
# Exact functors transport exact couples

Source: Stacks Project, Homology, Section 12.21, Tags 011Q, 011R, 011S, 0AMJ,
and the transport argument of the blueprint (blueprint: lem-sp-exact-functor-couple).
The index `r` denotes the actual page `r + 2`. Object equalities identify the initial
mapped datum; subsequent identifications of subobjects are commuting isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

/-- An exact additive functor transports an exact couple, all its derived pages, and
its half-plane abutment filtration, with the canonical cohomology comparisons.
Source: Stacks Project, Tags 011Q, 011R, 011S, 0AMJ, and the blueprint transport argument
(blueprint: lem-sp-exact-functor-couple).

Proof, step 1: exactness preserves the three image/kernel equalities and additivity
preserves the zero composites (def-sp-exact-couple, lem-sp-exact-functor-preserves-homology).
Step 2: one derived step commutes with the functor. The D term is an image and the E
term is cycles modulo boundaries. Preservation of images, kernels and cokernels gives
the comparisons. The defining restriction equations characterize alpha, f and g by
cancelling mono inclusions and epi projections (lem-sp-derived-couple-exact).
Step 3: induct on the derived-page index. The induced maps on cohomology give the next
E comparison; the image inclusions give the D comparison. All three structure maps
commute, hence so do differentials (lem-sp-couple-morphism).
Step 4: preservation of zero objects carries the half-plane vanishing conditions to
the image couple. The stabilization bound is unchanged; quotient comparisons commute
with the stabilization maps, giving the infinite-page comparison (thm-sp-half-plane-convergence).
Step 5: the abutment is D at (0,n). Exactness carries the images of all alpha powers
to their images, so each filtration step and its successive quotient are preserved
(def-sp-filtration, lem-sp-exact-functor-preserves-homology).
Step 6: at a sufficiently large page, transport the filtration along the inverse alpha
isomorphism to its D term. The induced g map identifies its quotient with E. Applying
the functor to this quotient equation and cancelling the epimorphic quotient map proves
the final graded-piece square (thm-sp-half-plane-convergence, def-sp-convergence). -/
theorem exactFunctor_couple
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (X : BigradedExactCouple C 0) :
    ∃ Y : BigradedExactCouple B 0,
    ∃ hD : ∀ p q : ℤ, Φ.obj (X.D p q) = Y.D p q,
    ∃ hE : ∀ p q : ℤ, Φ.obj (X.E p q) = Y.E p q,
    (∀ p q : ℤ, Φ.map (X.alpha p q) ≫ eqToHom (hD (p - 1) (q + 1)) =
      eqToHom (hD p q) ≫ Y.alpha p q) ∧
    (∀ p q : ℤ, Φ.map (X.f p q) ≫ eqToHom (hD (p + 2) (q - 1)) =
      eqToHom (hE p q) ≫ Y.f p q) ∧
    (∀ p q : ℤ, Φ.map (X.g p q) ≫ eqToHom (hE (p + 0) (q - 0)) =
      eqToHom (hD p q) ≫ Y.g p q) ∧
    ∃ δ : ∀ (r : ℕ) (p q : ℤ),
      Φ.obj ((X.pageCouple r).D p q) ≅ (Y.pageCouple r).D p q,
    ∃ φ : ∀ (r : ℕ) (p q : ℤ),
      Φ.obj ((X.pageCouple r).E p q) ≅ (Y.pageCouple r).E p q,
    ∃ iX : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q,
    ∃ iY : ∀ (r : ℕ) (p q : ℤ), (Y.pageCouple r).D p q ⟶ Y.D p q,
    (∀ p q : ℤ, δ 0 p q = eqToIso (hD p q) ∧ φ 0 p q = eqToIso (hE p q)) ∧
    (∀ p q : ℤ, iX 0 p q = 𝟙 _ ∧ iY 0 p q = 𝟙 _) ∧
    (∀ (r : ℕ) (p q : ℤ),
      iX (r + 1) p q = (X.pageCouple r).derivedDInclusion p q ≫ iX r p q ∧
      iY (r + 1) p q = (Y.pageCouple r).derivedDInclusion p q ≫ iY r p q) ∧
    (∀ (r : ℕ) (p q : ℤ), Mono (iX r p q) ∧ Mono (iY r p q) ∧
      (δ r p q).hom ≫ iY r p q = Φ.map (iX r p q) ≫ eqToHom (hD p q)) ∧
    (∀ (r : ℕ) (p q : ℤ),
      Φ.map ((X.pageCouple r).alpha p q) ≫ (δ r (p - 1) (q + 1)).hom =
        (δ r p q).hom ≫ (Y.pageCouple r).alpha p q) ∧
    (∀ (r : ℕ) (p q : ℤ),
      Φ.map ((X.pageCouple r).f p q) ≫ (δ r (p + 2) (q - 1)).hom =
        (φ r p q).hom ≫ (Y.pageCouple r).f p q) ∧
    (∀ (r : ℕ) (p q : ℤ),
      Φ.map ((X.pageCouple r).g p q) ≫ (φ r (p + r) (q - r)).hom =
        (δ r p q).hom ≫ (Y.pageCouple r).g p q) ∧
    (∀ (r : ℕ) (p q : ℤ),
      Φ.map ((X.pageCouple r).d p q) ≫ (φ r (p + 2 + r) (q - 1 - r)).hom =
        (φ r p q).hom ≫ (Y.pageCouple r).d p q) ∧
    (∀ (r : ℕ) (p q : ℤ),
      ∃ k : Φ.obj (kernel ((X.pageCouple r).d p q)) ⟶
        kernel ((Y.pageCouple r).d p q),
      IsIso k ∧
      k ≫ kernel.ι ((Y.pageCouple r).d p q) =
        Φ.map (kernel.ι ((X.pageCouple r).d p q)) ≫ (φ r p q).hom ∧
      Φ.map ((X.pageCouple r).derivedEProjection p q) ≫ (φ (r + 1) p q).hom =
        k ≫ (Y.pageCouple r).derivedEProjection p q) ∧
    (∀ (a : ℤ)
      (_ : ∀ p q : ℤ, q < a → IsZero (X.D p q))
      (_ : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q)),
      (∀ p q : ℤ, q < a → IsZero (Y.D p q)) ∧
      (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (Y.E p q)) ∧
      ∃ LX : LimitSubobjects X, ∃ LY : LimitSubobjects Y,
      ∃ AX : ∀ n : ℤ, AlphaColimit X n, ∃ AY : ∀ n : ℤ, AlphaColimit Y n,
      ∃ hAX : ∀ n : ℤ, (AX n).obj = X.D 0 n,
      ∃ hAY : ∀ n : ℤ, (AY n).obj = Y.D 0 n,
      ∃ eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj,
      (∀ n : ℤ, (AX n).ι 0 ≫ eqToHom (hAX n) =
        eqToHom (by congr 1; omega)) ∧
      (∀ n : ℤ, (AY n).ι 0 ≫ eqToHom (hAY n) =
        eqToHom (by congr 1; omega)) ∧
      (∀ n p : ℤ, Φ.map ((AX n).ι p) ≫ (eA n).hom =
        eqToHom (hD p (n - p)) ≫ (AY n).ι p) ∧
      (∀ n p : ℤ, p ≤ 0 →
        (X.imageFiltration n (AX n)).step p = ⊤ ∧
        (Y.imageFiltration n (AY n)).step p = ⊤) ∧
      (∀ n : ℤ, (X.imageFiltration n (AX n)).IsFinite ∧
        (Y.imageFiltration n (AY n)).IsFinite) ∧
      X.ConvergesTo LX AX ∧ Y.ConvergesTo LY AY ∧
      ∃ τ : ∀ n p : ℤ,
        Φ.obj ((X.imageFiltration n (AX n)).step p : C) ≅
          ((Y.imageFiltration n (AY n)).step p : B),
      ∃ κ : ∀ n p : ℤ,
        Φ.obj ((X.imageFiltration n (AX n)).gradedPiece p) ≅
          (Y.imageFiltration n (AY n)).gradedPiece p,
      (∀ n p : ℤ,
        (τ n p).hom ≫ ((Y.imageFiltration n (AY n)).step p).arrow =
          Φ.map (((X.imageFiltration n (AX n)).step p).arrow) ≫ (eA n).hom) ∧
      (∀ n p : ℤ,
        Φ.map (cokernel.π (Subobject.ofLE
          ((X.imageFiltration n (AX n)).step (p + 1))
          ((X.imageFiltration n (AX n)).step p)
          ((X.imageFiltration n (AX n)).antitone_step (by omega)))) ≫ (κ n p).hom =
        (τ n p).hom ≫ cokernel.π (Subobject.ofLE
          ((Y.imageFiltration n (AY n)).step (p + 1))
          ((Y.imageFiltration n (AY n)).step p)
          ((Y.imageFiltration n (AY n)).antitone_step (by omega)))) ∧
      (∀ (r : ℕ) (p q : ℤ), (r : ℤ) + 2 > max (q - a + 1) p →
        ∃ sX : (X.pageCouple r).E p q ≅ (X.pageCouple (r + 1)).E p q,
        ∃ sY : (Y.pageCouple r).E p q ≅ (Y.pageCouple (r + 1)).E p q,
        kernel.ι ((X.pageCouple r).d p q) ≫ sX.hom =
          (X.pageCouple r).derivedEProjection p q ∧
        kernel.ι ((Y.pageCouple r).d p q) ≫ sY.hom =
          (Y.pageCouple r).derivedEProjection p q ∧
        Φ.map sX.hom ≫ (φ (r + 1) p q).hom = (φ r p q).hom ≫ sY.hom) ∧
      (∃ φInfinity : ∀ p q : ℤ, Φ.obj (X.pageInfinity LX p q) ≅ Y.pageInfinity LY p q,
        (∀ p q : ℤ, Φ.map (X.toPageInfinity LX p q) ≫ (φInfinity p q).hom =
          eqToHom (hD p q) ≫ Y.toPageInfinity LY p q) ∧
        (∀ (r : ℕ) (p q : ℤ), (r : ℤ) + 2 > max (q - a + 1) p →
          ∃ hZX : X.cycleBoundaryTower.Z r p q = LX.Z p q,
          ∃ hZY : Y.cycleBoundaryTower.Z r p q = LY.Z p q,
          ∃ eX : (X.pageCouple r).E p q ≅ X.pageInfinity LX p q,
          ∃ eY : (Y.pageCouple r).E p q ≅ Y.pageInfinity LY p q,
          X.cycleBoundaryTower.projection r p q ≫ eX.hom =
            eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : C)) hZX) ≫
              cokernel.π (Subobject.ofLE (LX.B p q) (LX.Z p q)
                (limitBoundary_le_cycle X LX p q)) ∧
          Y.cycleBoundaryTower.projection r p q ≫ eY.hom =
            eqToHom (congrArg (fun S : Subobject (Y.E p q) ↦ (S : B)) hZY) ≫
              cokernel.π (Subobject.ofLE (LY.B p q) (LY.Z p q)
                (limitBoundary_le_cycle Y LY p q)) ∧
          Φ.map eX.hom ≫ (φInfinity p q).hom = (φ r p q).hom ≫ eY.hom) ∧
        ∀ p q : ℤ,
          ∃ ξX : X.pageInfinity LX p q ≅
            (X.imageFiltration (p + q) (AX (p + q))).gradedPiece p,
          ∃ ξY : Y.pageInfinity LY p q ≅
            (Y.imageFiltration (p + q) (AY (p + q))).gradedPiece p,
          X.toPageInfinity LX p q ≫ ξX.hom = X.toGradedPiece AX p q ∧
          Y.toPageInfinity LY p q ≫ ξY.hom = Y.toGradedPiece AY p q ∧
          Φ.map ξX.hom ≫ (κ (p + q) p).hom = (φInfinity p q).hom ≫ ξY.hom) ∧
      (∀ (r : ℕ) (p q : ℤ),
        (r : ℤ) + 2 ≥ max (p + 3) (q - a + 2) →
        ∃ lambdaX : (AX (p + q)).obj ≅ X.D (p - r) (q + r),
        ∃ lambdaY : (AY (p + q)).obj ≅ Y.D (p - r) (q + r),
        ∃ tX : ((X.imageFiltration (p + q) (AX (p + q))).step p : C) ≅
          (X.pageCouple r).D (p - r) (q + r),
        ∃ tY : ((Y.imageFiltration (p + q) (AY (p + q))).step p : B) ≅
          (Y.pageCouple r).D (p - r) (q + r),
        ∃ ψX : (X.imageFiltration (p + q) (AX (p + q))).gradedPiece p ≅
          (X.pageCouple r).E p q,
        ∃ ψY : (Y.imageFiltration (p + q) (AY (p + q))).gradedPiece p ≅
          (Y.pageCouple r).E p q,
        lambdaX.inv = eqToHom (by congr 1; omega) ≫ (AX (p + q)).ι (p - r) ∧
        lambdaY.inv = eqToHom (by congr 1; omega) ≫ (AY (p + q)).ι (p - r) ∧
        tX.hom ≫ iX r (p - r) (q + r) =
          ((X.imageFiltration (p + q) (AX (p + q))).step p).arrow ≫ lambdaX.hom ∧
        tY.hom ≫ iY r (p - r) (q + r) =
          ((Y.imageFiltration (p + q) (AY (p + q))).step p).arrow ≫ lambdaY.hom ∧
        cokernel.π (Subobject.ofLE
          ((X.imageFiltration (p + q) (AX (p + q))).step (p + 1))
          ((X.imageFiltration (p + q) (AX (p + q))).step p)
          ((X.imageFiltration (p + q) (AX (p + q))).antitone_step (by omega))) ≫
          ψX.hom = tX.hom ≫ (X.pageCouple r).g (p - r) (q + r) ≫
            eqToHom (by congr 1 <;> omega) ∧
        cokernel.π (Subobject.ofLE
          ((Y.imageFiltration (p + q) (AY (p + q))).step (p + 1))
          ((Y.imageFiltration (p + q) (AY (p + q))).step p)
          ((Y.imageFiltration (p + q) (AY (p + q))).antitone_step (by omega))) ≫
          ψY.hom = tY.hom ≫ (Y.pageCouple r).g (p - r) (q + r) ≫
            eqToHom (by congr 1 <;> omega) ∧
        Φ.map ψX.hom ≫ (φ r p q).hom = (κ (p + q) p).hom ≫ ψY.hom)) := by
  sorry

end CategoryTheory.BigradedExactCouple
