/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.CategoryTheory.TruncationCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Sheaf.CategoryTheory.ImageFiltration
import Sheaf.CategoryTheory.HalfPlaneSharpBounds
import Sheaf.CategoryTheory.HalfPlaneConvergence
import Sheaf.CategoryTheory.DerivedCoupleExact
import Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.Filtration

/-! Canonical truncation-couple proof step. -/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Canonical abutment maps and finite image filtration of a truncation couple.
Source: Stacks Tags 011R, 011T, 012F, 012U (3), 05TC (2);
blueprint steps 5--7 of thm-sp-truncation-e2
(blueprint: lem-sp-truncation-canonical-abutment).

Proof: Include each iterated D image recursively in D. Sharp stabilization identifies
its stable cycles and boundaries with their intersection and union, defining L.
Take H^n=H^n(RF K), and define j by the bridge followed by RF of the truncation
inclusion. Functoriality and the transition-inclusion equation identify j with the
alpha composites. The inclusion tau<=n K -> K is an isomorphism after degree-n
derived cohomology by 05TC (2), so c is an isomorphism. Filter D(0,n) by incoming
alpha images and transport this filtration along c. Negative initial E degrees
make alpha an isomorphism to the left of p=0, giving fullness for p<=0; lower D
vanishing gives zero for p>=n-a+1. Thus the filtration is finite, exhaustive,
separated, and its quotient tower is eventually H^n, proving the inverse-limit
property. At r=max(p+3,q-a+2), lambda=alpha^(-u) identifies F^p with D_r(u,v)
and F^(p+1) with its incoming alpha image. The next D is zero. Exactness therefore
makes g_r induce the quotient isomorphism psi, with the displayed commuting
equation. Transport across c on graded objects and the stabilized quotient map
to obtain Theta. For p<0 both graded objects and the infinite page vanish.
The alpha diagonal colimit is D(0,n); transport its cocone along c to H^n.
The cocone equation follows from the composite-inclusion identity. Its canonical
comparison with the stable page is exactly Theta, so these maps give convergence. -/
theorem truncation_canonical_abutment
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (a : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q))
    (X : BigradedExactCouple B 0)
    (hD : X.D = TruncationCouple.D F K)
    (hE : X.E = TruncationCouple.E F K)
    (halpha : (∀ p q : ℤ, X.alpha p q =
        eqToHom (by rw [hD]) ≫ TruncationCouple.alpha F K p q ≫
          eqToHom (by rw [hD])))
    (hf : (∀ p q : ℤ, X.f p q =
        eqToHom (by rw [hE]) ≫ TruncationCouple.f F K p q ≫
          eqToHom (by rw [hD])))
    (hg : (∀ p q : ℤ, X.initialG p q =
        eqToHom (by rw [hD]) ≫ TruncationCouple.g F K p q ≫
          eqToHom (by rw [hE])))
    (hDzero : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hEzero : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q)) :
    ∃ (inc : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q)
        (L : X.LimitSubobjects)
        (H : ℤ → B)
        (hH : H = fun n : ℤ ↦ (DerivedCategory.homologyFunctor B n).obj
          (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj)))
        (j : ∀ n q : ℤ, X.D (n - q) q ⟶ H n)
        (c : ∀ n : ℤ, X.D 0 n ⟶ H n)
        (FA : ∀ n : ℤ, DecreasingFiltration (X.D 0 n))
        (FH : ∀ n : ℤ, DecreasingFiltration (H n)),
        (∀ p q : ℤ, inc 0 p q = 𝟙 _) ∧
        (∀ (r : ℕ) (p q : ℤ), inc (r + 1) p q =
          (X.pageCouple r).derivedDInclusion p q ≫ inc r p q) ∧
        (∀ p q : ℤ,
          L.Z p q = X.cycleBoundaryTower.Z
            ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q ∧
          L.B p q = X.cycleBoundaryTower.B
            ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q ∧
          Nonempty (X.pageInfinity L p q ≅
            X.page (max 2 (max (q - a + 2) (p + 1))).toNat p q)) ∧
        (∀ n q : ℤ, j n q =
          eqToHom (by rw [hD]; unfold TruncationCouple.D; congr 1; omega) ≫
          (TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) n).inv ≫
          (DerivedCategory.homologyFunctor B n).map
            (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE q))) ≫
          eqToHom (by rw [hH])) ∧
        (∀ n : ℤ, c n = eqToHom (by congr 1; omega) ≫ j n n) ∧
        (∀ n : ℤ, IsIso (c n)) ∧
        (∀ n p : ℤ, 0 ≤ p → (FA n).step p =
          imageSubobject (X.incomingAlphaIter p.toNat 0 n)) ∧
        (∀ n p : ℤ, p ≤ 0 → (FA n).step p = ⊤) ∧
        (∀ n : ℤ, FH n = (FA n).image (c n)) ∧
        (∀ n p : ℤ, (FH n).step p = imageSubobject (j n (n - p))) ∧
        (∀ n p : ℤ, p ≤ 0 → (FH n).step p = ⊤) ∧
        (∀ n p : ℤ, n - a + 1 ≤ p → (FH n).step p = ⊥) ∧
        (∀ n : ℤ, (FH n).IsFinite ∧ (FH n).IsExhaustive ∧ (FH n).IsSeparated ∧
          BigradedExactCouple.IsInverseLimit (FH n)) ∧
        (∀ p q : ℤ, p < 0 → IsZero ((FH (p + q)).gradedPiece p) ∧
          IsZero (X.pageInfinity L p q)) ∧
        (∀ (p q : ℤ) (hp : 0 ≤ p),
          ∃ (lambda : X.D 0 (p + q) ⟶
              X.D (p - max (p + 3) (q - a + 2) + 2) (q + max (p + 3) (q - a + 2) - 2))
            (lift : ((FA (p + q)).step p : B) ⟶
              (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).D
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2))
            (psi : (FA (p + q)).gradedPiece p ≅
              X.page (max (p + 3) (q - a + 2)).toNat p q)
            (grc : (FA (p + q)).gradedPiece p ≅ (FH (p + q)).gradedPiece p)
            (stable : X.page (max (p + 3) (q - a + 2)).toNat p q ≅
              X.pageInfinity L p q)
            (Theta : (FH (p + q)).gradedPiece p ≅ X.pageInfinity L p q)
            (cStep : ((FA (p + q)).step p : B) ⟶ ((FH (p + q)).step p : B))
            (hZ : X.cycleBoundaryTower.Z
                ((max (p + 3) (q - a + 2)).toNat - 2) p q = L.Z p q),
            IsIso lambda ∧
            lambda = X.alphaIter
              (-(p - max (p + 3) (q - a + 2) + 2)).toNat 0 (p + q) ≫
                eqToHom (by congr 1 <;> omega) ∧
            IsIso lift ∧
            lift ≫ inc ((max (p + 3) (q - a + 2)).toNat - 2)
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2) =
              ((FA (p + q)).step p).arrow ≫ lambda ∧
            cStep ≫ ((FH (p + q)).step p).arrow =
              ((FA (p + q)).step p).arrow ≫ c (p + q) ∧
            cStep ≫ cokernel.π (Subobject.ofLE ((FH (p + q)).step (p + 1))
                ((FH (p + q)).step p) ((FH (p + q)).antitone_step (by omega))) =
              cokernel.π (Subobject.ofLE ((FA (p + q)).step (p + 1))
                ((FA (p + q)).step p) ((FA (p + q)).antitone_step (by omega))) ≫ grc.hom ∧
            X.cycleBoundaryTower.projection
                ((max (p + 3) (q - a + 2)).toNat - 2) p q ≫ stable.hom =
              eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : B)) hZ) ≫
                cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
                  (X.limitBoundary_le_cycle L p q)) ∧
            cokernel.π (Subobject.ofLE ((FA (p + q)).step (p + 1))
                ((FA (p + q)).step p) ((FA (p + q)).antitone_step (by omega))) ≫
              psi.hom = lift ≫
              (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).g
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2) ≫
              eqToHom (by unfold BigradedExactCouple.page; congr 1 <;> omega) ∧
            Theta = grc.symm ≪≫ psi ≪≫ stable) ∧
        ∃ (AH : ∀ n : ℤ, X.AlphaColimit n) (hAH : ∀ n : ℤ, (AH n).obj = H n),
          (∀ n p : ℤ, (AH n).ι p ≫ eqToHom (hAH n) =
            eqToHom (by congr 1; omega) ≫ j n (n - p)) ∧
          X.ConvergesTo L AH := by
  sorry

end CategoryTheory
