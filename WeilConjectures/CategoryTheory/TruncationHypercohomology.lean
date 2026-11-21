/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.TruncationCouple
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
public import WeilConjectures.CategoryTheory.ImageFiltration
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.TruncationRawExact
import WeilConjectures.CategoryTheory.TruncationQuadrantVanishing
import WeilConjectures.CategoryTheory.HalfPlaneSharpBounds
import WeilConjectures.CategoryTheory.TruncationCanonicalAbutment

/-!
# The truncation hypercohomology spectral sequence

Source: Stacks Project, Tags 015J, 05TC, 011Q, 011R, 011T, 0BDU, 0BDV and 012U.

The integer `a` is a cohomological lower bound, not a bound on the terms of `K`.
The natural index of `pageCouple` and of the cycle/boundary tower is the page minus two.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def singleComparison
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] (p : ℕ) :
    DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor B p ≅ F.rightDerived p :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
    (Functor.isoWhiskerRight F.rightDerivedFunctorPlusCompatibility.symm
      (DerivedCategory.homologyFunctor B p)) ≪≫
    F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p

/-- The six assertions of the truncation hypercohomology theorem, including the
canonical maps to the abutment, the natural second-page comparison, and the map
on graded pieces induced by the iterated couple.
Source: Stacks Tags 015J, 05TC, 011Q, 011R, 011T, 0BDU, 0BDV, 012U. -/
theorem exists_truncationHypercohomology
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (a : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q)) :
    ∃ (X : BigradedExactCouple B 0)
      (hD : X.D = TruncationCouple.D F K)
      (hE : X.E = TruncationCouple.E F K),
      (∀ p q : ℤ, X.alpha p q =
        eqToHom (by rw [hD]) ≫ TruncationCouple.alpha F K p q ≫
          eqToHom (by rw [hD])) ∧
      (∀ p q : ℤ, X.f p q =
        eqToHom (by rw [hE]) ≫ TruncationCouple.f F K p q ≫
          eqToHom (by rw [hD])) ∧
      (∀ p q : ℤ, X.initialG p q =
        eqToHom (by rw [hD]) ≫ TruncationCouple.g F K p q ≫
          eqToHom (by rw [hE])) ∧
      (∀ p : ℕ, ∀ q : ℤ,
        ∃ e : (CochainComplex.Plus.ι A ⋙
            HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q) ⋙
            DerivedCategory.singleFunctor A q ⋙ F.rightDerivedFunctor ⋙
            DerivedCategory.homologyFunctor B ((p : ℤ) + q) ≅
          (CochainComplex.Plus.ι A ⋙
            HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q) ⋙ F.rightDerived p,
          (∀ L : CochainComplex.Plus A, e.app L =
            (DerivedCategory.homologyFunctor B ((p : ℤ) + q)).mapIso
              (F.rightDerivedFunctor.mapIso
                (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0
                  (by omega)).app (L.obj.homology q)).symm) ≪≫
            (DerivedCategory.homologyFunctor B ((p : ℤ) + q)).mapIso
              ((F.rightDerivedFunctor.commShiftIso (-q)).app
                ((DerivedCategory.singleFunctor A 0).obj (L.obj.homology q))) ≪≫
            ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) ((p : ℤ) + q) p
              (by omega)).app
                (F.rightDerivedFunctor.obj
                  ((DerivedCategory.singleFunctor A 0).obj (L.obj.homology q))) ≪≫
            F.homologyRightDerivedFunctorObjSingleFunctorIso (L.obj.homology q) p) ∧
          (∃ eK : X.E p q ≅ (F.rightDerived p).obj (K.obj.homology q),
            eK = eqToIso (by rw [hE]; rfl) ≪≫
              (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K q)
                ((p : ℤ) + q)).symm ≪≫ e.app K)) ∧
      (∀ p q : ℤ, p < 0 → IsZero (X.E p q)) ∧
      (∀ p q : ℤ, q < a → IsZero (X.D p q)) ∧
      (∀ (r : ℕ) (p q : ℤ), 2 ≤ r → (p < 0 ∨ q < a) → IsZero (X.page r p q)) ∧
      (∀ (r : ℕ) (p q : ℤ), 2 ≤ r → ¬ IsZero (X.page r p q) →
        a ≤ q ∧ q ≤ p + q ∧ 0 ≤ p ∧ p ≤ p + q - a) ∧
      X.IsBounded ∧
      (∀ (r : ℕ) (p q : ℤ), 2 ≤ r → max (q - a + 1) p < (r : ℤ) →
        (X.pageCouple (r - 2)).d p q = 0 ∧
          (X.pageCouple (r - 2)).dInto p q = 0) ∧
      (∀ (p q : ℤ) (t : ℕ), max 2 (max (q - a + 2) (p + 1)) ≤ (t : ℤ) →
        X.cycleBoundaryTower.Z (t - 2) p q =
          X.cycleBoundaryTower.Z ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q ∧
        X.cycleBoundaryTower.B (t - 2) p q =
          X.cycleBoundaryTower.B ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q) ∧
      X.IsRegular ∧
      (∀ (r : ℕ) (p q : ℤ), q - a < (r : ℤ) →
        imageSubobject (X.incomingAlphaIter r p q) = ⊥) ∧
      X.IsComplete ∧
      ∃ (inc : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q)
        (L : X.LimitSubobjects)
        (H : ℤ → B)
        (hH : H = fun n : ℤ ↦ (DerivedCategory.homologyFunctor B n).obj
          (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj)))
        (j : ∀ n q : ℤ, X.D (n - q) q ⟶ H n)
        (c : ∀ n : ℤ, X.D 0 n ⟶ H n)
        (FA : ∀ n : ℤ, PBCDecreasingFiltration (X.D 0 n))
        (FH : ∀ n : ℤ, PBCDecreasingFiltration (H n)),
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
  classical
  obtain ⟨hα, hf, hg⟩ := truncation_raw_exact F K
  let X : BigradedExactCouple B 0 := by
    refine
      { D := TruncationCouple.D F K
        E := TruncationCouple.E F K
        alpha := TruncationCouple.alpha F K
        f := TruncationCouple.f F K
        g := fun p q ↦ TruncationCouple.g F K p q ≫ eqToHom (by simp)
        alpha_f_zero := fun p q ↦ (hα p q).choose
        f_g_zero := ?_
        g_alpha_zero := ?_
        exact_alpha := fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
          (hα p q).choose_spec
        exact_f := ?_
        exact_g := ?_ }
    · exact fun p q ↦ (hf p q).choose
    · exact fun p q ↦ (hg p q).choose
    · exact fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp (hf p q).choose_spec
    · exact fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp (hg p q).choose_spec
  have hαX : ∀ p q : ℤ, X.alpha p q =
      eqToHom (by rfl) ≫ TruncationCouple.alpha F K p q ≫ eqToHom (by rfl) := by
    intro p q
    simp [X]
  have hfX : ∀ p q : ℤ, X.f p q =
      eqToHom (by rfl) ≫ TruncationCouple.f F K p q ≫ eqToHom (by rfl) := by
    intro p q
    simp [X]
  have hgX : ∀ p q : ℤ, X.initialG p q =
      eqToHom (by rfl) ≫ TruncationCouple.g F K p q ≫ eqToHom (by rfl) := by
    intro p q
    simp [X, BigradedExactCouple.initialG]
  obtain ⟨hneg, hDzero, hEzero⟩ := truncation_quadrant_vanishing F K a ha
  have hEX : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q) := by
    intro p q h
    exact h.elim (hneg p q) (hEzero p q)
  refine ⟨X, rfl, rfl, hαX, hfX, hgX, ?_, hneg, hDzero, ?_⟩
  · intro p q
    let Hq := CochainComplex.Plus.ι A ⋙
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q
    let e₁ := Functor.isoWhiskerRight
      (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0 (by omega)).symm)
      (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B ((p : ℤ) + q))
    let e₂ := Functor.isoWhiskerLeft (DerivedCategory.singleFunctor A 0)
      (Functor.isoWhiskerRight (F.rightDerivedFunctor.commShiftIso (-q))
        (DerivedCategory.homologyFunctor B ((p : ℤ) + q)))
    let e₃ := Functor.isoWhiskerLeft
      (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor)
      ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) ((p : ℤ) + q) p (by omega))
    let e := Functor.isoWhiskerLeft Hq (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ singleComparison F p)
    refine ⟨e, ?_, ?_⟩
    · intro L
      rfl
    · refine ⟨eqToIso (by rfl) ≪≫
        (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K q)
          ((p : ℤ) + q)).symm ≪≫ e.app K, rfl⟩
  · obtain ⟨hpage, hsupport, hbounded, hd, hstable, hregular, himage, hcomplete⟩ :=
      halfPlane_sharp_bounds X a hDzero hEX
    exact ⟨hpage, hsupport, hbounded, hd, hstable, hregular, himage, hcomplete,
      truncation_canonical_abutment F K a ha X rfl rfl hαX hfX hgX hDzero hEX⟩

end CategoryTheory
