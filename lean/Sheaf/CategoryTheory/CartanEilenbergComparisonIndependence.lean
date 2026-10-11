/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.CategoryTheory.CartanEilenbergPresentation
import Sheaf.CategoryTheory.FilteredPageTwoModel
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Independence of Cartan--Eilenberg comparison maps

Source: Stacks Project, Derived Categories, Remarks and Lemmas 015K and 015N
(blueprint: lem-sp-cartan-eilenberg-comparison-independence).
-/

universe uAT vAT uBT vBT uCT vCT

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Comparison maps between the chosen Cartan--Eilenberg presentations are independent
of their lifts from page two. The second-page identifications are natural for the
original map. Identity and composition are preserved. The abutment is identified with
total cohomology, with its image filtration and stabilized pages, naturally for lifts.
Source: Stacks, Tags 015K and 015N
(blueprint: lem-sp-cartan-eilenberg-comparison-independence).

Proof:
1. Choose the resolutions as in lem-sp-cartan-eilenberg-exists. The convention here
   is that the first index is the complex degree and the second the resolution degree.
   The lift of lem-weil-pbc-cartesian-eilenberg-functorial preserves both degrees,
   hence the second filtration of def-sp-double-complex-total after applying G.
2. Two lifts of the same f between injective resolutions are homotopic by
   lem-weil-pbc-lift-to-injective-unique-up-to-homotopy. Additivity of F preserves
   this homotopy. By lem-sp-cartan-eilenberg-comparison-homotopy their CE lifts
   have a total homotopy lowering the resolution filtration by one. Applying G
   preserves this homotopy and its filtration shift.
3. The first-quadrant filtrations are finite in each total degree. Apply
   lem-sp-filtered-homotopy-spectral-sequence: the maps agree on E_r for r ≥ 2
   and on the filtered abutment. The page-two quotient-image model fixes which
   induced page maps are meant; the spectral-sequence compatibility determines
   the induced maps on every subsequent page.
4. Compare identity and composite lifts with chosen lifts by Steps 2--3.
   Functoriality of thm-sp-double-complex-spectral-sequences gives the identity
   and composition equations. The injective horizontal cycles, boundaries and
   homology, together with lem-sp-cart-eilenberg-left-exact-cohomology, identify
   E_2 with R^p G(R^q F(-)); def-sp-left-exact-additive computes these via the
   injective resolutions. These identifications and the abutment identifications
   use the same filtered maps, so their naturality squares commute.
-/
theorem cartanEilenberg_comparison_independence
    {A : Type uAT} [Category.{vAT} A] [Abelian A] [IsGrothendieckAbelian.{vAT} A]
    {B : Type uBT} [Category.{vBT} B] [Abelian B] [IsGrothendieckAbelian.{vBT} B]
    {C : Type uCT} [Category.{vCT} C] [Abelian C] [IsGrothendieckAbelian.{vCT} C]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (M : FilteredPageTwoModel C) :
    ∃ (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G)),
      let T := fun P : CartanEilenbergPresentation F ↦
        (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ))
      (∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
        (L P).complexStep p n =
          ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)) ∧
      (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q),
        ∃ t : T P ⟶ T Q,
          t.hom = HomologicalComplex₂.total.map
            ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ)) ∧
      (∀ (P Q : CartanEilenbergPresentation F) (c c' : P.Comparison Q)
        (t t' : T P ⟶ T Q),
        c.f = c'.f →
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) →
        t'.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c'.α) (ComplexShape.up ℤ) →
        M.S.map t = M.S.map t') ∧
      (∀ (P : CartanEilenbergPresentation F) (c : P.Comparison P) (t : T P ⟶ T P),
        c.f = 𝟙 P.X →
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) →
        M.S.map t = 𝟙 (M.S.obj (T P))) ∧
      (∀ (P Q R : CartanEilenbergPresentation F)
        (c : P.Comparison Q) (d : Q.Comparison R) (c' : P.Comparison R)
        (t : T P ⟶ T Q) (u : T Q ⟶ T R) (v : T P ⟶ T R),
        c'.f = c.f ≫ d.f →
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) →
        u.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map d.α) (ComplexShape.up ℤ) →
        v.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c'.α) (ComplexShape.up ℤ) →
        M.S.map v = M.S.map t ≫ M.S.map u) ∧
      (∃ e : ∀ (P : CartanEilenbergPresentation F) (p q : ℕ),
          ((M.S.obj (T P)).page 2).X ((p : ℤ), (q : ℤ)) ≅
            ((F.rightDerived q ⋙ G.rightDerived p).obj P.X),
        ∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q)
          (t : T P ⟶ T Q),
          t.hom = HomologicalComplex₂.total.map
            ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) →
          ∀ p q : ℕ,
            ((M.S.map t).hom 2).f ((p : ℤ), (q : ℤ)) ≫ (e Q p q).hom =
              (e P p q).hom ≫ (F.rightDerived q ⋙ G.rightDerived p).map c.f) ∧
      (∃ (H : CartanEilenbergPresentation F → ℤ → C)
        (h : ∀ (P : CartanEilenbergPresentation F) (n : ℤ), H P n ≅ (P.total G).homology n)
        (HF : ∀ (P : CartanEilenbergPresentation F) (n : ℤ), DecreasingFiltration (H P n))
        (m : ∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (n : ℤ),
          H P n ⟶ H Q n),
        (∀ (P : CartanEilenbergPresentation F) (n : ℤ), (HF P n).IsFinite) ∧
        (∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
          (Subobject.«exists» (h P n).hom).obj ((HF P n).step p) =
            imageSubobject (HomologicalComplex.homologyMap ((L P).step p).arrow n)) ∧
        (∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
          ∃ (R : ℤ) (hR : 2 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
            Nonempty (((M.S.obj (T P)).page r (le_trans hR hr)).X (p, n - p) ≅
              (HF P n).gradedPiece p)) ∧
        (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (n : ℤ),
          m P Q c n ≫ (h Q n).hom = (h P n).hom ≫
            HomologicalComplex.homologyMap
              (HomologicalComplex₂.total.map
                ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ)) n) ∧
        (∀ (P Q : CartanEilenbergPresentation F) (c c' : P.Comparison Q),
          c.f = c'.f → ∀ n : ℤ, m P Q c n = m P Q c' n) ∧
        (∀ (P : CartanEilenbergPresentation F) (c : P.Comparison P),
          c.f = 𝟙 P.X → ∀ n : ℤ, m P P c n = 𝟙 (H P n)) ∧
        (∀ (P Q R : CartanEilenbergPresentation F)
          (c : P.Comparison Q) (d : Q.Comparison R) (e : P.Comparison R),
          e.f = c.f ≫ d.f → ∀ n : ℤ, m P R e n = m P Q c n ≫ m Q R d n) ∧
        (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (p n : ℤ),
          ∃ a : ((HF P n).step p : C) ⟶ ((HF Q n).step p : C),
            a ≫ ((HF Q n).step p).arrow = ((HF P n).step p).arrow ≫ m P Q c n)) := by
  sorry

end CategoryTheory
