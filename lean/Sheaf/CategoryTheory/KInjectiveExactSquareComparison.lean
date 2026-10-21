/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Normalized comparison for an exact square preserving K-injectives

Source: Stacks Project, Derived Categories, Tags 070I, 070Y and 070K; exact-square
extraction of the tower normalization argument
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison).

The units are expressed on the homotopy category, as in def-sfb-right-derived-functor.
The canonical localization factors are retained in the two normalization arrows.

## Main definitions and statements

* `KInjectiveExactSquare.leftUnit` and `rightUnit`: the arrows a and b.
* `KInjectiveExactSquare.delta`: the comparison b a⁻¹ on K-injectives.
* `KInjectiveExactSquare.existsUnique_normalized`: descent, formula and uniqueness.
-/

@[expose] public section

set_option autoImplicit false

universe uA' uA uB' uB vA' vA vB' vB wA' wA wB' wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.KInjectiveExactSquare

variable {A' : Type uA'} {A : Type uA} {B' : Type uB'} {B : Type uB}
  [Category.{vA'} A'] [Category.{vA} A] [Category.{vB'} B'] [Category.{vB} B]
  [Abelian A'] [Abelian A] [Abelian B'] [Abelian B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wA} A]
  [HasDerivedCategory.{wB'} B'] [HasDerivedCategory.{wB} B]
  (H' : A' ⥤ B') (H : A ⥤ B) (r : A' ⥤ A) (s : B' ⥤ B)
  [H'.Additive] [H.Additive] [r.Additive] [s.Additive]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [PreservesFiniteLimits s] [PreservesFiniteColimits s]
  (h : H' ⋙ s = r ⋙ H)
  (RH' : DerivedCategory A' ⥤ DerivedCategory B')
  (RH : DerivedCategory A ⥤ DerivedCategory B)
  (η' : H'.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RH')
  (η : H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RH)

/-- The canonical strict-square identification on homotopy categories, directed from Hr to sH'.
Source: Stacks Tags 070I and 070Y, exact-square extraction, proof step 1
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison). -/
def sourceIso :
    r.mapHomotopyCategory (.up ℤ) ⋙ H.mapHomotopyCategory (.up ℤ) ≅
      H'.mapHomotopyCategory (.up ℤ) ⋙ s.mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ H)) (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (eqToIso h) (.up ℤ)).symm

/-- The arrow a_J, including the inverse exact-localization factor for s.
Source: Stacks Tags 070Y and 070K, exact-square extraction, proof step 1
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison). -/
noncomputable def leftUnit (J : CochainComplex A' ℤ) :
    DerivedCategory.Qh.obj ((H.mapHomotopyCategory (.up ℤ)).obj
      ((r.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A' (.up ℤ)).obj J))) ⟶
      (RH' ⋙ s.mapDerivedCategory).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) :=
  DerivedCategory.Qh.map ((sourceIso H' H r s h).hom.app
      ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) ≫
    s.mapDerivedCategoryFactorsh.inv.app ((H'.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) ≫
    s.mapDerivedCategory.map (η'.app ((HomotopyCategory.quotient A' (.up ℤ)).obj J))

/-- The arrow b_J, including RH of the inverse exact-localization factor for r.
Source: Stacks Tags 070Y and 070K, exact-square extraction, proof step 1
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison). -/
noncomputable def rightUnit (J : CochainComplex A' ℤ) :
    DerivedCategory.Qh.obj ((H.mapHomotopyCategory (.up ℤ)).obj
      ((r.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A' (.up ℤ)).obj J))) ⟶
      (r.mapDerivedCategory ⋙ RH).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) :=
  η.app ((r.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) ≫
    RH.map (r.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient A' (.up ℤ)).obj J))

/-- The normalized comparison δ_J = b_J a_J⁻¹, when a_J is invertible.
Source: Stacks Tags 070I, 070Y and 070K, exact-square extraction, proof step 1
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison). -/
noncomputable def delta (J : CochainComplex A' ℤ)
    (ha : IsIso (leftUnit H' H r s h RH' η' J)) :
    (RH' ⋙ s.mapDerivedCategory).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) ⟶
      (r.mapDerivedCategory ⋙ RH).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) :=
  letI := ha
  inv (leftUnit H' H r s h RH' η' J) ≫ rightUnit H r RH η J

/-- An exact strictly commuting square preserving K-injectives has a unique comparison
normalized only on K-injectives, natural on homotopy classes and independent of resolutions.
Source: Stacks Project, Derived Categories, Tags 070I, 070Y and 070K; exact-square extraction
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison).

Proof plan:
1. The units of the fixed universal pairs are invertible on K-injectives by
   def-sfb-right-derived-functor. The preservation hypothesis applies this also to rJ.
   The canonical factors of lem-weil-pbc-exact-functor-derived-factorization are invertible,
   so a_J and b_J are isomorphisms with common source Q(HrJ).
2. Additive functors preserve chain homotopies. Naturality of the units and localization
   factors gives A(Qf)a_J = a_J'V(f) and B(Qf)b_J = b_J'V(f). Cancelling a gives naturality
   of delta for every homotopy class between K-injectives.
3. By lem-weil-pbc-kinjective-hom-derived every derived map between these objects is the
   image of a homotopy class. Every derived object is isomorphic to QJ for a K-injective J,
   by the arbitrary-quasi-isomorphism hypothesis and def-weil-abstract-derived-category.
4. For u : M ≅ QJ define beta_M = A(u) delta_J B(u inverse). For another v : M ≅ QJ',
   apply step 3 to u inverse followed by v. Its naturality identity proves independence.
5. For f : M ⟶ N use resolutions u and v and the derived map u inverse followed by f
   followed by v. Step 3 proves naturality of beta. Its factors are invertible, hence beta
   is a natural isomorphism. Choosing u = identity gives the normalization and the formula.
6. Any other normalized natural isomorphism agrees with delta on QJ by cancelling a_J.
   Naturality along each u gives the same formula everywhere, proving uniqueness using
   normalization only on K-injectives. No adjunction, tower or monomorphic resolution is used.
-/
theorem existsUnique_normalized
    (enough' : ∀ K : CochainComplex A' ℤ,
      ∃ (J : CochainComplex A' ℤ) (f : K ⟶ J), J.IsKInjective ∧ QuasiIso f)
    (enough : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (f : K ⟶ J), J.IsKInjective ∧ QuasiIso f)
    (preserves : ∀ J : CochainComplex A' ℤ, J.IsKInjective →
      CochainComplex.IsKInjective ((r.mapHomologicalComplex (.up ℤ)).obj J))
    (universal' : ∀ G : DerivedCategory A' ⥤ DerivedCategory B',
      Function.Bijective (fun α : RH' ⟶ G ↦ η' ≫ Functor.whiskerLeft DerivedCategory.Qh α))
    (universal : ∀ G : DerivedCategory A ⥤ DerivedCategory B,
      Function.Bijective (fun α : RH ⟶ G ↦ η ≫ Functor.whiskerLeft DerivedCategory.Qh α)) :
    ∃ (ha : ∀ J : CochainComplex A' ℤ, J.IsKInjective →
        IsIso (leftUnit H' H r s h RH' η' J))
      (_hb : ∀ J : CochainComplex A' ℤ, J.IsKInjective → IsIso (rightUnit H r RH η J))
      (β : RH' ⋙ s.mapDerivedCategory ≅ r.mapDerivedCategory ⋙ RH),
      (∀ (J : CochainComplex A' ℤ), J.IsKInjective →
        leftUnit H' H r s h RH' η' J ≫
          β.hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) =
        rightUnit H r RH η J) ∧
      (∀ γ : RH' ⋙ s.mapDerivedCategory ≅ r.mapDerivedCategory ⋙ RH,
        (∀ (J : CochainComplex A' ℤ), J.IsKInjective →
          leftUnit H' H r s h RH' η' J ≫
            γ.hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) =
          rightUnit H r RH η J) → γ = β) ∧
      (∀ (J J' : CochainComplex A' ℤ) (hJ : J.IsKInjective) (hJ' : J'.IsKInjective)
          (f : (HomotopyCategory.quotient A' (.up ℤ)).obj J ⟶
            (HomotopyCategory.quotient A' (.up ℤ)).obj J'),
        (RH' ⋙ s.mapDerivedCategory).map (DerivedCategory.Qh.map f) ≫
            delta H' H r s h RH' RH η' η J' (ha J' hJ') =
          delta H' H r s h RH' RH η' η J (ha J hJ) ≫
            (r.mapDerivedCategory ⋙ RH).map (DerivedCategory.Qh.map f)) ∧
      (∀ (M : DerivedCategory A') (J : CochainComplex A' ℤ) (hJ : J.IsKInjective)
          (u : M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)),
        β.hom.app M = (RH' ⋙ s.mapDerivedCategory).map u.hom ≫
          delta H' H r s h RH' RH η' η J (ha J hJ) ≫
            (r.mapDerivedCategory ⋙ RH).map u.inv) ∧
      (∀ (M : DerivedCategory A') (J J' : CochainComplex A' ℤ)
          (hJ : J.IsKInjective) (hJ' : J'.IsKInjective)
          (u : M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J))
          (v : M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J')),
        (RH' ⋙ s.mapDerivedCategory).map u.hom ≫
            delta H' H r s h RH' RH η' η J (ha J hJ) ≫
              (r.mapDerivedCategory ⋙ RH).map u.inv =
          (RH' ⋙ s.mapDerivedCategory).map v.hom ≫
            delta H' H r s h RH' RH η' η J' (ha J' hJ') ≫
              (r.mapDerivedCategory ⋙ RH).map v.inv) := by
  sorry

end CategoryTheory.KInjectiveExactSquare
