/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap

/-!
# Right shifts of the Hom complex

## References

* Stacks Project, Cohomology on Sites, Sections 21.34--21.35 (Tags 0A8X, 08JA, 0A95)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace CategoryTheory

/-- Moving a shift across a functorial K-injective replacement does not change
localized Hom complexes, naturally in both input complexes. -/
theorem homComplex_resolution_shift_comparison
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (η : 𝟭 _ ⟶ I)
    (hI : ∀ M, QuasiIso (η.app M) ∧ (I.obj M).IsKInjective) (n : ℤ) :
    Nonempty (
      (𝟭 _).prod (I ⋙ shiftFunctor _ n) ⋙
        Functor.uncurry.obj (homComplexFunctor (C := C) (J := J) (R := R)) ⋙
          DerivedCategory.Q ≅
      (𝟭 _).prod (shiftFunctor _ n ⋙ I) ⋙
        Functor.uncurry.obj (homComplexFunctor (C := C) (J := J) (R := R)) ⋙
          DerivedCategory.Q) := by
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let S := shiftFunctor (CochainComplex A ℤ) n
  let H := Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q
  have hinv (F G : CochainComplex A ℤ ⥤ CochainComplex A ℤ) (α : F ⟶ G)
      (hα : ∀ M, QuasiIso (α.app M))
      (hF : ∀ M, (F.obj M).IsKInjective)
      (hG : ∀ M, (G.obj M).IsKInjective) :
      IsIso (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) α) H) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have : QuasiIso (α.app X.2) := hα X.2
    have : (F.obj X.2).IsKInjective := hF X.2
    have : (G.obj X.2).IsKInjective := hG X.2
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact quasiIso_homComplex_map (α.app X.2) (𝟙 X.1.unop)
  let α := Functor.whiskerLeft (I ⋙ S) η
  let β := Functor.whiskerRight (Functor.whiskerRight η S) I
  have hIS (M : CochainComplex A ℤ) : ((I ⋙ S).obj M).IsKInjective := by
    have : (I.obj M).IsKInjective := (hI M).2
    dsimp [S]
    infer_instance
  have hβ (M : CochainComplex A ℤ) : QuasiIso (β.app M) := by
    have : QuasiIso (η.app M) := (hI M).1
    have : QuasiIso (S.map (η.app M)) := by dsimp [S]; infer_instance
    have : QuasiIso (η.app (S.obj M)) := (hI _).1
    have : QuasiIso (η.app (S.obj (I.obj M))) := (hI _).1
    apply (quasiIso_iff_comp_left (η.app (S.obj M)) _).mp
    change QuasiIso (η.app (S.obj M) ≫ I.map (S.map (η.app M)))
    have hn := η.naturality (S.map (η.app M))
    dsimp at hn
    rw [← hn]
    infer_instance
  have : IsIso (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) α) H) :=
    hinv _ _ _ (fun M ↦ (hI _).1) hIS (fun M ↦ (hI _).2)
  have : IsIso (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) β) H) :=
    hinv _ _ _ hβ (fun M ↦ (hI _).2) (fun M ↦ (hI _).2)
  exact ⟨asIso (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) α) H) ≪≫
    (asIso (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) β) H)).symm⟩

end CategoryTheory
