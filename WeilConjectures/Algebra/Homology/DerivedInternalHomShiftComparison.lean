/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftLeft
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftRight

/-! # Shift comparison for derived internal Hom
## References

* Stacks Project, Sections 21.34 and 21.35 of Cohomology on Sites (Tag 08JA)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace CategoryTheory

private theorem shiftComparisonOfOneVariable
    {D : Type*} [Category D] [HasShift D ℤ] (H : Dᵒᵖ × D ⥤ D)
    (hl : ∀ (P : D) (m : ℤ), Nonempty
      ((Functor.curry.obj H).obj (op P) ⋙ shiftFunctor D (-m) ≅
        (Functor.curry.obj H).obj (op (P⟦m⟧))))
    (hr : ∀ (P : D) (n : ℤ), Nonempty
      ((Functor.curry.obj H).obj (op P) ⋙ shiftFunctor D n ≅
        shiftFunctor D n ⋙ (Functor.curry.obj H).obj (op P))) :
    ∃ e : ∀ (P Q : D) (m n : ℤ),
      (H.obj (op P, Q))⟦n - m⟧ ≅ H.obj (op (P⟦m⟧), Q⟦n⟧),
      ∀ (P Q Q' : D) (m n : ℤ) (q : Q ⟶ Q'),
        (H.map ((𝟙 P).op, q))⟦n - m⟧' ≫ (e P Q' m n).hom =
          (e P Q m n).hom ≫ H.map ((𝟙 (P⟦m⟧)).op, q⟦n⟧') := by
  classical
  let F := Functor.curry.obj H
  let c (P : D) (m n : ℤ) :
      F.obj (op P) ⋙ shiftFunctor D (n - m) ≅
        shiftFunctor D n ⋙ F.obj (op (P⟦m⟧)) :=
    Functor.isoWhiskerLeft (F.obj (op P))
        (shiftFunctorAdd' D n (-m) (n - m) (sub_eq_add_neg n m).symm) ≪≫
      Functor.isoWhiskerRight (hr P n).some (shiftFunctor D (-m)) ≪≫
      Functor.isoWhiskerLeft (shiftFunctor D n) (hl P m).some
  refine ⟨fun P Q m n ↦ (c P m n).app Q, ?_⟩
  intro P Q Q' m n q
  exact (c P m n).hom.naturality q


/-- Shifting the two arguments of internal derived Hom shifts its value by their
relative degree, naturally in the second argument. This is a comparison in the
sheaf derived category; no global-section or cohomology functor occurs here. -/
theorem derivedInternalHom_shift_comparison
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))] :
    ∃ e : ∀ (P Q : DerivedCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) (m n : ℤ),
      ((derivedInternalHom.{u, w} (C := C) J R).obj (op P, Q))⟦n - m⟧ ≅
        (derivedInternalHom.{u, w} (C := C) J R).obj (op (P⟦m⟧), Q⟦n⟧),
      ∀ (P Q Q' : DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
        (m n : ℤ) (q : Q ⟶ Q'),
        ((derivedInternalHom.{u, w} (C := C) J R).map ((𝟙 P).op, q))⟦n - m⟧' ≫
            (e P Q' m n).hom =
          (e P Q m n).hom ≫
            (derivedInternalHom.{u, w} (C := C) J R).map ((𝟙 (P⟦m⟧)).op, q⟦n⟧') := by
  exact shiftComparisonOfOneVariable (derivedInternalHom.{u, w} (C := C) J R)
    (derivedInternalHom_shift_left J R) (derivedInternalHom_shift_right J R)

end CategoryTheory
