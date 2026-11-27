/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import
  WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Exact K-injective replacement


## Main definitions and statements

* `HomotopyCategory.KInjectives.inclusionCommShift`: inherited shifts for the inclusion.
* `HomotopyCategory.KInjectives.localizationCommShift`: composite shifts for localization.
* `HomotopyCategory.KInjectives.replacement_triangulated`: equivalence and exact replacement.

## References

* [Stacks Project, Tag 05QX](https://stacks.math.columbia.edu/tag/05QX)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 070Y](https://stacks.math.columbia.edu/tag/070Y)
* [Stacks Project, Tag 0FXC](https://stacks.math.columbia.edu/tag/0FXC)
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Pretriangulated.Opposite

universe w v u

namespace HomotopyCategory.KInjectives

/-- The inclusion uses the inherited integer shifts of the full right orthogonal. -/
noncomputable instance inclusionCommShift (C : Type u) [Category.{v} C] [Abelian C] :
    (ι (C := C)).CommShift ℤ :=
  inferInstanceAs ((ObjectProperty.ι (subcategoryAcyclic C).rightOrthogonal).CommShift ℤ)

/-- Localization on K-injectives uses the composite shift comparison of inclusion and Qh. -/
noncomputable instance localizationCommShift (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] : (Qh (C := C)).CommShift ℤ :=
  inferInstanceAs ((ι (C := C) ⋙ DerivedCategory.Qh).CommShift ℤ)

private theorem triangulated_inverse (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (E : KInjectives C ≌ DerivedCategory C)
    [E.functor.CommShift ℤ] [E.functor.IsTriangulated]
    [(ι (C := C)).IsTriangulated] :
    ∃ S : E.inverse.CommShift ℤ,
      (fun [_s : E.inverse.CommShift ℤ] ↦
        E.inverse.IsTriangulated ∧ (E.inverse ⋙ ι).IsTriangulated ∧
          (E.inverse ⋙ ι).op.IsTriangulated) (_s := S) := by
  let := E.commShiftInverse ℤ
  have : E.CommShift ℤ := E.commShift_of_functor ℤ
  have : E.IsTriangulated := Equivalence.IsTriangulated.mk' E inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- K-injective localization is a triangulated equivalence, and every quasi-inverse gives
an exact replacement functor, also on opposite categories. -/
theorem replacement_triangulated (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C]
    (h : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (i : K ⟶ I),
      I.IsKInjective ∧ QuasiIso i) :
    (subcategoryAcyclic C).rightOrthogonal.IsTriangulated ∧
    CategoryTheory.IsTriangulated (KInjectives C) ∧
    (ι (C := C)).IsTriangulated ∧
    (Qh (C := C)).IsEquivalence ∧
    (Qh (C := C)).IsTriangulated ∧
    ∀ (G : DerivedCategory C ⥤ KInjectives C)
      (_η : 𝟭 (KInjectives C) ≅ Qh ⋙ G) (_ε : G ⋙ Qh ≅ 𝟭 (DerivedCategory C)),
      ∃ S : G.CommShift ℤ,
        (fun [_s : G.CommShift ℤ] ↦
          G.IsTriangulated ∧ (G ⋙ ι).IsTriangulated ∧ (G ⋙ ι).op.IsTriangulated)
          (_s := S) := by
  have horth : (subcategoryAcyclic C).rightOrthogonal.IsTriangulated := inferInstance
  have hcat : CategoryTheory.IsTriangulated (KInjectives C) := inferInstance
  have hι : (ι (C := C)).IsTriangulated :=
    inferInstanceAs ((ObjectProperty.ι (subcategoryAcyclic C).rightOrthogonal).IsTriangulated)
  have hQ : (Qh (C := C)).IsTriangulated :=
    inferInstanceAs ((ι (C := C) ⋙ DerivedCategory.Qh).IsTriangulated)
  have : (Qh (C := C)).EssSurj := by
    refine ⟨fun X ↦ ?_⟩
    obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Qh) X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨I, i, hI, hi⟩ := h K
    have := Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
      ((HomotopyCategory.quotient _ _).map i)
        (by simpa [quotient_map_mem_quasiIso_iff])
    exact ⟨mk I,
      ⟨(asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map i))).symm ≪≫ e⟩⟩
  have heq : (Qh (C := C)).IsEquivalence := { }
  refine ⟨horth, hcat, hι, heq, hQ, ?_⟩
  intro G η ε
  let E : KInjectives C ≌ DerivedCategory C := CategoryTheory.Equivalence.mk Qh G η ε
  let : E.functor.CommShift ℤ := localizationCommShift C
  have : E.functor.IsTriangulated := hQ
  exact triangulated_inverse C E

end HomotopyCategory.KInjectives
