/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct

/-!
# Internal Hom restrictions to total tensor summands

## References

* [Stacks Project, Tag 03EK](https://stacks.math.columbia.edu/tag/03EK)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option synthInstance.maxSize 256 in
/-- Restriction to every summand determines a morphism into the internal Hom
from a total tensor term. -/
theorem homTensorSummandRestriction_ext
    (K L : CochainComplex Mod ℤ) (t : ℤ) (A N : Mod) :
    letI := SheafOfModules.monoidalCategory R
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    ∀ (f g : A ⟶ SheafOfModules.homObj (R := R) (T.X t) N),
      (∀ (p q : ℤ) (h : p + q = t),
        f ≫ SheafOfModules.homObjMap (R := R)
          (CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q t h) (𝟙 N) =
        g ≫ SheafOfModules.homObjMap (R := R)
          (CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q t h) (𝟙 N)) →
      f = g := by
  let := SheafOfModules.monoidalCategory R
  dsimp
  intro f g h
  let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
  let I := {x : ℤ × ℤ // x.1 + x.2 = t}
  let M : I → Mod := fun x ↦ K.X x.1.1 ⊗ L.X x.1.2
  let c : Limits.Cofan M := Limits.Cofan.mk (T.X t) (fun x ↦
    CochainComplex.ιMapBifunctor K L (curriedTensor Mod) x.1.1 x.1.2 t x.2)
  have hc : Limits.IsColimit c := by
    refine Limits.Cofan.IsColimit.mk c
      (fun s ↦ HomologicalComplex.mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor Mod)
        (fun p q hpq ↦ s.inj ⟨(p, q), hpq⟩)) ?_ ?_
    · intro s x
      exact HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor Mod)
        (fun p q hpq ↦ s.inj ⟨(p, q), hpq⟩) x.1.1 x.1.2 x.2
    · intro s m hm
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q hpq
      exact (hm ⟨(p, q), hpq⟩).trans
        (HomologicalComplex.ι_mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor Mod)
          (fun p q hpq ↦ s.inj ⟨(p, q), hpq⟩) p q hpq).symm
  obtain ⟨hcHom⟩ := SheafOfModules.internalHomCoproductFanIsLimit R M c hc N
  apply Limits.Fan.IsLimit.hom_ext hcHom f g
  rintro ⟨x, hx⟩
  simpa [c, I, M] using h x.1 x.2 hx

end CategoryTheory
