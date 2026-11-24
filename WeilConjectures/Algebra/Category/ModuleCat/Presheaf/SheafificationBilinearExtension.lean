/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafifyBilinearExtExistence
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafifyBilinearExtUniqueness

/-!
# Extension of bilinear maps through module sheafification

## References

* Stacks Project, Modules on Sites, Lemma 18.26.1 (Tag 0GMW)
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace PresheafOfModules

/-- A restriction-compatible bilinear map into a sheaf extends uniquely through the two
module sheafification units. The locally bijective ring map `α` presents `R` as the
sheafification of `O`. Curried linear maps encode sectionwise bilinearity; the naturality
identities encode morphisms of (pre)sheaves of sets. -/
theorem existsUnique_bilinear_sheafification_extension
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (O : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (R : Sheaf J CommRingCat.{max u v w})
    (α : (O ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (F G : PresheafOfModules.{max u v w} (O ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}))
    (H : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R))
    (β : ∀ X : Cᵒᵖ, F.obj X →ₗ[O.obj X] G.obj X →ₗ[O.obj X]
      ((restrictScalars α).obj H.val).obj X)
    (hβ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X) (y : G.obj X),
      β Y (F.map f x) (G.map f y) = H.val.map f (β X x y)) :
    ∃! γ : ∀ X : Cᵒᵖ,
      ((sheafification α).obj F).val.obj X →ₗ[R.obj.obj X]
        ((sheafification α).obj G).val.obj X →ₗ[R.obj.obj X] H.val.obj X,
      (∀ {X Y : Cᵒᵖ} (f : X ⟶ Y)
        (x : ((sheafification α).obj F).val.obj X)
        (y : ((sheafification α).obj G).val.obj X),
        γ Y (((sheafification α).obj F).val.map f x)
          (((sheafification α).obj G).val.map f y) = H.val.map f (γ X x y)) ∧
      (∀ (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X),
        γ X (((sheafificationAdjunction α).unit.app F).app X x)
          (((sheafificationAdjunction α).unit.app G).app X y) = β X x y) := by
  obtain ⟨γ, hγmap, hγunit⟩ :=
    exists_bilinear_sheafification_extension O R α F G H β hβ
  refine ⟨γ, ⟨hγmap, hγunit⟩, ?_⟩
  intro δ hδ
  apply unique_bilinear_sheafification_extension O R α F G H hδ.1 hγmap
  intro X x y
  rw [hγunit X x y, hδ.2 X x y]

end PresheafOfModules
