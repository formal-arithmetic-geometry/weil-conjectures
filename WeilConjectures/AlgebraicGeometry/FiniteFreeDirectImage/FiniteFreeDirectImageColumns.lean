/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImagePullbackCoordinates

/-! # Finite-free basis columns of the direct-image coefficient comparison

Source: Stacks Project, Tags 0B56 and 0944.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

private theorem mate_columns_private
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ C} {R : C ⥤ A} {L' : B ⥤ D} {R' : D ⥤ B}
    {E : A ⥤ B} {U : B ⥤ A} {E' : C ⥤ D} {U' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (b : L' ⋙ U' ≅ U ⋙ L) (θ : E ⋙ L' ≅ L ⋙ E')
    (δ : R' ⋙ U ≅ U' ⋙ R)
    (hδ : ∀ (X : B) (Y : D) (t : L'.obj X ⟶ Y),
      adj.homEquiv _ _ (b.inv.app X ≫ U'.map t) =
        U.map (adj'.homEquiv X Y t) ≫ δ.hom.app Y)
    {I : Type*}
    (cW : ∀ (X : A) (_ : I), X ⟶ U.obj (E.obj X))
    (cZ : ∀ (X : C) (_ : I), X ⟶ U'.obj (E'.obj X))
    (hcZ : ∀ {X Y : C} (f : X ⟶ Y) (i : I),
      cZ X i ≫ U'.map (E'.map f) = f ≫ cZ Y i)
    (hpull : ∀ X i, L.map (cW X i) ≫ b.inv.app (E.obj X) ≫
      U'.map (θ.hom.app X) = cZ (L.obj X) i)
    (M : C) (i : I) :
    cW (R.obj M) i ≫
      U.map ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ θ.hom)).app M) ≫
      δ.hom.app (E'.obj M) = R.map (cZ M i) := by
  have ht' : adj'.homEquiv _ _
      (θ.hom.app (R.obj M) ≫ E'.map (adj.counit.app M)) =
      (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ θ.hom)).app M := by
    apply (adj'.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (mateEquiv_counit adj adj' (TwoSquare.mk _ _ _ _ θ.hom) M).symm
  rw [← ht']
  have hs := hδ
    (E.obj (R.obj M)) (E'.obj ((𝟭 C).obj M))
    (θ.hom.app (R.obj M) ≫ E'.map (adj.counit.app M))
  change cW (R.obj M) i ≫
    (U.map (adj'.homEquiv (E.obj (R.obj M)) (E'.obj ((𝟭 C).obj M))
      (θ.hom.app (R.obj M) ≫ E'.map (adj.counit.app M))) ≫
      δ.hom.app (E'.obj ((𝟭 C).obj M))) = _
  rw [← hs]
  rw [← adj.homEquiv_naturality_left]
  have hp := congrArg (fun f ↦ f ≫ U'.map (E'.map (adj.counit.app M)))
    (hpull (R.obj M) i)
  have hcomp :
      L.map (cW (R.obj M) i) ≫ b.inv.app (E.obj (R.obj M)) ≫
        U'.map (θ.hom.app (R.obj M) ≫ E'.map (adj.counit.app M)) =
      adj.counit.app M ≫ cZ M i := by
    calc
      _ = cZ (L.obj (R.obj M)) i ≫ U'.map (E'.map (adj.counit.app M)) := by
        simpa only [Functor.map_comp, Category.assoc] using hp
      _ = _ := hcZ (adj.counit.app M) i
  rw [hcomp]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    adj.right_triangle_components, Category.id_comp]

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage

namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage
/-- Public export of the private `mate_columns_private` (used by `import all` importers; linter.privateModule). -/
alias mate_columns := mate_columns_private
end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
