/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Category.Preorder
public import WeilConjectures.Compactification.FiniteTypeExtension
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.Compactification.FiniteTypeDirected
import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
import WeilConjectures.AlgebraicGeometry.DirectedIdealModuleColimit
import WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The canonical family of finite-type subideals presents an ideal module as a colimit.
(Stacks, Tag 01PG.) -/
theorem exists_finiteType_ideal_module_diagram (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (_hI : I.toModules.IsQuasicoherent) :
    ∃ (D : {K : X.IdealSheafData // K ≤ I ∧ K.ofFiniteType} ⥤ X.Modules)
      (τ : D ⟶ (Functor.const _).obj I.toModules)
      (_ : IsColimit (Cocone.mk I.toModules τ)),
      ∀ a, a.val.toModules.IsFiniteType ∧
        ∃ e : D.obj a ≅ a.val.toModules,
          e.inv ≫ τ.app a ≫ I.toModulesι = a.val.toModulesι := by
  let A := {K : X.IdealSheafData // K ≤ I ∧ K.ofFiniteType}
  let D : A ⥤ X.Modules :=
    { obj := fun a ↦ a.val.toModules
      map := fun f ↦ IdealSheafData.toModulesOfLE (leOfHom f)
      map_id := fun a ↦ by
        apply (cancel_mono a.val.toModulesι).mp
        simp
      map_comp := fun {a b c} f g ↦ by
        apply (cancel_mono c.val.toModulesι).mp
        simp }
  let τ : D ⟶ (Functor.const A).obj I.toModules :=
    { app := fun a ↦ IdealSheafData.toModulesOfLE a.property.1
      naturality := fun a b f ↦ by
        apply (cancel_mono I.toModulesι).mp
        simp [D] }
  have he : ∀ a : A, (Iso.refl a.val.toModules).inv ≫ τ.app a ≫ I.toModulesι =
      a.val.toModulesι := by
    intro a
    simp [τ]
  obtain ⟨hc⟩ := IdealSheafData.nonempty_isColimit_of_directed_ideal_modules
    I {K | K ≤ I ∧ K.ofFiniteType}
    ⟨⊥, bot_le, IdealSheafData.ofFiniteType_bot⟩
    I.directedOn_ofFiniteType_le I.sSup_ofFiniteType_le_eq D τ
    (fun a ↦ Iso.refl a.val.toModules) he
  refine ⟨D, τ, hc, fun a ↦ ⟨?_, Iso.refl _, he a⟩⟩
  exact IdealSheafData.isFiniteType_toModules a.val a.property.2

end AlgebraicGeometry.Scheme
