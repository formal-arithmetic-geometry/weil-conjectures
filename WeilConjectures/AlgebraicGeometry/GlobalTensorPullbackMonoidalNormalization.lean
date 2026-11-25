/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import WeilConjectures.AlgebraicGeometry.ModuleCupNaiveMap
public import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.GlobalSectionsLaxMonoidalData
import WeilConjectures.AlgebraicGeometry.GlobalTensorPullbackOplaxIsIso
/-! # Tensor-counit normalization of the global pullback

## References

* Stacks Project, Tags 008A, 008Y, 0B6A and 0FKU.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
local instance : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance : SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
local instance : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
-- Keep the derived-category instance: omitting it cascades into the dependent statements.
set_option linter.unusedSectionVars false in
/-- The concrete global pullback admits the tensor constraint normalized by its counit
(Stacks, Tags 008A, 008Y and 0FKU). -/
theorem globalTensorPullback_monoidal_normalization
    (e : SheafOfModules.{u} (moduleRings (globalSectionsPoint X)) ≌
        ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      (_he : Nonempty (e.functor ≅ RingedSpace.globalSectionsFunctor (globalSectionsPoint X)))
      (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (h : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
          X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
            ⟨(toGlobalSectionsPoint X).hom.c⟩)
        (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
          (globalSectionsPoint X).sheaf (e.inverse.obj M)))
      (_hm : ∀ {M N} (a : M ⟶ N), P.map a = eqToHom (h M) ≫
        SheafOfModules.changeOfRingsHom.{u, u, u}
          (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
            X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
              ⟨(toGlobalSectionsPoint X).hom.c⟩)
          (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M))
          (TopCat.Sheaf.inverseImageModuleMap (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M) (e.inverse.map a)) ≫
          eqToHom (h N).symm)
    [P.Additive]
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace) :
    ∃ mon : P.Monoidal,
      letI := mon
      ∀ M N : SheafOfModules.{u} (moduleRings X.toRingedSpace),
        Functor.LaxMonoidal.μ P
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N) ≫
          P.map (moduleCup_sectionTensorMap X M N) ≫ adj.counit.app (M ⊗ N) =
        adj.counit.app M ⊗ₘ adj.counit.app N := by
  obtain ⟨lax, hε, hμ⟩ := globalSectionsFunctor_laxMonoidal_data X
  let := lax
  let oplax : P.OplaxMonoidal := adj.leftAdjointOplaxMonoidal
  let := oplax
  obtain ⟨hη, hδ⟩ := globalTensorPullback_oplax_isIso X P adj lax hε hμ
  let : IsIso (adj.leftAdjointOplaxMonoidal.η) := hη
  let : ∀ A B, IsIso (adj.leftAdjointOplaxMonoidal.δ A B) := hδ
  let mon : P.Monoidal := Functor.Monoidal.ofOplaxMonoidal P
  refine ⟨mon, ?_⟩
  intro M N
  change inv (oplax.δ _ _) ≫ _ ≫ _ = _
  rw [← hμ M N, adj.map_μ_comp_counit_app_tensor]
  simp
end
end AlgebraicGeometry.Scheme.Modules
