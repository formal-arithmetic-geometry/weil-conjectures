/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.GlobalDerivedHom
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.Topology.PointModuleEvaluationEquivalence
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Sheaf.AlgebraicGeometry.InverseImageTensorPullbackComparison

/-! # K-flat behavior of global tensor pullback

Source: Stacks Project, Tags 06YC and 06YJ, after the one-point module identification
of Tag 0B6A. (blueprint: lem-sc-global-tensor-pullback-kflat).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance globalKFlatDataCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalKFlatDataMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalKFlatDataSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
local instance globalKFlatDataColimits :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance globalKFlatDataPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalKFlatDataClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
/-- Global tensor pullback sends K-flat complexes to K-flat complexes and inverts
quasi-isomorphisms between K-flat objects after localization.
Source: Stacks Project, Tags 06YC, 06YJ, 079U and 06XN.
(blueprint: lem-sc-global-tensor-pullback-kflat)

Proof: point evaluation identifies sheaves on the one-point ringed space with modules
on its global ring. Evaluation commutes with tensor products (evaluate the sheafified
sectionwise tensor at the only nonempty open); its inverse is therefore monoidal.
Both directions are exact equivalences and preserve coproducts. Applying them termwise
preserves acyclicity and the total tensor, hence preserves K-flatness. The object and
morphism formulas identify P applied to a complex with concrete tensor pullback of its
image under the inverse equivalence, including the differentials. Pullback preserves
K-flatness by Tag 06YC. Inverse image is exact; extension of scalars preserves
quasi-isomorphisms between K-flat complexes by Tag 06YJ. Thus P preserves such
quasi-isomorphisms. Lift homotopy morphisms to cochain morphisms using fullness of the
quotient, and apply the quasi-isomorphism criterion for the quotient and localization.
The argument includes the zero ring, zero complex, and all unbounded complexes. -/
theorem globalTensorPullback_kflat
    (e : SheafOfModules.{u} (moduleRings (globalSectionsPoint X)) ≌
        ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      (he : Nonempty (e.functor ≅ RingedSpace.globalSectionsFunctor (globalSectionsPoint X)))
      (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (h : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
          X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
            ⟨(toGlobalSectionsPoint X).hom.c⟩)
        (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
          (globalSectionsPoint X).sheaf (e.inverse.obj M)))
      (hm : ∀ {M N} (a : M ⟶ N), P.map a = eqToHom (h M) ≫
        SheafOfModules.changeOfRingsHom.{u, u, u}
          (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
            X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
              ⟨(toGlobalSectionsPoint X).hom.c⟩)
          (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M))
          (TopCat.Sheaf.inverseImageModuleMap (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M) (e.inverse.map a)) ≫
          eqToHom (h N).symm)
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint] :
    (∀ K : HomotopyCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (ComplexShape.up ℤ),
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat K →
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat
          ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ∧
    (∀ K M : HomotopyCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (ComplexShape.up ℤ),
      ∀ a : K ⟶ M,
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat K →
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat M →
        HomotopyCategory.quasiIso _ (ComplexShape.up ℤ) a →
        IsIso ((P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map a)) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
