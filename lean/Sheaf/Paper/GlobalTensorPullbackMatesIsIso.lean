/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module
public import Sheaf.Paper.ModuleCupNaiveMap
/-! # Tensor-counit normalization of the global pullback

Source: Stacks Tags 008A, 008Y, 0B6A and 0FKU. -/

@[expose] public section
universe u
set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable (X : Scheme.{u})
local instance globalPullbackMatesCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalPullbackMatesMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalPullbackMatesSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
local instance globalPullbackMatesColimits :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance globalPullbackMatesPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalPullbackMatesClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
/-- The unit and tensor mates for global sections are isomorphisms.
Source: Stacks, Modules Lemma 17.16.4 (Tag 01CA), and Sheaves Tags 008A and 008Y.
(blueprint: lem-sc-global-tensor-pullback-mates-isiso)
Proof: let A be the global section ring and p the ringed-space map from X to the
one-point ringed space with ring A. Point evaluation identifies its module category
with A-modules, and the inverse-image/change-of-rings adjunction identifies the left
adjoint of global sections with p*. For this adjunction the unit mate is the canonical
map p*(A) to O_X, with local formula a tensor r maps to ar, and inverse r maps to
r tensor 1. The tensor mate sends a tensor (m tensor n) to
(a tensor m) tensor (1 tensor n). Its inverse sends
(a tensor m) tensor (b tensor n) to ab tensor (m tensor n). The tensor balancing
relations make these maps well defined and mutually inverse. Inverse image and
sheafification preserve these local formulas, giving the sheaf isomorphisms of
Lemma 17.16.4. The Hom equivalence identifies these maps with exactly the two mates
in the statement: the tensor mate is transposed from the tensor of the two adjunction
units followed by the section tensor map. For any other left adjoint P and adjunction,
the unique isomorphism of left adjoints compatible with the units conjugates these
mates by isomorphisms, so they remain isomorphisms. No flatness, finite generation,
or nonempty-space hypothesis is used; zero modules and the empty scheme obey the
same formulas. -/
theorem globalTensorPullback_mates_isIso
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace) :
    IsIso ((adj.homEquiv (𝟙_ _) (𝟙_ _)).symm
      (ModuleCat.ofHom (unitSectionsEquiv (X := X) ⊤).toLinearMap)) ∧
    ∀ A B : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)),
      IsIso ((adj.homEquiv _ _).symm
        ((adj.unit.app A ⊗ₘ adj.unit.app B) ≫
          moduleCup_sectionTensorMap X (P.obj A) (P.obj B))) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
