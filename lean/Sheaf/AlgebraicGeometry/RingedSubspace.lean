/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Sheaves.Functors

/-!
# Ringed subspaces with the inverse-image structure sheaf

Source: Stacks Project, Tag 0API, the space `(E, O_X|E)`.
(blueprint: def-a1-ringed-subspace)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace

/-- The inclusion of an arbitrary subset, with its subspace topology.
Source: Stacks Project, Tag 0API (blueprint: def-a1-ringed-subspace). -/
def subspaceInclusion (X : LocallyRingedSpace.{u}) (S : Set X) :
    TopCat.of S ⟶ X.toTopCat :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The ringed subspace uses the inverse-image sheaf, even when `S` is not open.
Source: Stacks Project, Tag 0API (blueprint: def-a1-ringed-subspace). -/
noncomputable def ringedSubspace (X : LocallyRingedSpace.{u}) (S : Set X) :
    SheafedSpace CommRingCat.{u} where
  carrier := TopCat.of S
  presheaf := ((TopCat.Sheaf.pullback CommRingCat (subspaceInclusion X S)).obj X.sheaf).obj
  IsSheaf := ((TopCat.Sheaf.pullback CommRingCat (subspaceInclusion X S)).obj X.sheaf).property

/-- The ringed-space inclusion is induced by the inverse-image adjunction unit.
Source: Stacks Project, Tag 0API (blueprint: def-a1-ringed-subspace). -/
noncomputable def ringedSubspaceι (X : LocallyRingedSpace.{u}) (S : Set X) :
    ringedSubspace X S ⟶ X.toSheafedSpace :=
  InducedCategory.homMk
    { base := subspaceInclusion X S
      c := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
        (subspaceInclusion X S)).unit.app X.sheaf).hom }

/-- Bundle the ringed subspace as locally ringed once locality of its stalks is supplied.
This argument is proof data only; the topology and sheaf are the explicit constructions above.
Source: Stacks Project, Tag 0API (blueprint: def-a1-ringed-subspace). -/
noncomputable def locallyRingedSubspace (X : LocallyRingedSpace.{u}) (S : Set X)
    (h : ∀ x : S, IsLocalRing ((ringedSubspace X S).presheaf.stalk x)) :
    LocallyRingedSpace.{u} where
  toSheafedSpace := ringedSubspace X S
  isLocalRing := h

end AlgebraicGeometry.LocallyRingedSpace
