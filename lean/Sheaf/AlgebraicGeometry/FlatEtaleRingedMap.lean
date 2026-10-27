/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.AlgebraicGeometry.SmallEnlargedEtaleModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Flatness of the canonical ringed étale morphism

Source: Stacks Project, Morphisms of Spaces, Tag 073C, and Modules on Sites, Tag 03ER
(blueprint: def-sfb-flat-etale-ringed-map).

Scalar extension is specified by its adjunction to the actual restriction of scalars.
Its ring map is the adjoint of the canonical chart-normalized structural map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Flatness of the canonical ringed étale morphism, written as exact scalar extension.
The inverse-image ring functor is specified by adjunction to the EXISTING canonical
ring direct image. The structural ring map is its adjoint, so it cannot vary freely.
The scalar-extension functor is specified by adjunction to restriction along that map;
this is exactly O_X tensor over h^{-1}O_Y. Exactness of this functor is flatness of O_X
as an h^{-1}O_Y-module, in the sense of [def-pc-flat-sheaf-modules]. The enlarged-site
model is equivalent by restriction to the small étale model, with unchanged modules.
Source: Stacks, Tags 073C, 03G1, 03H7, 03ER and 03EK
(blueprint: def-sfb-flat-etale-ringed-map). -/
def IsFlatEtaleRingedMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∃ (I : Sheaf Y.enlargedEtaleTopology RingCat.{u} ⥤
      Sheaf X.enlargedEtaleTopology RingCat.{u})
    (a : I ⊣ enlargedDirectImage f RingCat.{u}),
    ∃ E : SheafOfModules.{u} (I.obj Y.enlargedStructureSheaf) ⥤
        SheafOfModules.{u} X.enlargedStructureSheaf,
      Nonempty (E ⊣ SheafOfModules.restrictScalars
        ((a.homEquiv Y.enlargedStructureSheaf X.enlargedStructureSheaf).symm
          (enlargedStructuralMap f))) ∧ exactFunctor _ _ E

end AlgebraicGeometry.AlgebraicSpace
