/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The ordinary projection formula for a closed structure sheaf

Source: Stacks Project, Modules, Tags 08KS and 01CB; Sheaves, Tag 0098.
(blueprint: lem-pc-closed-structure-tensor-projection). -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 512
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- The closed-immersion ordinary projection formula, natural in the module.
Source: Stacks Project, Modules, Tags 08KS and 01CB; Sheaves, Tag 0098 for pullback stalks.
(blueprint: lem-pc-closed-structure-tensor-projection).

Proof: use the canonical tensor-pullback adjunction. For an open V of Y, a section
s of M over V, and a section r of O_Z over i^{-1}V, pair them by multiplying r
with the pullback unit applied to s. This is bilinear over O_Y(V), with the
pushforward scalar action, and commutes with restriction. It induces a map from
the sectionwise tensor presheaf to i_*i^*M, and sheafification gives a map
M tensor i_*O_Z -> i_*i^*M. At i(z), the tensor-stalk and closed-pushforward
comparisons identify the source with M_{i(z)} tensor O_{Z,z}; the pullback-stalk
and closed-pushforward comparisons identify the target with O_{Z,z} tensor M_{i(z)}.
The germ formulas show that the map sends m tensor r to r tensor m, the scalar
extension symmetry isomorphism. Off the closed image both stalks are zero,
as witnessed by the open complement. Stalks jointly reflect isomorphisms, so
all components are invertible. The section pairing is natural in M, giving a
natural transformation; invert it componentwise to obtain a natural isomorphism.
No quasi-coherence or flatness is required. The identity immersion recovers the
right unitor, and the empty source gives the zero functor. -/
theorem nonempty_closedStructure_tensor_projection
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    Nonempty ((tensorRight B : SheafOfModules.{u} Y.ringCatSheaf ⥤
      SheafOfModules.{u} Y.ringCatSheaf) ≅
      Scheme.Modules.tensorPullback i ⋙ Scheme.Modules.pushforward i) := by
  sorry

end AlgebraicGeometry
