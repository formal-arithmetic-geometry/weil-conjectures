/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# The basis-normalized tensor pullback of a free module sheaf

Source: Stacks Project, sheaves.tex, Tag 0096,
`lemma-adjoint-pullback-pushforward-modules`; modules.tex, Tag 01C8,
`lemma-pullback-locally-free`
(blueprint: def-trf-tensor-pullback-free-basis-iso).

The coproduct comparison uses the pinned structure-sheaf map on every summand.
Its data is constructed with Mathlib's `mapFreeIso`, not chosen from existence.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical isomorphism from the tensor pullback of the free sheaf on `I`
to the free sheaf on the same basis. On the summand indexed by `i`, its map is
`tensorPullbackObjUnitToUnit g` followed by the `i`th free-sheaf inclusion.
The inverse is the coproduct comparison constructed by `SheafOfModules.mapFreeIso`.
Source: Stacks Project, Tags 0096 and 01C8
(blueprint: def-trf-tensor-pullback-free-basis-iso). -/
noncomputable def tensorPullbackFreeBasisIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (I : Type u) :
    (tensorPullback g).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I :=
  letI := (Classical.choose (exists_tensorPullbackAdjunction g)).isLeftAdjoint
  letI := (tensorPullbackObjUnitToUnit_isIso g).1
  (SheafOfModules.mapFreeIso (tensorPullback g) I
    (asIso (tensorPullbackObjUnitToUnit g)).symm).symm

end AlgebraicGeometry.Scheme.Modules
