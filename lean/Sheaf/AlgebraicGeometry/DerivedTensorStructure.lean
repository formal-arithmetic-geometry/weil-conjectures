/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Derived tensor structure on O_X-modules

Source: Stacks Project, Cohomology, Tags 06Y7, 06YH and 03EO
(blueprint: def-pc-scheme-derived-tensor-structure).
The tensor is the upstream K-flat derived monoidal construction, specialized to the
shared category of O_X-modules, rather than an arbitrary monoidal structure.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The recorded sheaf tensor structure, specialized to O_X.
Source: Stacks, 06Y7 (blueprint: def-pc-scheme-derived-tensor-structure). -/
noncomputable local instance moduleTensor :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- O_X-modules admit functorial flat resolutions. Source: Stacks, 06Y7
(blueprint: def-pc-scheme-derived-tensor-structure).
Proof: take the sum of extension-by-zero free modules indexed by all local sections
on all opens, with its evaluation epimorphism. These modules are flat on stalks.
Iterate the construction on kernels. Maps of modules act on the section indices,
so this resolution is functorial. -/
theorem schemeModule_hasFunctorialFlatResolution :
    Abelian.HasFunctorialFlatResolution
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := by
  sorry

/-- The K-flat derived tensor monoidal structure on D(O_X): the upstream derived monoidal
structure of the localization `Qh` of the homotopy category, for the recorded sheaf tensor
`SheafOfModules.monoidalCategory X.sheaf` with its symmetry. The additivity and closedness
of that tensor (the first two clauses of `SheafOfModules.tensorClosed`,
lem-pc-sheaf-modules-tensor-closed), the Grothendieck structure and the functorial flat resolutions
(`schemeModule_hasFunctorialFlatResolution`) enter only as propositions used by the
construction; its tensor on objects and morphisms is the K-flat derived tensor.
It is a global instance, so every statement about `schemeDerivedCategory X` uses this one
monoidal structure.
Source: Stacks, 06YH (blueprint: def-pc-scheme-derived-tensor-structure). -/
@[instance_reducible]
noncomputable def schemeDerivedTensorMonoidal
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    MonoidalCategory (schemeDerivedCategory X) := by
  letI := SheafOfModules.symmetricCategory X.sheaf
  haveI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  haveI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  haveI := schemeModule_hasFunctorialFlatResolution X
  haveI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  exact inferInstanceAs (MonoidalCategory
    (DerivedMonoidal (DerivedCategory.Qh
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))))

attribute [instance] schemeDerivedTensorMonoidal

end AlgebraicGeometry
