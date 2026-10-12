/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # Coherence of the module pullback tensor comparison

Source: Stacks Project, Modules, Tag 01CD; Cohomology, Tag 079U and Section 20.27
(blueprint: lem-pc-module-pullback-tensor-coherence).
-/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

noncomputable local instance pullbackCoherenceModuleTensor (S : Scheme.{uModel}) :
    MonoidalCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.monoidalCategory S.sheaf

/-- The recorded module pullback tensor comparison is coherent with a unit comparison.
Source: Stacks Project, Modules, Tag 01CD; Cohomology, Tag 079U and Section 20.27
(blueprint: lem-pc-module-pullback-tensor-coherence).
Proof: identify F with tensor-formula pullback using hF and hmap. On local pure tensors,
the comparison sends a pullback of s tensor t to the tensor of their pullbacks, by the
section formula of module_pullback_tensor. Thus its two iterates on three factors agree
with the associator: both send a pure triple tensor to the same triple tensor. Equality
extends by linearity, the tensor universal property, and sheafification. The structure
sheaf is taken to the structure sheaf by multiplication after extension of scalars;
the inverse sends a local section a to a tensor 1. These maps are inverse by the balanced
tensor relations. The left and right unit diagrams reduce on pure tensors to 1 times s
and s times 1. Invert the recorded tensor comparisons and use this unit isomorphism to
form CoreMonoidal. Transport along the identification of F gives exactly the displayed
conjugation by eqToHom. No exactness of pullback is required. -/
theorem modulePullback_tensor_coherent {T X : Scheme.{uModel}} (g : T ⟶ X)
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    : ∃ mF : F.CoreMonoidal,
    ∀ M N, (mF.μIso M N).inv = eqToHom (hF _) ≫
      ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) M N).hom ≫
      (eqToHom (hF M).symm ⊗ₘ eqToHom (hF N).symm) := by sorry

end AlgebraicGeometry
