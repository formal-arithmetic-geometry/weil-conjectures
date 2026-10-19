/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree

/-!
# Exactness of tensoring by a finite locally free module

Source: the Picard-duality blueprint, proof of `lem-sc-ext-locally-free`; Stacks Project,
Tags 01C6 and 05NE (blueprint: lem-sc-ext-tensor-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensoring on the left by a finite locally free module is exact: it preserves finite
limits and finite colimits, equivalently short exact sequences in the abelian module category.
The local finite ranks may vary across the scheme.

Source: the Picard-duality blueprint, proof of `lem-sc-ext-locally-free`; Stacks Project,
Tags 01C6, 01CB, 01AG and 05NE (blueprint: lem-sc-ext-tensor-exact).

Proof:
1. For each point choose a neighbourhood trivializing `P` with finite rank `d`. Taking germs
   of its basis and coordinate maps identifies its stalk with the free stalk module of rank
   `d` (def-weil-pbc-module-stalk). No uniform rank is required.
2. The natural stalk-tensor comparison (lem-weil-pbc-module-stalk-tensor, Tag 01CB) identifies
   the stalk of `P` tensor a module and of its tensor maps with tensoring by this free module.
   This is the direct sum of `d` copies: send a basis tensor to its coordinate tuple and
   invert by summing the basis tensors, also for `d = 0`.
3. A short exact sequence is short exact on every stalk (lem-weil-pbc-module-stalk-exact,
   Tag 01AG). Finite direct sums preserve its kernels, images and surjectivity coordinatewise.
   Apply the reverse stalkwise criterion to obtain short exactness of the tensor sequence.
   Naturality ensures these are the actual tensor maps. In an abelian category, preservation
   of short exact sequences is equivalent to preservation of finite limits and colimits. -/
theorem finiteLocallyFree_tensorLeft_exact {X : Scheme.{u}} (P : X.Modules)
    [P.IsFiniteLocallyFree] :
    PreservesFiniteLimits (tensorLeft P) ∧ PreservesFiniteColimits (tensorLeft P) := by
  -- Finite locally free biduality identifies tensoring by P with internal Hom from its dual.
  have := IsFiniteLocallyFree.dual P
  have := SheafOfModules.isIso_bidual (R := X.sheaf) P
  let e : tensorLeft P ≅ ihom (dual P) :=
    (tensoringLeft X.Modules).mapIso (asIso (SheafOfModules.bidual (R := X.sheaf) P)) ≪≫
      NatIso.ofComponents (fun N ↦ asIso (dualTensorHom (dual P) N)) fun g ↦
        dualTensorHom_naturality_right (dual P) g
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
    (ihom.adjunction P).leftAdjoint_preservesColimits
  exact ⟨preservesFiniteLimits_of_natIso e.symm, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
