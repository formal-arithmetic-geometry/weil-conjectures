/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

import Sheaf.AlgebraicGeometry.ConductorIdealRestriction
import Sheaf.AlgebraicGeometry.ConductorIdealZeroIntersection
import Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Additive restriction on conductor tensor sections -/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction on conductor tensor sections is an additive bijection compatible with
inclusion into the ambient tensor power.

Source: Stacks Project, Varieties Remark 09NW and the displayed equality in Lemma 09NX.
(blueprint: lem-sc-conductor-sections-restriction).

Proof: use conductorIdealZeroIntersection on the component cover. Identify the image of
its adjoint ideal map with the module of the ideal comap, by the closed-immersion quotient
calculation and conductorIdeal_restriction_isIso. Tensor pullback commutes with tensor
powers; transport the stated bijection of image sheaves through that comparison. The
ideal multiplication maps are monomorphisms because the tensor powers are invertible,
so their corestrictions to their categorical images are isomorphisms. Evaluate these
isomorphisms and the conductor restriction morphism on the top open. Their composite is
an additive bijection between the ideal tensor sections. The commutative square in the
zero-intersection theorem, transported through the comparisons, gives compatibility
with the canonical unit of tensor pullback. The canonical unit is fixed by its explicit
section formula, so the restriction used here is the stated one. -/
theorem conductor_sections_restriction {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (C : ι → Scheme.{u}) (i : ∀ b : ι, C b ⟶ Y)
    [∀ b : ι, IsReduced (C b)] [∀ b : ι, IsClosedImmersion (i b)]
    (hcomponents : ∀ b : ι, Set.range (i b) ∈ irreducibleComponents Y)
    (hdistinct : Function.Injective fun b : ι => Set.range (i b))
    (hcover : (⋃ b : ι, Set.range (i b)) = Set.univ) (a : ι)
    {Z : Scheme.{u}} [IsReduced Z] (j : Z ⟶ Y) [IsClosedImmersion j]
    (hZ : Set.range j = ⋃ b : ι, ⋃ (_ : b ≠ a), Set.range (i b))
    (M : Y.Modules) [M.IsInvertible] (m : ℕ) :
    let N := M.tensorPow m
    let N₁ := (tensorPullback (i a)).obj N
    let adj₁ := Classical.choose (exists_tensorPullbackAdjunction (i a))
    let res₁ : Γ(N, ⊤) → Γ(N₁, ⊤) := fun t ↦ (adj₁.unit.app N).val.app (op ⊤) t
    let I := j.ker
    let I₁ := I.comap (i a)
    let μ : I.toModules ⊗ N ⟶ N := I.toModulesι ▷ N ≫ (λ_ N).hom
    let μ₁ : I₁.toModules ⊗ N₁ ⟶ N₁ := I₁.toModulesι ▷ N₁ ≫ (λ_ N₁).hom
    ∃ r : Γ(I.toModules ⊗ N, ⊤) →+ Γ(I₁.toModules ⊗ N₁, ⊤),
      Function.Bijective r ∧ ∀ s, μ₁.app ⊤ (r s) = res₁ (μ.app ⊤ s) := by sorry

end AlgebraicGeometry.Scheme.Modules
