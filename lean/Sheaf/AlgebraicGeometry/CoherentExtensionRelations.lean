/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Coherent ExtensionRelations

Source: Stacks Project, Modules, Lemma 01BY
(blueprint: lem-weil-pbc-coherent-extension-relations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Relations in the middle term of an extension of coherent modules are of finite type.
Source: Stacks Project, Modules, Lemma 01BY (lemma-coherent-abelian), proof of (4),
the relation-kernel diagram (blueprint: lem-weil-pbc-coherent-extension-relations).

Proof: Restrict the short exact sequence to U and compose g with the quotient map.
The kernel K3 of this composite is finite type by coherence of the last term,
which remains coherent on restriction to U. The composite of K3 into the middle
term lands in the first term because its image in the last term is zero. Exactness
identifies the kernel K of g with the kernel of this induced map K3 to the first
term on U. The first term remains coherent on restriction, so part (2) of Lemma
01BY makes K finite type. Equivalently, the snake lemma applied to the diagram
with top row zero-free-free and identity gives the exact sequence
zero-K-K3-first. This assertion concerns only the relation kernels; finite type
of the middle term is supplied separately by Lemma 01B7. -/
theorem coherent_extension_relations (X : RingedSpace.{u})
    (S : ShortComplex (SheafOfModules.{u} (moduleRings X))) (hS : S.ShortExact)
    (h₁ : IsCoherent X S.X₁) (h₃ : IsCoherent X S.X₃)
    (U : Opens X) (n : ℕ)
    (g : SheafOfModules.free (R := (moduleRings X).over U) (ULift.{u} (Fin n)) ⟶
      S.X₂.over U) :
    (kernel g).IsFiniteType := by sorry

end AlgebraicGeometry.RingedSpace
