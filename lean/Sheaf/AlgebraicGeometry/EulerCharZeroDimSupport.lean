/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.FiniteSchemeCohomologyTensor
import Sheaf.AlgebraicGeometry.ZeroSupportFiniteScheme
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Euler characteristic of modules with zero-dimensional support

Source: Stacks Project, Varieties, Tag 0AYT, parts (3)--(5), with rank one
(blueprint: lem-pc-chi-zero-dim-support).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module with zero-dimensional support on a proper scheme over a field has
no positive cohomology. Its Euler characteristic is the dimension of its global sections.
Tensoring with an invertible module preserves coherence, support and Euler characteristic.
Source: Stacks Project, Varieties, Tag 0AYT, parts (3)--(5), with rank one
(blueprint: lem-pc-chi-zero-dim-support).

Proof:
1. Properness implies finite type (`def-weil-proper-morphism`). Coherence
   (`pqf-def-coherent`) makes the support closed. The dimension hypothesis and
   `lem-sc-dim0-finite` make it a finite set of closed points.
2. By `lem-pc-zero-support-finite-scheme`, write the module as the pushforward of a
   coherent module on a finite affine closed subscheme Spec A. The projection formula
   identifies its tensor with an invertible module with the corresponding pushforward
   on Spec A; coherence and support are preserved.
3. The algebra A is finite dimensional. By `lem-pc-finite-scheme-cohomology-tensor`,
   positive cohomology vanishes, global sections are finite dimensional, and tensoring
   with the restricted invertible module preserves their dimension. Transport these
   facts using the cohomology identifications of `lem-pc-zero-support-finite-scheme`.
4. In the sum of `def-pc-euler-characteristic`, only degree zero survives, and degree-zero
   cohomology is global sections. The dimension equality from step 3 gives tensor
   invariance of the Euler characteristic. -/
theorem eulerChar_zero_dim_support (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hdim : topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ≤ 0) :
    (∀ i : ℕ, 0 < i → Subsingleton (F.H i)) ∧
    F.eulerChar k = (Module.finrank k (F.H 0) : ℤ) ∧
    Module.finrank k (F.H 0) =
      @Module.finrank k Γ(F, ⊤) _ _ (Module.compHom Γ(F, ⊤) (globalSectionsRingHom k (X := X))) ∧
    (∀ (N : X.Modules) [N.IsInvertible],
      RingedSpace.IsCoherent X.toRingedSpace (F ⊗ N : X.Modules) ∧
      {x : X | ¬ Subsingleton ((F ⊗ N).presheaf.stalk x)} =
        {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      (F ⊗ N).eulerChar k = F.eulerChar k) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
