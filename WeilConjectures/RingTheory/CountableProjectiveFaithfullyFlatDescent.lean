/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Data.Set.Countable
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.IsMittagLeffler
import WeilConjectures.RingTheory.MittagLefflerFaithfullyFlatDescent
import WeilConjectures.SecTraceFormula.CountableFlatMittagLefflerProjective

/-!
# Faithfully flat descent of countably generated projective modules

Source: Stacks Project, Algebra, Tag 05A6, `lemma-ffdescent-countable-projectivity`.
(blueprint: lem-trf-countable-projective-faithfully-flat-descent)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Module

/-- Countable generation and projectivity descend along a faithfully flat ring map.
Countable generation is expressed by an at most countable subset spanning the module.
The scalar extension has its standard first-factor `B`-action; no finite-generation or
finite-presentation hypothesis is imposed.

Source: Stacks Project, Algebra, Tag 05A6, `lemma-ffdescent-countable-projectivity`.
(blueprint: lem-trf-countable-projective-faithfully-flat-descent)

Proof:
1. Put `N = B ⊗[A] P`. Expand every member of a countable generating subset of `N`
   as a finite sum of pure tensors (`def-weil-pbc-module-tensor-product`). Their second
   factors form an at most countable subset of `P`. Let `P₀` be its span. The image of
   `B ⊗[A] P₀ → N` is a `B`-submodule containing every generator, hence the map is
   surjective. Faithful exactness (`def-weil-pbc-faithfully-flat-ring-map`) implies
   `P₀ = P`, proving countable generation, including the empty generating-set case
   (Stacks Tag 0GVD).
2. Projectivity of `N` implies flatness (`lem-weil-pbc-projective-module-flat`).
   Flatness descends to `P` by `lem-weil-pbc-flatness-descends-faithfully-flat`.
3. Split `N` off a free `B`-module `F` (`def-weil-pbc-projective-module`). For any
   family of modules, the tensor-to-product map for `F` is injective: in free
   coordinates, a finitely supported family of tuples vanishes when all its
   coordinates vanish. Naturality and the retraction transfer this injectivity
   to `N`, so `N` is Mittag-Leffler (`def-trf-mittag-leffler-module`).
4. Apply `lem-trf-mittag-leffler-faithfully-flat-descent` (Tag 05A5) to obtain the
   Mittag-Leffler property of `P`.
5. Apply `lem-trf-countable-flat-mittag-leffler-projective` (Tag 059X) to the
   countable generation, flatness and Mittag-Leffler property of `P`. This proves
   projectivity and, together with step 1, both conclusions. -/
theorem countablyGenerated_projective_of_faithfullyFlat
    (A : Type u) (B : Type v) (P : Type w)
    [CommRing A] [CommRing B] [AddCommGroup P] [Algebra A B] [Module A P]
    [Module.FaithfullyFlat A B]
    (hcountable : ∃ s : Set (B ⊗[A] P), s.Countable ∧ Submodule.span B s = ⊤)
    (hprojective : Module.Projective B (B ⊗[A] P)) :
    (∃ s : Set P, s.Countable ∧ Submodule.span A s = ⊤) ∧ Module.Projective A P := by
  sorry

end Module
