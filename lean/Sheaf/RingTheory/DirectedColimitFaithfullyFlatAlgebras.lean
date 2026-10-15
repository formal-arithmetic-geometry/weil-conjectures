/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise
import Sheaf.Algebra.Category.ModuleCat.FilteredColimitFlat

/-!
# Directed colimits of faithfully flat algebras

Source: Stacks Project, Algebra, Tag 090N, `lemma-colimit-faithfully-flat`
(blueprint: lem-weil-pbc-directed-colimit-faithfully-flat-algebras).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- A nonempty directed colimit of faithfully flat commutative `R`-algebras is
faithfully flat over `R`. No condition is imposed on the transition algebra maps.

Source: Stacks Project, Algebra, Tag 090N, `lemma-colimit-faithfully-flat`
(blueprint: lem-weil-pbc-directed-colimit-faithfully-flat-algebras).

Proof:
1. Each stage is flat by `def-weil-pbc-faithfully-flat-ring-map`. Forgetting the
   algebra colimit to modules and applying `lem-weil-pbc-filtered-colimit-flat-modules`
   makes the colimit flat over `R`.
2. For every maximal ideal `m` of `R`, every stage quotient by `m` is nonzero by
   `lem-weil-pbc-faithfully-flat-maximal-ideal-nonzero`. Apply
   `lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise` with `R / m`.
   If the class of one vanished in the colimit quotient, it would vanish at a
   later stage. Unitality of the transition maps contradicts the nonzero stage
   quotients. Thus the colimit quotient by `m` is nonzero.
3. Apply `lem-weil-pbc-flat-faithfully-flat-maximal-ideals` to the flat colimit
   and these nonzero maximal-ideal quotients to obtain faithful flatness. -/
theorem directedColimit_faithfullyFlat
    (R : Type u) [CommRing R]
    {I : Type v} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (F : I ⥤ CommAlgCat.{v, u} R) [HasColimit F]
    (hfaithful : ∀ i : I, Module.FaithfullyFlat R (F.obj i)) :
    Module.FaithfullyFlat R (colimit F : CommAlgCat.{v, u} R) := by
  sorry

end CommAlgCat
