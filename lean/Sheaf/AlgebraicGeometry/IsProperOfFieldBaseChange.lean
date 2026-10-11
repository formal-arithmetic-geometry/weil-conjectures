/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-!
# Properness descends along a field extension

Source: Stacks Project, Descent, Lemma 35.23.16 (Tag 02L1), specialized to a field extension
(blueprint: lem-pc-proper-descends-field).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite type scheme over a field is proper if its base change to an extension field is
proper. Source: Stacks Project, Descent, Tag 02L1 (lemma-descending-property-proper)
(blueprint: lem-pc-proper-descends-field).

Proof:
1. The map `Spec K → Spec k` is flat, surjective and quasi-compact, so its singleton family
   is an fpqc cover (lem-pc-field-extension-fpqc-cover). Its base change of `f` is the second
   pullback projection (def-pc-base-change), which is proper by hypothesis.
2. Properness of this projection implies separatedness (def-weil-proper-morphism).
   Separatedness descends along the cover (lem-weil-pbc-fpqc-descend-separated).
3. Properness of the projection also implies universal closedness (def-weil-proper-morphism),
   which descends along the same cover (lem-weil-pbc-fpqc-descend-universally-closed).
4. The structure morphism `f` is of finite type by hypothesis (def-pc-scheme,
   def-weil-finite-type-morphism). Together with separatedness and universal closedness,
   this gives properness by definition (def-weil-proper-morphism). -/
theorem isProper_of_field_baseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))] :
    IsProper f := by
  sorry

end AlgebraicGeometry
