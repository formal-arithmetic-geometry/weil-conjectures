/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
import Sheaf.Topology.LocallyConstantMapsSheaf

/-!
# The locally constant description of the constant abelian sheaf

Source: literature/stacks-project/sheaves.tex, Definition 006W and Example 0081.
(blueprint: lem-sc-constant-sheaf-locally-constant-comparison)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace TopCat

/-- The constant abelian sheaf is naturally the group of locally constant maps on opens.

Source: literature/stacks-project/sheaves.tex, Definition 006W and Example 0081.
(blueprint: lem-sc-constant-sheaf-locally-constant-comparison)
Proof: give locally constant maps pointwise addition and restriction by precomposition.
Compatible maps on an open cover glue pointwise, and the glued map is locally constant,
so this is an abelian sheaf. Send each element of the constant presheaf to its constant
map. For any morphism from the constant presheaf to an abelian sheaf G, send a locally
constant map f to the section obtained by gluing the images of its values on an open
cover where f is constant. On a nonempty overlap the two values agree; on an empty
one the sheaf has a unique section. The result is independent of the chosen cover,
by passage to a common refinement and uniqueness of gluing. Addition and restriction
commute with this construction, as can be checked on the same covers. Conversely,
a morphism extending the constant maps must have these values locally, hence globally
by the uniqueness part of the sheaf condition. Thus this construction has the universal
property of sheafification. Uniqueness of sheafification identifies it with
`constantSheaf`, by additive equivalences commuting with every restriction. This argument
uses neither irreducibility nor nonemptiness of opens; in particular the sections on the
empty open are the trivial group, as are the locally constant maps from the empty set. -/
theorem constantSheaf_locallyConstant_comparison
    (X : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (A : Type v) [AddCommGroup A] :
    ∃ e : ∀ U : Opens X,
      AddEquiv (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of A)).1.obj (op U)) (LocallyConstant U A),
      ∀ (U V : Opens X) (hVU : V ≤ U) (s :
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of A)).1.obj (op U)) (x : V),
        e V (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of A)).1.map (homOfLE hVU).op s) x =
            e U s ⟨x.1, hVU x.2⟩ := by
  sorry

end TopCat
