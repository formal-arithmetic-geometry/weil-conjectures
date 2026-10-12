/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf
public import Mathlib.Topology.Sheaves.Stalks
import Sheaf.Topology.NestedSliceExtensionStalkIso

/-! # Stalks of nested slice extensions

Source: Stacks Project, Cohomology, Lemma 0A38 final paragraph; Sheaves, Lemma 00A5.
(blueprint: new-lem-sc-nested-slice-extension-stalks).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- Nested slice extensions of a sheaf admit a map inducing isomorphisms at interior points.
Source: Stacks Project, Cohomology, Lemma 0A38 final paragraph; Sheaves, Lemma 00A5.

Proof: at an open W, send the direct-sum injection indexed by φ : W → V to the
injection indexed by φ followed by V → U, acting identically on F(W). The restriction
maps on both sides precompose the index and restrict the section by F, so naturality
follows from associativity and direct-sum extensionality. On W contained in V, the
index types W → V and W → U are both singleton, and the map is the identity on their
unique summands. Every germ at x in V can be represented on an open contained in V,
by intersecting with V. This proves stalk surjectivity. For injectivity, represent two
germs on such opens, and restrict further to a common neighborhood where equality
of image germs is witnessed. Intersect this neighborhood with V; there the component
map is injective, so the original germs are equal. Bijectivity gives an isomorphism of
abelian groups. Empty V gives a vacuous condition, V = U gives identity reindexing,
and the argument does not assume connectedness or constancy of F.
(blueprint: new-lem-sc-nested-slice-extension-stalks). -/
theorem nested_slice_extension_stalks {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) (hVU : V ≤ U) :
    ∃ g : (siteExtensionByZeroPresheaf V).obj (F.over V).obj ⟶
        (siteExtensionByZeroPresheaf U).obj (F.over U).obj,
      ∀ x : X, x ∈ V →
        IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map g) := by
  refine ⟨nestedSliceExtensionMap F U V hVU, ?_⟩
  exact nestedSliceExtensionMap_stalk_isIso F U V hVU

end TopCat.Sheaf
