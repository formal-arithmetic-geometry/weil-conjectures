/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree

/-! # Natural comparison with the source library's ordinary cohomology

Source: Stacks Project, Tag 03FD, and the Ext definition of sheaf cohomology.
(blueprint: lem-sc-module-cohomology-source-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Module right-derived sections agree naturally with the ordinary Ext model H.
Source: Stacks Project, Tag 03FD, Lemma 21.12.4; Mathlib's constant-sheaf and
free-abelian-Yoneda adjunctions identify the two terminal Ext source objects.
(blueprint: lem-sc-module-cohomology-source-comparison)

Proof: Use zariskiModuleAbelianCohomologyAgree to compare module right-derived
sections with Ext from the sheafified free abelian representable at the top open.
That source object is canonically isomorphic to the constant integer sheaf:
for every abelian sheaf A, the free-abelian-Yoneda/sheafification adjunctions
identify maps from the former with A(top); the constant-sheaf adjunction identifies
maps from the latter with the same group, by evaluation at 1. These additive
identifications are natural in A, so Yoneda yields the source isomorphism.
Precomposition by it identifies the Ext groups, naturally in the target sheaf,
in every degree. Reindex any differing HasExt models using homAddEquiv through
the same derived category; postcomposition commutes with this reindexing.
Compose the natural isomorphisms and forget the module structure on the first
group. The resulting naturality square is exactly H.map, since H and H.map are
defined using the underlying abelian sheaf. This construction includes q=0,
zero modules and the empty scheme. No quasi-coherence is required. -/
theorem exists_moduleCohomology_source_comparison (X : Scheme.{u}) (q : ℕ) :
    ∃ e : ∀ F : X.Modules,
        ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+ H F q,
      ∀ (F G : X.Modules) (φ : F ⟶ G)
          (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F),
        e G (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x) =
          H.map φ q (e F x) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
