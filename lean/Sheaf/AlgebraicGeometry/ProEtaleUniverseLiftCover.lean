/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.AlgebraicGeometry.SchemeUniverseEnlargement
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fpqc covers after canonical universe enlargement

Source: Bhatt--Scholze, Definition 4.1.1; Stacks Project, Tags 01JA and 022B
(blueprint: lem-a1-universe-enlarged-proetale-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Canonical universe enlargement transports fpqc covering families.
This allows empty covers of the empty base, arbitrary index sets in the larger
universe, and families whose individual arrows are not quasi-compact.

Source: Stacks Project, Tags 01JA and 022B, the definition of fpqc covering and
its affine recognition criterion
(blueprint: lem-a1-universe-enlarged-proetale-cover).

Proof: on affine charts canonical enlargement replaces A by its ring-equivalent
ULift A. The prime-spectrum equivalence identifies affine opens and their images;
flatness of each ring map is unchanged under these ring equivalences. Cover the
base by its affine opens and use the affine recognition criterion for fpqc covers.
The finitely many affine opens of the sources witnessing the original covering
condition transport to affine opens with the same union of images in each base
chart. The affine-colimit universal property identifies the transported chart
maps with schemeUniverseLiftMap. These finite refinements give the quasi-compact
covering condition. Joint surjectivity follows from their union on each base
chart. No quasi-compactness of an individual family member is asserted.
The empty family covers only the empty base, and its transport is again empty. -/
theorem fpqc_cover_universeLift (X : Scheme.{u})
    {I : Type (u + 1)} (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ X)
    (hcover : Presieve.ofArrows U f ∈ fpqcPrecoverage X) :
    Presieve.ofArrows (fun i ↦ schemeUniverseLift.{u, u + 1} (U i))
      (fun i ↦ schemeUniverseLiftMap.{u, u + 1} (f i)) ∈
        fpqcPrecoverage (schemeUniverseLift.{u, u + 1} X) := by
  sorry

end AlgebraicGeometry.Scheme
