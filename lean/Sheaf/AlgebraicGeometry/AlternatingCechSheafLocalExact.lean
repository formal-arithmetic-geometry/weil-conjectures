/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSheafConstruction
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Exactness of the local alternating complex

Source: Stacks Project, Tag 02FU (cohomology-lemma-covering-resolution),
with increasing tuples as in Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-local-exact).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Positive-degree local exactness, without choosing any splittings.
Source: Stacks Project, Tag 02FU (cohomology-lemma-covering-resolution),
adapted to the increasing-tuple convention of Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-local-exact).

Proof: On an open V contained in U i, let z be a positive-degree cocycle.
For an increasing tuple t omitting i, define its primitive by the coordinate
of z obtained by inserting i in position b, multiplied by (-1)^b.
For a tuple containing i, set the primitive coordinate to zero. Insertion
leaves V intersect the tuple intersection unchanged, so these are linear
maps commuting with restrictions. The cocycle equation evaluated on the
inserted tuple says that the signed face sum of this primitive is z:
the face deleting i has coefficient (-1)^b twice and all other faces give
the cocycle equation. For a tuple containing i, the only nonzero face is
its deletion of i, again with sign squared equal to one. Thus the kernel
of each positive differential is the image of the preceding differential
on every test open. The intersection presheaf V ↦ G(V intersect W) is
already a sheaf: it is the direct image of the restriction to W. Its finite
products are sheaves as well. Hence the sheafification unit on each term is
an isomorphism, natural with respect to the face differential. Restrict
these units to U i to identify the specified sheaf complex with the complex
just computed. Kernel sheaves are sectionwise kernels, and the sectionwise
boundary formula makes the map to the kernel an epimorphism. Transport along
extendXIso identifies the adjacent integer degrees with these nonnegative
degrees. This proves exactness of the indicated short complex. No degree-zero
assertion or splitting is used. If V is empty all sections vanish; if r=0
there is no i; beyond the maximum tuple length the middle term is zero. -/
theorem alternatingCechSheaf_restrict_local_exact
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (k : ℤ) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    0 < k → (C.sc' (k - 1) k (k + 1)).Exact := by sorry

end AlgebraicGeometry
