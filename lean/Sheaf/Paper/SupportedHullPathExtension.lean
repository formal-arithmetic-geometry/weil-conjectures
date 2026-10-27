/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.Paper.SupportedImageGenerationHull

/-! # Support extension preserves generated modules

Source: step 6 of lem-sfb-supported-image-bounded-derived-generation, an
agent-formulated structural input below blueprint refinement (2), first paragraph.
Exact reference WANTED; HRS Section 4.1 supplies the component-site setting only.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Extending a degree-zero object in the supported hull along a finite support
path preserves its membership. No finite-model condition on the module is imposed.
Source: step 6 of lem-sfb-supported-image-bounded-derived-generation;
Stacks Tags 09AA, 09AH and 09BN for the open and closed operations.
(blueprint: lem-sfb-supported-hull-path-extension).

Proof: each edge functor is exact. For open edges, extension by zero preserves
ordinary derived products by the open-extension limits theorem and preserves
sheaf colimits as a left adjoint. For closed edges it preserves derived products
as the right adjoint of exact inverse image, and filtered sheaf colimits by qcqs
continuity with quasi-compact complement. Applying either edge termwise to
complexes preserves a common lower bound. Exactness gives compatibility with
localization, shifts and distinguished triangles; functoriality preserves
retracts. Concatenate a source support path with the edge, completing the
resulting finite chain to a binary open-closed tree with complementary sibling
leaves. Thus supported finite scalar generators on the source go to supported
finite scalar generators on the target. The inverse image of every admissible
target class is therefore an admissible source class. Apply the defining
intersection, then induct on the path. At a root the functor is the identity.
Specialize the derived statement to N[0], using exactness to identify its image
with the degree-zero object of the ordinary extension. Empty schemes and zero
modules are included, and no coefficient admissibility assumption is needed.
-/
theorem supported_hull_path_extension
    {X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hN : supportedImageGenerationHull Λ S ((DerivedCategory.singleFunctor _ 0).obj N)) :
    supportedImageGenerationHull Λ X
      ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj N)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
