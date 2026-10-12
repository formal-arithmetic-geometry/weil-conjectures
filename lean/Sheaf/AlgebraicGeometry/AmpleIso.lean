/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # Ampleness is invariant under module isomorphisms

Source: Stacks Project, Properties, Definition 01PS.
(blueprint: lem-sc-ample-iso).
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Isomorphic invertible modules have the same ampleness predicate.
Source: Stacks Project, Properties, Definition 01PS and Section 01PR.
(blueprint: lem-sc-ample-iso).

Proof: an isomorphism induces isomorphisms of every tensor power, compatible with
restriction and hence with germs. Use the inverse tensor-power isomorphism to
transport a global section of `N` to one of `L`. At every point the induced stalk
isomorphism is linear over the local ring and maps the maximal ideal times the
whole stalk onto the corresponding submodule. Thus the transported section has
exactly the same nonvanishing locus. The same affine open and positive exponent
witness ampleness at each point; compactness is unchanged. Apply this argument to
the inverse isomorphism for the converse. This also works on the empty scheme.
-/
theorem isAmple_iff_of_iso {X : Scheme.{u}} {L N : X.Modules}
    [L.IsInvertible] [N.IsInvertible] (e : L ≅ N) :
    IsAmple X L ↔ IsAmple X N := by
  sorry

end AlgebraicGeometry.Scheme.Modules
