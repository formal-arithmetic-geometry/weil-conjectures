/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Local retractions of transposed epimorphisms

Source: Stacks Project, Tag 0EKP, proof of (2) to (3), local splitting of the quotient.
(blueprint: lem-sbc-dual-map-local-retraction)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The transpose of an epimorphism onto a finite locally free module is locally split.

Source: Stacks Project, Tag 0EKP, proof of (2) to (3), local splitting of the quotient.
(blueprint: lem-sbc-dual-map-local-retraction)

Proof: Around a point trivialize Q with a finite basis. An epimorphism of sheaves is
locally surjective, so each basis section lifts on a neighbourhood of the point.
Intersect these finitely many neighbourhoods; the lifted basis defines a section of
f on that neighbourhood. Precomposition with this section retracts precomposition
with f. Restriction of internal Hom identifies these maps with the restriction of
dualMap f, giving its retraction. No quasi-coherence of P is needed. For rank zero the
unique map from the zero module is already a section; the empty scheme has no points.
-/
theorem exists_local_retraction_dualMap_of_epi
    {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q) [Epi f] [Q.IsFiniteLocallyFree] :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map (dualMap f)) := by sorry

end AlgebraicGeometry.Scheme.Modules
