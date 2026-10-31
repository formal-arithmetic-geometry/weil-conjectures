/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.QuasiAffine
import WeilConjectures.AlgebraicGeometry.QuasiAffineOpenPrincipalComparisonCover
import WeilConjectures.Topology.ProconstructibleClosureSpecialization
import Mathlib.Topology.Constructible
import Mathlib.Topology.Spectral.Basic

/-! # Quasi-affine neighbourhoods of quasi-compact flat monomorphisms

Source: Michel Raynaud, Un critère d'effectivité de descente, §3, Proposition 3.4
(heading 3.5 in the primary scan), printed pp.14–15
(blueprint: lem-sfb-flat-monomorphism-quasiaffine-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact flat monomorphism from a quasi-affine scheme into a quasi-separated
scheme has image contained in a quasi-compact quasi-affine open subscheme of the target.
There is no local finite-presentation or Noetherian hypothesis.

Source: Michel Raynaud, Un critère d'effectivité de descente, §3, Proposition 3.4
(heading 3.5 in the primary scan), printed pp.14–15
(blueprint: lem-sfb-flat-monomorphism-quasiaffine-neighbourhood).

Proof:
1. Put E = f(X). It is quasi-compact and stable under generalization by
   lem-sfb-proopen-global-section-extension. For y in E choose x above y and an affine
   open A containing y. Apply lem-a1-quasi-affine-open-principal-comparison-cover to
   f⁻¹(A) → X to find a global section a with x in the affine basic open X_a ⊆ f⁻¹(A).
2. By lem-sfb-proopen-global-section-extension, extend a to a section g on a quasi-compact
   open V containing E. Local homomorphisms reflect units, giving f⁻¹(V_g) = X_a.
   Thus y lies in V_g and E ∩ V_g is contained in A.
3. The difference F = V_g ∖ A is constructible in V, using
   def-weil-constructible-subset and quasi-separatedness. By
   lem-weil-pbc-qcqs-scheme-spectral, V is spectral. Apply
   lem-weil-pbc-spectral-proconstructible-closure-specialization to the singleton
   family F: if closure(F) met E, a point of F would generalize a point of E, contrary
   to generalization stability and F ∩ E = ∅. Choose a quasi-compact open W containing
   E in V ∖ closure(F). Then W ∩ V_g is a quasi-compact open of A, hence quasi-affine,
   and contains y. It is the basic open of the restriction of g to W.
4. These W and restricted sections satisfy condition (ii) of
   lem-sfb-quasiaffine-principal-neighbourhood-criterion. Its implication to (i)
   supplies U. When X is empty take the empty open, the spectrum of the zero ring. -/
theorem exists_quasiAffine_open_neighbourhood_of_flat_mono
    {X T : Scheme.{u}} (f : X ⟶ T) [QuasiCompact f] [Flat f] [Mono f]
    [X.IsQuasiAffine] [QuasiSeparatedSpace T] :
    ∃ U : T.Opens, IsCompact (U : Set T) ∧ U.toScheme.IsQuasiAffine ∧
      Set.range f ⊆ (U : Set T) := by
  sorry

end AlgebraicGeometry.Scheme
