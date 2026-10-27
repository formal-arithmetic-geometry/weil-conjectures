/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback

import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
import Sheaf.CategoryTheory.Sites.GrothendieckTopos
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization

/-!
# Weak uniformization of quasi-excellent schemes with a proper refinement

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VII, Theorem 1.1,
printed p.81, with empty boundary; Expose II, Theorem 3.2.1, ordinary case
(parameter 1), printed p.29 (blueprint: lem-per-qe-weak-uniformization-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- An integral Noetherian scheme covered by quasi-excellent affine charts has a finite
family of integral regular Noetherian alterations, with an integral proper surjective
refinement that factors through these alterations on a finite Zariski open cover.
Finiteness is imposed on the canonical generic stalk maps, without separability or
any restriction on their degrees.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, VII Theorem 1.1 (p.81), with
empty boundary, and II Theorem 3.2.1 (p.29), ordinary case with parameter 1
(blueprint: lem-per-qe-weak-uniformization-cover).

Proof plan, following the eight steps of the node:
1. Use def-per-ordinary-alteration-topology and its marked predicate U(S,Z).
   By lem-per-ordinary-uniformization-local-reduction, reduce bounded dimension
   induction, and then the unbounded case, to normal complete local domains.
2. In dimension zero the domain is a field. In dimension one,
   lem-sc-normal-dim1-dvr gives a DVR (def-sc-discrete-valuation-ring). Its spectrum
   is regular; the empty set or the closed point is an SNC boundary
   (def-trf-strict-normal-crossings-boundary). The identity gives U.
3. In dimension d at least two, assume U in dimensions at most d-1. Apply
   lem-per-complete-local-nodal-dimension-reduction to obtain a finite ordinary
   covering by excellent integral log regular pairs, whose Cartier ideals cut out
   the pulled-back marked closed subset (def-nagata-effective-cartier-ideal).
4. Apply lem-per-noetherian-log-pair-strict-resolution to each pair. Its proper
   birational map is a singleton ordinary alteration cover: its closed image
   contains a dense open and its function-field degree is one. Compose these
   covers using finite-type composition (lem-sfb-finite-type-composition-base-change)
   and covering-sieve transitivity (def-weil-pbc-topos).
5. The pulled-back Cartier ideal stays Cartier under these dominant integral maps.
   A local generator becomes a unit after inverting the boundary parameters.
   By lem-trf-regular-local-ufd-boundary-factorization it is a unit times a monomial
   in them. Its reduced support is a union of boundary components, hence SNC.
6. The bounded clause of lem-per-ordinary-uniformization-local-reduction completes
   the induction; its unbounded clause removes any global dimension bound.
7. Apply U to Y with empty boundary. The resulting finite regular integral sources
   are objects of the ordinary alteration category: finite type, dominant and
   inducing finite extensions of the generic stalk fields.
8. Apply lem-per-ordinary-alteration-proper-refinement. It gives integral Noetherian
   P, proper surjective generically finite g, and finitely many opens mapping to
   the regular sources. Reindex those sources by the opens, allowing repetitions.
   The factorization triangles give the final equations. No prime is selected. -/
theorem exists_regular_weakUniformization_cover
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (hqe : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧ IsQuasiExcellent Γ(Y, U.1)) :
    ∃ (n : ℕ) (T : Fin n → Scheme.{u}) (_hT : ∀ i : Fin n, IsIntegral (T i))
      (f : ∀ i : Fin n, T i ⟶ Y),
      (∀ i : Fin n, IsRegularScheme (T i) ∧ IsNoetherian (T i) ∧
        IsDominant (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i) ∧
        ∃ hη : f i (genericPoint (T i)) = genericPoint Y,
          ((f i).functionFieldMap hη).hom.Finite) ∧
      ∃ (P : Scheme.{u}) (_hP : IsIntegral P) (g : P ⟶ Y),
        IsNoetherian P ∧ IsProper g ∧ Surjective g ∧
        (∃ hη : g (genericPoint P) = genericPoint Y, (g.functionFieldMap hη).hom.Finite) ∧
        ∃ (U : Fin n → P.Opens) (lift : ∀ i : Fin n, (U i).toScheme ⟶ T i),
          (⨆ i : Fin n, U i) = ⊤ ∧ ∀ i : Fin n, lift i ≫ f i = (U i).ι ≫ g := by
  sorry

end AlgebraicGeometry
