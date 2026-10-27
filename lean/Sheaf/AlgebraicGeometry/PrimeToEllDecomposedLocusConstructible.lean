/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.LocallyClosed
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Basic
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import Sheaf.RingTheory.MinimalPrimeFiniteTypeFiniteAway

/-!
# The prime-to-ell decomposed locus of an étale morphism

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II,
Proposition 2.2.2, printed pp. 26--27
(blueprint: lem-per-prime-to-ell-decomposed-locus-constructible).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped Topology

namespace AlgebraicGeometry.Scheme.Hom

/-- The locus with a finite residue-field lift of degree not divisible by `ell` is a union
of locally closed subsets and is open in the constructible topology. The field extension
is the canonical map `κ(f(y)) → κ(y)`; `residueDegree` is its vector-space dimension.

Source: ILO, Travaux de Gabber, Exposé II, 2.2.1 and Proposition 2.2.2, pp. 26--27
(blueprint: lem-per-prime-to-ell-decomposed-locus-constructible).

Proof:
1. Given a point x in the locus and a lift y of degree d prime to ell, choose affine
   neighbourhoods X₀ = Spec R of x and W = Spec B₀ of y in f⁻¹(X₀). Replace X₀ by
   Z = Spec(R/p), the reduced closure of x, with generic field K = κ(x). The ring
   R/p is Noetherian by projecting generators of ideals. Étale open restriction and
   ring base change preserve the hypotheses. The closed-immersion residue-field iso
   and fibre-product point/residue-field statements lift y to W ×[X₀] Z with the same
   residue field (the affine fibre-product identification gives the tensor algebra).
2. The generic étale algebra is a finite product of finite separable fields over K.
   The lift selects a factor L of degree d. Express its factor idempotent as b/s;
   inverting b isolates L. The affine étale criterion makes this localization finite
   type over R/p. Its generic fibre has one prime, so the minimal-prime generic
   finiteness lemma makes it finite after one further localization of R/p.
3. This gives a finite étale map with generic fibre degree d. It is finite locally
   free, and the finite-flat rank theorem gives an open neighbourhood U of the
   generic point on which every fibre has dimension d. Affine fibre products and
   étale ring base change identify these fibres as étale residue-field algebras.
4. Each fibre is a finite product of finite separable fields, whose degrees sum to d.
   Since ell does not divide d, at least one factor has degree not divisible by ell.
   Closed-immersion, fibre-product and open-immersion residue-field identifications
   show that its image in the original Y witnesses membership in the locus.
5. Thus U contains x, is locally closed in X and is contained in the locus. Taking
   all such neighbourhoods expresses the locus as a union of locally closed sets;
   the empty locus is the empty union. No finiteness or separation of Y is used.
6. Every open of a Noetherian scheme is quasi-compact. Hence locally closed sets
   are open in the constructible topology, giving the second conclusion. Conversely
   finite intersections of constructible subbasic sets are locally closed, so every
   constructible open is a union of locally closed sets, as asserted by the node's
   equivalent formulation. -/
theorem primeToEllDecomposedLocus_indConstructible
    {X Y : Scheme.{u}} [IsNoetherian X] (ell : ℕ) (hell : ell.Prime)
    (f : Y ⟶ X) [Etale f] :
    (∃ S : Set (Set X), (∀ s ∈ S, IsLocallyClosed s) ∧
      ⋃₀ S = {x : X | ∃ y : Y, f y = x ∧
        (f.residueFieldMap y).hom.Finite ∧ ¬ ell ∣ f.residueDegree y}) ∧
    IsOpen[constructibleTopology X]
      {x : X | ∃ y : Y, f y = x ∧
        (f.residueFieldMap y).hom.Finite ∧ ¬ ell ∣ f.residueDegree y} := by
  sorry

end AlgebraicGeometry.Scheme.Hom
