/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# Trivial componentwise normalization of normal schemes

Source: Stacks Project, Morphisms, Tags 0H7D and 0CDV; Properties, Tag 0357
(blueprint: lem-sfb-normalization-normal-locally-finite).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The canonical componentwise normalization of a scheme with normal domain stalks and
finitely many irreducible components on each quasi-compact open is an isomorphism.
The scheme may be empty and need not be quasi-compact or locally Noetherian.

Source: Stacks Project, Morphisms, Tags 0H7D and 0CDV; Properties, Tag 0357
(blueprint: lem-sfb-normalization-normal-locally-finite).

Proof plan:
1. Apply lem-sfb-normal-locally-finite-components to the two hypotheses. Its clopen
   reduced components Z_i are normal integral schemes and their coproduct is X.
   By def-weil-pbc-reduced-normalization, the displayed morphism is the coproduct of
   their function-field normalizations followed by their inclusions into X.
2. On a nonempty affine open V of Z_i, put A = O(V) and K = k(Z_i).
   By lem-sc-integral-function-field-affine-fraction, A is a domain and K its fraction
   field. By lem-weil-pbc-affine-open-stalk-localization (c), every maximal localization
   is a stalk, hence a normal domain. The criterion
   lem-weil-pbc-normal-domain-of-local-normal makes A integrally closed in K.
3. The generic-point morphism j_i : Spec K -> Z_i is the canonical local-scheme map
   of lem-weil-pbc-spec-local-ring-canonical-morphism. Its source is a one-point scheme
   (def-weil-affine-spectrum). Preimages of affine opens under j_i and its diagonal
   are empty or singletons, hence quasi-compact (def-weil-pbc-quasi-compact-scheme).
   Thus j_i is quasi-compact and quasi-separated by def-weil-finite-type-morphism
   and def-weil-quasi-separated-morphism.
4. Every nonempty open of Z_i contains its generic point, so j_i pushes the structure
   sheaf to the constant function-field sheaf, with structural map given by generic germs;
   both give the zero ring on the empty open. Thus def-sc-normalization agrees with
   lem-weil-pbc-relative-normalization applied to j_i, including its structural map.
   Clause (iii) identifies the inverse image of V with Spec of the integral closure A'
   of A in K and identifies the normalization map with Spec of the inclusion A -> A'.
5. By Step 2 and def-weil-pbc-normal-ring, every element of A' lies in A; conversely
   every a in A is integral, using T-a. The inclusion is bijective since A embeds in K.
   The spectrum of its inverse ring isomorphism gives an inverse over V.
6. These affine inverses agree on overlaps because two inverses of one morphism agree.
   They glue as scheme morphisms (def-pc-scheme). Their two inverse identities hold on
   the affine cover of Z_i and its inverse-image cover, hence hold globally.
7. The coproduct property of lem-weil-pbc-scheme-coproduct-family assembles the inverses
   into an inverse of X.fromReducedNormalization: both composites are identities on
   every summand, hence globally. When X is empty, both coproducts are empty and the
   same identities follow from uniqueness of the map out of an empty coproduct.
-/
theorem isIso_fromReducedNormalization_of_normal_locally_finite (X : Scheme.{u})
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIso X.fromReducedNormalization := by
  sorry

end AlgebraicGeometry.Scheme
