/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.GenericComponentsSplit
import WeilConjectures.AlgebraicGeometry.SpreadFiniteSeparableExtension
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finite étale splitting of generic components

Source: Stacks Project, Tag 0551, with Tags 054R and 025O.
(blueprint: lem-trf-finite-etale-generic-component-splitting)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite type family over an integral Noetherian scheme has geometrically irreducible
components in its generic fibre after a finite étale surjective integral affine cover of
some nonempty affine open of the base. Geometric irreducibility of a component is expressed
by irreducibility, including nonemptiness, of its inverse image after every field extension.

Source: Stacks Project, Tag 0551 (integral Noetherian specialization), with Tags 054R and 025O.
(blueprint: lem-trf-finite-etale-generic-component-splitting)

Proof:
1. Choose a nonempty affine open V = Spec A of T by lem-weil-pbc-affine-opens-basis.
The ring A is a domain by def-pc-integral-scheme and Noetherian by
pqf-lem-affine-open-locnoeth. Let K be its fraction field. The generic fibre
Y = X ×_T Spec K is finite type by lem-sfb-finite-type-composition-base-change.
2. Apply lem-sbc-generic-components-split to Y/K to obtain a finite étale field extension
L/K splitting all components geometrically. Its finiteness gives finite dimension, and
lem-weil-pbc-etale-residue-field-extension-separable gives separability of this extension.
3. Apply lem-weil-pbc-spread-finite-separable-extension to A, K and L. This gives c ≠ 0,
a localization A[c⁻¹], and a finite étale domain B inside L with fraction field L and
surjective spectrum map, with the original compatible maps from A through K to L.
4. The open U = D(c) in V is nonempty and affine. Identify Spec A[c⁻¹] with U using
lem-weil-pbc-spec-localization-away-basic-open and lem-weil-pbc-affine-open-stalk-localization:
on stalks the inverse sends (a/cⁿ)/(b/cᵐ) to acᵐ/(bcⁿ); stalk surjectivity lifts sections
locally, and stalk injectivity makes the local lifts agree and glue. Put S = Spec B and
transport its finite étale surjective map to π : S → U.
5. The open U is integral, hence reduced. By etale-proposition-etale-reduced, S is reduced.
The zero prime of the domain B is its generic point ξ, so S is integral and affine.
Its stalk B_(0) is L, a field with maximal ideal zero; thus def-weil-residue-field gives
κ(ξ) = L, compatibly with the maps from A and K.
6. The fibre H = (X ×_T S)_ξ is isomorphic over L to Y ×_K Spec L by two applications of
def-pc-fibre-product. Both represent compatible maps to X and Spec L over T. The comparison
maps are inverse by the projection identities, and remain so after every field extension.
The resulting homeomorphisms preserve maximal irreducible subsets and their inverse images.
Step 2 therefore gives the conclusion for each component of H. If Y is empty, H is empty
and has no components; the same nonempty U and S work. No flatness, properness, reducedness
or dimension assumption on X/T is used. -/
theorem exists_finite_etale_generic_component_splitting {X T : Scheme.{u}}
    [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : T.Opens, (U : Set T).Nonempty ∧ IsAffineOpen U ∧
      ∃ S : Scheme.{u}, IsIntegral S ∧ IsAffine S ∧
        ∃ π : S ⟶ U.toScheme, IsFinite π ∧ Etale π ∧ Surjective π ∧
          ∃ ξ : S, IsGenericPoint ξ Set.univ ∧
            ∀ A ∈ irreducibleComponents ↥((pullback.snd f (π ≫ U.ι)).fiber ξ),
              ∀ (E : Type u) (_ : Field E) (z : Spec (CommRingCat.of E) ⟶ Spec (S.residueField ξ)),
                IsIrreducible
                  ((pullback.fst
                    ((pullback.snd f (π ≫ U.ι)).fiberToSpecResidueField ξ) z) ⁻¹' A) := by
  sorry

end AlgebraicGeometry
