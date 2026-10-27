/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Topology.Sober
import WeilConjectures.AlgebraicGeometry.AffineFibreSectionsTensor
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods
import WeilConjectures.AlgebraicGeometry.GenericComponentsSplit
import Sheaf.AlgebraicGeometry.EtaleResiduePolynomialLift
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Étale splitting of generic components over an irreducible base

Source: Stacks Project, More on Morphisms, Tag 0551,
`lemma-make-components-generic-fibre-geometrically-irreducible`, statements (1)--(7).
(blueprint: lem-sfb-etale-generic-component-splitting)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite type morphism over a nonempty irreducible scheme acquires geometrically
irreducible generic-fibre components after a finite étale surjective cover of a nonempty
open by an irreducible affine scheme. The inverse image of each component after every
field extension is irreducible, including nonemptiness. The generic fibre may be empty.

Source: Stacks Project, Tag 0551,
`lemma-make-components-generic-fibre-geometrically-irreducible`, statements (1)--(7).
(blueprint: lem-sfb-etale-generic-component-splitting)

Proof:
1. Choose a nonempty affine open V = Spec A by lem-weil-pbc-affine-opens-basis.
   Its nilradical p is prime by lem-zl-spectrum-irreducible-nilradical-prime and is
   generic. Put K = κ(p) and Y = X ×_S Spec K; finite type survives base change by
   lem-sfb-finite-type-composition-base-change.
2. Apply lem-sbc-generic-components-split to Y/K. Obtain a finite étale extension L/K
   splitting its components geometrically. Finiteness gives finite dimension and
   lem-weil-pbc-etale-residue-field-extension-separable gives separability. Choose a
   primitive element α by lem-weil-pbc-finite-separable-primitive-element.
3. By lem-weil-pbc-etale-residue-polynomial-lift, scale α by a nonzero residue of an
   element of A and lift its minimal polynomial to a monic F in A[T] of degree d ≥ 1.
   D = A[T]/(F) is finite free by lem-weil-pbc-monic-quotient-free and faithfully flat
   by lem-sfb-monic-quotient-faithful-tensor-coordinates. Thus h : Spec D → V is flat
   by lem-weil-pbc-flat-ring-map-iff-flat-affine, finite by
   lem-weil-pbc-spec-finite-ring-map-finite, and locally of finite presentation by its
   one-generator one-relation presentation (def-sbc-locally-finite-presentation).
4. The fibre at p is affine by lem-weil-pbc-finite-morphism-permanence and has algebra
   D ⊗_A K by lem-sbc-affine-fibre-sections-tensor. Mapping the polynomial generator
   to the scaled primitive element identifies it with K[T]/(F̄) = L: polynomial
   division identifies the evaluation kernel and primitivity gives surjectivity.
   Hence the fibre has precisely one point q and is Spec L over K.
5. By lem-sbc-flat-fibre-etale-neighbourhoods, h is étale on an open W containing q.
   The image Z = h(Spec D ∖ W) is closed by lem-weil-pbc-finite-closed-map-finite-fibres
   and misses p. Choose an affine neighbourhood U of p in V ∖ Z using the affine basis.
6. Set B = h⁻¹(U). By lem-weil-pbc-finite-morphism-permanence, B is affine and B → U
   finite. It lies in W and is étale by lem-weil-pbc-etale-scheme-base-change. Its image
   is closed by lem-weil-pbc-finite-closed-map-finite-fibres and contains the generic
   point p, so is all U. Thus B → U is surjective and B is nonempty.
7. By lem-weil-pbc-etale-morphism-open-map every nonempty open of B has open nonempty
   image in U, hence contains q, the sole point over p. Thus q is generic and B is
   irreducible (def-sc-generic-point, def-weil-irreducible-components). No reducedness
   or domain assertion is needed.
8. By lem-weil-pbc-affine-open-stalk-localization the local ring at q is D_q, with
   D_q/pD_q = L. This quotient is a field, so pD_q is the maximal ideal and κ_B(q) = L
   by def-weil-residue-field, compatibly with the original maps from A and K.
9. Put P = X ×_S B and ξ = q. By def-pc-fibre-product and def-pc-scheme-fibre its
   generic fibre identifies over L with Y_L: both represent compatible maps to X and
   Spec L over S. The projection-preserving comparisons are inverse by uniqueness,
   also after every E/L. Their homeomorphisms identify components and inverse images,
   so Step 2 gives the assertion. Empty generic fibres have no components; L = K and
   d = 1 are allowed. No Noetherian, reducedness, separatedness or flatness assumption
   on S or f occurs. -/
theorem exists_finite_etale_irreducible_generic_component_splitting
    {X S : Scheme.{u}} [IrreducibleSpace S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      ∃ B : Scheme.{u}, IrreducibleSpace B ∧ IsAffine B ∧
        ∃ g : B ⟶ U.toScheme, IsFinite g ∧ Etale g ∧ Surjective g ∧
          ∃ ξ : B, IsGenericPoint ξ Set.univ ∧
            ∀ A ∈ irreducibleComponents ↥((pullback.snd f (g ≫ U.ι)).fiber ξ),
              ∀ (E : Type u) (_ : Field E)
                (z : Spec (CommRingCat.of E) ⟶ Spec (B.residueField ξ)),
                IsIrreducible
                  ((pullback.fst
                    ((pullback.snd f (g ≫ U.ι)).fiberToSpecResidueField ξ) z) ⁻¹' A) := by
  sorry

end AlgebraicGeometry
