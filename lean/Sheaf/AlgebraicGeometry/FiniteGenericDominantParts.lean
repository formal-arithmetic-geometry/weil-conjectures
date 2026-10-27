/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import Sheaf.AlgebraicGeometry.DominantReducedPart
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.DimZeroFiniteOverField
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import WeilConjectures.AlgebraicGeometry.UnramifiedFibrePointIsolated
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite generic fibres and reduced dominant parts

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II 1.2.5--1.2.6, 2.1.1
and Exposé III, proof of Proposition 3.1(iii), printed pp. 25--26, 38
(blueprint: lem-per-finite-generic-dominant-parts).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The reduced union of dominant components has finite generic residue extensions;
finite-type étale families have finite generic fibres, and completely decomposed families
remain completely decomposed after restriction to this reduced union.

Source: ILO, Exposé II 1.2.5--1.2.6 and 2.1.1, pp. 25--26; Exposé III, proof of
Proposition 3.1(iii), p. 38 (blueprint: lem-per-finite-generic-dominant-parts).

Proof:
1. By lem-per-dominant-part-coreflection the reduced dominant closure is exactly the
   reduced union of the components dominating the integral base. Its component generic
   points map to the base generic point. Its inclusion is a closed immersion, hence of
   finite type (lem-weil-pbc-closed-immersion-proper); composition is of finite type by
   lem-sfb-finite-type-composition-base-change.
2. Write the generic fibre as Spec B with B finite-dimensional over the generic residue
   field (lem-weil-pbc-finite-over-field-affine-finite-dim). Every prime quotient of B is
   a finite-dimensional domain, hence a field by lem-weil-pbc-finite-dimensional-domain-is-field.
   Thus all primes are maximal, all residue extensions are finite, and the fibre is
   zero-dimensional by lem-weil-pbc-spec-irreducible-closed-subsets-primes. It is finite
   and discrete by lem-weil-pbc-finite-type-dim-zero-artinian. This includes B = 0.
3. A component generic point of the dominant part maps to the base generic point by
   Step 1. The fibre-product point and residue-field descriptions
   (lem-weil-pbc-fibre-product-points, lem-weil-pbc-fibre-product-point-residue-field)
   identify its residue field with that of a point of the generic fibre: the tensor
   ring is the original residue field tensored with the base field over itself.
   The closed immersion of the reduced part preserves residue fields, giving finiteness.
4. Each generic fibre of V j is finite type and maps étale to the discrete generic fibre
   of T (lem-sfb-finite-type-composition-base-change, lem-weil-pbc-etale-scheme-base-change).
   By lem-weil-pbc-unramified-fibre-point-isolated each point is isolated in its fibre.
   That fibre is open, since its image singleton is open. Thus the source is discrete;
   no separatedness is needed.
5. A discrete space has dimension at most zero. Use lem-pc-scheme-dimension-local-rings
   to pass to scheme dimension, and lem-pc-algebraic-dim-zero-affine-finite to conclude
   that each generic fibre is finite over the base field. The empty fibre is Spec 0.
6. Given a residue-preserving lift z of the image of a point t' of the dominant part,
   the tensor of their residue fields over the residue field of the common image is
   canonically the residue field of t'. Its zero prime gives a point of the pullback
   with unchanged residue field, by lem-weil-pbc-fibre-product-points and
   lem-weil-pbc-fibre-product-point-residue-field. This proves complete decomposition.
   The projections remain étale by lem-weil-pbc-etale-scheme-base-change. All assertions
   over an empty dominant part, including for the empty family, are vacuous.
-/
theorem finite_generic_dominant_parts {S T : Scheme.{u}} [IsIntegral S]
    [IsNoetherian S] (f : T ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hfinite : IsFinite (f.fiberToSpecResidueField η)) :
    LocallyOfFiniteType ((dominantReducedPartIdeal f).subschemeι ≫ f) ∧
    QuasiCompact ((dominantReducedPartIdeal f).subschemeι ≫ f) ∧
    (∀ ξ : (dominantReducedPartIdeal f).subscheme,
      closure ({ξ} : Set (dominantReducedPartIdeal f).subscheme) ∈
          irreducibleComponents (dominantReducedPartIdeal f).subscheme →
        ((dominantReducedPartIdeal f).subschemeι ≫ f) ξ = η ∧
          (((dominantReducedPartIdeal f).subschemeι ≫ f).residueFieldMap ξ).hom.Finite) ∧
    ∀ (J : Type v) [Finite J] (V : J → Scheme.{u}) (a : ∀ j, V j ⟶ T),
      (∀ j, Etale (a j)) →
      (∀ j, LocallyOfFiniteType (a j ≫ f) ∧ QuasiCompact (a j ≫ f)) →
      (∀ j, IsFinite ((a j ≫ f).fiberToSpecResidueField η)) ∧
      ((∀ t : T, ∃ (j : J) (z : V j), a j z = t ∧ IsIso ((a j).residueFieldMap z)) →
        ∀ t' : (dominantReducedPartIdeal f).subscheme,
          ∃ (j : J) (z' : ↥(pullback (a j) (dominantReducedPartIdeal f).subschemeι)),
            pullback.snd (a j) (dominantReducedPartIdeal f).subschemeι z' = t' ∧
              IsIso ((pullback.snd (a j)
                (dominantReducedPartIdeal f).subschemeι).residueFieldMap z')) := by
  sorry

end AlgebraicGeometry
