/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# Finite type of an Artinian local algebra and its residue field

Source: Stacks Project, Algebra, Tag 07DT, part (2), and Morphisms, Tag 02HV
(blueprint: lem-sfb-artinian-finite-type-residue-criterion).

The algebraic criterion is stated for a ring homomorphism and its composite with
its target's canonical residue map. The second statement is the equivalent criterion
for the corresponding morphisms of affine schemes.
-/

@[expose] public section

set_option autoImplicit false

universe u v

/-- An Artinian local algebra is of finite type exactly when its residue field is.

Source: Stacks Project, Algebra, Tag 07DT, part (2)
(blueprint: lem-sfb-artinian-finite-type-residue-criterion).

Proof:
1. Images of finitely many algebra generators generate the quotient residue field
   (`def-weil-pbc-finite-type-algebra`).
2. Conversely, lift generators of the residue field to `A` and let `C` be the image
   of their polynomial evaluation map. Then `C` surjects onto the residue field,
   which is therefore a finite `C`-module. The Jacobson radical of the local ring
   `A` is its maximal ideal. By `lem-weil-pbc-artinian-finite-over-residue-finite`,
   applied to `C → A`, the Artinian ring `A` is a finite `C`-module.
3. Adjoin these finitely many module generators to the lifted algebra generators.
   Every element of `A` is a linear combination of the former with coefficients
   polynomial in the latter, so this finite set generates `A` over `R`.
-/
theorem RingHom.finiteType_iff_residue_of_isArtinianRing
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [IsArtinianRing A] [IsLocalRing A] (f : R →+* A) :
    f.FiniteType ↔ ((IsLocalRing.residue A).comp f).FiniteType := by
  sorry

/-- Finite type of the spectrum map of an Artinian local algebra is detected on its residue field.

Source: Stacks Project, Morphisms, Tag 02HV, with affine target, and Algebra, Tag 07DT (2)
(blueprint: lem-sfb-artinian-finite-type-residue-criterion).

Proof:
1. By `def-weil-affine-spectrum`, the maps on whole affine charts are `f` and its
   composite with the canonical residue map.
2. Apply `lem-weil-pbc-lft-affine-pairs` to whole charts for the forward direction,
   and `lem-weil-pbc-lft-pointwise-criterion` with whole charts for the converse:
   each spectrum map is locally of finite type exactly when its ring map is.
3. The algebraic equivalence follows by reducing generators modulo the maximal
   ideal in one direction. In the other, lift residue-field generators, take the
   image `C` of the polynomial algebra they define, and apply
   `lem-weil-pbc-artinian-finite-over-residue-finite` to `C → A`: the quotient by
   the Jacobson radical is finite over `C`, so `A` is finite over `C`. Its module
   generators together with the lifted generators generate it over `R`.
4. By `lem-weil-pbc-artinian-local-unique-prime`, `Spec A` has one point; by
   `def-weil-field` and `def-weil-affine-spectrum`, so does the residue spectrum.
   Every inverse image of an affine open is empty or a singleton and is compact.
5. Thus both maps are quasi-compact, and `def-weil-finite-type-morphism` identifies
   finite type with locally finite type and quasi-compact. Combine steps 2–4.
-/
theorem AlgebraicGeometry.Spec.finiteType_iff_residue_of_isArtinianRing
    {R A : Type u} [CommRing R] [CommRing A]
    [IsArtinianRing A] [IsLocalRing A] (f : R →+* A) :
    (AlgebraicGeometry.LocallyOfFiniteType
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)) ∧
      AlgebraicGeometry.QuasiCompact
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f))) ↔
    (AlgebraicGeometry.LocallyOfFiniteType
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((IsLocalRing.residue A).comp f))) ∧
      AlgebraicGeometry.QuasiCompact
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((IsLocalRing.residue A).comp f)))) := by
  sorry
