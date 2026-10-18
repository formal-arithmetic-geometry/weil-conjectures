/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Sheaf.RingTheory.ColimitCategoryFpAlgebras
import Sheaf.RingTheory.FiniteMapColimitDescent
import Sheaf.RingTheory.ColimitFlatRingMap
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Sheaf.AlgebraicGeometry.GeometricallyReducedFibreLocus
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import Sheaf.FieldTheory.SeparatingTranscendenceBasisFiniteSubextension
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Spreading a finite generic modification from a valuation subring

Source: Temkin, *Stable modification of relative curves*, Theorem 3.5.5, Step 5,
printed p. 24; section 3.1 and Remark 3.1.1(i), printed pp. 14--15
(blueprint: lem-trf-finite-eta-modification-spreading).

Tensor products are written with the base extension on the left. Tensor symmetry
identifies these with the right-hand base extensions in the node. An algebra structure
is specified by its actual algebra homomorphism `u`, and finiteness refers to that map.
The equation for `e` says that it is an isomorphism over the original base-changed
algebra, and therefore preserves its specified generic identification after extension
to `L`. The final scheme clauses spell out Temkin's integral-source, separated
finite-type quasi-alteration convention; they do not assert an integral morphism.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A finite generic modification with flat finitely presented geometrically reduced
fibres over a valuation subring of a separable algebraic extension spreads to a
finitely generated subalgebra with the same properties.

Source: Temkin, *Stable modification of relative curves*, Theorem 3.5.5, Step 5,
printed p. 24; section 3.1 and Remark 3.1.1(i), printed pp. 14--15; the quasi-alteration
convention at the start of section 3, printed pp. 13--14
(blueprint: lem-trf-finite-eta-modification-spreading).

Proof plan, following the ten steps of the DAG:
1. Order the finitely generated `R`-subalgebras of `V` by inclusion. They form a
   directed system with union `V`; their fraction fields have union `L`. Apply
   `lem-weil-pbc-limit-affine-transition`. The spectra are qcqs by
   `lem-weil-pbc-affine-scheme-qcqs`, with affine transition maps by
   `lem-weil-pbc-fibre-product-affine-spectra`.
2. Descend the finitely presented `V`-algebra `B` to a stage using
   `lem-kun-fp-algebra-descent`. Extend it and `A` to subsequent stages using
   `lem-weil-pbc-finite-presentation-base-change-composition` and tensor associativity.
3. Descend `u` using part (2) of `lem-weil-pbc-colimit-category-fp-algebras`.
   The descended base-change isomorphism is consequently linear over the actual
   base-changed algebra `A`, as required by the equation for `e`.
4. The descended algebra is finitely presented over the descended `A`: choose finite
   presentations over the base and add relations equating the generators of `A`
   with their images. Substitution gives mutually inverse maps, using
   `def-weil-pbc-finitely-presented-algebra`.
5. Apply `lem-weil-pbc-colimit-finite-ring-map` to descend finiteness. Finitely many
   module generators remain generators after every subsequent base change.
6. Apply `lem-weil-pbc-colimit-flat-ring-map` to the finitely presented structure map
   to descend flatness on an upper tail. All finite-presentation and finite-module
   properties persist.
7. By `lem-trf-affine-geometric-reducedness-criterion`, the hypothesis on algebraically
   closed fields gives geometrically reduced fibres over `V`. The constructible locus
   in `lem-trf-geometrically-reduced-fibre-locus` pulls back to the whole spectrum of
   `V`. Apply `lem-weil-pbc-limit-contained-in-constructible` to reach a stage where
   every fibre is geometrically reduced. Maps to algebraically closed fields factor
   through the residue field of their kernel. Empty fibres are included.
8. Descend the inverse of the given generic map over the directed system of fraction
   fields, using part (2) of `lem-weil-pbc-colimit-category-fp-algebras`. Use part (3)
   twice and take a common upper bound to make both composites identities. This
   descends the actual generic map, with the given identification over `L`.
9. The fraction field of a finitely generated subalgebra `R[r₁,...,rₙ]` is
   `F(r₁,...,rₙ)`. Apply
   `lem-weil-pbc-separating-transcendence-basis-finite-subextension` with empty
   transcendence basis: it is finite separable over `F`, including `n = 0`.
10. The inclusions give the spectrum factorization. By
    `lem-weil-pbc-spec-domain-stalks-function-field` the source spectrum is integral
    with the displayed fraction field. It is separated by
    `lem-weil-pbc-affine-source-morphism-separated`. The affine fibre-product formula
    (`lem-weil-pbc-fibre-product-affine-spectra`) gives finite type, since the same
    finitely many algebra generators generate after restriction to each target
    affine open; its preimage is quasi-compact by `lem-weil-pbc-affine-scheme-qcqs`.
    This is precisely Temkin's quasi-alteration. The isomorphism `e` from step 3 and
    step 8 retain the specified generic identification and all preceding properties.
-/
theorem exists_finite_eta_modification_spreading
    (R F L A : Type u) [CommRing R] [IsDomain R] [Field F] [Field L]
    [Algebra R F] [IsFractionRing R F] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] [Algebra.IsSeparable F L]
    (V : ValuationSubring L) [Algebra R V] [IsScalarTower R V L]
    [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (B : Type u) [CommRing B] [Algebra V B]
    (u : (V ⊗[R] A) →ₐ[V] B) (hu : u.Finite)
    [Module.Flat V B] [Algebra.FinitePresentation V B]
    (hgeneric : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id L L) u))
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra V Ω],
      _root_.IsReduced (Ω ⊗[V] B)) :
    ∃ R' : Subalgebra R V, R'.FG ∧
      ∃ (F' : Type u) (_ : Field F') (_ : Algebra R' F') (_ : Algebra F F'),
        IsFractionRing R' F' ∧ Module.Finite F F' ∧ Algebra.IsSeparable F F' ∧
        (∀ r : R, algebraMap R' F' (algebraMap R R' r) =
          algebraMap F F' (algebraMap R F r)) ∧
        ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra R' B')
          (u' : (R' ⊗[R] A) →ₐ[R'] B'),
          u'.Finite ∧ u'.FinitePresentation ∧
          Module.Flat R' B' ∧ Algebra.FinitePresentation R' B' ∧
          (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R' Ω],
            _root_.IsReduced (Ω ⊗[R'] B')) ∧
          Function.Bijective (Algebra.TensorProduct.map (AlgHom.id F' F') u') ∧
          (∃ e : (V ⊗[R'] B') ≃ₐ[V] B,
            ∀ a : A, e (1 ⊗ₜ[R'] u' (1 ⊗ₜ[R] a)) = u (1 ⊗ₜ[R] a)) ∧
          IsIntegral (Spec (CommRingCat.of R')) ∧
          IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
          LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
          QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
          Spec.map (CommRingCat.ofHom R'.val.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (algebraMap R R')) =
            Spec.map (CommRingCat.ofHom (algebraMap R V)) := by
  sorry

end AlgebraicGeometry
