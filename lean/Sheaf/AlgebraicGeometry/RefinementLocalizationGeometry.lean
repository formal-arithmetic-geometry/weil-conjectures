/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Spec

/-!
# Geometry of the explicit common localization

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-refinement-localization-geometry)
-/

@[expose] public section

set_option autoImplicit false
universe u v
open scoped TensorProduct
open AlgebraicGeometry

/-- Source: smooth purity blueprint, sk-prop-sf-cbc,
lem-weil-pbc-finite-pushforward-generic-constructible, steps 4--9.
(blueprint: lem-weil-pbc-refinement-localization-geometry)

Proof: The product t of the nonzero s_j is nonzero in the domain S. Surjectivity
of Spec(C) -> Spec(S) makes S -> C injective: an element of the kernel belongs to
every prime ideal of S and hence is nilpotent, so is zero. The injective maps
C -> D_j then make the images of t nonzero in every D_j. C_T and E_j are the
localizations of C and D_j at the image of t, so the latter are domains.
Finiteness and etaleness of C_T over T, and finiteness of E_j over C_T, follow
by base change; the cover remains surjective by base change. Each s_j is a unit
in T since it divides t, so C_T -> E_j is also the base change of the given
universal homeomorphism over S[1/s_j]. Universal homeomorphisms persist under
base change and are surjective. Finally U -> T is an isomorphism by its
bijectivity, so the cover properties over T transport to U. No assertion about
a reduced tensor-product splitting is used or proved here. -/
theorem refinement_localization_geometry
    (S : Type u) [CommRing S] [IsDomain S]
    (C : Type u) [CommRing C] [IsDomain C] [Algebra S C]
    [Module.Finite S C] [Algebra.Etale S C]
    (hcover : Surjective (Spec.map (CommRingCat.ofHom (algebraMap S C))))
    (r : ℕ) (D : Fin r → Type u) [∀ j, CommRing (D j)] [∀ j, IsDomain (D j)]
    [∀ j, Algebra C (D j)] [∀ j, Module.Finite C (D j)]
    (hinj : ∀ j, Function.Injective (algebraMap C (D j)))
    [∀ j, Algebra S (D j)] [∀ j, IsScalarTower S C (D j)]
    (s : Fin r → S) (hs : ∀ j, s j ≠ 0)
    (hhomeo : ∀ j, (topologically IsHomeomorph).universally
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S C (D j))
          (AlgHom.id S (Localization.Away (s j)))).toRingHom)))
    (T : Type u) [CommRing T] [Algebra S T]
    [IsLocalization.Away (∏ j, s j) T]
    (U : Type u) [CommRing U] [Algebra U T]
    (hUT : Function.Bijective (algebraMap U T)) :
    let C' := T ⊗[S] C
    letI := Algebra.TensorProduct.rightAlgebra (R := S) (A := T) (B := C)
    Module.Finite U C' ∧ Algebra.Etale U C' ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap U C'))) ∧
      ∀ j, Module.Finite C' (C' ⊗[C] D j) ∧ IsDomain (C' ⊗[C] D j) ∧
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap C' (C' ⊗[C] D j)))) ∧
        (topologically IsHomeomorph).universally
          (Spec.map (CommRingCat.ofHom (algebraMap C' (C' ⊗[C] D j)))) := by
  sorry
