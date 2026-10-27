/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.JacobsonDenominatorFunctionField
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Two semilocal rings cover the spectrum of their intersection

Source: Stacks Project, Varieties, Tag 09N3, in Situation 09MY
(blueprint: lem-trf-two-semilocal-rings-intersection-cover).

The helper `Subring.infTensorProductMap` equips the factors with the canonical algebra
structures given by the inclusions from their intersection, and uses Mathlib's tensor map.
-/

@[expose] public section

universe u

/-- The multiplication homomorphism from `C ⊗[C ⊓ D] D` to the ambient commutative ring.
The two algebra structures are induced by the inclusion homomorphisms from `C ⊓ D`.
Its value on a pure tensor `c ⊗ d` is `(c : K) * (d : K)`.

Source: Stacks Project, Varieties, Situation 09MY and Tag 09N3
(blueprint: lem-trf-two-semilocal-rings-intersection-cover). -/
noncomputable def Subring.infTensorProductMap {K : Type u} [CommRing K] (C D : Subring K) :=
  letI : Algebra (C ⊓ D : Subring K) C :=
    (Subring.inclusion (inf_le_left : C ⊓ D ≤ C)).toAlgebra
  letI : Algebra (C ⊓ D : Subring K) D :=
    (Subring.inclusion (inf_le_right : C ⊓ D ≤ D)).toAlgebra
  (Algebra.TensorProduct.productMap
    ({ C.subtype with commutes' := fun _ ↦ rfl } : C →ₐ[(C ⊓ D : Subring K)] K)
    ({ D.subtype with commutes' := fun _ ↦ rfl } : D →ₐ[(C ⊓ D : Subring K)] K)).toRingHom

namespace AlgebraicGeometry

/-- Two independent Noetherian semilocal subrings of a common fraction field, both of
Krull dimension one, give open charts covering the spectrum of their intersection.
Their canonical multiplication homomorphism over that intersection is a ring isomorphism.

Source: Stacks Project, Varieties, Tag 09N3 in Situation 09MY
(blueprint: lem-trf-two-semilocal-rings-intersection-cover).

Proof:
1. Apply lem-sc-jacobson-denominator-function-field to C and the singleton family D,
   and then with C and D exchanged. Tensor symmetry preserves the multiplication map
   (def-weil-pbc-module-tensor-product). Obtain nonzero f in C and g in D such that
   t = 1/f lies in Jac(D), and s = 1/g lies in Jac(C).
2. Put a = fs in Jac(C), b = gt in Jac(D), so ab = 1. The Jacobson radicals are ideals.
   By lem-weil-pbc-jacobson-radical-one-plus-units, 1+a and 1+b are units. Set
   x = 1/(1+a) = b/(1+b), y = a/(1+a) = 1/(1+b). Then x is a unit of C and lies in
   Jac(D); y is a unit of D and lies in Jac(C). Both belong to R = C intersection D,
   both are nonzero, and x+y = 1.
3. Show C_y = K and D_x = K (def-weil-ring-localization-away). For nonzero d in either
   ring B, any prime containing d is nonzero and is contained in a maximal ideal by
   lem-weil-pbc-proper-ideal-contained-in-maximal. Dimension one forces that prime to
   be maximal. Thus its radical contains the chosen h in Jac(B), by
   lem-weil-pbc-zero-locus-eq-iff-radical-eq. Some positive power h^n = de, hence
   1/d = e/h^n belongs to B_h. The fraction-field property gives B_h = K; injectivity
   follows from the zero-numerator criterion in the domain B.
4. Show C = R_x and D = R_y inside K. Since x is a unit of C, R_x lies in C. For c in C,
   write c = d/x^n using K = D_x. Then d = x^n c belongs to C and D, hence to R.
   The same argument with y gives D = R_y. The localization maps are injective by the
   zero-numerator criterion (def-weil-ring-localization-away).
5. Apply lem-weil-pbc-principal-localization-open-immersion to obtain the stated
   inclusion-induced open immersions, with images D(x) and D(y). These cover because
   a prime outside both would contain x+y = 1.
6. Apply the module clause of lem-weil-pbc-localization-tensor to R_x and the R-module D.
   It identifies C tensor_R D with D_x = K, sending each c tensor d to cd. Pure tensors
   generate by def-weil-pbc-module-tensor-product, so this is the canonical ring map.
   Its bijectivity says that the ring homomorphism is an isomorphism.
-/
theorem two_semilocal_rings_intersection_cover
    {K : Type u} [Field K] (C D : Subring K)
    [IsFractionRing C K] [IsFractionRing D K]
    [IsNoetherianRing C] [IsNoetherianRing D]
    [Finite (MaximalSpectrum C)] [Finite (MaximalSpectrum D)]
    (hCdim : ringKrullDim C = 1) (hDdim : ringKrullDim D = 1)
    (hsurj : Function.Surjective (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom ℤ C K) (IsScalarTower.toAlgHom ℤ D K))) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (Subring.inclusion (inf_le_left : C ⊓ D ≤ C)))) ∧
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (Subring.inclusion (inf_le_right : C ⊓ D ≤ D)))) ∧
    (∀ x : Spec (CommRingCat.of (C ⊓ D : Subring K)),
      x ∈ Set.range
        (Spec.map (CommRingCat.ofHom (Subring.inclusion (inf_le_left : C ⊓ D ≤ C)))) ∨
      x ∈ Set.range
        (Spec.map (CommRingCat.ofHom (Subring.inclusion (inf_le_right : C ⊓ D ≤ D))))) ∧
    Function.Bijective (Subring.infTensorProductMap C D) := by
  sorry

end AlgebraicGeometry
