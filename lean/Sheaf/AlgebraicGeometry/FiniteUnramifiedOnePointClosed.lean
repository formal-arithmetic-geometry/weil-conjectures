/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct

/-!
# A finite unramified morphism with one purely inseparable fibre point is locally a closed immersion

Source: Stacks Project, Etale Morphisms, Lemma 04DG
(blueprint: lem-weil-pbc-finite-unramified-one-point-closed).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Let `π : X ⟶ S` be finite and unramified. If `x` is the unique point of the fibre over
`s` and the residue-field extension at `x` over `s` is purely inseparable, then `π` is a
closed immersion after restriction to some open neighbourhood of `s`.
Source: Stacks Project, Etale Morphisms, Lemma 04DG
(blueprint: lem-weil-pbc-finite-unramified-one-point-closed).

Proof (the seven steps of the DAG node):
1. Choose an affine open `V = Spec A` containing `s`. Finiteness makes its inverse image
   `Spec B`, with `B` a finite `A`-module. Write `p` and `q` for the primes of `s` and `x`.
   The Spec residue-field identification makes the given extension `κ(q)/κ(p)` purely
   inseparable (`def-weil-affine-spectrum`, `def-weil-finite-integral-morphism`,
   `lem-weil-pbc-spec-residue-field-identification`, `def-weil-residue-field`,
   `def-weil-pbc-finite-purely-inseparable-extension`).
2. Restrict the unramified morphism to `V` and base change to `Spec κ(p)`. Its fibre algebra
   `F = κ(p) ⊗[A] B` is a finite product of finite separable field extensions of `κ(p)`
   (`lem-weil-pbc-unramified-base-change-open`, `lem-weil-pbc-fibre-product-affine-spectra`,
   `lem-weil-pbc-unramified-algebra-over-field-product`, `def-weil-unramified-morphism`).
3. The map to `κ(q)` makes `F` nonzero, so the product has at least one factor. The primes of
   the factors contract to distinct primes of `B` over `p`, so uniqueness gives exactly one
   factor. The residue-field comparison identifies this field with `κ(q)` over `κ(p)`
   (`lem-weil-pbc-fibre-ring-localization-quotient`,
   `lem-weil-pbc-prime-residue-field-algebra`, `def-weil-pbc-localization-at-prime`,
   `lem-weil-pbc-fibre-ring-residue-field-iso`).
4. A separable and purely inseparable algebraic field extension is trivial: in characteristic
   zero this is the pure-inseparability condition; in characteristic `p > 0` the separable
   minimal polynomial divides a power of a linear polynomial, so has degree one. Thus
   `κ(p) → F` is surjective (`def-weil-pbc-finite-purely-inseparable-extension`,
   `def-weil-pbc-separable-algebraic-extension`).
5. Over the local ring `A_p`, the finite module `B_p` is generated modulo `pB_p` by `1`.
   Nakayama gives surjectivity of `A_p → B_p` (`def-weil-pbc-localization-at-prime`,
   `lem-weil-pbc-nakayama-local-generators`).
6. The finite module `Q = B / image(A)` vanishes at `p`. Its annihilator contains an element
   `f` outside `p`; hence `A_f → B_f` is surjective (`def-weil-finitely-generated-module`,
   `lem-weil-pbc-finite-module-support-annihilator`).
7. The principal-localization open immersions identify the restriction over `U = D(f) ⊆ V`
   with `Spec B_f → Spec A_f`. The affine closed-immersion criterion applies to the surjective
   ring map, and `s ∈ U` (`lem-weil-pbc-principal-localization-open-immersion`,
   `def-weil-affine-spectrum`, `lem-weil-pbc-closed-immersion-affine-cover-criterion`,
   `def-weil-closed-immersion`).
-/
theorem finite_unramified_one_point_closed
    {X S : Scheme.{u}} (π : X ⟶ S) (s : S) (x : X)
    (hx : π x = s)
    (hunique : ∀ y : X, π y = s → y = x)
    (hfinite : IsFinite π)
    (hunramified : LocallyOfFiniteType π ∧ IsOpenImmersion (pullback.diagonal π))
    (hpure : letI : Algebra (S.residueField (π x)) (X.residueField x) :=
      (π.residueFieldMap x).hom.toAlgebra
      IsPurelyInseparable (S.residueField (π x)) (X.residueField x)) :
    ∃ U : S.Opens, s ∈ U ∧ IsClosedImmersion (π ∣_ U) := by
  sorry

end AlgebraicGeometry
