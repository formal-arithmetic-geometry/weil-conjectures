/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.Separable

/-!
# The points of an etale fibre

Source: Stacks Project, Morphisms, Lemma 02GL, part (2)
(blueprint: lem-weil-pbc-etale-fibre-discrete-separable-points).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The fibre of an etale morphism is discrete, and each singleton open subscheme is the
spectrum of its residue field, finite and separable over the base residue field.
Source: Stacks Project, Morphisms, Lemma 02GL(2)
(blueprint: lem-weil-pbc-etale-fibre-discrete-separable-points).

Proof:
1. The fibre projection is etale by base change
   (`lem-weil-pbc-etale-base-change-finite-limits`, Stacks 02GO).
2. An affine open around a fibre point is etale over the base field by restriction and
   composition (`lem-weil-pbc-etale-composition-cancellation`). Its coordinate algebra is
   a finite product of finite separable fields
   (`lem-weil-pbc-etale-algebra-over-field-product`, Stacks 00U3).
3. The spectrum of that product has open singleton components, each isomorphic over the
   base field to the spectrum of the corresponding factor
   (`lem-weil-pbc-spec-finite-product-fields`).
4. Every point is open, so every subset is open and every singleton is also closed.
5. The residue field at the point agrees with that of its singleton open subscheme,
   hence with the corresponding finite separable factor. Transport the component
   isomorphism along this identification to obtain the claimed isomorphism over the base.

The ring map `i` is the canonical base-field map obtained by applying the fully faithful
spectrum functor to the composite from the point's residue-field spectrum to the base. -/
theorem Scheme.Hom.etale_fibre_discrete_separable_points
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (s : S) :
    DiscreteTopology (f.fiber s) ∧
      ∀ y : f.fiber s,
        let i := Spec.homEquiv
          ((f.fiber s).fromSpecResidueField y ≫ f.fiberToSpecResidueField s)
        letI := i.hom.toAlgebra
        Module.Finite (S.residueField s) ((f.fiber s).residueField y) ∧
          (∀ a : (f.fiber s).residueField y,
            ∃ p : Polynomial (S.residueField s), p.Separable ∧ Polynomial.aeval a p = 0) ∧
          ∃ U : (f.fiber s).Opens,
            (U : Set (f.fiber s)) = {y} ∧
              ∃ e : U.toScheme ≅ Spec ((f.fiber s).residueField y),
                e.hom ≫ Spec.map i = U.ι ≫ f.fiberToSpecResidueField s := by
  sorry

end AlgebraicGeometry
