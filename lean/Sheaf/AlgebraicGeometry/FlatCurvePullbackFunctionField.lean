/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Category.Ring.Constructions
public import Sheaf.FieldTheory.FieldTower
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import WeilConjectures.AlgebraicGeometry.FieldFractionRingGeometricIntegrality
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest

/-!
# Integral pullbacks and their function fields

Source: de Jong, Families of curves and alterations (1997), Theorem 5.9 proof,
printed p.617; Stacks Project, Tags 0BCM, 00DK, 00D2, 01RV, 0559 and 035X
(blueprint: lem-sfb-flat-curve-pullback-function-field).

The tensor product of function fields is expressed as their pushout in `CommRingCat`.
Mathlib's `CommRingCat.pushoutCoconeIsColimit` identifies this with the ordinary tensor
product, taking the two coprojections to `l ↦ l ⊗ 1` and `m ↦ 1 ⊗ m`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The ordinary pullback of this flat family is integral, has geometrically integral
 generic fibre, and has the tensor product of the two function fields as its function field.
 The identification commutes with the maps of generic stalks induced by both projections.
 The tensor product is a field finite over the function field of `V`. Reducedness also
 holds after pullback to every field-valued point of `B`.

 Source: de Jong, Theorem 5.9 proof, printed p.617; Stacks Project, Tags 0BCM, 00DK,
 00D2, 01RV, 0559 and 035X (blueprint: lem-sfb-flat-curve-pullback-function-field).

 Proof plan (the numbered steps are those of the DAG node):
 1. Dominance sends the generic point of `P` to that of `B`. Pullback pasting identifies
    the generic fibre over `P` with the extension of the generic fibre of `v` from
    `k(B)` to `k(P)`. Its further extensions are integral, proving geometric integrality.
    Use `def-pc-fibre-product` and `def-pc-geometrically-irreducible`.
 2. The projection to `P` is flat by `lem-weil-pbc-flat-morphism-base-change`.
    On affine charts, `lem-weil-pbc-flat-morphism-affine-criterion` and
    `lem-trf-flat-module-torsionfree-domain` embed the coordinate ring into its generic
    localization. `lem-weil-pbc-localization-tensor-over-base` identifies this with the
    chart of the generic fibre, using `lem-sc-integral-function-field-affine-fraction`,
    `lem-weil-pbc-fibre-product-affine-spectra` and `lem-weil-pbc-open-fibre-product`.
 3. Every nonempty affine chart therefore embeds into a domain and meets the generic
    fibre. These charts are reduced; irreducibility of the generic fibre makes any two
    nonempty opens intersect. The total space is nonempty, reduced and irreducible,
    hence integral by `def-pc-integral-scheme` and `def-pc-reduced-scheme`.
 4. Choose nonempty affine charts in `B`, `V`, `P`. The affine fraction-field node and
    the localization and fibre-product nodes identify the generic chart of `V` with
    a geometrically integral affine scheme having fraction field `k(V)` over `k(B)`.
 5. `lem-sbc-field-fraction-ring-geometric-integrality` transfers geometric integrality
    to `Spec k(V)`. Its base change to `k(P)` is the spectrum of the tensor product,
    which is therefore a nonzero domain.
 6. A finite `k(B)`-basis of `k(P)` spans the tensor product over `k(V)`.
    `lem-weil-pbc-finite-dimensional-domain-is-field` makes this domain a finite field.
 7. The affine fibre-product and localization-tensor nodes identify the localization
    of the pullback chart at the nonzero elements from both factors with this tensor
    product. Balancing over the base ring extends to balancing over its fraction field:
    equal actions of a nonzero element have equal inverses.
 8. The maps from both fields into the tensor field are injective. Thus every localized
    denominator is nonzero. This field is the fraction field of the pullback chart,
    hence `k(W)` by `lem-sc-integral-function-field-affine-fraction`. The projections
    send the generic point to the generic points of the factors, and the resulting
    isomorphism commutes with their generic-stalk maps, so it is the canonical one.
 9. A field-valued point factors through its residue field. Apply
    `lem-trf-geometric-reducedness-algebraic-closure-test` to the reduced geometric
    fibre, then extend to that field, using pullback pasting. Empty fibres are allowed.
    The construction throughout uses the ordinary pullback. -/
theorem flatCurvePullback_functionField
    {k : Type u} [Field k] {B V P : Scheme.{u}}
    [B.Over (Spec (.of k))] [V.Over (Spec (.of k))] [P.Over (Spec (.of k))]
    [IsIntegral B] [IsIntegral V] [IsIntegral P]
    [LocallyOfFiniteType (B ↘ Spec (.of k))] [QuasiCompact (B ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (P ↘ Spec (.of k))] [QuasiCompact (P ↘ Spec (.of k))]
    (v : V ⟶ B) [v.IsOver (Spec (.of k))]
    [Flat v] [LocallyOfFiniteType v] [QuasiCompact v] [IsDominant v]
    (hred : ∀ b : B, IsReduced (pullback v
      (Spec.map (CommRingCat.ofHom
        (algebraMap (B.residueField b) (AlgebraicClosure (B.residueField b)))) ≫
          B.fromSpecResidueField b)))
    (hgeneric : GeometricallyIntegral (v.fiberToSpecResidueField (genericPoint B)))
    (h : P ⟶ B) [h.IsOver (Spec (.of k))] [IsDominant h]
    (hfinite : (h.functionFieldMap h.apply_genericPoint_of_isDominant).hom.Finite) :
    IsReduced (pullback v h : Scheme.{u}) ∧
      GeometricallyIntegral ((pullback.snd v h).fiberToSpecResidueField (genericPoint P)) ∧
      (∀ (F : Type u) [Field F] (b : Spec (.of F) ⟶ B), IsReduced (pullback v b)) ∧
      ∃ (_ : IsIntegral (pullback v h : Scheme.{u}))
        (hp : (pullback.fst v h) (genericPoint (pullback v h : Scheme.{u})) = genericPoint V)
        (hq : (pullback.snd v h) (genericPoint (pullback v h : Scheme.{u})) = genericPoint P),
        ∃ e : pushout (v.functionFieldMap v.apply_genericPoint_of_isDominant)
            (h.functionFieldMap h.apply_genericPoint_of_isDominant) ≅
              (pullback v h : Scheme.{u}).functionField,
          pushout.inl (v.functionFieldMap v.apply_genericPoint_of_isDominant)
              (h.functionFieldMap h.apply_genericPoint_of_isDominant) ≫ e.hom =
            (pullback.fst v h).functionFieldMap hp ∧
          pushout.inr (v.functionFieldMap v.apply_genericPoint_of_isDominant)
              (h.functionFieldMap h.apply_genericPoint_of_isDominant) ≫ e.hom =
            (pullback.snd v h).functionFieldMap hq ∧
          IsField (pushout (v.functionFieldMap v.apply_genericPoint_of_isDominant)
            (h.functionFieldMap h.apply_genericPoint_of_isDominant) : CommRingCat.{u}) ∧
          (pushout.inl (v.functionFieldMap v.apply_genericPoint_of_isDominant)
            (h.functionFieldMap h.apply_genericPoint_of_isDominant)).hom.Finite := by
  sorry

end AlgebraicGeometry
