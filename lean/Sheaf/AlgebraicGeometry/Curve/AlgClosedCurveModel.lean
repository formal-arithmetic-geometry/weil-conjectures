/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import Sheaf.AlgebraicGeometry.AffineProjectiveCompactification
import Sheaf.TraceFormula.ReducedSchemeImage
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Smooth proper models of one-variable fields

Source: Stacks Project, Curves, Theorem 0BY1 (theorem-curves-rational-maps)
and Lemma 0BY3 (lemma-nonsingular-model-smooth); Morphisms, Tag 0BX5,
the proper valuative criterion (blueprint: lem-trf-algclosed-curve-model).

The function field is the actual generic stalk. Its field isomorphism is over `k`
by the displayed equality of morphisms to `Spec k`. A subalgebra `B` of `E`
encodes precisely a subring containing the given copy of `k`, with its canonical
inclusion and `k`-algebra structure; the fraction-field hypothesis refers to that
inclusion. The two final equalities express extension and being a `k`-morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A finitely generated field of transcendence degree one over an algebraically closed
field is the function field of a smooth integral proper finite-type curve. Its generic
point extends over every valuation subring containing the base and with this fraction field.

Source: Stacks Project, Curves, Theorem 0BY1 (theorem-curves-rational-maps), its final
compactify-then-normalize construction, and Lemma 0BY3 (lemma-nonsingular-model-smooth);
Morphisms, Tag 0BX5 (blueprint: lem-trf-algclosed-curve-model).

Proof plan, following the seven steps of the live DAG node:
1. Choose field generators e_i and form the finite-type domain A = k[e_i] inside E.
   Its fraction field is E because it contains k and all the field generators.
   Set U = Spec A; lem-sc-integral-function-field-affine-fraction identifies its
   generic stalk with E, since localization at zero inverts all nonzero elements.
2. Apply lem-weil-pbc-finite-type-domain-dimension-trdeg to A. Together with
   def-weil-pbc-krull-dimension-ring this gives dim U = trdeg_k E = 1.
3. Apply lem-kun-compactification-affine to U, using its scheme-theoretic closure X
   in projective space. It has dimension one. By lem-trf-reduced-scheme-image it
   is reduced, and density of the irreducible nonempty U makes it irreducible and
   nonempty, hence integral by def-pc-integral-scheme. The open immersion identifies
   generic stalks by def-weil-open-immersion, so k(X) is k-isomorphic to E.
4. By lem-kun-projective-implies-proper, X is proper, hence finite type by
   def-weil-proper-morphism, as needed for normalization.
5. The field k is perfect: every irreducible polynomial has a root, hence degree
   one. Thus every algebraic element lies in k and is separable.
6. Take C = X.normalization, as in def-sc-normalization. On each nonempty affine
   chart Spec R its integral closure in k(X) is a domain between R and k(X),
   with the same fraction field; use lem-sc-integral-function-field-affine-fraction.
   The charts have a common generic point, so C is integral and k(C) = k(X) over k.
   By lem-sc-normalization-properties, C is proper of dimension one and smooth
   over the perfect field k. Properness also gives finite type.
7. For B contained in E and containing k with fraction field E, use the chosen
   k-isomorphism to form Spec E to C. The inclusions k to B to E give the lower
   side of a commutative valuative square. Apply
   lemma-nagata-proper-valuative-criterion-existence-api to the proper map C to
   Spec k, with valuation ring B and fraction field E. Its lift is the required
   k-morphism Spec B to C and restricts to the chosen generic-point morphism.
   This also applies to the field valuation B = E. -/
theorem exists_smooth_proper_integral_curve_model
    (k E : Type u) [Field k] [IsAlgClosed k] [Field E] [Algebra k E]
    (hfg : (⊤ : IntermediateField k E).FG) (htrdeg : Algebra.trdeg k E = 1) :
    ∃ (C : Scheme.{u}) (s : C ⟶ Spec (.of k)) (_ : IsIntegral C)
      (e : C.functionField ≃+* E),
      Smooth s ∧ IsProper s ∧ LocallyOfFiniteType s ∧ QuasiCompact s ∧
      topologicalKrullDim C = 1 ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecStalk (genericPoint C) ≫ s =
        Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      ∀ (B : Subalgebra k E) [ValuationRing B] [IsFractionRing B E],
        ∃ f : Spec (.of B) ⟶ C,
          Spec.map (CommRingCat.ofHom B.val.toRingHom) ≫ f =
            Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecStalk (genericPoint C) ∧
          f ≫ s = Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
  sorry

end AlgebraicGeometry
