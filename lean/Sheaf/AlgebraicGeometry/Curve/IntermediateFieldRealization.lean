/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.AlgebraicGeometry.Curve.ProperFunctionFieldMorphisms
public import Mathlib.Algebra.Field.Subfield.Basic

import Sheaf.AlgebraicGeometry.Curve.AlgClosedCurveModel
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Realizing an intermediate function field by a curve factorization

Source: Stacks Project, Curves, Proposition 0CD2, the intermediate-field sentence of its proof;
Theorem 0BY1 and Lemma 0BY3 (blueprint: lem-sfb-curve-intermediate-field-realization).

An intermediate field is given by a field `E` and embeddings `i : k(Y) →+* E` and
`j : E →+* k(X)` whose composite is the canonical generic-stalk pullback of `f`.
Ring homomorphisms from fields are injective, so this includes precisely the intermediate
subfields and their isomorphic realizations. Scalars on `E` come from `i` and the canonical
scalar map of `Y`. The final range equalities express the two induced extension identifications.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every intermediate field of a nonconstant map of smooth proper integral curves is
realized by a compatible smooth proper integral curve factorization, with the specified
function-field isomorphism and both canonical pullbacks.

Source: Stacks Project, Curves, Proposition 0CD2, proof; Theorem 0BY1 and Lemma 0BY3
(blueprint: lem-sfb-curve-intermediate-field-realization).

Proof plan, following the six steps of the node:
1. Apply lem-sfb-proper-curve-function-field-morphisms to f. It sends the generic point
   to the generic point, its field extension is finite, and both function fields are
   finitely generated of transcendence degree one. Identify K with its image under f*.
   Apply lem-sfb-finite-field-tower-intermediate to obtain finiteness of E/K and L/E.
2. Choose finitely many field generators of K/k and a finite K-spanning family of E,
   using def-weil-finite-dimensional-subspace. Together these generate E as a field:
   the field they generate contains every K-linear combination of the spanning family.
3. By lem-weil-pbc-finite-algebra-is-integral, finiteness makes L/E algebraic.
   Apply lem-kun-transcendence-degree-tower to k, E, L. Since trdeg_E L = 0 and
   trdeg_k L = 1, it gives trdeg_k E = 1.
4. Apply lem-trf-algclosed-curve-model to E/k. It gives a smooth proper integral
   finite-type dimension-one curve Z and a k-isomorphism theta : k(Z) to E.
   Properness includes separatedness (def-weil-proper-morphism), so Z is a curve.
5. Apply the surjectivity of lem-sfb-proper-curve-function-field-morphisms to the
   embeddings j composed with theta and theta inverse composed with i. This produces
   nonconstant k-morphisms a : X to Z and b : Z to Y with the prescribed pullbacks.
6. Both maps send generic point to generic point, hence so does their composite.
   If it factored through a k-point, def-weil-residue-field would give a k-embedding
   K into k. Injectivity forces every element of K to be a scalar, contradicting
   trdeg_k K = 1. Thus the composition clause of the curve correspondence applies:
   (a followed by b)* = a* composed with b* = j composed with i = f*.
   Injectivity of the correspondence gives a followed by b = f. Surjectivity of theta
   identifies the image of a* with j(E), and theta sends the image of b* to i(K),
   giving exactly the two claimed extension identifications. -/
theorem exists_curve_intermediate_field_realization
    (k : Type u) [Field k] [IsAlgClosed k]
    (X Y : Scheme.{u}) (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] [IsCurve sX] [IsCurve sY]
    [Smooth sX] [Smooth sY] [IsProper sX] [IsProper sY]
    (hXdim : topologicalKrullDim X = 1) (hYdim : topologicalKrullDim Y = 1)
    (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (hf_nonconstant : ¬ ∃ y : Spec (.of k) ⟶ Y, y ≫ sY = 𝟙 _ ∧ sX ≫ y = f) :
    ∃ hfη : f (genericPoint X) = genericPoint Y,
      ∀ (E : Type u) [Field E] (i : Y.functionField →+* E) (j : E →+* X.functionField),
        j.comp i = (f.functionFieldMap hfη).hom →
        @Module.Finite Y.functionField E _ _ (@Algebra.toModule _ _ _ _ i.toAlgebra) ∧
        @Module.Finite E X.functionField _ _ (@Algebra.toModule _ _ _ _ j.toAlgebra) ∧
        @IntermediateField.FG k _ E _
          (i.comp sY.curveFunctionFieldBaseMap).toAlgebra ⊤ ∧
        @Algebra.trdeg k E _ _ (i.comp sY.curveFunctionFieldBaseMap).toAlgebra = 1 ∧
        ∃ (Z : Scheme.{u}) (sZ : Z ⟶ Spec (.of k)) (_ : IsIntegral Z)
          (θ : Z.functionField ≃+* E) (a : X ⟶ Z) (b : Z ⟶ Y),
          IsCurve sZ ∧ Smooth sZ ∧ IsProper sZ ∧ topologicalKrullDim Z = 1 ∧
          θ.toRingHom.comp sZ.curveFunctionFieldBaseMap =
            i.comp sY.curveFunctionFieldBaseMap ∧
          a ≫ sZ = sX ∧ b ≫ sY = sZ ∧ a ≫ b = f ∧
          (¬ ∃ z : Spec (.of k) ⟶ Z, z ≫ sZ = 𝟙 _ ∧ sX ≫ z = a) ∧
          (¬ ∃ y : Spec (.of k) ⟶ Y, y ≫ sY = 𝟙 _ ∧ sZ ≫ y = b) ∧
          ∃ (haη : a (genericPoint X) = genericPoint Z)
            (hbη : b (genericPoint Z) = genericPoint Y),
            (a.functionFieldMap haη).hom = j.comp θ.toRingHom ∧
            (b.functionFieldMap hbη).hom = θ.symm.toRingHom.comp i ∧
            (a.functionFieldMap haη).hom.fieldRange = j.fieldRange ∧
            (b.functionFieldMap hbη).hom.fieldRange.map θ.toRingHom = i.fieldRange := by
  sorry

end AlgebraicGeometry
