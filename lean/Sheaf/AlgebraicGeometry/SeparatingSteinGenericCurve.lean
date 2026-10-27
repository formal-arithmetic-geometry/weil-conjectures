/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Topology.KrullDimension
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.FieldTheory.SeparableExtension
public import Sheaf.TraceFormula.LocalDimensionFormula
import WeilConjectures.FieldTheory.SeparablyGeneratedSeparable
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.BaseChange
import Sheaf.AlgebraicGeometry.IrreducibleDominantGenericFibre
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import Sheaf.AlgebraicGeometry.GeometricReducednessFromGenericStalks
import Sheaf.FieldTheory.FiniteSeparableClosure
import Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg

/-!
# Separating Stein fields and the generic curve

Source: Stacks Project, Tags 054Q, 0B1C, 030W, 037Q; de Jong, Lemma 5.2,
final generic-fibre argument (blueprint: lem-sfb-separating-stein-generic-curve).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A separating one-variable field extension with relatively algebraically closed constants
is the function field of a proper normal geometrically integral generic curve.
Source: Stacks Project, Tags 054Q, 04KS, 0B1C, 030X, 030U, 037Q and 01J6;
de Jong, Lemma 5.2, final generic-fibre argument
(blueprint: lem-sfb-separating-stein-generic-curve).

The pullback cone `C, j, c` presents precisely `T ×[Y] Spec L`, with its actual generic
point map determined by `eY`. The two structure-map equations make `eT` and `eY`
identifications over k; `hmap` identifies the canonical generic-stalk map with L → E.
The last equation in the conclusion makes the function-field identification over L.

Proof, following the seven steps of the node:
1. Apply lem-weil-pbc-separably-generated-separable to E/F and its finitely generated
   subextension L/F. A finite extension has transcendence degree zero, so its separating
   basis is empty and L/F is separable (lem-kun-transcendence-degree-tower).
2. A separating basis t for E/F has one element. It stays transcendental over finite L/F.
   A spanning family over F(t) spans over L(t). The minimal polynomial over L(t) divides
   the separable one over F(t), so it is separable. Thus E/L is separably generated of
   transcendence degree one; t and a finite vector-space basis generate it as a field.
3. Dominance makes the generic fibre irreducible
   (lem-zl-irreducible-dominant-generic-fibre); proper base change
   (lem-pc-proper-base-change) makes it proper and finite type over L.
4. The local-spectrum calculation lem-sfb-local-spectrum-base-change-stalks identifies
   its local rings with those of T, so it is normal, reduced and integral. On affine
   charts the localization has zero prime over the zero prime of T. The generic stalk
   is therefore E with its prescribed L-structure, using
   lem-sc-integral-function-field-affine-fraction,
   lem-weil-pbc-generic-fibre-localization-domain-irreducible and
   lem-weil-pbc-spec-domain-stalks-function-field.
5. For every field extension K/L, E tensor_L K is reduced by
   lem-weil-pbc-separably-generated-tensor-reduced. Apply
   lem-pur-geometric-reducedness-from-generic-stalks to obtain geometric reducedness.
6. The relative separable algebraic closure of L in E is L. Apply
   lem-zl-finite-separable-closure and lem-zl-generic-point-geometric-irreducibility.
   Every field base change is now reduced and irreducible, hence integral.
7. Apply lem-sc-closed-irreducible-dimension-trdeg to C/L, Y/k and T/k.
   The tower formula lem-kun-transcendence-degree-tower and finiteness of L/F give
   the dimensions 1, trdeg_k F and trdeg_k F + 1. -/
theorem separating_stein_generic_curve
    (k F L E : Type u) [Field k] [Field F] [Field L] [Field E]
    [Algebra k F] [Algebra k L] [Algebra k E]
    [Algebra F L] [Algebra F E] [Algebra L E]
    [IsScalarTower k F L] [IsScalarTower k F E]
    [IsScalarTower k L E] [IsScalarTower F L E]
    (hEfg : (⊤ : IntermediateField k E).FG)
    (hFfg : (⊤ : IntermediateField k F).FG)
    (hsep : Algebra.IsSeparablyGenerated F E) (htrdeg : Algebra.trdeg F E = 1)
    [FiniteDimensional F L]
    (hclosed : ∀ a : E, IsAlgebraic L a → ∃ b : L, algebraMap L E b = a)
    {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y]
    (t : T ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType t] [QuasiCompact t] [LocallyOfFiniteType y] [QuasiCompact y]
    (g : T ⟶ Y) [IsProper g] [IsDominant g] (hg : g ≫ y = t)
    (hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧
      IsIntegrallyClosed (T.presheaf.stalk x))
    (eT : T.functionField ≃+* E) (eY : Y.functionField ≃+* L)
    (heT : Spec.map (CommRingCat.ofHom eT.toRingHom) ≫ T.fromSpecFunctionField ≫ t =
      Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (heY : Spec.map (CommRingCat.ofHom eY.toRingHom) ≫ Y.fromSpecFunctionField ≫ y =
      Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (hmap : ∀ a : Y.functionField,
      eT (@algebraMap Y.functionField T.functionField _ _
        g.dominantFunctionFieldAlgebra a) = algebraMap L E (eY a))
    (C : Scheme.{u}) (j : C ⟶ T) (c : C ⟶ Spec (CommRingCat.of L))
    (hC : IsPullback j c g
      (Spec.map (CommRingCat.ofHom eY.toRingHom) ≫ Y.fromSpecFunctionField)) :
    Algebra.IsSeparable F L ∧ Algebra.IsSeparablyGenerated L E ∧
      Algebra.trdeg L E = 1 ∧
      IsProper c ∧ LocallyOfFiniteType c ∧ QuasiCompact c ∧
      (∀ x : C, IsDomain (C.presheaf.stalk x) ∧
        IsIntegrallyClosed (C.presheaf.stalk x)) ∧
      GeometricallyIntegral c ∧
      (∃ _ : IsIntegral C, ∃ eC : C.functionField ≃+* E,
        Spec.map (CommRingCat.ofHom eC.toRingHom) ≫ C.fromSpecFunctionField ≫ c =
          Spec.map (CommRingCat.ofHom (algebraMap L E))) ∧
      topologicalKrullDim C = 1 ∧
      topologicalKrullDim Y = (Cardinal.toENat (Algebra.trdeg k F) : WithBot ℕ∞) ∧
      topologicalKrullDim T = (Cardinal.toENat (Algebra.trdeg k F) : WithBot ℕ∞) + 1 := by
  sorry

end AlgebraicGeometry
