/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sober
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-! # Equivariant affine component charts and canonical generic germs

Source: Stacks Project, Tags 01I3, 01HV, 00EE, 01RV and 008M; inverse-pullback
and canonical-germ calculations (blueprint: lem-sfb-equivariant-component-affine-germs).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

/-- The actual intersection of a component open with the inverse image of an affine chart.
Source: Stacks Project, Tags 01I3 and 00EE
(blueprint: lem-sfb-equivariant-component-affine-germs). -/
abbrev componentAffineChart {X Z : Scheme.{u}} (q : X ⟶ Z) (V : Z.Opens)
    (U : X.Opens) : X.Opens := U ⊓ q ⁻¹ᵁ V

/-- Affine component restrictions, inverse pullbacks and generic residue maps are compatible.
Source: Stacks Project, Tags 01I3, 01HV, 00EE, 01RV and 008M
(blueprint: lem-sfb-equivariant-component-affine-germs).

Proof:
1. A finite morphism is affine. Disjointness of the target components excludes indices
   outside the fibre of j. A nonempty open contains the generic point, so each chart
   contains its component's generic point. Intersect the clopen decomposition with the
   inverse image to get its disjoint clopen cover.
2. By lem-weil-pbc-spec-clopen-idempotent the clopen charts in the affine inverse image
   are principal idempotent opens. They are affine by
   lem-weil-pbc-affine-open-section-vanishing-prime. Integrality makes their rings domains.
3. Induct on the finite nonempty fibre using lem-weil-pbc-sheaf-disjoint-union-product.
   Every coordinate of the resulting ring equivalence is the actual restriction.
4. Invariance of q preserves the inverse image; inverse pullback sends the chart at i
   to that at h i. Restriction naturality proves equivariance and compatibility with A.
5. Apply lem-sc-integral-function-field-affine-fraction on each integral component.
   Open-subscheme stalks agree with ambient stalks, and the residue field of a field is
   itself. Thus the actual evaluations make the residue fields fields of fractions.
6. By lem-weil-pbc-scheme-stalk-map-composition, evaluation commutes with the specified
   residue map of q. Its injectivity implies injectivity of the map on chart sections.
   The unique extension and fraction formula follow from lem-weil-pbc-fraction-field-lift.
7. A stabilizer fixes the generic point by lem-sc-scheme-sober. Apply the same germ
   naturality to its inverse and then extend to fractions; stalk-map composition gives
   exactly the inverse-pullback action, including its left-action convention. -/
theorem equivariant_component_affine_germs
    {X Z : Scheme.{u}} {I : Type v} {J : Type w} [Finite I] [Finite J]
    (U : I → X.Opens) (T : J → Z.Opens)
    (hUc : ∀ i : I, IsClosed (U i : Set X))
    (hTc : ∀ j : J, IsClosed (T j : Set Z))
    (hUd : Pairwise (fun i k : I ↦ Disjoint (U i) (U k)))
    (hTd : Pairwise (fun j k : J ↦ Disjoint (T j) (T k)))
    (hU : iSup U = ⊤) (hT : iSup T = ⊤)
    [∀ i : I, IsIntegral (U i).toScheme] [∀ j : J, IsIntegral (T j).toScheme]
    (η : I → X) (ξ : J → Z)
    (hη : ∀ i : I, IsGenericPoint (η i) (U i : Set X))
    (hξ : ∀ j : J, IsGenericPoint (ξ j) (T j : Set Z))
    (q : X ⟶ Z) [IsFinite q] (φ : I → J)
    (hqU : ∀ i : I, q '' (U i : Set X) = (T (φ i) : Set Z))
    (hqη : ∀ i : I, q (η i) = ξ (φ i))
    (H : Type t) [Group H] [Finite H] [MulAction H I] (a : H →* Aut X)
    (haU : ∀ (h : H) (i : I), (a h).hom '' (U i : Set X) = (U (h • i) : Set X))
    (haq : ∀ h : H, (a h).hom ≫ q = q)
    (hφ : ∀ (h : H) (i : I), φ (h • i) = φ i)
    (j : J) (hO : Set.Nonempty {i : I | φ i = j})
    (V : Z.Opens) (hVj : V ≤ T j) (hV : IsAffineOpen V) (hVn : Set.Nonempty (V : Set Z)) :
    ∃ (hξV : ξ j ∈ V)
      (hηW : ∀ i : {i : I // φ i = j}, η i.val ∈ componentAffineChart q V (U i.val))
      (hρ : ∀ h : H, q ⁻¹ᵁ V ≤ (a h⁻¹).hom ⁻¹ᵁ (q ⁻¹ᵁ V))
      (hβ : ∀ (h : H) (i : {i : I // φ i = j}),
        componentAffineChart q V (U (h • i.val)) ≤
          (a h⁻¹).hom ⁻¹ᵁ componentAffineChart q V (U i.val))
      (hfix : ∀ (h : H) (i : {i : I // φ i = j}), h • i.val = i.val →
        (a h⁻¹).hom (η i.val) = η i.val)
      (hδ : ∀ (h : H) (i : {i : I // φ i = j}), h • i.val = i.val →
        componentAffineChart q V (U i.val) ≤
          (a h⁻¹).hom ⁻¹ᵁ componentAffineChart q V (U i.val)),
      IsAffineOpen (q ⁻¹ᵁ V) ∧
      (∀ i : {i : I // φ i = j}, IsAffineOpen (componentAffineChart q V (U i.val)) ∧
        Set.Nonempty (componentAffineChart q V (U i.val) : Set X) ∧
        IsClopen ((fun x : (q ⁻¹ᵁ V) ↦ (x : X)) ⁻¹'
          (componentAffineChart q V (U i.val) : Set X))) ∧
      (⨆ i : {i : I // φ i = j}, componentAffineChart q V (U i.val)) = q ⁻¹ᵁ V ∧
      IsDomain Γ(Z, V) ∧
      (∀ i : {i : I // φ i = j}, IsDomain Γ(X, componentAffineChart q V (U i.val))) ∧
      (∀ h : H, Function.Bijective ((a h⁻¹).hom.appLE _ _ (hρ h))) ∧
      (∀ (h : H) (i : {i : I // φ i = j}),
        Function.Bijective ((a h⁻¹).hom.appLE _ _ (hβ h i))) ∧
      (∃ e : Γ(X, q ⁻¹ᵁ V) ≃+*
          ((i : {i : I // φ i = j}) → Γ(X, componentAffineChart q V (U i.val))),
        (∀ (s : Γ(X, q ⁻¹ᵁ V)) (i : {i : I // φ i = j}),
          e s i = X.presheaf.map (homOfLE inf_le_right).op s) ∧
        ∀ (h : H) (s : Γ(X, q ⁻¹ᵁ V)) (i : {i : I // φ i = j}),
          e ((a h⁻¹).hom.appLE _ _ (hρ h) s) ⟨h • i.val, (hφ h i.val).trans i.property⟩ =
            (a h⁻¹).hom.appLE _ _ (hβ h i) (e s i)) ∧
      @IsFractionRing Γ(Z, V) _ (Z.residueField (ξ j)) _
        (Z.evaluation V (ξ j) hξV).hom.toAlgebra ∧
      ∀ i : {i : I // φ i = j},
        Function.Injective (q.appLE V (componentAffineChart q V (U i.val)) inf_le_right) ∧
        @IsFractionRing Γ(X, componentAffineChart q V (U i.val)) _
          (X.residueField (η i.val)) _ (X.evaluation _ _ (hηW i)).hom.toAlgebra ∧
        (∀ f : Z.residueField (ξ j) →+* X.residueField (η i.val),
          (∀ b : Γ(Z, V), f (Z.evaluation V (ξ j) hξV b) =
            X.evaluation _ _ (hηW i) (q.appLE V _ inf_le_right b)) ↔
          f = ((Z.residueFieldCongr ((hqη i.val).trans (congrArg ξ i.property))).inv ≫
            q.residueFieldMap (η i.val)).hom) ∧
        (∀ (b c : Γ(Z, V)), c ≠ 0 →
          ((Z.residueFieldCongr ((hqη i.val).trans (congrArg ξ i.property))).inv ≫
              q.residueFieldMap (η i.val))
            (Z.evaluation V (ξ j) hξV b / Z.evaluation V (ξ j) hξV c) =
          X.evaluation _ _ (hηW i) (q.appLE V _ inf_le_right b) /
            X.evaluation _ _ (hηW i) (q.appLE V _ inf_le_right c)) ∧
        (∀ (h : H) (hh : h • i.val = i.val) (b c : Γ(X, componentAffineChart q V (U i.val))),
          c ≠ 0 →
          ((X.residueFieldCongr (hfix h i hh)).inv ≫
              (a h⁻¹).hom.residueFieldMap (η i.val))
            (X.evaluation _ _ (hηW i) b / X.evaluation _ _ (hηW i) c) =
          X.evaluation _ _ (hηW i) ((a h⁻¹).hom.appLE _ _ (hδ h i hh) b) /
            X.evaluation _ _ (hηW i) ((a h⁻¹).hom.appLE _ _ (hδ h i hh) c)) := by
  sorry

end AlgebraicGeometry.Scheme
