/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.RelClasses
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import WeilConjectures.RingTheory.MapIntoHenselianColimit

/-! # Local lifts of a separable algebraic residue extension

Source: Stacks Project, Algebra, Tags 09E0 and 04GT
(blueprint: lem-sfb-local-separable-residue-ind-finite-etale).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace IsLocalRing

/-- Witness data for the local finite-etale system in Stacks Project, Tag 09E0.
The residue fields use the actual maximal ideals; `stage_maximalIdeal` identifies
these with the extensions of the base maximal ideal. The cocone is an algebra
colimit, so all its arrows and its universal property respect the base ring.
Source: Stacks Project, Tag 09E0
(blueprint: lem-sfb-local-separable-residue-ind-finite-etale). -/
structure LocalSeparableResidueFiniteEtaleSystem
    (R E : Type u) [CommRing R] [IsLocalRing R] [Field E]
    [Algebra (ResidueField R) E] where
  I : Type u
  [order : PartialOrder I]
  [nonempty : Nonempty I]
  [directed : IsDirected I (· ≤ ·)]
  diagram : I ⥤ CommAlgCat.{u} R
  [stageLocal : ∀ i : I, IsLocalRing (diagram.obj i)]
  stage_finite : ∀ i : I, Module.Finite R (diagram.obj i)
  stage_etale : ∀ i : I,
    Etale (Spec.map (CommRingCat.ofHom (algebraMap R (diagram.obj i))))
  stage_injective : ∀ i : I, Function.Injective (algebraMap R (diagram.obj i))
  stage_local : ∀ i : I,
    (maximalIdeal (diagram.obj i)).comap (algebraMap R (diagram.obj i)) = maximalIdeal R
  transition_finite : ∀ (i j : I) (h : i ≤ j), (diagram.map (homOfLE h)).hom.toRingHom.Finite
  transition_etale : ∀ (i j : I) (h : i ≤ j),
    Etale (Spec.map (CommRingCat.ofHom (diagram.map (homOfLE h)).hom.toRingHom))
  transition_injective : ∀ (i j : I) (h : i ≤ j),
    Function.Injective (diagram.map (homOfLE h)).hom
  transition_local : ∀ (i j : I) (h : i ≤ j),
    (maximalIdeal (diagram.obj j)).comap (diagram.map (homOfLE h)).hom.toRingHom =
      maximalIdeal (diagram.obj i)
  stage_maximalIdeal : ∀ i : I,
    (maximalIdeal R).map (algebraMap R (diagram.obj i)) = maximalIdeal (diagram.obj i)
  residueEmbedding : ∀ i : I, ResidueField (diagram.obj i) →+* E
  residue_scalar : ∀ i : I,
    (residueEmbedding i).comp ((residue (diagram.obj i)).comp
      (algebraMap R (diagram.obj i))) = (algebraMap (ResidueField R) E).comp (residue R)
  residue_compatible : ∀ (i j : I) (h : i ≤ j),
    ((residueEmbedding j).comp (residue (diagram.obj j))).comp
      (diagram.map (homOfLE h)).hom.toRingHom =
        (residueEmbedding i).comp (residue (diagram.obj i))
  residue_union : ∀ x : E, ∃ (i : I) (y : ResidueField (diagram.obj i)),
    residueEmbedding i y = x
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  [colimitLocal : IsLocalRing cocone.pt]
  coprojection_injective : ∀ i : I, Function.Injective (cocone.ι.app i).hom
  coprojection_local : ∀ i : I,
    (maximalIdeal cocone.pt).comap (cocone.ι.app i).hom.toRingHom =
      maximalIdeal (diagram.obj i)
  colimit_maximalIdeal :
    (maximalIdeal R).map (algebraMap R cocone.pt) = maximalIdeal cocone.pt
  residueIso : ResidueField cocone.pt ≃+* E
  residueIso_coprojection : ∀ i : I,
    (residueIso.toRingHom.comp (residue cocone.pt)).comp (cocone.ι.app i).hom.toRingHom =
      (residueEmbedding i).comp (residue (diagram.obj i))

attribute [instance] LocalSeparableResidueFiniteEtaleSystem.order
  LocalSeparableResidueFiniteEtaleSystem.nonempty
  LocalSeparableResidueFiniteEtaleSystem.directed
  LocalSeparableResidueFiniteEtaleSystem.stageLocal
  LocalSeparableResidueFiniteEtaleSystem.colimitLocal

/-- Source: Stacks Project, Algebra, Tags 09E0 and 04GT
(blueprint: lem-sfb-local-separable-residue-ind-finite-etale).

Proof:
1. At a successor lift the monic minimal polynomial of a chosen element of E.
   The monic quotient has a power basis and closed fibre the simple residue extension
   (lem-weil-pbc-minimal-polynomial-quotient-field-iso,
   lem-sfb-separable-algebraic-intermediate-base, lem-weil-pbc-monic-quotient-free).
2. The quotient is integral by the multiplication-endomorphism argument. All its
   maximal ideals contract to the base maximal ideal; the closed fibre is a field,
   so it is local. Separability makes the derivative a unit; the standard-etale
   criterion proves etaleness (lem-weil-pbc-endomorphism-finite-module-monic,
   lem-weil-pbc-integral-maximal-contracts-maximal,
   lem-weil-pbc-standard-etale-monic-derivative).
3. Well-order E and apply transfinite recursion. At limits take unions: an element
   outside the union of the maximal ideals is already a unit at its stage, and
   the union ideal is the extension of the original maximal ideal. The residue
   images are the corresponding field unions and finally exhaust E
   (lem-weil-pbc-well-ordering-theorem, lem-trf-well-order-ordinal-enumeration,
   lem-weil-pbc-transfinite-recursion, def-weil-pbc-category-colimit).
4. Apply lem-sfb-transfinite-finite-etale-union. The finite-etale subalgebras form
   a nonempty directed poset exhausting the tower. Their transitions are finite
   and etale by lem-weil-pbc-etale-composition-cancellation.
5. The final ring is integral over each finite stage. Lying over and maximality
   over a maximal ideal show every stage is local, with local inclusions
   (lem-weil-pbc-integral-injective-lying-over,
   lem-weil-pbc-integral-prime-over-maximal-maximal).
6. Each closed fibre is a nonzero local finite-etale algebra over the residue field.
   It is a product of separable fields, hence a single field. Its maximal ideal
   is therefore the extended base ideal. Their embeddings exhaust E
   (lem-weil-pbc-etale-ring-base-change, lem-weil-pbc-etale-algebra-over-field-product).
7. The union has the algebra-colimit universal property: compatible maps agree
   on common stages, defining a unique algebra map on the union.
8. For each strictly henselian target, lem-weil-pbc-map-into-henselian-colimit
   applied to a single stage gives the unique local map with the specified residue.
   Uniqueness gives compatibility; the colimit map is local and has that residue
   because both assertions can be checked on representatives at stages.
-/
theorem exists_local_separable_residue_ind_finite_etale
    (R E : Type u) [CommRing R] [IsLocalRing R] [Field E]
    [Algebra (ResidueField R) E] [Algebra.IsSeparable (ResidueField R) E] :
    ∃ P : LocalSeparableResidueFiniteEtaleSystem R E,
      ∀ (S : Type v) [CommRing S] [Algebra R S] [IsStrictlyHenselianLocalRing S]
        [IsLocalHom (algebraMap R S)] (τ : E →+* ResidueField S),
        τ.comp (algebraMap (ResidueField R) E) =
          ResidueField.map (algebraMap R S) →
        ∃ (h : ∀ i : P.I, P.diagram.obj i →ₐ[R] S),
          (∀ i : P.I, IsLocalHom (h i)) ∧
          (∀ i : P.I, (residue S).comp (h i).toRingHom =
            (τ.comp (P.residueEmbedding i)).comp (residue (P.diagram.obj i))) ∧
          (∀ (i : P.I) (g : P.diagram.obj i →ₐ[R] S), IsLocalHom g →
            (residue S).comp g.toRingHom =
              (τ.comp (P.residueEmbedding i)).comp (residue (P.diagram.obj i)) → g = h i) ∧
          (∀ (i j : P.I) (hij : i ≤ j),
            (h j).comp (P.diagram.map (homOfLE hij)).hom = h i) ∧
          ∃ f : P.cocone.pt →ₐ[R] S, IsLocalHom f ∧
            (∀ i : P.I, f.comp (P.cocone.ι.app i).hom = h i) ∧
            (residue S).comp f.toRingHom =
              τ.comp (P.residueIso.toRingHom.comp (residue P.cocone.pt)) := by
  sorry

end IsLocalRing
