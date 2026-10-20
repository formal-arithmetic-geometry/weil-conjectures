/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.ModuleExchangeCompositeBaseChange
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.AlgebraicGeometry.LimitFibreProducts
import Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit
import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import Sheaf.AlgebraicGeometry.FieldExtensionExchange
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.CategoryTheory.MateIsoAlongEquivalences

/-!
# Generic direct-image exchange with finite constant coefficients

Source: Stacks Project, Tags 0F09 and 0F1C, geometric-generic specialization;
blueprint sec-six-functors, sk-prop-sf-biduality-general
(blueprint: lem-sf-etale-generic-direct-image-exchange).

The helpers describe the two canonical squares on the chosen corners `W ×_B Spec L`,
not iterated pullbacks. In the outer square the projection to W is written as the
composite through `W ×_B Spec Q`; the pullback equations identify it with `pullback.fst`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option linter.defProp false in
/-- The ordinary generic base-change square (also used for the outer base change).
Only the commutativity proof is packaged: all four maps are the canonical maps of the
chosen pullbacks. Source: Stacks Tags 01JX, 0F09
(blueprint: lem-sf-etale-generic-direct-image-exchange). -/
noncomputable def genericDirectImageFirstSquare {B S : Scheme.{u}}
    {T Y : Over B} (h : T ⟶ Y) (q : S ⟶ B) :
    CommSq (pullback.fst T.hom q) (((Over.pullback q).map h).left)
      h.left (pullback.fst Y.hom q) :=
  ⟨by simp [Over.pullback_map_left]⟩

set_option linter.defProp false in
/-- The field-extension square on the chosen corners `T ×_B S'`, `Y ×_B S'`.
Its horizontal maps are the existing `AlgebraicGeometry.baseChangeMap`, not freely chosen morphisms.
Source: Stacks Tags 01JX, 0F1C; base-change pasting
(blueprint: lem-sf-etale-generic-direct-image-exchange). -/
noncomputable def genericDirectImageSecondSquare {B S S' : Scheme.{u}}
    {T Y : Over B} (h : T ⟶ Y) (q : S ⟶ B) (l : S' ⟶ S) :
    CommSq (AlgebraicGeometry.baseChangeMap T.hom (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q))
      (((Over.pullback (l ≫ q)).map h).left) (((Over.pullback q).map h).left)
      (AlgebraicGeometry.baseChangeMap Y.hom (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q)) :=
  ⟨by
    apply pullback.hom_ext <;>
      simp [AlgebraicGeometry.baseChangeMap, Over.pullback_map_left, Category.assoc]⟩

/-- Both conclusions of the generic-exchange lemma, written on the unbounded module
categories. The outer rectangle has corners `W ×_B S'`; its horizontal projection is
`AlgebraicGeometry.baseChangeMap W.hom l ≫ pullback.fst W.hom q = pullback.fst W.hom (l ≫ q)`.
The displayed equality includes both canonical inverse-image composition comparisons.
Source: Stacks Tags 0F09 and 0F1C, successive base changes
(blueprint: lem-sf-etale-generic-direct-image-exchange). -/
def genericDirectImageExchangeConclusion (A : Type (u + 1)) [CommRing A]
    {B S S' : Scheme.{u}} {T Y : Over B} (h : T ⟶ Y)
    (q : S ⟶ B) (l : S' ⟶ S) (E : DerivedCategoryModule A T.left) : Prop :=
  IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
    ((genericDirectImageSecondSquare h q l).horiz_comp
      (genericDirectImageFirstSquare h q))).app E) ∧
  (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
    ((genericDirectImageSecondSquare h q l).horiz_comp
      (genericDirectImageFirstSquare h q))).app E =
    (moduleInverseImageCompIso A (pullback.fst Y.hom q)
      (AlgebraicGeometry.baseChangeMap Y.hom
        (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q))).inv.app
        ((R(lowerStar (ModuleCat.{u + 1} A) h.left)).obj E) ≫
    D(upperStar (ModuleCat.{u + 1} A)
      (AlgebraicGeometry.baseChangeMap Y.hom (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q))).map
        ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
          (genericDirectImageFirstSquare h q)).app E) ≫
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (genericDirectImageSecondSquare h q l)).app
        ((D(upperStar (ModuleCat.{u + 1} A) (pullback.fst T.hom q))).obj E) ≫
    (R(lowerStar (ModuleCat.{u + 1} A) (((Over.pullback (l ≫ q)).map h).left))).map
      ((moduleInverseImageCompIso A (pullback.fst T.hom q)
        (AlgebraicGeometry.baseChangeMap T.hom
          (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q))).hom.app E)

/-- Generic direct-image exchange is invertible and equals the two successive exchanges.
Source: Stacks Project, Tags 0F09 and 0F1C, geometric-generic specialization
(blueprint: lem-sf-etale-generic-direct-image-exchange).

Proof plan (the five steps of the node):
1. By lem-sc-integral-function-field-affine-fraction identify Q with the generic stalk.
   Lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods expresses Spec Q over B as
   the directed limit of its nonempty affine generic neighbourhoods, with affine transitions.
2. The field F is Noetherian. Lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-locally-noetherian-quasi-separated make B Noetherian and quasi-separated.
   Lem-weil-pbc-qcqs-morphism-permanence makes the affine neighbourhood inclusions qcqs.
   They are smooth by lem-pc-open-immersion-smooth-composition. Base change preserves
   smoothness (lem-pc-proper-base-change, clause 2) and qcqs. The constant Y and B systems
   and lem-weil-pbc-limit-fibre-products identify Y_Q with the limit of Y ×_B U_i.
3. Forget coefficients using lem-kun-unbounded-abelian-exchange-comparison. Since NA=0,
   all cohomology stalks are N-torsion, and the inverse of N in F remains an inverse on
   Y and all its base changes. The underlying object is bounded below. Apply lem-kun-0f09
   to h with stages Y ×_B U_i and limit Y_Q. Lem-kun-unbounded-exchange-agrees identifies
   the bounded-below and unbounded abelian mates. The endpoint comparison isomorphisms
   and conservativity in lem-kun-unbounded-abelian-exchange-comparison give invertibility
   of the actual module exchange to Q.
4. The base change h_Q is qcqs by lem-weil-pbc-qcqs-morphism-permanence. Exact inverse
   image (prop-weil-pbc-inverse-image-modules-exact) preserves bounded belowness. Apply
   lem-kun-0f1c-exchange to L/Q, including its inseparable case. The same forgetting and
   bounded-below comparison gives the unbounded module exchange on iterated corners.
   By def-pc-base-change and lem-weil-pbc-cartesian-square-pasting the canonical maps
   from W_L to (W_Q)_L are isomorphisms respecting both projections. Their inverse images
   are equivalences by lem-weil-pbc-inverse-image-composition (2),(3); hence their mate
   is invertible by lem-weil-mate-iso-along-equivalences. Apply
   lem-fin-module-exchange-composite-base-change to obtain the exchange for the chosen
   second square on W_L itself.
5. Paste these two squares. By def-pc-base-change their horizontal composite is the
   geometric-generic square. Lem-fin-module-exchange-composite-base-change gives exactly
   the four-arrow equality in genericDirectImageExchangeConclusion, including the two
   moduleInverseImageCompIso comparisons. Its middle arrows are isomorphisms by steps
   3 and 4; functors preserve inverses and composites of isomorphisms are isomorphisms.
   This proves both invertibility of the specified mate and the compatibility clause. -/
theorem genericDirectImageExchange
    (F : Type u) [Field F] [IsAlgClosed F]
    (N : ℕ) (hN : 1 ≤ N) (hNF : IsUnit (N : F))
    (A : Type (u + 1)) [CommRing A] [Finite A] (hNA : ∀ a : A, N • a = 0)
    (B : Scheme.{u}) [B.Over (Spec (.of F))]
    [Smooth (B ↘ Spec (.of F))] [IsIntegral B]
    [LocallyOfFiniteType (B ↘ Spec (.of F))] [QuasiCompact (B ↘ Spec (.of F))]
    (hBdim : topologicalKrullDim B = 1)
    (U : B.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (Q : Type u) [Field Q] [Algebra (B.presheaf.obj (op U)) Q]
    [IsFractionRing (B.presheaf.obj (op U)) Q]
    (L : Type u) [Field L] [Algebra Q L] [IsAlgClosed L] [Algebra.IsAlgebraic Q L]
    (T Y : Over B) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (h : T ⟶ Y) [QuasiCompact h.left] [QuasiSeparated h.left]
    (E : _root_.DerivedCategory.Plus (Sheaf T.left.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    genericDirectImageExchangeConclusion A h
      (Spec.map (CommRingCat.ofHom (algebraMap (B.presheaf.obj (op U)) Q)) ≫ hU.fromSpec)
      (Spec.map (CommRingCat.ofHom (algebraMap Q L))) E.obj := by
  sorry

end AlgebraicGeometry.Etale
