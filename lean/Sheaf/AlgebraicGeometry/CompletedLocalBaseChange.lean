/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.FiniteTypeBaseChangeAdicQuotients

/-!
# Completed local rings after base change to the completed base

Source: Stacks Project, More on Morphisms, Tag 0GDX, first proof paragraph, and
Commutative Algebra, Tag 00MA(3) (blueprint: lem-trf-completed-local-base-change).
The auxiliary definitions are the canonical base morphism, its fibre product,
and the two ring maps used to specify the completed isomorphism.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical morphism from the spectrum of the completed stalk to the scheme.
Source: Stacks, Tag 0GDX, first proof paragraph
(blueprint: lem-trf-completed-local-base-change). -/
noncomputable def completionBaseMap (S : Scheme.{u}) (s : S) :
    Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s))) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
    (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s)))) ≫ S.fromSpecStalk s

/-- The fibre product with the spectrum of the completed base stalk.
Source: Stacks, Tag 0GDX, first proof paragraph
(blueprint: lem-trf-completed-local-base-change). -/
noncomputable abbrev Hom.completionBaseChange {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    Scheme.{u} :=
  pullback f (S.completionBaseMap s)

/-- The canonical local map on stalks at a point over `x` in the completed base change.
Source: Stacks, Tag 0GDX, first proof paragraph, and Tag 00MA(3)
(blueprint: lem-trf-completed-local-base-change). -/
noncomputable def Hom.completionBaseChangeLocalMap {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (x : X) (z : f.completionBaseChange s)
    (hx : pullback.fst f (S.completionBaseMap s) z = x) :
    X.presheaf.stalk x →+* (f.completionBaseChange s).presheaf.stalk z :=
  ((X.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫
    (pullback.fst f (S.completionBaseMap s)).stalkMap z).hom

/-- The completed base acts on a base-changed stalk by the second projection.
Source: Stacks, Tag 0GDX, first proof paragraph
(blueprint: lem-trf-completed-local-base-change). -/
noncomputable def Hom.completionBaseChangeScalarMap {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (z : f.completionBaseChange s) :
    AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s) →+* (f.completionBaseChange s).presheaf.stalk z :=
  (StructureSheaf.toStalk _ (pullback.snd f (S.completionBaseMap s) z) ≫
    (pullback.snd f (S.completionBaseMap s)).stalkMap z).hom

/-- There is a unique point over `(x,b)`, and the canonical local base-change map
induces an isomorphism of completed stalks over the completed base.
The two levelwise formulas characterize the completion of the local base-change map
and the canonical completed-base action `α`. The last formula says that the ring
isomorphism respects that action, equivalently that it is an algebra isomorphism.

Source: Stacks Project, Tag 0GDX, first proof paragraph (context), and Tag 00MA(3).
(blueprint: lem-trf-completed-local-base-change).

Proof:
1. Choose finite-type affine charts around `s` and `x`. The fibre-product point
   correspondence (lem-weil-pbc-fibre-product-points) identifies points over `(x,b)`
   with the spectrum of the tensor of the residue fields. Completion preserves the
   base residue field (lem-weil-pbc-local-completion-local-ring), so this tensor is
   the field κ(x). Thus the point exists uniquely; its residue field is κ(x) by
   lem-weil-pbc-fibre-product-point-residue-field.
2. The completed base is Noetherian and local, and its canonical map is flat, by
   lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring,
   and lem-weil-pbc-noetherian-completion-flat. On the affine charts, the stalk map
   is the localization of the canonical inclusion into the tensor base change.
3. Apply lem-trf-finite-type-base-change-adic-quotients at every positive exponent.
   Its canonical quotient isomorphisms commute with transitions. The compatible
   inverse-limit lemma lem-trf-adic-inverse-limit-iso gives the displayed ring
   isomorphism, with the asserted formula on quotient representatives.
4. The local map from the base stalk to the original stalk similarly induces the
   completed-base map `α`, characterized at every quotient level. Naturality of
   localization and the quotient projections identifies its composite with the
   isomorphism with the action through the second projection. This proves scalar
   compatibility and independence of the affine charts.
-/
theorem completedLocalBaseChange {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) (x : X) (hxs : f x = s) :
    ∃ z : f.completionBaseChange s,
      ∃ hx : pullback.fst f (S.completionBaseMap s) z = x,
        pullback.snd f (S.completionBaseMap s) z =
          IsLocalRing.closedPoint
            (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
              (S.presheaf.stalk s)) ∧
        (∀ w : f.completionBaseChange s,
          pullback.fst f (S.completionBaseMap s) w = x →
          pullback.snd f (S.completionBaseMap s) w =
            IsLocalRing.closedPoint
              (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
                (S.presheaf.stalk s)) → w = z) ∧
        ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x) ≃+*
          AdicCompletion
            (IsLocalRing.maximalIdeal ((f.completionBaseChange s).presheaf.stalk z))
            ((f.completionBaseChange s).presheaf.stalk z),
          (∀ (n : ℕ)
            (t : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x)) (a : X.presheaf.stalk x),
            AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) n t =
              Ideal.Quotient.mk _ a →
            AdicCompletion.evalₐ
              (IsLocalRing.maximalIdeal ((f.completionBaseChange s).presheaf.stalk z))
              n (e t) = Ideal.Quotient.mk _ (f.completionBaseChangeLocalMap s x z hx a)) ∧
          ∃ α : AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
              (S.presheaf.stalk s) →+*
            AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x),
            (∀ (n : ℕ)
              (t : AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
                (S.presheaf.stalk s)) (a : S.presheaf.stalk s),
              AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (S.presheaf.stalk s)) n t =
                Ideal.Quotient.mk _ a →
              AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) n (α t) =
                Ideal.Quotient.mk _
                  (((S.presheaf.stalkCongr (.of_eq hxs.symm)).hom ≫ f.stalkMap x).hom a)) ∧
            ∀ t : AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
                (S.presheaf.stalk s),
              e (α t) = algebraMap ((f.completionBaseChange s).presheaf.stalk z)
                (AdicCompletion
                  (IsLocalRing.maximalIdeal ((f.completionBaseChange s).presheaf.stalk z))
                  ((f.completionBaseChange s).presheaf.stalk z))
                (f.completionBaseChangeScalarMap s z t) := by
  sorry

end AlgebraicGeometry.Scheme
