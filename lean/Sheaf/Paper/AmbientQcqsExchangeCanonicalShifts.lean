/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.ModuleDerivedFunctorShifts
import Sheaf.Paper.KFlatDerivedAdjunctionTransportShifts
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Canonical shifts of the ambient condensed-module exchange

Source: Stacks Project, derived.tex, Tags 015F, 05SU and 0DVC; blueprint
compactification coherence, refinement (2)
(blueprint: lem-sfb-ambient-qcqs-exchange-canonical-shifts).

All categories are ordinary unbounded derived categories. The pullback shifts are
transported from exact termwise inverse image by `modulePullbackExactComparison`;
the pushforward shifts are the fixed K-injective shifts. The transformation is the
published `condensedAmbientExchange`, rather than a choice of base-change map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
  {f : X ⟶ Y} {f' : X' ⟶ C}

/-- The specified adjunction has its fixed shifts, by the published transport theorem. -/
private theorem ambientAdjunction_commShift {U V : Scheme.{u}} (h : U ⟶ V) :
    Adjunction.CommShift
      (F := moduleObjectDerivedPullback Λ h) (G := moduleObjectDerivedPushforward Λ h)
      (derivedUpperStarLowerStarAdjunction Λ h) ℤ := by
  exact (kflat_derived_adjunction_transport_shifts (Mon.mk Λ) h).2.2

/-- The actual ambient square is the specified shift-compatible compositor square. -/
private theorem ambientPullbackComparison_commShift
    (sq : ChosenCartesianSquare a f' f c) :
    NatTrans.CommShift
      (F₁ := moduleObjectDerivedPullback Λ c ⋙ moduleObjectDerivedPullback Λ f')
      (F₂ := moduleObjectDerivedPullback Λ f ⋙ moduleObjectDerivedPullback Λ a)
      (condensedAmbientPullbackComparison Λ sq).hom ℤ := by
  change NatTrans.CommShift
    (modulePullbackSquareComparison Λ f c a f' sq.toCommSq.w.symm).hom ℤ
  constructor
  intro n
  ext K
  exact (module_pullback_square_shift Λ f c a f' sq.toCommSq.w.symm K n).symm

/-- Taking the mate preserves compatibility with the specified shifts. -/
private theorem ambientExchange_commShift (sq : ChosenCartesianSquare a f' f c) :
    NatTrans.CommShift
      (F₁ := moduleObjectDerivedPushforward Λ f ⋙ moduleObjectDerivedPullback Λ c)
      (F₂ := moduleObjectDerivedPullback Λ a ⋙ moduleObjectDerivedPushforward Λ f')
      (condensedAmbientExchange Λ sq) ℤ := by
  have := ambientAdjunction_commShift Λ f
  have := ambientAdjunction_commShift Λ f'
  have := ambientPullbackComparison_commShift Λ sq
  exact NatTrans.CommShift.mateEquiv
    (G := moduleObjectDerivedPullback Λ c) (H := moduleObjectDerivedPullback Λ a)
    (L₁ := moduleObjectDerivedPullback Λ f) (R₁ := moduleObjectDerivedPushforward Λ f)
    (L₂ := moduleObjectDerivedPullback Λ f') (R₂ := moduleObjectDerivedPushforward Λ f')
    (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (condensedAmbientPullbackComparison Λ sq).hom)

/-- Both ambient composites are triangulated, and their actual exchange commutes
with every integer shift using the specified termwise/K-injective comparisons.
Source: Stacks Tags 015F, 05SU and 0DVC; blueprint refinement (2)
(blueprint: lem-sfb-ambient-qcqs-exchange-canonical-shifts).

Proof: (1) Apply `lem-sfb-module-derived-functor-compositor-shifts` to the four edges.
Its exact comparison identifies K-flat pullback with exact termwise pullback; it also
fixes the K-injective pushforward shifts. Compose triangulated functors using
`lem-weil-pbc-triangulated-functor-composite`.
(2) `lem-sfb-kflat-derived-adjunction-transport-shifts` identifies the actual adjunctions
with their exact-left forms and proves compatibility of their units and counits with
these fixed shifts.
(3) Expand `def-weil-pbc-ambient-ringed-exchange` as unit, whiskered canonical square,
and whiskered counit. The square is built from the specified pullback compositors;
under the exact comparisons it is the localized termwise square by step (1).
The adjunction transport formulas identify the units and counits in this expansion.
(4) By `lem-weil-pbc-commshift-nattrans-comp-whisker`, each factor commutes with [n].
Compose the three identities: the intermediate comparisons cancel, leaving exactly
the displayed equation, for every integer n, without assuming exchange invertible. -/
theorem ambient_qcqs_exchange_canonical_shifts (sq : ChosenCartesianSquare a f' f c) :
    (moduleObjectDerivedPushforward Λ f ⋙ moduleObjectDerivedPullback Λ c).IsTriangulated ∧
      (moduleObjectDerivedPullback Λ a ⋙ moduleObjectDerivedPushforward Λ f').IsTriangulated ∧
      ∀ (n : ℤ) (L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
        (condensedAmbientExchange Λ sq).app (L⟦n⟧) ≫
            ((moduleObjectDerivedPullback Λ a ⋙
              moduleObjectDerivedPushforward Λ f').commShiftIso n).hom.app L =
          ((moduleObjectDerivedPushforward Λ f ⋙
            moduleObjectDerivedPullback Λ c).commShiftIso n).hom.app L ≫
            ((condensedAmbientExchange Λ sq).app L) ⟦n⟧' := by
  have := (module_derived_functors_exact_and_comparison_shifts Λ f).2.1
  have := (module_derived_functors_exact_and_comparison_shifts Λ c).1
  have := (module_derived_functors_exact_and_comparison_shifts Λ a).1
  have := (module_derived_functors_exact_and_comparison_shifts Λ f').2.1
  have := ambientExchange_commShift Λ sq
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro n L
  exact (NatTrans.shift_app_comm
    (F₁ := moduleObjectDerivedPushforward Λ f ⋙ moduleObjectDerivedPullback Λ c)
    (F₂ := moduleObjectDerivedPullback Λ a ⋙ moduleObjectDerivedPushforward Λ f')
    (condensedAmbientExchange Λ sq) n L).symm

/-- The units, counits and actual localized pullback square used by the exchange
respect the same fixed integer shift structures.
Source: Stacks Tags 015F, 05SU and 0DVC; blueprint refinement (2)
(blueprint: lem-sfb-ambient-qcqs-exchange-canonical-shifts).

Proof: use `lem-sfb-kflat-derived-adjunction-transport-shifts` for f and f'. Its unit
formula is eta^P = G(c.inv) eta^A and its counit formula is eps^P = eps^A c.hom.
The exact comparisons c commute with shifts by
`lem-sfb-module-derived-functor-compositor-shifts`, so these are the actual units
and counits with their fixed K-injective right shifts, not shifts chosen anew from
an adjunction. For the square, the same compositor normalization identifies it with
the localized ordinary square. The two shifted differential signs agree degreewise;
whiskering, composition and inversion preserve shift compatibility by
`lem-weil-pbc-commshift-nattrans-comp-whisker`. -/
theorem ambient_qcqs_exchange_canonical_normalization
    (sq : ChosenCartesianSquare a f' f c) :
    NatTrans.CommShift
        (F₁ := 𝟭 _) (F₂ := moduleObjectDerivedPullback Λ f ⋙
          moduleObjectDerivedPushforward Λ f)
        (derivedUpperStarLowerStarAdjunction Λ f).unit ℤ ∧
      NatTrans.CommShift
        (F₁ := moduleObjectDerivedPushforward Λ f ⋙ moduleObjectDerivedPullback Λ f)
        (F₂ := 𝟭 _) (derivedUpperStarLowerStarAdjunction Λ f).counit ℤ ∧
      NatTrans.CommShift
        (F₁ := 𝟭 _) (F₂ := moduleObjectDerivedPullback Λ f' ⋙
          moduleObjectDerivedPushforward Λ f')
        (derivedUpperStarLowerStarAdjunction Λ f').unit ℤ ∧
      NatTrans.CommShift
        (F₁ := moduleObjectDerivedPushforward Λ f' ⋙ moduleObjectDerivedPullback Λ f')
        (F₂ := 𝟭 _) (derivedUpperStarLowerStarAdjunction Λ f').counit ℤ ∧
      NatTrans.CommShift
        (F₁ := moduleObjectDerivedPullback Λ c ⋙ moduleObjectDerivedPullback Λ f')
        (F₂ := moduleObjectDerivedPullback Λ f ⋙ moduleObjectDerivedPullback Λ a)
        (condensedAmbientPullbackComparison Λ sq).hom ℤ := by
  have := ambientAdjunction_commShift Λ f
  have := ambientAdjunction_commShift Λ f'
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    ambientPullbackComparison_commShift Λ sq⟩

/-- On a distinguished triangle, the three actual exchange components form a morphism
between the two distinguished image triangles, including the connecting-arrow square.
Source: Stacks Tags 015F, 05SU and 0DVC; blueprint refinement (2)
(blueprint: lem-sfb-ambient-qcqs-exchange-canonical-shifts).

Proof: step (1) of the node makes both image triangles distinguished. Naturality of
`condensedAmbientExchange` gives the first two squares. For the connecting morphism
w, naturality gives Ex(K3) followed by Psi(w) = Phi(w) followed by Ex(K1[1]).
Compose with zeta and apply step (4) at n = 1, replacing Ex(K1[1]) followed by zeta
by xi followed by Ex(K1)[1]. This is precisely the third triangle-morphism square.
This argument uses no geometric, boundedness or constructibility restriction. -/
theorem ambient_qcqs_exchange_distinguished_triangle
    (sq : ChosenCartesianSquare a f' f c)
    (T : Triangle (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (_hT : T ∈ distTriang _) :
    (moduleObjectDerivedPushforward Λ f ⋙
        moduleObjectDerivedPullback Λ c).mapTriangle.obj T ∈ distTriang _ ∧
      (moduleObjectDerivedPullback Λ a ⋙
        moduleObjectDerivedPushforward Λ f').mapTriangle.obj T ∈ distTriang _ ∧
      ∃ t : (moduleObjectDerivedPushforward Λ f ⋙
          moduleObjectDerivedPullback Λ c).mapTriangle.obj T ⟶
        (moduleObjectDerivedPullback Λ a ⋙
          moduleObjectDerivedPushforward Λ f').mapTriangle.obj T,
        t.hom₁ = (condensedAmbientExchange Λ sq).app T.obj₁ ∧
        t.hom₂ = (condensedAmbientExchange Λ sq).app T.obj₂ ∧
        t.hom₃ = (condensedAmbientExchange Λ sq).app T.obj₃ := by
  obtain ⟨hΦ, hΨ, hshift⟩ := ambient_qcqs_exchange_canonical_shifts Λ sq
  have := hΦ
  have := hΨ
  refine ⟨Functor.map_distinguished _ T _hT, Functor.map_distinguished _ T _hT, ?_⟩
  refine ⟨{
    hom₁ := (condensedAmbientExchange Λ sq).app T.obj₁
    hom₂ := (condensedAmbientExchange Λ sq).app T.obj₂
    hom₃ := (condensedAmbientExchange Λ sq).app T.obj₃
    comm₁ := ?_
    comm₂ := ?_
    comm₃ := ?_ }, rfl, rfl, rfl⟩
  · exact (condensedAmbientExchange Λ sq).naturality T.mor₁
  · exact (condensedAmbientExchange Λ sq).naturality T.mor₂
  · change
      ((moduleObjectDerivedPushforward Λ f ⋙ moduleObjectDerivedPullback Λ c).map T.mor₃ ≫
          ((moduleObjectDerivedPushforward Λ f ⋙
            moduleObjectDerivedPullback Λ c).commShiftIso 1).hom.app T.obj₁) ≫
          ((condensedAmbientExchange Λ sq).app T.obj₁) ⟦(1 : ℤ)⟧' =
        (condensedAmbientExchange Λ sq).app T.obj₃ ≫
          (moduleObjectDerivedPullback Λ a ⋙ moduleObjectDerivedPushforward Λ f').map T.mor₃ ≫
          ((moduleObjectDerivedPullback Λ a ⋙
            moduleObjectDerivedPushforward Λ f').commShiftIso 1).hom.app T.obj₁
    rw [Category.assoc, ← hshift 1 T.obj₁, ← Category.assoc]
    have hnat :
        (moduleObjectDerivedPushforward Λ f ⋙ moduleObjectDerivedPullback Λ c).map T.mor₃ ≫
            (condensedAmbientExchange Λ sq).app (T.obj₁⟦(1 : ℤ)⟧) =
          (condensedAmbientExchange Λ sq).app T.obj₃ ≫
            (moduleObjectDerivedPullback Λ a ⋙
              moduleObjectDerivedPushforward Λ f').map T.mor₃ :=
      (condensedAmbientExchange Λ sq).naturality T.mor₃
    rw [hnat, Category.assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
