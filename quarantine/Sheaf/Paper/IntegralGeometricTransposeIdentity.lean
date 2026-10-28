/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.IntegralGeometricComparisonData

/-! # A component of integral geometric comparison realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IntegralGeometricComparison

private theorem inverse_five {C : Type*} [Category C] {S A B D E T : C}
    (r : S ≅ T) (a : S ≅ A) (b : A ≅ B) (c : B ≅ D) (d : E ≅ D) (e : T ≅ E)
    (h : r.hom = a.hom ≫ b.hom ≫ c.hom ≫ d.inv ≫ e.inv) :
    r.inv = e.hom ≫ d.hom ≫ c.inv ≫ b.inv ≫ a.inv := by
  apply (cancel_mono r.hom).1
  rw [r.inv_hom_id, h]
  simp [Category.assoc]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X' X Y' Y : Scheme.{u}} {gx : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {gy : Y' ⟶ Y} {sq : IsPullback gx f' f gy}
  {c : Compactification f}
  [∀ z : X, Invertible (l : X.residueField z)]
  [∀ z : Y, Invertible (l : Y.residueField z)]
  [∀ z : X', Invertible (l : X'.residueField z)]
  [∀ z : Y', Invertible (l : Y'.residueField z)]
  (a : SpTowerMate.Data l E b o q sq c)
  (s : SpExceptionalBaseChange.IntegralData l E b o q a)


/-- A whole-tower mate reconstructs to the integral counit transpose.
This only asserts equality of two already constructed morphisms; it asserts no existence
of geometric data, comparison isomorphisms, or purity.
Source: latest blueprint integral geometric realization, Step 9;
integral-adjunction-bijection, Bijections.
(blueprint: lem-pur-integral-geometric-transpose-identity).

Proof: apply red_Y' to the integral adjunct-counit equation. Substitute s.counit,
s.counit', the beta reduction equation, and the two pullback comparison naturality
squares. Full faithfulness identifies the reduction of reconstructed with the conjugated
actual tower mate. Naturality of supportComparison moves that conjugation past F', and
naturality of exceptionalComparison and the two counits cancels its target factor.
The resulting equation is the defining tower mate counit equation. Thus faithfulness
of red_Y' gives the integral counit equation. Injectivity of the adjunction Hom equivalence then
identifies reconstructed with integralTranspose. This uses whole-tower maps only;
neither evaluation nor scalar restriction is assumed faithful. The calculation is
valid for any coefficient extension and also for a zero object or an identity square.
-/
theorem integral_geometric_transpose_identity
    (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    (beta : SpIntegralAdjunction.support l E c s.support_closed ⋙
        constructibleIntegralPullback l E gy ≅
      constructibleIntegralPullback l E gx ⋙
        SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed')
    (hbeta : ∀ M : sfIntegralConstructibleCategory l E X,
      (SpExceptionalBaseChange.red l E b q s.rY').map (beta.hom.app M) =
        SpExceptionalBaseChange.exchangeReduction l E b o q a s x M)
    (K : sfIntegralConstructibleCategory l E Y) :
    SpExceptionalBaseChange.reconstructed l E b o q a s x hb K =
      SpExceptionalBaseChange.integralTranspose l E b o q a s beta K := by
  let : IsIso (SpTowerMate.beta l E b o q a x) := hb
  let F := SpIntegralAdjunction.support l E c s.support_closed
  let F' := SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed'
  let Fb := SpTowerGluing.support l E b o q c a.support_closed
  let Fb' := SpTowerGluing.support l E b o q (c.ofIsPullback sq) a.support_closed'
  let RX := SpExceptionalBaseChange.red l E b q s.rX
  let RY := SpExceptionalBaseChange.red l E b q s.rY
  let RX' := SpExceptionalBaseChange.red l E b q s.rX'
  let RY' := SpExceptionalBaseChange.red l E b q s.rY'
  let U := SpTowerMate.U l E b o q a
  let V := SpTowerMate.V l E b o q a
  let Q := constructibleIntegralPullback l E gx
  let P := constructibleIntegralPullback l E gy
  let B := asIso (SpTowerMate.beta l E b o q a x)
  let t := SpExceptionalBaseChange.reconstructed l E b o q a s x hb K
  have hi (M : sfIntegralConstructibleCategory l E X) :
      RY'.map (beta.inv.app M) =
        s.supportComparison'.hom.app (Q.obj M) ≫
          Fb'.map (s.pullComparison.hom.app M) ≫ B.inv.app (RX.obj M) ≫
          V.map (s.supportComparison.inv.app M) ≫ s.pullComparison'.inv.app (F.obj M) := by
    have hh := hbeta M
    unfold SpExceptionalBaseChange.exchangeReduction at hh
    exact inverse_five (RY'.mapIso (beta.app M))
      (s.pullComparison'.app (F.obj M)) (V.mapIso (s.supportComparison.app M))
      (B.app (RX.obj M)) (Fb'.mapIso (s.pullComparison.app M))
      (s.supportComparison'.app (Q.obj M)) hh
  have ht : RX'.map t =
      s.pullComparison.hom.app (s.right.obj K) ≫ U.map (s.exceptionalComparison.hom.app K) ≫
        (SpTowerMate.mate l E b o q a x hb).app (RY.obj K) ≫
        a.right'.map (s.pullComparison'.inv.app K) ≫
        s.exceptionalComparison'.inv.app (P.obj K) := by
    dsimp only [t]
    unfold SpExceptionalBaseChange.reconstructed
    erw [s.rX'.fullyFaithful.map_preimage]
    simp [SpExceptionalBaseChange.source, SpExceptionalBaseChange.target,
      Category.assoc, U, P, RY]
  have hm : Fb'.map ((SpTowerMate.mate l E b o q a x hb).app (RY.obj K)) ≫
      a.adjunction'.counit.app (V.obj (RY.obj K)) =
        B.inv.app (a.right.obj (RY.obj K)) ≫ V.map (a.adjunction.counit.app (RY.obj K)) := by
    exact mateEquiv_counit a.adjunction a.adjunction'
      (TwoSquare.mk _ _ _ _ (inv (SpTowerMate.beta l E b o q a x))) (RY.obj K)
  apply (s.adjunction'.homEquiv _ _).symm.injective
  rw [SpExceptionalBaseChange.integralTranspose, Equiv.symm_apply_apply,
    Adjunction.homEquiv_counit]
  apply s.rY'.fullyFaithful.map_injective
  change RY'.map (F'.map t ≫ s.adjunction'.counit.app (P.obj K)) =
    RY'.map (beta.inv.app (s.right.obj K) ≫ P.map (s.adjunction.counit.app K))
  rw [Functor.map_comp, Functor.map_comp, hi, s.counit']
  erw [s.supportComparison'.hom.naturality_assoc t]
  simp only [Functor.comp_map]
  erw [ht]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% ((Fb'.mapIso (s.exceptionalComparison'.app (P.obj K))).inv_hom_id)]
  erw [a.adjunction'.counit.naturality]
  rw [reassoc_of% hm]
  erw [B.inv.naturality_assoc]
  erw [← s.pullComparison'.inv.naturality (s.adjunction.counit.app K)]
  simp only [Functor.comp_map]
  rw [s.counit]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% ((V.mapIso (s.supportComparison.app (s.right.obj K))).inv_hom_id)]
  simp only [Functor.id_map, Functor.id_obj]
  rfl

end AlgebraicGeometry.ProEtale.IntegralGeometricComparison
