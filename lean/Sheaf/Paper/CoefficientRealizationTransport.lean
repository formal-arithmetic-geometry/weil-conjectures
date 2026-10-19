/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Coefficient and realization transport of the specified composites

Source: Weil blueprint, `sec-six-functors/sk-prop-sf-pf-coherence`, final paragraph
(blueprint: lem-sf-pf-coefficient-realization-transport).

The six categories are the supplied closed domains on X, bar X, Y, X', bar X', Y'.
Only primitive comparison squares are hypotheses. The four conclusions use the
actual adjunction mates and compactification composites of def-exchange-projection.
The subsequent statements express whiskering, finite pasting, successive comparisons,
identity transport, conditional refinement, and forward transport of equalities.
-/

set_option autoImplicit false

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃
universe vX vB vY vX' vB' vY' uX uB uY uX' uB' uY'

@[expose] public section

open scoped CategoryTheory.Functor

namespace CategoryTheory

section SuppliedDomains

variable {DX : Type uX} {DB : Type uB} {DY : Type uY}
  {DX' : Type uX'} {DB' : Type uB'} {DY' : Type uY'}
  [Category.{vX} DX] [Category.{vB} DB] [Category.{vY} DY]
  [Category.{vX'} DX'] [Category.{vB'} DB'] [Category.{vY'} DY']

/-- Reproduces `compactificationExchangeFromData` in the recorded
`Sheaf.Paper.ExchangeProjection` verbatim, with only its declaration name changed.
Compactification exchange from the supplied operation data on closed full domains.
Here `J,J'` are the open extensions, `P,P'` the proper pullbacks, `R,R'` their
right adjoints, and `G,H,B` the three horizontal pullbacks. `theta` is the specified
composition comparison for the proper square; `beta` is the specified open base change.
This is `Ex_{*,p}(j_! K)` followed by `Rp'_*(beta_K)`, with functor associators inserted.
At the integral, rational, and algebraically closed stages these are respectively the
completed, rationalized, and common-finite-field operations supplied by the node.
Source: blueprint, node def-exchange-projection, chosen compactification and other stages
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
noncomputable def compactificationExchangeFromTransportData
    (J : DX ⥤ DB) (J' : DX' ⥤ DB')
    (P : DY ⥤ DB) (R : DB ⥤ DY) (adj : P ⊣ R)
    (P' : DY' ⥤ DB') (R' : DB' ⥤ DY') (adj' : P' ⊣ R')
    (G : DY ⥤ DY') (H : DX ⥤ DX') (B : DB ⥤ DB')
    (theta : G ⋙ P' ≅ P ⋙ B) (beta : J ⋙ B ≅ H ⋙ J') :
    (J ⋙ R) ⋙ G ⟶ H ⋙ (J' ⋙ R') :=
  (Functor.associator J R G).hom ≫
    Functor.whiskerLeft J
      (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ theta.hom)).natTrans ≫
    (Functor.associator J B R').inv ≫
    Functor.whiskerRight beta.hom R' ≫
    (Functor.associator H J' R').hom

/-- Reproduces `compactificationProjectionFromData` in the recorded
`Sheaf.Paper.ExchangeProjection` verbatim, with only its declaration name changed.
Compactification projection from the supplied tensor, adjunction, and comparison data.
`mu` is the tensor-pullback isomorphism for the proper factor. `gamma` is the open
projection isomorphism followed by `Lj^* Lp^* ≅ Lf^*`, with exactly that order.
The first arrow is the existing counit-defined right-adjoint projection mate, so its
transpose is `mu` followed by `epsilon ⊗ 1`. The second arrow is `Rp_*(gamma)`.
No assertion that the resulting natural transformation is invertible is made.
Source: blueprint, node def-exchange-projection, projection and other coefficient stages
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
noncomputable def compactificationProjectionFromTransportData
    (J : DX ⥤ DB) (F : DY ⥤ DX) (P : DY ⥤ DB) (R : DB ⥤ DY) (adj : P ⊣ R)
    (TX : DX ⥤ DX ⥤ DX) (TB : DB ⥤ DB ⥤ DB) (TY : DY ⥤ DY ⥤ DY)
    (mu : (Functor.postcompose₂.obj P).obj TY ≅
      (((Functor.whiskeringLeft₂ DB).obj P).obj P).obj TB)
    (gamma : (((Functor.whiskeringLeft₂ DB).obj J).obj P).obj TB ≅
      (Functor.postcompose₂.obj J).obj
        ((((Functor.whiskeringLeft₂ DX).obj (𝟭 DX)).obj F).obj TX)) :
    J ⋙ (R ⋙ TY) ⟶
      (Functor.postcompose₂.obj (J ⋙ R)).obj
        ((((Functor.whiskeringLeft₂ DX).obj (𝟭 DX)).obj F).obj TX) :=
  Functor.whiskerLeft J (adj.rightAdjointProjectionMap mu.hom) ≫
    (Functor.postcompose₂.obj R).map gamma.hom

/-- Reproduces `ExchangeProjectionStage` in the recorded `Sheaf.Paper.ExchangeProjection`
verbatim, with only its declaration name changed. This helper belongs to the present local
transport statement; the recorded dependency and its finite-coefficient realization remain
unchanged.
The supplied operation and comparison data for one coefficient stage on its closed domains.
The categories are the prescribed full domains, rather than assumed ambient categories on
which higher-coefficient operations need not exist. The fields retain the square pullback
comparison, both adjunctions, the chosen-compactification identifications, and the actual
natural isomorphisms beta, mu, and gamma. These are data, not existence assertions.
Source: blueprint, node def-exchange-projection, other coefficient stages and domains
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
structure ExchangeProjectionTransportStage where
  pull : DY ⥤ DX
  push : DX ⥤ DY
  adjunction : pull ⊣ push
  pull' : DY' ⥤ DX'
  push' : DX' ⥤ DY'
  adjunction' : pull' ⊣ push'
  horizontal : DY ⥤ DY'
  horizontal' : DX ⥤ DX'
  pullbackComparison : horizontal ⋙ pull' ≅ pull ⋙ horizontal'
  openExtension : DX ⥤ DB
  openExtension' : DX' ⥤ DB'
  properPull : DY ⥤ DB
  properPush : DB ⥤ DY
  properAdjunction : properPull ⊣ properPush
  properPull' : DY' ⥤ DB'
  properPush' : DB' ⥤ DY'
  properAdjunction' : properPull' ⊣ properPush'
  compactifyingHorizontal : DB ⥤ DB'
  properPullbackComparison :
    horizontal ⋙ properPull' ≅ properPull ⋙ compactifyingHorizontal
  openBaseChange : openExtension ⋙ compactifyingHorizontal ≅ horizontal' ⋙ openExtension'
  tensorX : DX ⥤ DX ⥤ DX
  tensorBar : DB ⥤ DB ⥤ DB
  tensorY : DY ⥤ DY ⥤ DY
  tensorPullback : (Functor.postcompose₂.obj properPull).obj tensorY ≅
    (((Functor.whiskeringLeft₂ DB).obj properPull).obj properPull).obj tensorBar
  openProjection :
    (((Functor.whiskeringLeft₂ DB).obj openExtension).obj properPull).obj tensorBar ≅
      (Functor.postcompose₂.obj openExtension).obj
        ((((Functor.whiskeringLeft₂ DX).obj (𝟭 DX)).obj pull).obj tensorX)
  compactSupport : DX ⥤ DY
  compactSupport' : DX' ⥤ DY'
  compactSupportIdentification : compactSupport ≅ openExtension ⋙ properPush
  compactSupportIdentification' : compactSupport' ≅ openExtension' ⋙ properPush'

end SuppliedDomains


/-- An object in both systems with its specified invertible comparison.
Source: blueprint, final paragraph of prop-sf-pf-coherence
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
structure CoefficientRealizationObject
    {C₀ : Type u₀} {C₁ : Type u₁} [Category.{v₀} C₀] [Category.{v₁} C₁]
    (T : C₀ ⥤ C₁) where
  obj₀ : C₀
  obj₁ : C₁
  comparison : T.obj obj₀ ≅ obj₁

/-- Apply an operation with its supplied natural comparison to a compared object.
Source: blueprint, prop-sf-pf-coherence, operation comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def CoefficientRealizationObject.map
    {C₀ : Type u₀} {C₁ : Type u₁} {D₀ : Type u₂} {D₁ : Type u₃}
    [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} D₀] [Category.{v₃} D₁]
    {T : C₀ ⥤ C₁} {S : D₀ ⥤ D₁} (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁)
    (c : F₀ ⋙ S ≅ T ⋙ F₁) (x : CoefficientRealizationObject T) :
    CoefficientRealizationObject S where
  obj₀ := F₀.obj x.obj₀
  obj₁ := F₁.obj x.obj₁
  comparison := c.app x.obj₀ ≪≫ F₁.mapIso x.comparison

/-- Apply the supplied tensor comparison, including both input comparisons.
Source: blueprint, prop-sf-pf-coherence, tensor comparison
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def CoefficientRealizationObject.tensor
    {C₀ : Type u₀} {C₁ : Type u₁} [Category.{v₀} C₀] [Category.{v₁} C₁]
    {T : C₀ ⥤ C₁} (B₀ : C₀ ⥤ C₀ ⥤ C₀) (B₁ : C₁ ⥤ C₁ ⥤ C₁)
    (c : (Functor.postcompose₂.obj T).obj B₀ ≅
      (((Functor.whiskeringLeft₂ C₁).obj T).obj T).obj B₁)
    (x y : CoefficientRealizationObject T) : CoefficientRealizationObject T where
  obj₀ := (B₀.obj x.obj₀).obj y.obj₀
  obj₁ := (B₁.obj x.obj₁).obj y.obj₁
  comparison := (c.app x.obj₀).app y.obj₀ ≪≫
    (B₁.mapIso x.comparison).app (T.obj y.obj₀) ≪≫
    (B₁.obj x.obj₁).mapIso y.comparison

/-- One specified arrow in both systems, with fixed compared endpoints.
Source: blueprint, prop-sf-pf-coherence, equation b_t T(m) = m b_s
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
structure CoefficientRealizationArrow
    {C₀ : Type u₀} {C₁ : Type u₁} [Category.{v₀} C₀] [Category.{v₁} C₁]
    {T : C₀ ⥤ C₁} (source target : CoefficientRealizationObject T) where
  map₀ : source.obj₀ ⟶ target.obj₀
  map₁ : source.obj₁ ⟶ target.obj₁

/-- The comparison square for the specified arrow.
Source: blueprint, prop-sf-pf-coherence, displayed intertwining equation
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def CoefficientRealizationArrow.intertwines
    {C₀ : Type u₀} {C₁ : Type u₁} [Category.{v₀} C₀] [Category.{v₁} C₁]
    {T : C₀ ⥤ C₁} {x y : CoefficientRealizationObject T}
    (a : CoefficientRealizationArrow x y) : Prop :=
  T.map a.map₀ ≫ y.comparison.hom = x.comparison.hom ≫ a.map₁

section FormalTransport

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]

/-- Pasting two comparison squares, in Lean's left-to-right composition order.
Source: blueprint, prop-sf-pf-coherence, finite pasting calculation
(blueprint: lem-sf-pf-coefficient-realization-transport).
Proof: expand functoriality on the composite; substitute the second square and then
the first, reassociating at each step. This proves the finite-string calculation by
iteration, including the two complete base-change routes. -/
theorem coefficientRealizationTransport_comp
    {T : C₀ ⥤ C₁} {x y z : CoefficientRealizationObject T}
    (a : CoefficientRealizationArrow x y) (b : CoefficientRealizationArrow y z)
    (ha : a.intertwines) (hb : b.intertwines) :
    T.map (a.map₀ ≫ b.map₀) ≫ z.comparison.hom =
      x.comparison.hom ≫ (a.map₁ ≫ b.map₁) := by
  change T.map a.map₀ ≫ y.comparison.hom = x.comparison.hom ≫ a.map₁ at ha
  change T.map b.map₀ ≫ z.comparison.hom = y.comparison.hom ≫ b.map₁ at hb
  rw [T.map_comp, Category.assoc, hb, ← Category.assoc, ha, Category.assoc]

/-- Whiskering an intertwined arrow by any operation with its supplied natural comparison.
Source: blueprint, prop-sf-pf-coherence, whiskered composites
(blueprint: lem-sf-pf-coefficient-realization-transport).
Proof: apply the target operation to the original comparison equation and paste the
naturality square of c at the source arrow. The comparisons at both endpoints are
exactly those of CoefficientRealizationObject.map. -/
theorem coefficientRealizationTransport_map
    {D₀ : Type u₂} {D₁ : Type u₃} [Category.{v₂} D₀] [Category.{v₃} D₁]
    {T : C₀ ⥤ C₁} {S : D₀ ⥤ D₁} (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁)
    (c : F₀ ⋙ S ≅ T ⋙ F₁) {x y : CoefficientRealizationObject T}
    (a : CoefficientRealizationArrow x y) (ha : a.intertwines) :
    S.map (F₀.map a.map₀) ≫ (y.map F₀ F₁ c).comparison.hom =
      (x.map F₀ F₁ c).comparison.hom ≫ F₁.map a.map₁ := by
  change T.map a.map₀ ≫ y.comparison.hom = x.comparison.hom ≫ a.map₁ at ha
  change S.map (F₀.map a.map₀) ≫
      (c.hom.app y.obj₀ ≫ F₁.map y.comparison.hom) =
    (c.hom.app x.obj₀ ≫ F₁.map x.comparison.hom) ≫ F₁.map a.map₁
  have hc := c.hom.naturality a.map₀
  change S.map (F₀.map a.map₀) ≫ c.hom.app y.obj₀ =
    c.hom.app x.obj₀ ≫ F₁.map (T.map a.map₀) at hc
  rw [← Category.assoc, hc, Category.assoc, ← F₁.map_comp,
    ha, F₁.map_comp, Category.assoc]

/-- Tensor whiskering, including tensoring with an identity in either input.
Source: blueprint, prop-sf-pf-coherence, tensor naturality and complete routes
(blueprint: lem-sf-pf-coefficient-realization-transport).
Proof: paste the naturality squares of the tensor comparison in its two variables,
then substitute the two given arrow comparison equations. Identity arrows are included
by taking either arrow to be the identity. Finite pasting with the preceding statements
handles the specified pullback/tensor base-change routes. -/
theorem coefficientRealizationTransport_tensor
    {T : C₀ ⥤ C₁} (B₀ : C₀ ⥤ C₀ ⥤ C₀) (B₁ : C₁ ⥤ C₁ ⥤ C₁)
    (c : (Functor.postcompose₂.obj T).obj B₀ ≅
      (((Functor.whiskeringLeft₂ C₁).obj T).obj T).obj B₁)
    {x x' y y' : CoefficientRealizationObject T}
    (a : CoefficientRealizationArrow x x') (b : CoefficientRealizationArrow y y')
    (ha : a.intertwines) (hb : b.intertwines) :
    T.map ((B₀.map a.map₀).app y.obj₀ ≫ (B₀.obj x'.obj₀).map b.map₀) ≫
        (x'.tensor B₀ B₁ c y').comparison.hom =
      (x.tensor B₀ B₁ c y).comparison.hom ≫
        ((B₁.map a.map₁).app y.obj₁ ≫ (B₁.obj x'.obj₁).map b.map₁) := by
  change T.map a.map₀ ≫ x'.comparison.hom = x.comparison.hom ≫ a.map₁ at ha
  change T.map b.map₀ ≫ y'.comparison.hom = y.comparison.hom ≫ b.map₁ at hb
  have hc₁ := congrArg (fun t => t.app y.obj₀) (c.hom.naturality a.map₀)
  have hc₂ := (c.hom.app x'.obj₀).naturality b.map₀
  change T.map ((B₀.map a.map₀).app y.obj₀) ≫ (c.hom.app x'.obj₀).app y.obj₀ =
    (c.hom.app x.obj₀).app y.obj₀ ≫
      (B₁.map (T.map a.map₀)).app (T.obj y.obj₀) at hc₁
  change T.map ((B₀.obj x'.obj₀).map b.map₀) ≫ (c.hom.app x'.obj₀).app y'.obj₀ =
    (c.hom.app x'.obj₀).app y.obj₀ ≫
      (B₁.obj (T.obj x'.obj₀)).map (T.map b.map₀) at hc₂
  dsimp only [CoefficientRealizationObject.tensor, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom]
  simp only [T.map_comp, Category.assoc]
  rw [← Category.assoc _ _ ((B₁.map x'.comparison.hom).app _ ≫ _), hc₂]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ ((B₁.obj (T.obj x'.obj₀)).map _ ≫ _), hc₁]
  simp only [Category.assoc]
  rw [(B₁.map x'.comparison.hom).naturality_assoc]
  rw [← Category.assoc ((B₁.map (T.map a.map₀)).app _) _ _,
    ← NatTrans.comp_app, ← B₁.map_comp, ha, B₁.map_comp, NatTrans.comp_app]
  rw [← (B₁.obj x'.obj₁).map_comp, hb, (B₁.obj x'.obj₁).map_comp]
  simp only [Category.assoc]
  rw [(B₁.map a.map₁).naturality_assoc]

/-- Successive comparisons with the specified composition cocycle.
Source: blueprint, prop-sf-pf-coherence, successive comparison functors
(blueprint: lem-sf-pf-coefficient-realization-transport).
Proof: apply S to the first comparison equation and paste the second one. The endpoint
comparisons are S(b) followed by c; substitute the two supplied composition cocycles.
The same calculation applies to refinement comparisons when their primitive squares
intertwine: first apply the main theorem to those data and then paste the results.
No refinement comparison or compatibility is asserted to exist. -/
theorem coefficientRealizationTransport_successive
    (T : C₀ ⥤ C₁) (S : C₁ ⥤ C₂)
    {X₀ Y₀ : C₀} {X₁ Y₁ : C₁} {X₂ Y₂ : C₂}
    (bs : T.obj X₀ ≅ X₁) (bt : T.obj Y₀ ≅ Y₁)
    (cs : S.obj X₁ ≅ X₂) (ct : S.obj Y₁ ≅ Y₂)
    (ds : (T ⋙ S).obj X₀ ≅ X₂) (dt : (T ⋙ S).obj Y₀ ≅ Y₂)
    (sourceCocycle : ds.hom = S.map bs.hom ≫ cs.hom)
    (targetCocycle : dt.hom = S.map bt.hom ≫ ct.hom)
    (m₀ : X₀ ⟶ Y₀) (m₁ : X₁ ⟶ Y₁) (m₂ : X₂ ⟶ Y₂)
    (hT : T.map m₀ ≫ bt.hom = bs.hom ≫ m₁)
    (hS : S.map m₁ ≫ ct.hom = cs.hom ≫ m₂) :
    (T ⋙ S).map m₀ ≫ dt.hom = ds.hom ≫ m₂ := by
  change S.map (T.map m₀) ≫ dt.hom = ds.hom ≫ m₂
  rw [sourceCocycle, targetCocycle, ← Category.assoc, ← S.map_comp, hT,
    S.map_comp, Category.assoc, hS, Category.assoc]

/-- Identity transport with the required identity normalization.
Source: blueprint, prop-sf-pf-coherence, identity comparison cocycle
(blueprint: lem-sf-pf-coefficient-realization-transport).
Proof: substitute the identity comparison cocycles at both endpoints; identity
functoriality and the category identity laws give the equation. -/
theorem coefficientRealizationTransport_identity
    {X Y : C₀} (bs : X ≅ X) (bt : Y ≅ Y)
    (hs : bs = Iso.refl X) (ht : bt = Iso.refl Y) (m : X ⟶ Y) :
    (𝟭 C₀).map m ≫ bt.hom = bs.hom ≫ m := by
  subst bs
  subst bt
  simp

/-- Forward transport of equality for two displayed composites with common endpoints.
Source: blueprint, prop-sf-pf-coherence, final equality-transport sentence
(blueprint: lem-sf-pf-coefficient-realization-transport).
Proof: functoriality sends u₀ = v₀ to equal images. The two intertwining equations
then give source.hom followed by u₁ equal to source.hom followed by v₁. Cancel the
source isomorphism. Neither faithfulness nor invertibility of the displayed maps is used. -/
theorem coefficientRealizationTransport_eq_of_eq
    {T : C₀ ⥤ C₁} {X₀ Y₀ : C₀} {X₁ Y₁ : C₁}
    (source : T.obj X₀ ≅ X₁) (target : T.obj Y₀ ≅ Y₁)
    (u₀ v₀ : X₀ ⟶ Y₀) (u₁ v₁ : X₁ ⟶ Y₁)
    (hu : T.map u₀ ≫ target.hom = source.hom ≫ u₁)
    (hv : T.map v₀ ≫ target.hom = source.hom ≫ v₁)
    (h : u₀ = v₀) : u₁ = v₁ := by
  apply (cancel_epi source.hom).mp
  exact hu.symm.trans ((congrArg (fun f => T.map f ≫ target.hom) h).trans hv)

end FormalTransport

section Systems

variable {D₀ : Fin 6 → Type u₀} {D₁ : Fin 6 → Type u₁}
  [∀ i, Category.{v₀} (D₀ i)] [∀ i, Category.{v₁} (D₁ i)]

/-- The two actual operation systems and their supplied natural comparison isomorphisms.
No equation for a projection or exchange composite is assumed.
Source: blueprint, prop-sf-pf-coherence, supplied coefficient/site comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
structure CoefficientRealizationTransportData where
  system₀ : ExchangeProjectionTransportStage (DX := D₀ 0) (DB := D₀ 1) (DY := D₀ 2)
      (DX' := D₀ 3) (DB' := D₀ 4) (DY' := D₀ 5)
  system₁ : ExchangeProjectionTransportStage (DX := D₁ 0) (DB := D₁ 1) (DY := D₁ 2)
      (DX' := D₁ 3) (DB' := D₁ 4) (DY' := D₁ 5)
  comparison : ∀ i : Fin 6, D₀ i ⥤ D₁ i
  pull : system₀.pull ⋙ comparison 0 ≅ comparison 2 ⋙ system₁.pull
  horizontal : system₀.horizontal ⋙ comparison 5 ≅ comparison 2 ⋙ system₁.horizontal
  horizontal' : system₀.horizontal' ⋙ comparison 3 ≅ comparison 0 ⋙ system₁.horizontal'
  openExtension : system₀.openExtension ⋙ comparison 1 ≅ comparison 0 ⋙ system₁.openExtension
  openExtension' : system₀.openExtension' ⋙ comparison 4 ≅ comparison 3 ⋙ system₁.openExtension'
  properPull : system₀.properPull ⋙ comparison 1 ≅ comparison 2 ⋙ system₁.properPull
  properPush : system₀.properPush ⋙ comparison 2 ≅ comparison 1 ⋙ system₁.properPush
  properPull' : system₀.properPull' ⋙ comparison 4 ≅ comparison 5 ⋙ system₁.properPull'
  properPush' : system₀.properPush' ⋙ comparison 5 ≅ comparison 4 ⋙ system₁.properPush'
  compactifyingHorizontal : system₀.compactifyingHorizontal ⋙ comparison 4 ≅
    comparison 1 ⋙ system₁.compactifyingHorizontal
  tensorX : (Functor.postcompose₂.obj (comparison 0)).obj system₀.tensorX ≅
    (((Functor.whiskeringLeft₂ (D₁ 0)).obj (comparison 0)).obj
      (comparison 0)).obj system₁.tensorX
  tensorBar : (Functor.postcompose₂.obj (comparison 1)).obj system₀.tensorBar ≅
    (((Functor.whiskeringLeft₂ (D₁ 1)).obj (comparison 1)).obj
      (comparison 1)).obj system₁.tensorBar
  tensorY : (Functor.postcompose₂.obj (comparison 2)).obj system₀.tensorY ≅
    (((Functor.whiskeringLeft₂ (D₁ 2)).obj (comparison 2)).obj
      (comparison 2)).obj system₁.tensorY

namespace CoefficientRealizationTransportData

variable (d : CoefficientRealizationTransportData (D₀ := D₀) (D₁ := D₁))

/-- The operation `pull` with its natural coefficient comparison.
Source: blueprint, prop-sf-pf-coherence, operation comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def pullObj (x : CoefficientRealizationObject (d.comparison 2)) :
    CoefficientRealizationObject (d.comparison 0) :=
  x.map d.system₀.pull d.system₁.pull d.pull

/-- The operation `horizontal` with its natural coefficient comparison.
Source: blueprint, prop-sf-pf-coherence, operation comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def horizontalObj (x : CoefficientRealizationObject (d.comparison 2)) :
    CoefficientRealizationObject (d.comparison 5) :=
  x.map d.system₀.horizontal d.system₁.horizontal d.horizontal

/-- The operation `horizontal'` with its natural coefficient comparison.
Source: blueprint, prop-sf-pf-coherence, operation comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def horizontal'Obj (x : CoefficientRealizationObject (d.comparison 0)) :
    CoefficientRealizationObject (d.comparison 3) :=
  x.map d.system₀.horizontal' d.system₁.horizontal' d.horizontal'

/-- The operation `openExtension` with its natural coefficient comparison.
Source: blueprint, prop-sf-pf-coherence, operation comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def openExtensionObj (x : CoefficientRealizationObject (d.comparison 0)) :
    CoefficientRealizationObject (d.comparison 1) :=
  x.map d.system₀.openExtension d.system₁.openExtension d.openExtension

/-- The operation `openExtension'` with its natural coefficient comparison.
Source: blueprint, prop-sf-pf-coherence, operation comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def openExtension'Obj (x : CoefficientRealizationObject (d.comparison 3)) :
    CoefficientRealizationObject (d.comparison 4) :=
  x.map d.system₀.openExtension' d.system₁.openExtension' d.openExtension'

/-- The operation `properPull` with its natural coefficient comparison.
Source: blueprint, prop-sf-pf-coherence, operation comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def properPullObj (x : CoefficientRealizationObject (d.comparison 2)) :
    CoefficientRealizationObject (d.comparison 1) :=
  x.map d.system₀.properPull d.system₁.properPull d.properPull

/-- The operation `properPush` with its natural coefficient comparison.
Source: blueprint, prop-sf-pf-coherence, operation comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def properPushObj (x : CoefficientRealizationObject (d.comparison 1)) :
    CoefficientRealizationObject (d.comparison 2) :=
  x.map d.system₀.properPush d.system₁.properPush d.properPush

/-- The operation `properPull'` with its natural coefficient comparison.
Source: blueprint, prop-sf-pf-coherence, operation comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def properPull'Obj (x : CoefficientRealizationObject (d.comparison 5)) :
    CoefficientRealizationObject (d.comparison 4) :=
  x.map d.system₀.properPull' d.system₁.properPull' d.properPull'

/-- The operation `properPush'` with its natural coefficient comparison.
Source: blueprint, prop-sf-pf-coherence, operation comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def properPush'Obj (x : CoefficientRealizationObject (d.comparison 4)) :
    CoefficientRealizationObject (d.comparison 5) :=
  x.map d.system₀.properPush' d.system₁.properPush' d.properPush'

/-- The operation `compactifyingHorizontal` with its natural coefficient comparison.
Source: blueprint, prop-sf-pf-coherence, operation comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def compactifyingHorizontalObj (x : CoefficientRealizationObject (d.comparison 1)) :
    CoefficientRealizationObject (d.comparison 4) :=
  x.map d.system₀.compactifyingHorizontal d.system₁.compactifyingHorizontal
    d.compactifyingHorizontal

/-- Tensor on the domain 0, with both input comparisons.
Source: blueprint, prop-sf-pf-coherence, tensor comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def tensorXObj (x y : CoefficientRealizationObject (d.comparison 0)) :
    CoefficientRealizationObject (d.comparison 0) :=
  x.tensor d.system₀.tensorX d.system₁.tensorX d.tensorX y

/-- Tensor on the domain 1, with both input comparisons.
Source: blueprint, prop-sf-pf-coherence, tensor comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def tensorBarObj (x y : CoefficientRealizationObject (d.comparison 1)) :
    CoefficientRealizationObject (d.comparison 1) :=
  x.tensor d.system₀.tensorBar d.system₁.tensorBar d.tensorBar y

/-- Tensor on the domain 2, with both input comparisons.
Source: blueprint, prop-sf-pf-coherence, tensor comparisons
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def tensorYObj (x y : CoefficientRealizationObject (d.comparison 2)) :
    CoefficientRealizationObject (d.comparison 2) :=
  x.tensor d.system₀.tensorY d.system₁.tensorY d.tensorY y

/-- The specified primitive `unit`, with its composite endpoint comparisons.
Source: blueprint, prop-sf-pf-coherence, local unit/counit/structural formulas
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def unit (x : CoefficientRealizationObject (d.comparison 2)) :
    CoefficientRealizationArrow x (d.properPushObj (d.properPullObj x)) where
  map₀ := d.system₀.properAdjunction.unit.app x.obj₀
  map₁ := d.system₁.properAdjunction.unit.app x.obj₁

/-- The specified primitive `counit`, with its composite endpoint comparisons.
Source: blueprint, prop-sf-pf-coherence, local unit/counit/structural formulas
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def counit (x : CoefficientRealizationObject (d.comparison 1)) :
    CoefficientRealizationArrow (d.properPullObj (d.properPushObj x)) x where
  map₀ := d.system₀.properAdjunction.counit.app x.obj₀
  map₁ := d.system₁.properAdjunction.counit.app x.obj₁

/-- The specified primitive `unit'`, with its composite endpoint comparisons.
Source: blueprint, prop-sf-pf-coherence, local unit/counit/structural formulas
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def unit' (x : CoefficientRealizationObject (d.comparison 5)) :
    CoefficientRealizationArrow x (d.properPush'Obj (d.properPull'Obj x)) where
  map₀ := d.system₀.properAdjunction'.unit.app x.obj₀
  map₁ := d.system₁.properAdjunction'.unit.app x.obj₁

/-- The specified primitive `counit'`, with its composite endpoint comparisons.
Source: blueprint, prop-sf-pf-coherence, local unit/counit/structural formulas
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def counit' (x : CoefficientRealizationObject (d.comparison 4)) :
    CoefficientRealizationArrow (d.properPull'Obj (d.properPush'Obj x)) x where
  map₀ := d.system₀.properAdjunction'.counit.app x.obj₀
  map₁ := d.system₁.properAdjunction'.counit.app x.obj₁

/-- The specified primitive `mu`, with its composite endpoint comparisons.
Source: blueprint, prop-sf-pf-coherence, local unit/counit/structural formulas
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def mu (x y : CoefficientRealizationObject (d.comparison 2)) :
    CoefficientRealizationArrow (d.properPullObj (d.tensorYObj x y))
      (d.tensorBarObj (d.properPullObj x) (d.properPullObj y)) where
  map₀ := (d.system₀.tensorPullback.hom.app x.obj₀).app y.obj₀
  map₁ := (d.system₁.tensorPullback.hom.app x.obj₁).app y.obj₁

/-- The specified primitive `theta`, with its composite endpoint comparisons.
Source: blueprint, prop-sf-pf-coherence, local unit/counit/structural formulas
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def theta (x : CoefficientRealizationObject (d.comparison 2)) :
    CoefficientRealizationArrow (d.properPull'Obj (d.horizontalObj x))
      (d.compactifyingHorizontalObj (d.properPullObj x)) where
  map₀ := d.system₀.properPullbackComparison.hom.app x.obj₀
  map₁ := d.system₁.properPullbackComparison.hom.app x.obj₁

/-- The specified primitive `beta`, with its composite endpoint comparisons.
Source: blueprint, prop-sf-pf-coherence, local unit/counit/structural formulas
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def beta (k : CoefficientRealizationObject (d.comparison 0)) :
    CoefficientRealizationArrow (d.compactifyingHorizontalObj (d.openExtensionObj k))
      (d.openExtension'Obj (d.horizontal'Obj k)) where
  map₀ := d.system₀.openBaseChange.hom.app k.obj₀
  map₁ := d.system₁.openBaseChange.hom.app k.obj₁

/-- The specified primitive `gamma`, with its composite endpoint comparisons.
Source: blueprint, prop-sf-pf-coherence, local unit/counit/structural formulas
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def gamma (k : CoefficientRealizationObject (d.comparison 0))
    (n : CoefficientRealizationObject (d.comparison 2)) :
    CoefficientRealizationArrow (d.tensorBarObj (d.openExtensionObj k) (d.properPullObj n))
      (d.openExtensionObj (d.tensorXObj k (d.pullObj n))) where
  map₀ := (d.system₀.openProjection.hom.app k.obj₀).app n.obj₀
  map₁ := (d.system₁.openProjection.hom.app k.obj₁).app n.obj₁

/-- The actual specified composite `pi`; no intertwining equation is stored.
Source: blueprint, prop-sf-pf-coherence, four local composite definitions
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
noncomputable def pi (m : CoefficientRealizationObject (d.comparison 1))
    (n : CoefficientRealizationObject (d.comparison 2)) :
    CoefficientRealizationArrow (d.tensorYObj (d.properPushObj m) n)
      (d.properPushObj (d.tensorBarObj m (d.properPullObj n))) where
  map₀ := ((d.system₀.properAdjunction.rightAdjointProjectionMap
    d.system₀.tensorPullback.hom).app m.obj₀).app n.obj₀
  map₁ := ((d.system₁.properAdjunction.rightAdjointProjectionMap
    d.system₁.tensorPullback.hom).app m.obj₁).app n.obj₁

/-- The actual specified composite `exchange`; no intertwining equation is stored.
Source: blueprint, prop-sf-pf-coherence, four local composite definitions
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
noncomputable def exchange (m : CoefficientRealizationObject (d.comparison 1)) :
    CoefficientRealizationArrow (d.horizontalObj (d.properPushObj m))
      (d.properPush'Obj (d.compactifyingHorizontalObj m)) where
  map₀ := (mateEquiv d.system₀.properAdjunction d.system₀.properAdjunction'
    (TwoSquare.mk _ _ _ _ d.system₀.properPullbackComparison.hom)).natTrans.app m.obj₀
  map₁ := (mateEquiv d.system₁.properAdjunction d.system₁.properAdjunction'
    (TwoSquare.mk _ _ _ _ d.system₁.properPullbackComparison.hom)).natTrans.app m.obj₁

/-- The actual specified composite `projection`; no intertwining equation is stored.
Source: blueprint, prop-sf-pf-coherence, four local composite definitions
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
noncomputable def projection (k : CoefficientRealizationObject (d.comparison 0))
    (n : CoefficientRealizationObject (d.comparison 2)) :
    CoefficientRealizationArrow (d.tensorYObj (d.properPushObj (d.openExtensionObj k)) n)
      (d.properPushObj (d.openExtensionObj (d.tensorXObj k (d.pullObj n)))) where
  map₀ := ((compactificationProjectionFromTransportData d.system₀.openExtension d.system₀.pull
    d.system₀.properPull d.system₀.properPush d.system₀.properAdjunction
    d.system₀.tensorX d.system₀.tensorBar d.system₀.tensorY
    d.system₀.tensorPullback d.system₀.openProjection).app k.obj₀).app n.obj₀
  map₁ := ((compactificationProjectionFromTransportData d.system₁.openExtension d.system₁.pull
    d.system₁.properPull d.system₁.properPush d.system₁.properAdjunction
    d.system₁.tensorX d.system₁.tensorBar d.system₁.tensorY
    d.system₁.tensorPullback d.system₁.openProjection).app k.obj₁).app n.obj₁

/-- The actual specified composite `compactExchange`; no intertwining equation is stored.
Source: blueprint, prop-sf-pf-coherence, four local composite definitions
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
noncomputable def compactExchange (k : CoefficientRealizationObject (d.comparison 0)) :
    CoefficientRealizationArrow (d.horizontalObj (d.properPushObj (d.openExtensionObj k)))
      (d.properPush'Obj (d.openExtension'Obj (d.horizontal'Obj k))) where
  map₀ := (compactificationExchangeFromTransportData d.system₀.openExtension
    d.system₀.openExtension'
    d.system₀.properPull d.system₀.properPush d.system₀.properAdjunction
    d.system₀.properPull' d.system₀.properPush' d.system₀.properAdjunction'
    d.system₀.horizontal d.system₀.horizontal' d.system₀.compactifyingHorizontal
    d.system₀.properPullbackComparison d.system₀.openBaseChange).app k.obj₀
  map₁ := (compactificationExchangeFromTransportData d.system₁.openExtension
    d.system₁.openExtension'
    d.system₁.properPull d.system₁.properPush d.system₁.properAdjunction
    d.system₁.properPull' d.system₁.properPush' d.system₁.properAdjunction'
    d.system₁.horizontal d.system₁.horizontal' d.system₁.compactifyingHorizontal
    d.system₁.properPullbackComparison d.system₁.openBaseChange).app k.obj₁

/-- Exactly the primitive compatibility hypotheses; none is a composite conclusion.
`gamma` includes the specified pullback-composition comparison in the operation system.
Source: blueprint, prop-sf-pf-coherence, hypotheses on primitive maps
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
structure Preserves : Prop where
  unit : ∀ x, (d.unit x).intertwines
  counit : ∀ x, (d.counit x).intertwines
  unit' : ∀ x, (d.unit' x).intertwines
  counit' : ∀ x, (d.counit' x).intertwines
  mu : ∀ x y, (d.mu x y).intertwines
  theta : ∀ x, (d.theta x).intertwines
  beta : ∀ k, (d.beta k).intertwines
  gamma : ∀ k n, (d.gamma k n).intertwines

end CoefficientRealizationTransportData

/-- All four specified composites are transported by a comparison of operation systems.
Source: blueprint, prop-sf-pf-coherence, final paragraph
(blueprint: lem-sf-pf-coefficient-realization-transport).
Proof: expand pi as eta followed by the pushforward of mu and epsilon tensor identity.
Paste the unit, tensor and counit comparison squares. For exchange, expand the mate
as the primed unit followed by pushforward of theta and the pulled-back counit;
paste those three squares. Naturality of operation comparisons supplies every
whiskered square. Finally paste the beta and gamma squares with these two results
to obtain compact exchange and projection, respectively. These component equations
hold for every input, hence are equations of the corresponding natural transformations. -/
theorem coefficientRealizationTransport
    (d : CoefficientRealizationTransportData (D₀ := D₀) (D₁ := D₁))
    (h : d.Preserves) :
    (∀ m n, (d.pi m n).intertwines) ∧
      (∀ m, (d.exchange m).intertwines) ∧
      (∀ k n, (d.projection k n).intertwines) ∧
      (∀ k, (d.compactExchange k).intertwines) := by
  have hpi : ∀ m n, (d.pi m n).intertwines := by
    intro m n
    let q := d.properPullObj n
    let b : CoefficientRealizationArrow
        (d.tensorBarObj (d.properPullObj (d.properPushObj m)) q)
        (d.tensorBarObj m q) :=
      ⟨(d.system₀.tensorBar.map (d.counit m).map₀).app q.obj₀,
        (d.system₁.tensorBar.map (d.counit m).map₁).app q.obj₁⟩
    have hb : b.intertwines := by
      have hi : (CoefficientRealizationArrow.mk (𝟙 q.obj₀) (𝟙 q.obj₁)).intertwines := by
        simp [CoefficientRealizationArrow.intertwines]
      simpa only [CoefficientRealizationArrow.intertwines, b,
        CoefficientRealizationTransportData.tensorBarObj, Functor.map_id, Category.comp_id] using
        coefficientRealizationTransport_tensor d.system₀.tensorBar d.system₁.tensorBar
          d.tensorBar (d.counit m) ⟨𝟙 q.obj₀, 𝟙 q.obj₁⟩ (h.counit m) hi
    let a := d.mu (d.properPushObj m) n
    let c : CoefficientRealizationArrow _ _ :=
      ⟨a.map₀ ≫ b.map₀, a.map₁ ≫ b.map₁⟩
    have hc : c.intertwines := coefficientRealizationTransport_comp a b
      (h.mu (d.properPushObj m) n) hb
    have hm := coefficientRealizationTransport_map d.system₀.properPush
      d.system₁.properPush d.properPush c hc
    have hp := coefficientRealizationTransport_comp
      (d.unit (d.tensorYObj (d.properPushObj m) n))
      (show CoefficientRealizationArrow
        (d.properPushObj (d.properPullObj (d.tensorYObj (d.properPushObj m) n)))
        (d.properPushObj (d.tensorBarObj m q)) from
          ⟨d.system₀.properPush.map c.map₀, d.system₁.properPush.map c.map₁⟩)
      (h.unit _) hm
    simpa only [CoefficientRealizationArrow.intertwines, CoefficientRealizationTransportData.pi,
      Adjunction.rightAdjointProjectionMap_app_app, Adjunction.homEquiv_unit,
      CoefficientRealizationTransportData.unit, CoefficientRealizationTransportData.counit,
      CoefficientRealizationTransportData.mu, c, a, b, q, Category.assoc,
      CoefficientRealizationTransportData.tensorYObj,
      CoefficientRealizationTransportData.properPushObj,
      CoefficientRealizationTransportData.properPullObj,
      CoefficientRealizationObject.map, CoefficientRealizationObject.tensor] using hp
  have hex : ∀ m, (d.exchange m).intertwines := by
    intro m
    let a := d.theta (d.properPushObj m)
    let b : CoefficientRealizationArrow
        (d.compactifyingHorizontalObj (d.properPullObj (d.properPushObj m)))
        (d.compactifyingHorizontalObj m) :=
      ⟨d.system₀.compactifyingHorizontal.map (d.counit m).map₀,
        d.system₁.compactifyingHorizontal.map (d.counit m).map₁⟩
    have hb : b.intertwines := coefficientRealizationTransport_map
      d.system₀.compactifyingHorizontal d.system₁.compactifyingHorizontal
      d.compactifyingHorizontal (d.counit m) (h.counit m)
    let c : CoefficientRealizationArrow _ _ :=
      ⟨a.map₀ ≫ b.map₀, a.map₁ ≫ b.map₁⟩
    have hc : c.intertwines := coefficientRealizationTransport_comp a b
      (h.theta (d.properPushObj m)) hb
    have hm := coefficientRealizationTransport_map d.system₀.properPush'
      d.system₁.properPush' d.properPush' c hc
    have hp := coefficientRealizationTransport_comp
      (d.unit' (d.horizontalObj (d.properPushObj m)))
      (show CoefficientRealizationArrow
        (d.properPush'Obj (d.properPull'Obj (d.horizontalObj (d.properPushObj m))))
        (d.properPush'Obj (d.compactifyingHorizontalObj m)) from
          ⟨d.system₀.properPush'.map c.map₀, d.system₁.properPush'.map c.map₁⟩)
      (h.unit' _) hm
    simpa only [CoefficientRealizationArrow.intertwines,
      CoefficientRealizationTransportData.exchange, mateEquiv, Equiv.coe_fn_mk,
      NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.comp_map, Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
      Functor.map_comp, Functor.map_id, Category.assoc,
      CoefficientRealizationTransportData.unit', CoefficientRealizationTransportData.counit,
      CoefficientRealizationTransportData.theta, TwoSquare.mk, TwoSquare.natTrans, c, a, b,
      Functor.comp_obj, Functor.id_obj, CoefficientRealizationTransportData.horizontalObj,
      CoefficientRealizationTransportData.properPushObj,
      CoefficientRealizationObject.map] using hp
  refine ⟨hpi, hex, ?_, ?_⟩
  · intro k n
    have hm := coefficientRealizationTransport_map d.system₀.properPush
      d.system₁.properPush d.properPush (d.gamma k n) (h.gamma k n)
    have hp := coefficientRealizationTransport_comp (d.pi (d.openExtensionObj k) n)
      (show CoefficientRealizationArrow
        (d.properPushObj (d.tensorBarObj (d.openExtensionObj k) (d.properPullObj n)))
        (d.properPushObj (d.openExtensionObj (d.tensorXObj k (d.pullObj n)))) from
          ⟨d.system₀.properPush.map (d.gamma k n).map₀,
            d.system₁.properPush.map (d.gamma k n).map₁⟩) (hpi _ _) hm
    exact hp
  · intro k
    have hm := coefficientRealizationTransport_map d.system₀.properPush'
      d.system₁.properPush' d.properPush' (d.beta k) (h.beta k)
    have hp := coefficientRealizationTransport_comp (d.exchange (d.openExtensionObj k))
      (show CoefficientRealizationArrow
        (d.properPush'Obj (d.compactifyingHorizontalObj (d.openExtensionObj k)))
        (d.properPush'Obj (d.openExtension'Obj (d.horizontal'Obj k))) from
          ⟨d.system₀.properPush'.map (d.beta k).map₀,
            d.system₁.properPush'.map (d.beta k).map₁⟩) (hex _) hm
    simpa only [CoefficientRealizationArrow.intertwines,
      CoefficientRealizationTransportData.compactExchange,
      compactificationExchangeFromTransportData, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, CoefficientRealizationTransportData.exchange,
      CoefficientRealizationTransportData.beta,
      CoefficientRealizationTransportData.openExtensionObj,
      CoefficientRealizationObject.map] using hp

end Systems

/-- A finite composable string of the displayed arrows after their chosen whiskerings.
The endpoints are the actual compared objects, so intermediate comparisons agree.
Source: blueprint, prop-sf-pf-coherence, complete base-change routes
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
inductive CoefficientRealizationPath
    {C₀ : Type u₀} {C₁ : Type u₁} [Category.{v₀} C₀] [Category.{v₁} C₁]
    {T : C₀ ⥤ C₁} : CoefficientRealizationObject T →
      CoefficientRealizationObject T → Type (max u₀ u₁ v₀ v₁)
  | nil (x : CoefficientRealizationObject T) : CoefficientRealizationPath x x
  | cons {x y z : CoefficientRealizationObject T} (a : CoefficientRealizationArrow x y)
      (p : CoefficientRealizationPath y z) : CoefficientRealizationPath x z

/-- The composite in system 0, with the empty route equal to the identity.
Source: blueprint, prop-sf-pf-coherence, finite strings
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def CoefficientRealizationPath.map₀
    {C₀ : Type u₀} {C₁ : Type u₁} [Category.{v₀} C₀] [Category.{v₁} C₁]
    {T : C₀ ⥤ C₁} {x y : CoefficientRealizationObject T}
    (p : CoefficientRealizationPath x y) : x.obj₀ ⟶ y.obj₀ :=
  match p with
  | .nil x => 𝟙 x.obj₀
  | .cons a p => a.map₀ ≫ p.map₀

/-- The composite in system 1, with the empty route equal to the identity.
Source: blueprint, prop-sf-pf-coherence, finite strings
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def CoefficientRealizationPath.map₁
    {C₀ : Type u₀} {C₁ : Type u₁} [Category.{v₀} C₀] [Category.{v₁} C₁]
    {T : C₀ ⥤ C₁} {x y : CoefficientRealizationObject T}
    (p : CoefficientRealizationPath x y) : x.obj₁ ⟶ y.obj₁ :=
  match p with
  | .nil x => 𝟙 x.obj₁
  | .cons a p => a.map₁ ≫ p.map₁

/-- Every constituent comparison square in the finite route commutes.
Source: blueprint, prop-sf-pf-coherence, primitive and whiskered squares
(blueprint: lem-sf-pf-coefficient-realization-transport). -/
def CoefficientRealizationPath.compatible
    {C₀ : Type u₀} {C₁ : Type u₁} [Category.{v₀} C₀] [Category.{v₁} C₁]
    {T : C₀ ⥤ C₁} {x y : CoefficientRealizationObject T}
    (p : CoefficientRealizationPath x y) : Prop :=
  match p with
  | .nil _ => True
  | .cons a p => a.intertwines ∧ p.compatible

/-- The comparison equation for every finite route, including both full base-change routes.
Source: blueprint, prop-sf-pf-coherence, complete routes and conditional refinement
(blueprint: lem-sf-pf-coefficient-realization-transport).
Proof: induct on the finite string. The empty route is the functor identity law.
For a nonempty route paste its first comparison square with the induction hypothesis
using the two-arrow calculation. Obtain the constituent equations for the displayed
maps from the main theorem and for their whiskerings from map/tensor naturality above.
The same induction with the supplied refinement comparisons at all intermediate objects
proves the conditional refinement clause; it assumes only their primitive compatibilities. -/
theorem coefficientRealizationTransport_path
    {C₀ : Type u₀} {C₁ : Type u₁} [Category.{v₀} C₀] [Category.{v₁} C₁]
    {T : C₀ ⥤ C₁} {x y : CoefficientRealizationObject T}
    (p : CoefficientRealizationPath x y) (h : p.compatible) :
    T.map p.map₀ ≫ y.comparison.hom = x.comparison.hom ≫ p.map₁ := by
  induction p with
  | nil x => simp [CoefficientRealizationPath.map₀, CoefficientRealizationPath.map₁]
  | cons a p ih =>
    exact coefficientRealizationTransport_comp a ⟨p.map₀, p.map₁⟩ h.1 (ih h.2)

end CategoryTheory

end
