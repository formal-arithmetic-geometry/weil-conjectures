/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Pasting the open and proper compactification factors

Source: main-20261015, sec-six-functors/sk-prop-sf-pf-coherence,
prop-sf-pf-coherence.proof.md, base-change paragraph
(blueprint: lem-sf-pf-compactification-pasting).

We work in the supplied closed coefficient domains of `ExchangeProjectionStage`.
The tensors below are the supplied derived tensors, completed at integral coefficients.
The auxiliary record merely collects the displayed open-square and tensor comparisons;
it asserts neither existence of a coefficient stage nor invertibility of a proper mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false

universe uX uB uY uX' uB' uY' vX vB vY vX' vB' vY' uC vC

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace CategoryTheory.SuppliedExchangeProjection

variable {DX : Type uX} {DB : Type uB} {DY : Type uY}
  {DX' : Type uX'} {DB' : Type uB'} {DY' : Type uY'}
  [Category.{vX} DX] [Category.{vB} DB] [Category.{vY} DY]
  [Category.{vX'} DX'] [Category.{vB'} DB'] [Category.{vY'} DY']

/-- The notation of the conditional pasting lemma on one supplied coefficient domain.
The inherited stage supplies the proper adjunctions, square comparison theta, beta,
and unprimed proper tensor comparison. Here `openPull,openPull'` are J,J',
`horizontal'` is A, and `compactifyingHorizontal` is H. `openTensor` is the bare
open comparison, before identifying JF with the pullback of the composite.
The last field identifies it with the recorded compactification projection comparison.
Source: base-change paragraph of prop-sf-pf-coherence and the displayed notation of
lem-sf-pf-compactification-pasting (blueprint: lem-sf-pf-compactification-pasting). -/
structure CompactificationPastingData extends
    ExchangeProjectionStage (DX := DX) (DB := DB) (DY := DY)
      (DX' := DX') (DB' := DB') (DY' := DY') where
  openPull : DB ⥤ DX
  openPull' : DB' ⥤ DX'
  tensorX' : DX' ⥤ DX' ⥤ DX'
  tensorBar' : DB' ⥤ DB' ⥤ DB'
  tensorY' : DY' ⥤ DY' ⥤ DY'
  tensorPullback' : (Functor.postcompose₂.obj properPull').obj tensorY' ≅
    (((Functor.whiskeringLeft₂ DB').obj properPull').obj properPull').obj tensorBar'
  tensorHorizontal : (Functor.postcompose₂.obj horizontal).obj tensorY ≅
    (((Functor.whiskeringLeft₂ DY').obj horizontal).obj horizontal).obj tensorY'
  tensorCompactifying : (Functor.postcompose₂.obj compactifyingHorizontal).obj tensorBar ≅
    (((Functor.whiskeringLeft₂ DB').obj compactifyingHorizontal).obj
      compactifyingHorizontal).obj tensorBar'
  tensorOpenHorizontal : (Functor.postcompose₂.obj horizontal').obj tensorX ≅
    (((Functor.whiskeringLeft₂ DX').obj horizontal').obj horizontal').obj tensorX'
  openSquare : openPull ⋙ horizontal' ≅ compactifyingHorizontal ⋙ openPull'
  openTensor :
    (((Functor.whiskeringLeft₂ DB).obj openExtension).obj (𝟭 DB)).obj tensorBar ≅
      (Functor.postcompose₂.obj openExtension).obj
        ((((Functor.whiskeringLeft₂ DX).obj (𝟭 DX)).obj openPull).obj tensorX)
  openTensor' :
    (((Functor.whiskeringLeft₂ DB').obj openExtension').obj (𝟭 DB')).obj tensorBar' ≅
      (Functor.postcompose₂.obj openExtension').obj
        ((((Functor.whiskeringLeft₂ DX').obj (𝟭 DX')).obj openPull').obj tensorX')
  pullFactorization : properPull ⋙ openPull ≅ pull
  openProjectionNormalization : ∀ (K : DX) (L : DY),
    (openProjection.hom.app K).app L =
      (openTensor.hom.app K).app (properPull.obj L) ≫
        openExtension.map ((tensorX.obj K).map (pullFactorization.hom.app L))

namespace CompactificationPastingData

variable (D : CompactificationPastingData (DX := DX) (DB := DB) (DY := DY)
  (DX' := DX') (DB' := DB') (DY' := DY'))

/-- Proper exchange e is exactly the mate of theta under the recorded proper adjunctions.
Source: def-exchange-projection, proper factor in prop-sf-pf-coherence
(blueprint: lem-sf-pf-compactification-pasting). -/
def properExchange : D.properPush ⋙ D.horizontal ⟶
    D.compactifyingHorizontal ⋙ D.properPush' :=
  (mateEquiv D.properAdjunction D.properAdjunction'
    (TwoSquare.mk _ _ _ _ D.properPullbackComparison.hom)).natTrans

/-- The proper counit projection pi, with the dependency's actual mate construction.
Source: def-exchange-projection, projection paragraph
(blueprint: lem-sf-pf-compactification-pasting). -/
def properProjection : D.properPush ⋙ D.tensorY ⟶
    (Functor.postcompose₂.obj D.properPush).obj
      ((((Functor.whiskeringLeft₂ DB).obj (𝟭 DB)).obj D.properPull).obj D.tensorBar) :=
  D.properAdjunction.rightAdjointProjectionMap D.tensorPullback.hom

/-- The pulled-back proper counit projection pi', with no invertibility assumption.
Source: def-exchange-projection, projection paragraph after base change
(blueprint: lem-sf-pf-compactification-pasting). -/
def properProjection' : D.properPush' ⋙ D.tensorY' ⟶
    (Functor.postcompose₂.obj D.properPush').obj
      ((((Functor.whiskeringLeft₂ DB').obj (𝟭 DB')).obj D.properPull').obj D.tensorBar') :=
  D.properAdjunction'.rightAdjointProjectionMap D.tensorPullback'.hom

/-- The displayed map d: HQ to HM tensor F'GL, using theta inverse after mu_H.
Source: lem-sf-pf-compactification-pasting, definition of d
(blueprint: lem-sf-pf-compactification-pasting). -/
def tensorTarget (K : DX) (L : DY) :
    D.compactifyingHorizontal.obj
        ((D.tensorBar.obj (D.openExtension.obj K)).obj (D.properPull.obj L)) ⟶
      (D.tensorBar'.obj (D.compactifyingHorizontal.obj (D.openExtension.obj K))).obj
        (D.properPull'.obj (D.horizontal.obj L)) :=
  (D.tensorCompactifying.hom.app (D.openExtension.obj K)).app (D.properPull.obj L) ≫
    (D.tensorBar'.obj (D.compactifyingHorizontal.obj (D.openExtension.obj K))).map
      (D.properPullbackComparison.inv.app L)

/-- The displayed z_K: beta at K tensor JFL, then j'_! of mu_A followed by sigma.
Source: lem-sf-pf-compactification-pasting, definition of z_K
(blueprint: lem-sf-pf-compactification-pasting). -/
def openTarget (K : DX) (L : DY) :
    D.compactifyingHorizontal.obj (D.openExtension.obj
      ((D.tensorX.obj K).obj (D.openPull.obj (D.properPull.obj L)))) ⟶
      D.openExtension'.obj ((D.tensorX'.obj (D.horizontal'.obj K)).obj
        (D.openPull'.obj (D.compactifyingHorizontal.obj (D.properPull.obj L)))) :=
  D.openBaseChange.hom.app
      ((D.tensorX.obj K).obj (D.openPull.obj (D.properPull.obj L))) ≫
    D.openExtension'.map
      ((D.tensorOpenHorizontal.hom.app K).app (D.openPull.obj (D.properPull.obj L)) ≫
        (D.tensorX'.obj (D.horizontal'.obj K)).map
          (D.openSquare.hom.app (D.properPull.obj L)))

/-- The target comparison v: z_K followed by j'_!(1 tensor J'(theta inverse)).
Source: lem-sf-pf-compactification-pasting, definition of v
(blueprint: lem-sf-pf-compactification-pasting). -/
def targetComparison (K : DX) (L : DY) :
    D.compactifyingHorizontal.obj (D.openExtension.obj
      ((D.tensorX.obj K).obj (D.openPull.obj (D.properPull.obj L)))) ⟶
      D.openExtension'.obj ((D.tensorX'.obj (D.horizontal'.obj K)).obj
        (D.openPull'.obj (D.properPull'.obj (D.horizontal.obj L)))) :=
  D.openTarget K L ≫ D.openExtension'.map
    ((D.tensorX'.obj (D.horizontal'.obj K)).map
      (D.openPull'.map (D.properPullbackComparison.inv.app L)))

/-- The compactification projection PF^c = R(gamma_j) pi_p in bare JF coordinates.
`openProjectionNormalization` relates these coordinates to the dependency's PF^c.
Source: def-exchange-projection and lem-sf-pf-compactification-pasting
(blueprint: lem-sf-pf-compactification-pasting). -/
def projection (K : DX) (L : DY) :
    (D.tensorY.obj (D.properPush.obj (D.openExtension.obj K))).obj L ⟶
      D.properPush.obj (D.openExtension.obj
        ((D.tensorX.obj K).obj (D.openPull.obj (D.properPull.obj L)))) :=
  (D.properProjection.app (D.openExtension.obj K)).app L ≫
    D.properPush.map ((D.openTensor.hom.app K).app (D.properPull.obj L))

/-- The first displayed path, factored as G(PF^c), e_T, R'(v).
Source: lem-sf-pf-compactification-pasting, left side of the pasted identity
(blueprint: lem-sf-pf-compactification-pasting). -/
def leftPath (K : DX) (L : DY) : ComposableArrows DY' 3 :=
  ComposableArrows.mk₃
    (D.horizontal.map (D.projection K L))
    (D.properExchange.app (D.openExtension.obj
      ((D.tensorX.obj K).obj (D.openPull.obj (D.properPull.obj L)))))
    (D.properPush'.map (D.targetComparison K L))

/-- The second displayed path: mu_G, (R'(beta_K)e_M) tensor 1, pi', R'(gamma_j').
Source: lem-sf-pf-compactification-pasting, right side of the pasted identity
(blueprint: lem-sf-pf-compactification-pasting). -/
def rightPath (K : DX) (L : DY) : ComposableArrows DY' 4 :=
  ComposableArrows.mk₄
    ((D.tensorHorizontal.hom.app (D.properPush.obj (D.openExtension.obj K))).app L)
    ((D.tensorY'.map
      (D.properExchange.app (D.openExtension.obj K) ≫
        D.properPush'.map (D.openBaseChange.hom.app K))).app (D.horizontal.obj L))
    ((D.properProjection'.app (D.openExtension'.obj (D.horizontal'.obj K))).app
      (D.horizontal.obj L))
    (D.properPush'.map ((D.openTensor'.hom.app (D.horizontal'.obj K)).app
      (D.properPull'.obj (D.horizontal.obj L))))

/-- Exactly the two factor identities of the node, in Lean's left-to-right convention.
M and Q are expanded, and d and z_K are the actual composites defined above.
Source: lem-sf-pf-compactification-pasting, two displayed hypotheses
(blueprint: lem-sf-pf-compactification-pasting). -/
structure FactorIdentities (K : DX) (L : DY) : Prop where
  openFactor :
    D.compactifyingHorizontal.map
        ((D.openTensor.hom.app K).app (D.properPull.obj L)) ≫ D.openTarget K L =
      (D.tensorCompactifying.hom.app (D.openExtension.obj K)).app (D.properPull.obj L) ≫
        (D.tensorBar'.map (D.openBaseChange.hom.app K)).app
          (D.compactifyingHorizontal.obj (D.properPull.obj L)) ≫
        (D.openTensor'.hom.app (D.horizontal'.obj K)).app
          (D.compactifyingHorizontal.obj (D.properPull.obj L))
  properFactor :
    D.horizontal.map ((D.properProjection.app (D.openExtension.obj K)).app L) ≫
        D.properExchange.app
          ((D.tensorBar.obj (D.openExtension.obj K)).obj (D.properPull.obj L)) ≫
        D.properPush'.map (D.tensorTarget K L) =
      (D.tensorHorizontal.hom.app (D.properPush.obj (D.openExtension.obj K))).app L ≫
        (D.tensorY'.map (D.properExchange.app (D.openExtension.obj K))).app
          (D.horizontal.obj L) ≫
        (D.properProjection'.app
          (D.compactifyingHorizontal.obj (D.openExtension.obj K))).app (D.horizontal.obj L)

/-- Conditional pasting, including its naturality in componentwise diagram maps and
its preservation under compactification-comparison conjugation.
The diagrams in the second clause are the two specified component paths after an
arbitrary functor V. Morphisms of `ComposableArrows` mean precisely commuting squares
for the component arrows; equality of their endpoint components means a single map
of the original two-path diagram. Thus this clause includes changes of K,L and
all supplied diagram data, without asserting existence of comparison morphisms.
The final clause uses supplied endpoint isomorphisms only, never inverse exchange
or inverse proper projection.

Source: prop-sf-pf-coherence.proof.md, base-change paragraph and the seven steps of
lem-sf-pf-compactification-pasting (blueprint: lem-sf-pf-compactification-pasting).
Proof:
1. Put M=j_!K, Q=M tensor FL, T=j_!(K tensor JFL), t=theta_L inverse,
   b=beta_K, c=gamma_j, c'=gamma_j'. Expand PF^c as R(c) pi_p using
   def-exchange-projection.
2. Naturality of gamma_j' at t says j'_!(1 tensor J't) gamma_j' =
   c'(1 tensor t). Postcompose openFactor with j'_!(1 tensor J't).
   The tensor bifunctor law then gives H(c) followed by v = mu_H followed
   by (1 tensor t), (b tensor 1), and c', namely d then (b tensor 1) then c'.
3. Naturality of the mate e at c moves G(R(c)) through e_T, giving e_Q
   followed by R'(H(c)); substitute step 2 and preserve compositions with R'.
4. Substitute properFactor with exactly the M and Q of step 1.
5. Naturality of the counit projection pi' in its first variable at b moves
   R'(b tensor 1) through pi'. Tensor functoriality combines e_M and R'(b).
   This is the second displayed path. No exchange or projection is inverted.
6. For a map of the component chains, successively substitute the component
   commuting squares. This gives the endpoint square for each composite.
   Tensor and pullback comparison naturality is lem-pur-derived-pullback-tensor-iso;
   units, counits and the other maps are natural by def-exchange-projection.
7. Apply the functor to the equality and conjugate by the two supplied endpoint
   isomorphisms. This proves the last clause at every supplied coefficient stage,
   including completed integral tensors, without finite-level equality detection. -/
theorem compactification_pasting (K : DX) (L : DY) (h : D.FactorIdentities K L) :
    (D.leftPath K L).hom = (D.rightPath K L).hom ∧
    (∀ {C : Type uC} [Category.{vC} C] (V : DY' ⥤ C)
      (D' : CompactificationPastingData (DX := DX) (DB := DB) (DY := DY)
        (DX' := DX') (DB' := DB') (DY' := DY')) (K' : DX) (L' : DY)
      (a : D.leftPath K L ⋙ V ⟶ D'.leftPath K' L' ⋙ V)
      (b : D.rightPath K L ⋙ V ⟶ D'.rightPath K' L' ⋙ V)
      (_hs : a.app 0 = b.app 0) (_ht : a.app 3 = b.app 4),
      V.map (D.leftPath K L).hom ≫ a.app 3 =
          b.app 0 ≫ V.map (D'.rightPath K' L').hom ∧
        V.map (D.rightPath K L).hom ≫ b.app 4 =
          a.app 0 ≫ V.map (D'.leftPath K' L').hom) ∧
    (∀ {C : Type uC} [Category.{vC} C] (V : DY' ⥤ C) {U W : C}
      (source : U ≅ V.obj (D.leftPath K L).left)
      (target : V.obj (D.leftPath K L).right ≅ W),
      source.hom ≫ V.map (D.leftPath K L).hom ≫ target.hom =
        source.hom ≫ V.map (D.rightPath K L).hom ≫ target.hom) := by
  have hp : (D.leftPath K L).hom = (D.rightPath K L).hom := by
    change D.horizontal.map (D.projection K L) ≫
      D.properExchange.app (D.openExtension.obj
        ((D.tensorX.obj K).obj (D.openPull.obj (D.properPull.obj L)))) ≫
      D.properPush'.map (D.targetComparison K L) =
      (D.tensorHorizontal.hom.app (D.properPush.obj (D.openExtension.obj K))).app L ≫
      (D.tensorY'.map (D.properExchange.app (D.openExtension.obj K) ≫
        D.properPush'.map (D.openBaseChange.hom.app K))).app (D.horizontal.obj L) ≫
      (D.properProjection'.app (D.openExtension'.obj (D.horizontal'.obj K))).app
        (D.horizontal.obj L) ≫
      D.properPush'.map ((D.openTensor'.hom.app (D.horizontal'.obj K)).app
        (D.properPull'.obj (D.horizontal.obj L)))
    have hopen :
        D.compactifyingHorizontal.map
            ((D.openTensor.hom.app K).app (D.properPull.obj L)) ≫
            D.targetComparison K L =
          D.tensorTarget K L ≫
            (D.tensorBar'.map (D.openBaseChange.hom.app K)).app
              (D.properPull'.obj (D.horizontal.obj L)) ≫
            (D.openTensor'.hom.app (D.horizontal'.obj K)).app
              (D.properPull'.obj (D.horizontal.obj L)) := by
      have hg := (D.openTensor'.hom.app (D.horizontal'.obj K)).naturality
        (D.properPullbackComparison.inv.app L)
      have hb := (D.tensorBar'.map (D.openBaseChange.hom.app K)).naturality
        (D.properPullbackComparison.inv.app L)
      dsimp at hg hb
      dsimp only [targetComparison, tensorTarget]
      rw [← Category.assoc, h.openFactor]
      simp only [Category.assoc]
      rw [← hg]
      rw [← Category.assoc ((D.tensorBar'.map _).app _), ← hb]
      simp only [Category.assoc]
    have he := D.properExchange.naturality
      ((D.openTensor.hom.app K).app (D.properPull.obj L))
    change D.horizontal.map
        (D.properPush.map ((D.openTensor.hom.app K).app (D.properPull.obj L))) ≫
        D.properExchange.app (D.openExtension.obj
          ((D.tensorX.obj K).obj (D.openPull.obj (D.properPull.obj L)))) =
      D.properExchange.app
        ((D.tensorBar.obj (D.openExtension.obj K)).obj (D.properPull.obj L)) ≫
        D.properPush'.map
        (D.compactifyingHorizontal.map
          ((D.openTensor.hom.app K).app (D.properPull.obj L))) at he
    have hp' := NatTrans.naturality_app D.properProjection' (D.horizontal.obj L)
      (D.openBaseChange.hom.app K)
    change (D.tensorY'.map (D.properPush'.map (D.openBaseChange.hom.app K))).app
        (D.horizontal.obj L) ≫
        (D.properProjection'.app (D.openExtension'.obj (D.horizontal'.obj K))).app
          (D.horizontal.obj L) =
      (D.properProjection'.app
        (D.compactifyingHorizontal.obj (D.openExtension.obj K))).app (D.horizontal.obj L) ≫
        D.properPush'.map ((D.tensorBar'.map (D.openBaseChange.hom.app K)).app
          (D.properPull'.obj (D.horizontal.obj L))) at hp'
    dsimp only [projection]
    rw [D.horizontal.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (D.horizontal.map (D.properPush.map _)), he]
    simp only [Category.assoc, ← D.properPush'.map_comp]
    rw [hopen]
    simp only [D.properPush'.map_comp]
    have hproper := h.properFactor
    simp only [← Category.assoc] at hproper ⊢
    rw [hproper]
    simp only [Category.assoc]
    rw [← reassoc_of% hp']
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  constructor
  · exact hp
  constructor
  · intro C iC V D' K' L' a b hs ht
    constructor
    · have hb := b.naturality (X := (0 : Fin 5)) (Y := (4 : Fin 5))
        (homOfLE (by decide))
      simpa [hp, ht] using hb
    · have ha := a.naturality (X := (0 : Fin 4)) (Y := (3 : Fin 4))
        (homOfLE (by decide))
      simpa [hp, hs, ht] using ha
  · intro C iC V U W source target
    rw [hp]

end CompactificationPastingData
end CategoryTheory.SuppliedExchangeProjection
