/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtalePullbackStalkCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Formal laws of ordinary pro-etale exchange

Source: literature/blueprint/latest/blueprint/sec-smooth-base-change/
sk-lem-sbc-exchange-compatibility/det-sbc-exchange-formal.md, clauses (1)--(3);
Stacks Project, Tags 07A7, 0E46 and 0E47 (blueprint: det-sbc-exchange-formal).

The exchange is the published `proEtaleAmbientRingedExchange`, specialized to the
constant coefficient sheaves and their canonical constant-section identifications.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.SbcExchange

/-- The recorded ordinary unbounded direct image, specialized to constant coefficients.
Source: blueprint det-sbc-exchange-formal, opening paragraph, and Stacks Tag 07A7
(blueprint: det-sbc-exchange-formal). This abbreviation introduces no new operation. -/
abbrev directImage (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory Y A :=
  proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

/-- The ambient ringed exchange specialized to constant coefficients. The coefficient
identifications are the canonical constant-section comparisons, and the `HEq` witness
is their canonical equality for the commutative square. Source: blueprint
`det-sbc-exchange-formal`, opening paragraph, and Stacks Tag 07A7
(blueprint: det-sbc-exchange-formal). -/
abbrev exchange (Λ : Type u) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    directImage Λ f ⋙ proEtaleConstantRingDerivedPullback Λ g ⟶
      proEtaleConstantRingDerivedPullback Λ g' ⋙ directImage Λ f' :=
  proEtaleAmbientRingedExchange sq
    (proEtaleConstantRing X Λ) (proEtaleConstantRing Y Λ)
    (proEtaleConstantRing X' Λ) (proEtaleConstantRing Y' Λ)
    (proEtaleConstantRingComparison f Λ) (proEtaleConstantRingComparison g Λ)
    (proEtaleConstantRingComparison g' Λ) (proEtaleConstantRingComparison f' Λ)
    ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq g' f Λ)).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦ proEtaleConstantRingComparison q Λ) sq.w).trans
        (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq f' g Λ)).symm))

/-- The specified tensor-unit-normalized derived adjunction for the constant ring.
Source: blueprint det-sbc-exchange-formal, opening paragraph, and Stacks Tag 07A7
(blueprint: det-sbc-exchange-formal). -/
abbrev adjunction (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingDerivedPullback A f ⊣ directImage A f :=
  proEtaleRingDerivedAdjunction f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

/-- The direct-image compositor, conjugate to the canonical pullback compositor.
The latter is fixed by the ordinary sectionwise fibre-product comparison. The derived
composition-adjunction normalization theorem identifies this conjugate with the usual
K-injective direct-image comparison, so it is not an arbitrary endpoint isomorphism.
Source: blueprint det-sbc-exchange-formal, clause (3), and Stacks Tag 0D6E
(blueprint: det-sbc-exchange-formal). -/
def directImageComposition (A : Type u) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Z) :
    directImage A (f ≫ e) ≅ directImage A f ⋙ directImage A e :=
  conjugateIsoEquiv (adjunction A (f ≫ e)) ((adjunction A e).comp (adjunction A f))
    (proEtaleConstantRingPullbackComposition f e A)

/-- Naturality, identity, and horizontal and vertical pasting of the specified exchange.
Source: blueprint det-sbc-exchange-formal, clauses (1)--(3), and Stacks Tags
07A7, 0E46, 0E47 (blueprint: det-sbc-exchange-formal).

Proof, following the seven steps of the node:
1. The ordinary direct-image comparisons restrict along the canonical flattening of
   iterated fibre products. Both scalar actions restrict the same section. The fibre-product
   universal property proves associativity and identity. Conjugation by the specified
   adjunctions gives the normalized ordinary inverse-image comparisons
   (def-pc-fibre-product, def-weil-pbc-adjunction-conjugate,
   def-weil-pbc-composite-adjunction, lem-weil-pbc-mate-pasting).
2. Exact pullback descends these maps termwise to the unbounded derived categories.
   Localization uniqueness transports associativity and identity. Expand each square
   comparison as a compositor, transport by commutativity, and inverse compositor;
   cancel adjacent inverse pairs to obtain both square-pasting equations
   (lem-weil-pbc-localization-universal-property).
3. Module sheaves on the small ringed site are Grothendieck abelian. Apply the derived
   composition-adjunction normalization to the ordinary pullback compositor. Its conjugate
   is the sectionwise direct-image comparison; therefore directImageComposition is the
   canonical derived direct-image comparison, on all unbounded inputs
   (lem-pur-ringed-site-grothendieck-abelian,
   lem-sfb-derived-composition-adjunction-normalization).
4. The ambient ringed exchange is precisely the mate of that square comparison.
   Its counit characterization is the transpose in the opening paragraph. Each of unit,
   comparison and counit is natural in K (def-weil-pbc-adjunction-mate).
5. The identity square comparison becomes the identity after the normalized identity
   pullbacks. The mate of the identity is the identity by the triangle identities;
   whiskering restores the two identity comparisons in the displayed equation
   (lem-weil-pbc-mate-pasting, lem-weil-pbc-mate-whisker).
6. For two base changes, mate pasting and the horizontal square-pasting equation of step 2
   give the two exchange factors. Whiskering moves the two inverse-image compositors to
   the ends, with inverse at the source and forward comparison at the target
   (lem-weil-pbc-mate-pasting, lem-weil-pbc-mate-whisker).
7. For two vertical maps, use the composite adjunction and its composite counit. Vertical
   mate pasting gives exchange for e at Rf_*K followed by Re'_* of exchange for f.
   Conjugation changes the composite adjunctions to the recorded ones, introducing the
   direct-image compositor at the source and its inverse at the target
   (lem-weil-pbc-mate-pasting).
-/
theorem formal (A : Type u) [CommRing A] :
    (∀ {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
        {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare u f' f g)
        {K L : proEtaleDerivedCategory X A} (v : K ⟶ L),
      (proEtaleConstantRingDerivedPullback A g).map ((directImage A f).map v) ≫
          (exchange A sq).app L =
        (exchange A sq).app K ≫
          (directImage A f').map ((proEtaleConstantRingDerivedPullback A u).map v)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
        (sq : ChosenCartesianSquare (𝟙 X) f f (𝟙 Y))
        (K : proEtaleDerivedCategory X A),
      (exchange A sq).app K =
        (proEtaleStalkDerivedIdentityPullback A Y).hom.app ((directImage A f).obj K) ≫
          (directImage A f).map ((proEtaleStalkDerivedIdentityPullback A X).inv.app K)) ∧
    (∀ {X'' X' X Y'' Y' Y : Scheme.{u}} {u : X' ⟶ X} {u' : X'' ⟶ X'}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
        {g : Y' ⟶ Y} {h : Y'' ⟶ Y'}
        (sq₁ : ChosenCartesianSquare u f' f g)
        (sq₂ : ChosenCartesianSquare u' f'' f' h)
        (outer : ChosenCartesianSquare (u' ≫ u) f'' f (h ≫ g))
        (K : proEtaleDerivedCategory X A),
      (exchange A outer).app K =
        (proEtaleConstantRingPullbackComposition h g A).inv.app ((directImage A f).obj K) ≫
          (proEtaleConstantRingDerivedPullback A h).map
            ((exchange A sq₁).app K) ≫
          (exchange A sq₂).app
            ((proEtaleConstantRingDerivedPullback A u).obj K) ≫
          (directImage A f'').map ((proEtaleConstantRingPullbackComposition u' u A).hom.app K)) ∧
    (∀ {X' X Y' Y Z' Z : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
        {f : X ⟶ Y} {v : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {g : Z' ⟶ Z}
        (sq₁ : ChosenCartesianSquare u f' f v)
        (sq₂ : ChosenCartesianSquare v e' e g)
        (outer : ChosenCartesianSquare u (f' ≫ e') (f ≫ e) g)
        (K : proEtaleDerivedCategory X A),
      (exchange A outer).app K =
        (proEtaleConstantRingDerivedPullback A g).map
            ((directImageComposition A f e).hom.app K) ≫
          (exchange A sq₂).app ((directImage A f).obj K) ≫
          (directImage A e').map ((exchange A sq₁).app K) ≫
          (directImageComposition A f' e').inv.app
            ((proEtaleConstantRingDerivedPullback A u).obj K)) := by
  sorry

end AlgebraicGeometry.Scheme.SbcExchange
