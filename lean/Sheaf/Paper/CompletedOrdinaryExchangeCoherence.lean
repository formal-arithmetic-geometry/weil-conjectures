/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.CompletedOrdinaryComparisons
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Ordinary ringed exchange identity and pasting laws -/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Ordinary ringed exchange respects units and pasting, for the canonical comparisons.
Source: Stacks Tags 07A7, 0E46, 0E47 and 0D6E; blueprint completed-exchange
coherence, proof steps 4--6 before adjoining completion.
(blueprint: lem-weil-pbc-ordinary-ringed-exchange-coherence).
Proof: on ordinary module sheaves the direct-image comparisons are restriction along
fiber-product identity and pasting isomorphisms. Their section formulas satisfy unit
and associativity equations, since the fiber-product maps do. The coefficient maps
agree after every finite projection, so these maps are linear. The tensor-unit
adjunction conjugates give the corresponding equations for module pullback. Apply
these identities termwise on flat-term K-flat representatives and the universal
exact-derived factorization comparisons. Every derived object has such a representative,
so the unit and associativity equations hold on the unbounded derived categories.
The pullback square comparison is defined from precisely these canonical comparisons.
For horizontal pasting its outer comparison is the paste of the two inner comparisons;
apply mateEquiv_vcomp. For vertical pasting apply mateEquiv_hcomp, then change the
composite adjunction by its canonical conjugate, which is pushComp. For either identity
orientation the unit--square--counit formula reduces by the triangle identities to
the displayed conjugation by pullId or pushId. The chosen cartesian realization is
irrelevant: the formula depends only on its commutativity proof, and those proofs
are propositionally equal. No completion, properness or witness condition is used. -/
theorem AdicCoefficientDatum.integralExchange_coherence :
    (∀ {X Y : Scheme.{t}} (f : X ⟶ Y)
      (sq : ChosenCartesianSquare (𝟙 X) f f (𝟙 Y)) (K : d.derived X),
      (d.integralExchange sq).app K =
        (d.pullId Y).hom.app ((d.push f).obj K) ≫
          (d.push f).map ((d.pullId X).inv.app K)) ∧
    (∀ {U V : Scheme.{t}} (g : U ⟶ V)
      (sq : ChosenCartesianSquare g (𝟙 U) (𝟙 V) g) (K : d.derived V),
      (d.integralExchange sq).app K =
        (d.pull g).map ((d.pushId V).hom.app K) ≫
          (d.pushId U).inv.app ((d.pull g).obj K)) ∧
    (∀ {X X' X'' Y Y' Y'' : Scheme.{t}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
      {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
      (sq₁ : ChosenCartesianSquare g' f' f g)
      (sq₂ : ChosenCartesianSquare h' f'' f' h)
      (outer : ChosenCartesianSquare (h' ≫ g') f'' f (h ≫ g)) (K : d.derived X),
      (d.integralExchange outer).app K =
        (d.pullComp h g).hom.app ((d.push f).obj K) ≫
          (d.pull h).map ((d.integralExchange sq₁).app K) ≫
            (d.integralExchange sq₂).app ((d.pull g').obj K) ≫
              (d.push f'').map ((d.pullComp h' g').inv.app K)) ∧
    (∀ {X X' Y Y' Z Z' : Scheme.{t}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {e : Y ⟶ Z} {e' : Y' ⟶ Z'}
      {g' : X' ⟶ X} {g : Y' ⟶ Y} {k : Z' ⟶ Z}
      (sq₁ : ChosenCartesianSquare g' f' f g)
      (sq₂ : ChosenCartesianSquare g e' e k)
      (outer : ChosenCartesianSquare g' (f' ≫ e') (f ≫ e) k) (K : d.derived X),
      (d.integralExchange outer).app K =
        (d.pull k).map ((d.pushComp f e).inv.app K) ≫
          (d.integralExchange sq₂).app ((d.push f).obj K) ≫
            (d.push e').map ((d.integralExchange sq₁).app K) ≫
              (d.pushComp f' e').hom.app ((d.pull g').obj K)) := by
  sorry

end AlgebraicGeometry.Scheme
