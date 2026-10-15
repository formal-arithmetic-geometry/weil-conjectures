/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Coherence of composition of étale extension by zero

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-cbc`,
(blueprint: lem-cbc-extension-zero-composition).

The canonical natural isomorphism is already `Etale.openImmersionLowerShriekComp`,
with its inverse oriented from the iterated extension to the composite extension.
The theorem below supplies its two identity laws and its three-fold compatibility.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Etale

/-- The canonical natural composition isomorphisms of extension by zero obey both unit
laws and associativity. The identity comparison is the mate of `upperStarId`, namely
`Adjunction.leftAdjointIdIso`. Source: blueprint, `sec-smooth-purity/sk-prop-sf-cbc`
(blueprint: lem-cbc-extension-zero-composition).

Proof plan: (1) Use `openImmersionLowerShriekAdjunction` from
lem-weil-pbc-extension-by-zero-adjunction and the restriction model of its right adjoint.
Restriction along two open immersions composes by evaluation on site objects; restriction
along the identity is the identity. Composites are open immersions by
def-weil-open-immersion. (2) The composite adjunction of
def-weil-pbc-composite-adjunction and uniqueness in
lem-weil-pbc-conjugate-iso-unit-equation give the canonical comparison, already constructed
as `openImmersionLowerShriekComp`; it is a natural isomorphism. (3) The two unit laws
follow by checking the unit equation for the identity comparison and invoking that same
uniqueness. (4) Apply lem-sc-left-adjoint-composition-iso-associativity to the six
adjunctions for three open immersions. Both routes satisfy the same unit equation and
therefore agree. The transports below account only for scheme-category unit and
associativity equalities. -/
theorem Etale.openImmersionLowerShriekComp_coherence
    (Λ : Type (u + 1)) [CommRing Λ] :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) (𝟙 U) j).inv.app F ≫
        eqToHom (by simp only [Category.id_comp, Functor.id_obj]) =
      ((j)_!open[ModuleCat.{u + 1} Λ]).map
        ((Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 U))
          (upperStarId (ModuleCat.{u + 1} Λ) U)).hom.app F)) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j (𝟙 X)).inv.app F ≫
        eqToHom (by simp only [Category.comp_id, Functor.id_obj]) =
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
        (upperStarId (ModuleCat.{u + 1} Λ) X)).hom.app
          (((j)_!open[ModuleCat.{u + 1} Λ]).obj F)) ∧
    (∀ {U V W X : Scheme.{u}} (j₁ : U ⟶ V) (j₂ : V ⟶ W) (j₃ : W ⟶ X)
      [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      ((j₃)_!open[ModuleCat.{u + 1} Λ]).map
          ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j₁ j₂).inv.app F) ≫
        (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂) j₃).inv.app F ≫
        eqToHom (by simp only [Category.assoc]) =
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j₂ j₃).inv.app
          (((j₁)_!open[ModuleCat.{u + 1} Λ]).obj F) ≫
        (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j₁ (j₂ ≫ j₃)).inv.app F) := by
  sorry

end AlgebraicGeometry
