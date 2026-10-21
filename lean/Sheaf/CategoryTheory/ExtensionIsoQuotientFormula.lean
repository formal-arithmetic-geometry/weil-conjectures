/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.HasLimits

/-! # The quotient formula for extension along an invertible scalar morphism

Source: main-20261015 blueprint, def-sfb-module-open-lower-shriek-adjunction.proof.md,
last sentence, and def-sfb-modobj-extension-along-iso.proof.md
(blueprint: lem-sfb-extension-iso-quotient-formula).
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

/-- The adjoint-uniqueness comparison for extension along an invertible scalar morphism
is the unique factor of the inverse scalar action through the defining coequalizer.
Its inverse inserts the unit, both maps are linear and inverse, and both are natural.

Source: main-20261015 blueprint, def-sfb-module-open-lower-shriek-adjunction.proof.md,
last sentence, via def-sfb-modobj-extension-along-iso.proof.md
(blueprint: lem-sfb-extension-iso-quotient-formula).

Proof: (1) Restriction along the inverse and along the original scalar morphism have
an adjunction whose Hom bijection is the identity on underlying morphisms: the two
linearity equations are equivalent after precomposition with the scalar isomorphism
or its inverse (def-sfb-modobj-restriction, det-def-sfb-module-objects-definition).
(2) Its unit and counit have identity underlying maps, by the Hom-bijection construction
of lem-weil-pbc-adjunction-of-natural-bijection. (3) Extension is left adjoint to
restriction with unit given by unit insertion (def-sfb-modobj-extend-restrict-adjunction).
The unit equation of lem-weil-pbc-conjugate-iso-unit-equation identifies its comparison
with inverse restriction and gives p after unit insertion equal to the identity.
This is the specified comparison: the inverse-equivalence adjunction used in
 def-sfb-modobj-extension-along-iso has the same identity unit, by
 def-sfb-modobj-restriction-equivalence and lem-weil-pbc-quasi-inverse-adjoint; therefore
its Hom bijections agree with those in (1). (4) The induced extension action after
tensoring unit insertion is the quotient map, by associator naturality, the right
unit law and the monoidal triangle identity (def-sfb-modobj-extension,
 det-def-sfb-ring-object-monoid). (5) Linearity of p now gives q followed by p equal to
the inverse scalar action. Thus that action coequalizes the defining pair, and
uniqueness follows from the coequalizer property (def-weil-pbc-category-colimit).
(6) Unit insertion is the inverse of p by (3); hence it is S-linear and both inverse
identities hold (det-def-sfb-module-objects-definition). (7) The quotient formula
for extension on morphisms and linearity of an R-module morphism give naturality
of p after precomposition with q, which is epic. Naturality of tensoring and the
left unitor gives naturality of unit insertion directly
(def-sfb-modobj-extension, def-sfb-modobj-restriction).
-/
theorem extensionIso_quotient_formula
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
    [∀ X : C, PreservesColimits (tensorLeft X)]
    [∀ X : C, PreservesColimits (tensorRight X)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] (N : Mod C R) :
    ((S ◁ φ ≫ μ[S]) ▷ N.X) ≫ (asIso φ).inv ▷ N.X ≫ γ[R,N.X] =
      ((α_ S R N.X).hom ≫ S ◁ γ[R,N.X]) ≫ (asIso φ).inv ▷ N.X ≫ γ[R,N.X] ∧
    @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N ≫ ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom =
      (asIso φ).inv ▷ N.X ≫ γ[R,N.X] ∧
    (∀ f : (@extendScalarsObj C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N).X ⟶ N.X,
      @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N ≫ f = (asIso φ).inv ▷ N.X ≫ γ[R,N.X] →
        f = ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom) ∧
    ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).inv.app N).hom =
      (λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N ∧
    γ[S,(@extendScalarsObj C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N).X] ≫ ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom =
      S ◁ ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom ≫
        (asIso φ).inv ▷ N.X ≫ γ[R,N.X] ∧
    ((asIso φ).inv ▷ N.X ≫ γ[R,N.X]) ≫
        (λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N =
      S ◁ ((λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N) ≫
        γ[S,(@extendScalarsObj C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N).X] ∧
    ((λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N) ≫
        ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom = 𝟙 N.X ∧
    ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom ≫
        (λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N = 𝟙 (@extendScalarsObj C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N).X ∧
    (∀ (N' : Mod C R) (h : N ⟶ N'),
      ((@extendScalars C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _).map h).hom ≫ ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N').hom =
          ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom ≫ h.hom ∧
      h.hom ≫ (λ_ N'.X).inv ≫ η[S] ▷ N'.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N' =
        ((λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N) ≫ ((@extendScalars C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _).map h).hom) := by
  sorry

end CategoryTheory.Mod
