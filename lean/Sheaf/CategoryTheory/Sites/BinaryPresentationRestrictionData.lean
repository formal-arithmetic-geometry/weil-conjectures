/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V5
-/
module

public import Sheaf.CategoryTheory.Sites.BinaryPresentationModuleData

/-! # Simultaneous ringed slice comparisons for a specified nerve equivalence -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Restriction comparisons for fixed whole and localized module equivalences.
Source: Stacks Sites 03EH; Modules on Sites 04IE and 04J4.
(blueprint: lem-sp-nerve-module-restriction-coherence). -/
structure BinaryPresentationRestrictionData
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E}
    (R : Sheaf J CommRingCat.{u}) (ring : Sheaf K CommRingCat.{u})
    (F : E ⥤ Sheaf J (Type u)) (Z : Fin 4 → E)
    (g : RingedToposMorphism (localCoefficientRings ring) (localCoefficientRings R))
    (wholeModules : BinaryPresentationModules g)
    (e : ∀ i : Fin 4, RingedToposMorphism (localCoefficientRings (ring.over (Z i)))
      (localCoefficientRings (presentationElementRing R (F.obj (Z i)))))
    (loc : ∀ i : Fin 4, BinaryPresentationModules (e i)) where
  sourceContinuous : ∀ (i j : Fin 4) (f : Z i ⟶ Z j),
    Functor.IsContinuous (elementMap (F.map f))
      (elementTopology (F.obj (Z i)))
      (elementTopology (F.obj (Z j)))
  restriction : ∀ i : Fin 4,
    elementModulePullback.{u, u} (localCoefficientRings R) (F.obj (Z i)) ⋙
      (loc i).modules.functor ≅ wholeModules.modules.functor ⋙
        SheafOfModules.overFunctor.{u} (localCoefficientRings ring) (Z i)
  further : ∀ (i j : Fin 4) (f : Z i ⟶ Z j),
    elementModulePullbackOver.{u, u} (localCoefficientRings R) (F.map f)
        (sourceContinuous i j f) ⋙ (loc i).modules.functor ≅
      (loc j).modules.functor ⋙
        SheafOfModules.overMap.{u} (localCoefficientRings ring) f

  restrictionComposition : ∀ (i j : Fin 4) (f : Z i ⟶ Z j)
      (M : PresentationModules R),
    HEq ((restriction i).hom.app M)
      ((further i j f).hom.app
          ((elementModulePullback.{u, u} (localCoefficientRings R)
            (F.obj (Z j))).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings ring) f).map
          ((restriction j).hom.app M) ≫
        (SheafOfModules.overFunctorMap.{u} (localCoefficientRings ring) f).hom.app
          (wholeModules.modules.functor.obj M))
  furtherIdentity : ∀ (i : Fin 4)
      (M : PresentationModules (presentationElementRing R (F.obj (Z i)))),
    HEq ((further i i (𝟙 (Z i))).hom.app M)
      (𝟙 ((loc i).modules.functor.obj M))
  furtherComposition : ∀ (i j k : Fin 4) (f : Z i ⟶ Z j)
      (g : Z j ⟶ Z k)
      (M : PresentationModules (presentationElementRing R (F.obj (Z k)))),
    HEq ((further i k (f ≫ g)).hom.app M)
      ((further i j f).hom.app
          ((elementModulePullbackOver.{u, u} (localCoefficientRings R) (F.map g)
            (sourceContinuous j k g)).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings ring) f).map
          ((further j k g).hom.app M))

/-- The module restriction comparisons can be chosen with identity and composition laws.
Source: Stacks Sites 03EH; Modules on Sites 03CR, 04IE and 04J4.
(blueprint: lem-sp-nerve-module-restriction-coherence).

Proof: since F(Zᵢ) is subterminal, localization at it is an open
localization. Its restriction on module sheaves has fully faithful extension
by zero: at a section of the subterminal the direct-sum extension has exactly
one summand, so the adjunction unit is invertible. Thus restriction is a
localization functor, and precomposition by it is fully faithful on functor
categories (use the coreflective localization universal property).
Choose the restriction square cᵢ supplied by hc. For f : Zᵢ → Zⱼ,
precompose both proposed further functors with restriction to F(Zⱼ).
The canonical sectionwise restriction-composition isomorphism identifies
the first with restriction to F(Zᵢ) followed by locᵢ. The two squares cᵢ,cⱼ
then identify it with the second. Full faithfulness of precomposition
descends this natural isomorphism to a unique further comparison. This avoids
any unnormalized choice of comparison between the separate slice rings.
Precompose each asserted coherence equation with the same localization.
The defining equations of the descended maps reduce it to cancellation
of cⱼ with its inverse and the ordinary restriction associativity equations.
Faithfulness of precomposition gives the result. Endpoint transports are
the equality of the actual precomposition objects and scalar maps, obtained
from functor map_id/map_comp and category unit/associativity laws; these
transports give exactly the displayed HEq equations.
The required element-map continuity follows from element-site descent.
Empty opens and the zero coefficient ring satisfy the same formulas. -/
theorem exists_binaryPresentationRestrictionData
    {C E : Type u} [SmallCategory C] [SmallCategory E] [HasFiniteLimits E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E}
    (R : Sheaf J CommRingCat.{u}) (ring : Sheaf K CommRingCat.{u})
    (F : E ⥤ Sheaf J (Type u))
    (Z : Fin 4 → E) (hsub : ∀ i : Fin 4, IsSubterminal (F.obj (Z i)))
    (g : RingedToposMorphism (localCoefficientRings ring) (localCoefficientRings R))
    (whole : BinaryPresentationModules g)
    (e : ∀ i : Fin 4, RingedToposMorphism (localCoefficientRings (ring.over (Z i)))
      (localCoefficientRings (presentationElementRing R (F.obj (Z i)))))
    (loc : ∀ i : Fin 4, BinaryPresentationModules (e i))
    (hc : ∀ i : Fin 4, Nonempty
      (elementModulePullback (localCoefficientRings R) (F.obj (Z i)) ⋙
        (loc i).modules.functor ≅ whole.modules.functor ⋙
        SheafOfModules.overFunctor (localCoefficientRings ring) (Z i))) :
    Nonempty (BinaryPresentationRestrictionData R ring F Z g whole e loc) := by sorry

end CategoryTheory
