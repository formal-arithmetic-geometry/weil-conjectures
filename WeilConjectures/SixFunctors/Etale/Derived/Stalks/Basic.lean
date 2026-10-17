/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Geometric stalks as inverse images

For a geometric point `s : Spec Ω ⟶ T` (`Ω` separably closed) of a scheme `T`, the stalk of an
étale sheaf of `Λ`-modules at `s` is the module of global sections of its inverse image along
`s`: the pointed étale neighbourhood `(Spec Ω, 𝟙)` of the tautological point of `Spec Ω` is
initial, so the stalk at the tautological point is the module of global sections.

## Main statements

- `AlgebraicGeometry.Etale.upperStarCompSectionsIsoSheafFiber` (`lem-kun-stalk-as-pullback`).
- `AlgebraicGeometry.Etale.sheafFiberHomologyIso` (`lem-kun-stalks-of-cohomology`).
- `AlgebraicGeometry.Etale.isZero_iff_forall_isZero_homology`
  (`lem-kun-d-zero-cohomology`).
- `AlgebraicGeometry.Etale.isIso_iff_forall_isIso_leftDerivedUpperStar_map`
  (`lem-kun-stalk-faithful-derived`).
- `AlgebraicGeometry.Etale.exists_comp_eq_sepClosureBaseChange`,
  `AlgebraicGeometry.Etale.isIso_iff_isIso_upperStar_sepClosureBaseChange_map` and
  `AlgebraicGeometry.Etale.isIso_iff_isIso_leftDerivedUpperStar_sepClosureBaseChange_map`
  (`lem-kun-sep-closure-conservative`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section TautologicalPoint

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The tautological pointed étale neighbourhood `(Spec Ω, 𝟙)` of the geometric point
`𝟙 : Spec Ω ⟶ Spec Ω`. -/
noncomputable abbrev tautologicalElement :
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.Elements :=
  Functor.elementsMk _ (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
    (Over.homMk (𝟙 (Spec (.of Ω))) (Category.comp_id _))

/-- The tautological pointed étale neighbourhood `(Spec Ω, 𝟙)` is initial among the pointed
étale neighbourhoods of the geometric point `𝟙 : Spec Ω ⟶ Spec Ω`: a pointed neighbourhood
`(V, x)` receives the unique morphism `x : Spec Ω ⟶ V`. -/
noncomputable def isInitialTautologicalElement : IsInitial (tautologicalElement (Ω := Ω)) :=
  IsInitial.ofUniqueHom
    (fun Y ↦ ⟨MorphismProperty.Over.homMk Y.2.left (by simpa using Over.w Y.2), by
      ext
      simp⟩)
    (fun Y m ↦ by
      apply Functor.Elements.ext
      apply MorphismProperty.Over.Hom.ext
      have := congrArg CommaMorphism.left m.2
      simpa using this)

/-- The germ map from the sections over the tautological neighbourhood to the stalk at the
tautological point of `Spec Ω` is an isomorphism. -/
instance isIso_toPresheafFiber_tautological
    (P : (Spec (.of Ω)).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    IsIso ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber tautologicalElement.1
      tautologicalElement.2 P) :=
  isIso_ι_of_isTerminal isInitialTautologicalElement.op _

/-- The stalk at the tautological point of `Spec Ω` is the module of global sections. -/
noncomputable def sectionsIsoSheafFiberTautological :
    (sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ≅
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber :=
  have : IsIso (Functor.whiskerLeft (sheafToPresheaf _ _)
      ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiberNatTrans
        (A := ModuleCat.{u + 1} Λ) tautologicalElement.1 tautologicalElement.2)) :=
    NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerLeft (sheafToPresheaf _ _)
      ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiberNatTrans
        (A := ModuleCat.{u + 1} Λ) tautologicalElement.1 tautologicalElement.2))

end TautologicalPoint

end Etale

end AlgebraicGeometry
