/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
public import Sheaf.CategoryTheory.Sites.ConstructibleTorsor
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Torsors under an inverse-image group sheaf

Source: Stacks Project, Tags 03AH, 00YV and 099X, and the current blueprint,
sec-proetale-coefficients/sk-lem-pe-torsor-comparison
(blueprint: def-pe-comparison-torsor).

The group operations and torsor actions are transported by the canonical finite-product
comparisons of the recorded set-valued inverse image. No choice of an action is involved.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} (G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1})

/-- The underlying set sheaf of the group. Source: Stacks Tag 00YV
(blueprint: def-pe-comparison-torsor). -/
abbrev groupSets : Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  (sheafCompose X.smallEtaleTopology (forget GrpCat.{u + 1})).obj G₀

/-- Sectionwise group multiplication, as a morphism of set sheaves.
Source: Stacks Tag 00YV (blueprint: def-pe-comparison-torsor). -/
def groupMultiplication : groupSets G₀ ⊗ groupSets G₀ ⟶ groupSets G₀ :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun p : G₀.obj.obj U × G₀.obj.obj U ↦ p.1 * p.2)
     naturality := by
       intro U V f
       ext p
       change G₀.obj.obj U × G₀.obj.obj U at p
       change (G₀.obj.map f).hom p.1 * (G₀.obj.map f).hom p.2 =
         (G₀.obj.map f).hom (p.1 * p.2)
       exact (map_mul (G₀.obj.map f).hom p.1 p.2).symm }⟩

/-- The identity section. Source: Stacks Tag 00YV
(blueprint: def-pe-comparison-torsor). -/
def groupIdentity : 𝟙_ (Sheaf X.smallEtaleTopology (Type (u + 1))) ⟶ groupSets G₀ :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (1 : G₀.obj.obj U))
     naturality := by
       intro U V f
       ext p
       exact (map_one (G₀.obj.map f).hom).symm }⟩

/-- The recorded set-valued inverse image. Source: Stacks Tag 099R
(blueprint: def-pe-comparison-torsor). -/
abbrev comparisonSets (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
    (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The canonical product comparison, using recorded left exactness.
Source: Stacks Tags 00YV and 099R (blueprint: def-pe-comparison-torsor). -/
def comparisonProduct (F H : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (comparisonSets X).obj (F ⊗ H) ≅
      (comparisonSets X).obj F ⊗ (comparisonSets X).obj H := by
  letI := Scheme.preservesFiniteLimits_proEtaleSiteComparison X
  exact CartesianMonoidalCategory.prodComparisonIso (comparisonSets X) F H

/-- The actual multiplication on the inverse-image group sheaf.
Source: Stacks Tag 00YV (blueprint: def-pe-comparison-torsor). -/
def comparisonMultiplication :
    (comparisonSets X).obj (groupSets G₀) ⊗ (comparisonSets X).obj (groupSets G₀) ⟶
      (comparisonSets X).obj (groupSets G₀) :=
  (comparisonProduct (groupSets G₀) (groupSets G₀)).inv ≫
    (comparisonSets X).map (groupMultiplication G₀)

/-- The actual identity on the inverse-image group sheaf.
Source: Stacks Tag 00YV (blueprint: def-pe-comparison-torsor). -/
def comparisonIdentity :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) ⟶
      (comparisonSets X).obj (groupSets G₀) := by
  letI := Scheme.preservesFiniteLimits_proEtaleSiteComparison X
  exact (CartesianMonoidalCategory.preservesTerminalIso (comparisonSets X)).inv ≫
    (comparisonSets X).map (groupIdentity G₀)

/-- A torsor for the pulled-back, possibly noncommutative group sheaf.
The natural action obeys the unit and multiplication laws, is simply transitive wherever
sections exist, and has local sections for the pro-etale topology.
Source: Stacks Tags 03AH and 099X (blueprint: def-pe-comparison-torsor). -/
structure ComparisonTorsor where
  /-- The underlying pro-etale set sheaf. -/
  sheaf : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))
  /-- The action, including naturality in the site object. -/
  action : (comparisonSets X).obj (groupSets G₀) ⊗ sheaf ⟶ sheaf
  one_act (U : X.ProEtᵒᵖ) (t : sheaf.obj.obj U) :
    action.hom.app U ((comparisonIdentity G₀).hom.app U PUnit.unit, t) = t
  mul_act (U : X.ProEtᵒᵖ) (g h : ((comparisonSets X).obj (groupSets G₀)).obj.obj U)
      (t : sheaf.obj.obj U) :
    action.hom.app U ((comparisonMultiplication G₀).hom.app U (g, h), t) =
      action.hom.app U (g, action.hom.app U (h, t))
  bijective_act (U : X.ProEtᵒᵖ) (t : sheaf.obj.obj U) :
    Function.Bijective (fun g ↦ action.hom.app U (g, t))
  nonemptySieve_mem (U : X.ProEt) :
    CategoryTheory.Sheaf.nonemptySieve sheaf.obj U ∈ Scheme.ProEt.topology X U

variable {G₀}

/-- The action morphism of the recorded etale torsor structure.
Source: Stacks Tag 03AH (blueprint: def-pe-comparison-torsor). -/
def etaleTorsorAction (P : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀) :
    groupSets G₀ ⊗ P.sheaf ⟶ P.sheaf :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun p ↦ P.act U p.1 p.2)
     naturality := by
       intro U V f
       ext p
       exact (P.map_act f p.1 p.2).symm }⟩

/-- The canonical inverse-image action, obtained by applying inverse image to the action
and precomposing with the inverse product comparison.
Source: Stacks Tags 00YV and 099X (blueprint: def-pe-comparison-torsor). -/
def comparisonTorsorAction
    (P : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀) :
    (comparisonSets X).obj (groupSets G₀) ⊗ (comparisonSets X).obj P.sheaf ⟶
      (comparisonSets X).obj P.sheaf :=
  (comparisonProduct (groupSets G₀) P.sheaf).inv ≫
    (comparisonSets X).map (etaleTorsorAction P)

/-- An isomorphism from the canonical inverse image of an etale torsor to `T`.
Source: Stacks Tag 099X (blueprint: def-pe-comparison-torsor). -/
structure ComparisonTorsor.ModelIso
    (P : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀)
    (T : ComparisonTorsor G₀) where
  iso : (comparisonSets X).obj P.sheaf ≅ T.sheaf
  equivariant : comparisonTorsorAction P ≫ iso.hom =
    (𝟙 ((comparisonSets X).obj (groupSets G₀)) ⊗ₘ iso.hom) ≫ T.action

/-- A trivialization over a pro-etale object, expressed on every object of its slice.
Source: Stacks Tag 03AH (blueprint: def-pe-comparison-torsor). -/
structure ComparisonTorsor.Trivialization (T : ComparisonTorsor G₀) (U : X.ProEt) where
  equiv : ∀ (V : X.ProEt) (_f : V ⟶ U),
    T.sheaf.obj.obj (op V) ≃ ((comparisonSets X).obj (groupSets G₀)).obj.obj (op V)
  natural : ∀ {V W : X.ProEt} (f : V ⟶ U) (g : W ⟶ V)
      (t : T.sheaf.obj.obj (op V)),
    equiv W (g ≫ f) (T.sheaf.obj.map g.op t) =
      ((comparisonSets X).obj (groupSets G₀)).obj.map g.op (equiv V f t)
  equivariant : ∀ (V : X.ProEt) (f : V ⟶ U)
      (a : ((comparisonSets X).obj (groupSets G₀)).obj.obj (op V))
      (t : T.sheaf.obj.obj (op V)),
    equiv V f (T.action.hom.app (op V) (a, t)) =
      (comparisonMultiplication G₀).hom.app (op V) (a, equiv V f t)

end AlgebraicGeometry.ProEtale
