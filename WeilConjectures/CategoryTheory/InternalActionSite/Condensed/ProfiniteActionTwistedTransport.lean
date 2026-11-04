/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.Condensed.ProfiniteActionEquivalence
public import WeilConjectures.CategoryTheory.InternalActionSite.PresentationSections
public import WeilConjectures.CategoryTheory.InternalActionSite.ProjectionRingedTopos
public import WeilConjectures.CategoryTheory.CondensedBar.CondensedScalarAction

/-!
# Internal condensed actions as modules on the twisted ringed site

Source: paragraph (3) of the direct-image stability proof, action-site presentation
(blueprint: def-sfb-condensed-derived-invariants).

Composing `siteEquivalence` with an action-site presentation identifies internal actions
of `G` on internal `A`-modules with modules over the twisted ring on the twisted small
profinite site. Under this identification, scalar restriction of actions along `a : A ⟶ A'`
is restriction of scalars along the induced map of twisted rings, and the trivial action is
pullback along the projection to the small profinite site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CondensedBar.ActionSite

open InternalActionSite

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The twisted small profinite site of `G`. -/
abbrev twistedTopology : GrothendieckTopology (Object (groupPresheaf G)) :=
  topology (groupPresheaf G) modelPrecoverage.{u}

variable (A : Ring.{u})

/-- The twisted coefficient ring of `A` on the twisted small profinite site. -/
noncomputable abbrev twistedRingOf : Sheaf (twistedTopology G) RingCat.{u + 1} :=
  twistedRing (groupPresheaf G) modelPrecoverage modelPrecoverage_isSiteForCoverings
    (ringSheaf A)

/-- A chosen action-site presentation on the small profinite site. -/
noncomputable def presentationOf :
    Presentation (groupPresheaf G) modelPrecoverage modelPrecoverage_isSiteForCoverings
      (ringSheaf A) :=
  Classical.choice (presentation (groupPresheaf G) modelPrecoverage
    modelPrecoverage_isSiteForCoverings (groupPresheaf_isSheaf G) (ringSheaf A))

/-- Internal actions are modules over the twisted ring. -/
noncomputable def twistedEquivalence :
    Equivariant A G ≌ SheafOfModules.{u + 1} (twistedRingOf G A) :=
  (siteEquivalence A G).trans (presentationOf G A).sheafEquivalence

instance twistedEquivalence_functor_additive : (twistedEquivalence G A).functor.Additive := by
  have := (presentationOf G A).sheaf_additive
  exact inferInstanceAs (toSite ⋙ (presentationOf G A).sheafEquivalence.functor).Additive

variable {A G}

/-- The ring sheaf map on the small model induced by a map of condensed rings. -/
noncomputable def ringSheafMap {A A' : Ring.{u}} (a : A ⟶ A') : ringSheaf A ⟶ ringSheaf A' :=
  ⟨Functor.whiskerLeft (AsSmall.down : Model.{u} ⥤ Profinite.{u}).op
    (Functor.whiskerRight ((Monoidal.commMonFunctorCategoryEquivalence _ _).functor.map
      ((sheafToPresheaf _ _).mapCommMon.map a)) InternalAbelianSheafModule.commMonToRing)⟩

variable (G) in
/-- The map of twisted coefficient rings induced by a map of condensed rings. -/
noncomputable def twistedRingMap {A A' : Ring.{u}} (a : A ⟶ A') :
    twistedRingOf G A ⟶ twistedRingOf G A' :=
  (sheafCompose (twistedTopology G) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    ⟨Functor.whiskerLeft (projection (groupPresheaf G)).op (ringSheafMap a).hom⟩

example {A A' : Ring.{u}} (a : A ⟶ A') (X : Model.{u}) (r : sectionRing A (AsSmall.down.obj X)) :
    ((twistedRingMap G a).hom.app (op (Object.mk X))).hom r =
      (a.hom.hom.hom.app (op (AsSmall.down.obj X))).hom r := rfl

end CategoryTheory.CondensedBar.ActionSite
