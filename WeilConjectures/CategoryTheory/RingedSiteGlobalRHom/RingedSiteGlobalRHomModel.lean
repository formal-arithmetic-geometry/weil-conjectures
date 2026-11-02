/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Functor

/-! # Global derived Hom and its resolved-tower functors

Source: Stacks Project, sites-cohomology.tex, Tag 0B6E (section-global-RHom),
and spaces-perfect.tex, Tag 0D3F (lemma-pullback-and-limits), second proof paragraph.
(blueprint: lem-sfb-ringed-site-global-rhom-derived-limits).

The comparison is stated on the category of resolved strict towers: K-injective
complexes of towers whose terms are injective towers. Every strict tower admits
such a resolution. Its ordinary limit represents its resolution-derived limit.
The target uses ordinary limits of the resulting global Hom complexes; the Roos
triangle clause identifies these, with their actual projections, as derived limits.
Thus the natural isomorphism specifies the resolution-derived limiting cone.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r a w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteGlobalRHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}


/-- The recorded category of module sheaves, without any quasi-coherence restriction.
Source: Stacks 0B6E (blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
abbrev Modules [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r, r, v, c} ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The existing ring of compatible global ring sections.
Source: Stacks 0B6E (blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
abbrev Scalars (R : Sheaf J CommRingCat.{r}) :=
  RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r})

/-- The existing canonical global-section action on sheaf morphisms.
Source: Stacks 04TT (blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
instance modulesLinear [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r}) : Linear (Scalars.{c, v, r} R) (Modules.{c, v, r} R) :=
  SheafOfModules.homLinear.{r, v, c, r} R.obj
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).property

variable (R : Sheaf J CommRingCat.{max c v r})

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

variable [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  (A : Type a) [CommRing A] (φ : A →+* Scalars.{c, v, max c v r} R)
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)]

end CategoryTheory.RingedSiteGlobalRHom
