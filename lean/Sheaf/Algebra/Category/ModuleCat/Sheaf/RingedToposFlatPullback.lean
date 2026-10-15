/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.CategoryTheory.RingedToposSitePresentation
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-!
# Pullback of flat modules along morphisms of ringed topoi

Source: Stacks Project, Modules on Sites, Tag 05VD, lemma-pullback-flat
(blueprint: lem-weil-pbc-ringed-topos-flat-module-pullback).
-/

@[expose] public section

universe uC vC uD vD r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Pullback along an arbitrary morphism of ringed topoi preserves flat module sheaves.
The algebraic inverse-image presentation specifies transport of all ring and module
operations along the underlying inverse image. The pullback is its change of rings.
Source: Stacks Project, Tag 05VD, lemma-pullback-flat
(blueprint: lem-weil-pbc-ringed-topos-flat-module-pullback).

Proof plan:
1. Use lem-weil-pbc-ringed-topos-site-presentation to present the geometric morphism by
   a continuous finite-limit-preserving site functor, up to ringed-topos equivalences.
2. Such equivalences preserve exactness and tensor products, hence flatness.
3. By lem-weil-pbc-presheaf-pullback-sets-left-exact and
   lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction, inverse image is the
   sheafification of the filtered-colimit presheaf. The underlying-set and module
   sheafification interfaces identify the transported algebraic structures.
4. By lem-weil-pbc-site-sheafification-sections-local and
   lem-weil-pbc-filtered-colimit-sets-elementwise, any finite relation locally comes
   from a relation at one common stage; eventual equality makes it zero there.
   For an empty relation use the final object as a stage.
5. Apply lem-weil-pbc-site-flat-equational-criterion to the flat source module,
   obtaining local matrix factorizations of this relation.
6. Pull these coverings back by fibre products. Continuity and the site axioms
   give coverings, and the transported matrices satisfy the same equations.
   The converse equational criterion proves flatness over the inverse-image ring.
7. Finally, (G tensor B) tensor N is G tensor Res(N), by the balanced tensor
   universal property. Restriction of scalars is exact, and exactness is detected
   on underlying abelian sheaves, proving flatness after arbitrary change of rings.
-/
theorem isFlat_ringedToposPullback
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
    [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙ uliftFunctor.{r, max r m})]
    [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙ uliftFunctor.{r, max r m})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}] [HasWeakSheafify J AddCommGrpCat.{max r m}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
    [HasWeakSheafify K AddCommGrpCat.{max r m}]
    {R : Sheaf J CommRingCat.{r}} {RI S : Sheaf K CommRingCat.{r}}
    (uInv : Sheaf J (Type (max r m)) ⥤ Sheaf K (Type (max r m)))
    (uPush : Sheaf K (Type (max r m)) ⥤ Sheaf J (Type (max r m)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImageOfUniverses uInv R RI) (c : RI ⟶ S)
    (F : ringedSiteModules.{max r m, r, vC, uC}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (hF : IsFlatOnSite F) : IsFlatOnSite (changeOfRingsOfUniverses (J := K) c (I.modules.obj F))
      := by
  sorry

end SheafOfModules
