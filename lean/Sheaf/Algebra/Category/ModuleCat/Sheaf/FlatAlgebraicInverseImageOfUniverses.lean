/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-!
# Flatness under algebraic inverse image

Source: Stacks Project, Modules on Sites, Tag 05VD, the inverse-image portion of
lemma-pullback-flat, before the final change of rings.
-/

@[expose] public section

universe uC vC uD vD r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Inverse image transports a flat module to a flat module over the inverse-image ring.
Source: Stacks Project, Modules on Sites, Tag 05VD (lemma-pullback-flat), paragraphs
before the final scalar-extension reduction
(blueprint: lem-weil-pbc-flat-algebraic-inverse-image-universes).

Proof: present the geometric morphism by a continuous finite-limit-preserving functor
of sites, up to equivalences of sheaf topoi. Such equivalences induce exact module
category equivalences preserving balanced tensor products, so flatness is invariant.
For the resulting site functor the inverse image is the sheafification of the filtered
colimit over pairs consisting of a source object V and a map U to its image. Finite
limits make this index filtered. Addition, scalar multiplication and the zero section
are induced by their stage maps, and agree with I because its graph equations specify
these operations on every test sheaf.

Apply the local equational criterion for flatness. A finite relation in the pulled-back
module locally lifts through sheafification; after another cover the lifted relation
is zero in the colimit. Filteredness puts all its coefficients and module elements at
one stage, and eventual equality puts the zero relation at a later common stage. The
flat source module supplies a covering and a finite matrix factorization there, with
its coefficient products zero. Pull the covering back along U to the image of that
stage. Continuity and stability of covering sieves give a covering of U. The stage maps
preserve sums and scalar multiplication, so the transported matrix factorization has
the required equations for the original relation. For an empty relation take the empty
matrix and the maximal covering sieve. The reverse equational criterion gives flatness
over the inverse-image ring. Finally transport back through the presentation
equivalences and the algebraic underlying-sheaf isomorphisms of I. -/
theorem isFlat_algebraicInverseImageOfUniverses
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
    {R : Sheaf J CommRingCat.{r}} {RI : Sheaf K CommRingCat.{r}}
    (uInv : Sheaf J (Type (max r m)) ⥤ Sheaf K (Type (max r m)))
    (uPush : Sheaf K (Type (max r m)) ⥤ Sheaf J (Type (max r m)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImageOfUniverses uInv R RI)
    (F : ringedSiteModules.{max r m, r, vC, uC}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (hF : IsFlatOnSite F) : IsFlatOnSite (I.modules.obj F) := by sorry


end SheafOfModules
