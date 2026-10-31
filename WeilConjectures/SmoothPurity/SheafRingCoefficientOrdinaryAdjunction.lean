/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Ordinary coefficient adjunction on a ringed site

Source: Stacks Project, Modules on Sites, Tags 03D7 and 03DA
(blueprint: lem-pur-sheaf-ring-coefficient-ordinary-adjunction).

Sheafification of the sectionwise tensor/restriction Hom equivalence gives the normalized
ordinary adjunction. Exactness of restriction follows through the forgetful functor to
abelian sheaves.
-/

@[expose] public section

set_option autoImplicit false
universe w r u v
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules.CoefficientOrdinaryProof

-- Reuse the sectionwise proof of ScalarReductionProof, at independent site universes.
section SameSiteAdjunction

universe a b

variable {D : Type a} [Category.{b} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify K AddCommGrpCat.{r}]

private abbrev ringSheaf (A : Sheaf K CommRingCat.{r}) :=
  (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj A

private noncomputable abbrev restriction
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :=
  restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

private noncomputable def tensorPresheafFunctor
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (ringSheaf A) ⥤ PresheafOfModules.{r} (ringSheaf S).obj where
  obj M := changeOfRingsPresheaf.{b, a, r} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{b, a, r} c M ⟶
      changeOfRingsPresheaf.{b, a, r} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{b, a, r} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (ringSheaf A) ⥤ SheafOfModules.{r} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

end SameSiteAdjunction

end SheafOfModules.CoefficientOrdinaryProof

namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {O O' : Sheaf J CommRingCat.{r}}

omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
end SheafOfModules
