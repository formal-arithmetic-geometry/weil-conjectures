/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteStrictPerfectHom
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Perfect duality on a small ringed site

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ,
lemma-dual-perfect-complex (blueprint: lem-sfb-ringed-site-perfect-duality).
The canonical maps are explicit transposes of evaluation in a normalized K-flat
closed tensor-Hom presentation, rather than unspecified isomorphic morphisms.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r w w'
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

section Transport
variable {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
  (T : WeilConjectures.CoefficientClosedStructure H)
  (s : @SymmetricCategory D _ T.monoidal) (O : D) (u : T.monoidal.tensorUnit ≅ O)

end Transport

@[irreducible] private noncomputable def restrictScalarsSelfIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (S : Sheaf J RingCat.{r}) :
    SheafOfModules.restrictScalars.{max c v r} (𝟙 S) ≅
      𝟭 (SheafOfModules.{max c v r} S) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact { hom := { val := 𝟙 _ }, inv := { val := 𝟙 _ } }
  · intro M N f
    ext V x
    rfl

@[irreducible] private noncomputable def restrictionComplexIso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (U : C) :
    ringedSiteDualityRestrictionComplex.{c, v, r} J R U ≅
      (SheafOfModules.localizedSystemRestriction.{c, v, r} R U).mapHomologicalComplex
        (.up ℤ) := by
  let F := SheafOfModules.localizedSystemRestriction.{c, v, r} R U
  exact NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft F
    (restrictScalarsSelfIso _) ≪≫ Functor.rightUnitor F) (.up ℤ)

section LocalModels

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

set_option hygiene false in
set_option quotPrecheck false in
local notation "S" => ((sheafCompose J
  (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
set_option hygiene false in
set_option quotPrecheck false in
local notation "A" => SheafOfModules.{max c v r} S
set_option hygiene false in
set_option quotPrecheck false in
local notation "AU" U => SheafOfModules.{max c v r} ((S).over U)

variable [HasDerivedCategory.{w} A] [∀ U : C, HasDerivedCategory.{w'} (AU U)]
  (F : ∀ U : C, DerivedCategory A ⥤ DerivedCategory (AU U))

end LocalModels

section ComparisonData
variable {D D' B B' : Type*} [Category D] [Category D'] [Category B] [Category B']
  {H : Dᵒᵖ × D ⥤ D} {H' : D'ᵒᵖ × D' ⥤ D'}

end ComparisonData

section RestrictionData

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
  (U : C) [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (SheafOfModules.{max c v r} ((sheafCompose (J.over U)
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over U)))]

end RestrictionData

end CategoryTheory
