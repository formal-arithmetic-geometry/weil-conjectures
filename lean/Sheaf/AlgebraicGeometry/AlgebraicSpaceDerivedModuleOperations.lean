/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-! # Derived module operations on algebraic spaces

Source: Stacks Project, Properties of Spaces, 03G7 and 03G8; Cohomology on Sites,
06YS, 06YU and 079P (blueprint: def-sfb-space-derived-module-operations).
The tensor uses the existing small ringed model and categorical left-derived universal
property. The ambient derived category and direct image remain owned by the calculus node.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe c v r u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})

/-- Tensoring the identity in the second variable gives the identity transformation.
Source: Stacks 03EK (blueprint: def-sfb-space-derived-module-operations).
Proof: on pure tensors the map is the identity; apply module sheafification. -/
theorem siteTensorRightMap_id
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    siteSheafTensorRightMap.{c, v, r, r} (A := R) (𝟙 M) =
      𝟙 (siteSheafTensorRight.{v, c, r, r} (A := R) M) := by
  sorry

/-- Tensor maps preserve composition in the second variable.
Source: Stacks 03EK (blueprint: def-sfb-space-derived-module-operations).
Proof: both maps send x tensor y to x tensor g(f(y)); sheafify this equality. -/
theorem siteTensorRightMap_comp
    {M N P : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (f : M ⟶ N) (g : N ⟶ P) :
    siteSheafTensorRightMap.{c, v, r, r} (A := R) (f ≫ g) =
      siteSheafTensorRightMap.{c, v, r, r} (A := R) f ≫
        siteSheafTensorRightMap.{c, v, r, r} (A := R) g := by
  sorry

/-- The existing tensor, curried with the fixed right factor as the first argument.
Source: Stacks 03EK (blueprint: def-sfb-space-derived-module-operations). -/
def siteTensorRightFactors :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
        SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) where
  obj M := siteSheafTensorRight.{v, c, r, r} (A := R) M
  map f := siteSheafTensorRightMap.{c, v, r, r} (A := R) f
  map_id M := siteTensorRightMap_id R M
  map_comp f g := siteTensorRightMap_comp R f g

/-- The shared sectionwise tensor with arguments in their ordinary order.
Source: Stacks 03EK (blueprint: def-sfb-space-derived-module-operations). -/
def siteTensorAtCoefficientSize := (siteTensorRightFactors R).flip

/-- The tensor preserves zero maps in the first variable, without a site-size equality.
Source: Stacks 03EK (blueprint: def-sfb-space-derived-module-operations).
Proof: a zero linear map tensors to zero on pure tensors, and sheafification is additive. -/
@[instance] theorem siteTensorAtCoefficientSize_preservesZero :
    (siteTensorAtCoefficientSize R).PreservesZeroMorphisms := by
  sorry

/-- The tensor preserves zero maps in the second variable as well.
Source: Stacks 03EK (blueprint: def-sfb-space-derived-module-operations).
Proof: evaluate on pure tensors and use additivity of module sheafification. -/
@[instance] theorem siteTensorAtCoefficientSize_obj_preservesZero
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    ((siteTensorAtCoefficientSize R).obj M).PreservesZeroMorphisms := by
  sorry

/-- Total tensor with a fixed complex, with differential d tensor 1 plus (-1)^p 1 tensor d.
Source: Stacks 03EK and 06YN (blueprint: def-sfb-space-derived-module-operations). -/
def siteComplexTensorRight
    (G : CochainComplex
      (SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) :=
  ((siteTensorAtCoefficientSize R).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj G

end SheafOfModules

namespace AlgebraicGeometry.AlgebraicSpace

/-- Total tensor on the existing small model with the restriction of the given coefficient complex.
Source: Stacks 03EK and 06YN (blueprint: def-sfb-space-derived-module-operations). -/
def moduleComplexTensorRight {S : Scheme.{u}} (X : AlgebraicSpace S)
    (G : CochainComplex X.Modules ℤ) :
    CochainComplex X.SmallModules ℤ ⥤ CochainComplex X.SmallModules ℤ :=
  SheafOfModules.siteComplexTensorRight.{u, u, u}
    (J := X.smallEtaleModelTopology) X.smallStructureSheaf
    ((X.smallModuleRestriction.mapHomologicalComplex (.up ℤ)).obj G)

/-- Total tensor with a fixed complex has a left derived functor at quasi-isomorphisms.
Source: Stacks 06YS and 06YU (blueprint: def-sfb-space-derived-module-operations).
Proof: free module sheaves on the small affine étale basis give flat generators.
The standard unbounded flat resolution supplies a K-flat flat-term resolution of
every complex. Total tensor with the fixed complex preserves quasi-isomorphisms
between these resolutions, by the acyclic-cone criterion and K-flatness. The
resolution comparison and homotopy uniqueness give the right Kan extension along
localization. Its counit on a K-flat resolution is the usual tensor comparison. -/
@[instance] theorem moduleComplexTensor_hasLeftDerived
    {S : Scheme.{u}} (X : AlgebraicSpace S) [HasDerivedCategory.{w} X.SmallModules]
    (G : CochainComplex X.Modules ℤ) :
    ((moduleComplexTensorRight X G) ⋙
      DerivedCategory.Q.{w} (C := X.SmallModules)).HasLeftDerivedFunctor
        (HomologicalComplex.quasiIso X.SmallModules (.up ℤ)) := by
  sorry

/-- Derived tensor with the given coefficient complex, via its categorical universal property.
Source: Stacks 06YU (blueprint: def-sfb-space-derived-module-operations). -/
def moduleDerivedTensorComplex {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] (E : X.DerivedModules)
    (G : CochainComplex X.Modules ℤ) : X.DerivedModules :=
  (((moduleComplexTensorRight X G) ⋙
    DerivedCategory.Q.{w} (C := X.SmallModules)).totalLeftDerived
      (DerivedCategory.Q.{w} (C := X.SmallModules))
      (HomologicalComplex.quasiIso X.SmallModules (.up ℤ))).obj E

end AlgebraicGeometry.AlgebraicSpace
