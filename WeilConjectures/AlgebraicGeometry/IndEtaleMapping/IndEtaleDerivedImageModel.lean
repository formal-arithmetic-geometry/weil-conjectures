/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-! # The direct-image part of affine ind-etale continuity

The complex diagram here lives on the fixed small etale site of the base. Its
normalization uses the actual derived inverse-image/direct-image adjunction.

## Implementation details

* `imageHomIso` is constructed by conjugating the canonical monoidal and constant-pullback
  comparisons; no witness of an existence theorem is used to define it.
* `exists_imageValue_strictModel` is a missing input from derived inverse and direct images: the
  project has the derived adjunctions `Lg^* ⊣ Rg_*` and their coherence, but no strict
  functorial models of `Rg_* Lg^*` along diagrams of schemes (these would come from functorial
  `g_*`-acyclic resolutions of the pulled-back complexes).
* `isColimit_homology_imageValue` is a missing input from cohomology and limits: the project has
  the absolute statement for global sections with abelian coefficients
  (`AlgebraicGeometry.derivedEtaleCohomology_limit`, Stacks 0GIT), but not the relative,
  sheaf-level version over a fixed base with module coefficients.

## References

* Bhatt–Scholze, The pro-étale topology for schemes, proof of Lemma 6.3.16
* Stacks Project, Tags 0GIU, 0EYM, 09YQ, 08JA
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (M : DerivedCategoryModule A X)

/-- The actual derived direct image of the pullback of the coefficient complex. -/
def imageValue (T : Over X) : DerivedCategoryModule A X :=
  ((lowerStar (ModuleCat.{u + 1} A) T.hom).rightDerivedFunctor).obj
    ((ExternalRHom.pull A T.hom).obj M)

/-- The transition is adjoint to pullback of the earlier counit. The two composition
isomorphisms identify iterated inverse images with the specified inverse image. -/
def imagePullback {T S : Over X} (f : T ⟶ S) :
    imageValue A M S ⟶ imageValue A M T :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom).homEquiv _ _
    (((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
        f.w.symm).hom.app (imageValue A M S)) ≫
      (ExternalRHom.pull A f.left).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) S.hom).counit.app
          ((ExternalRHom.pull A S.hom).obj M)) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
        f.w.symm).inv.app M)

/-- The canonical comparison of the two left adjoints whose right adjoints
compute global Hom on X and on T. -/
def imageTensorIso (K : DerivedCategoryModule A X) (T : Over X) :
    ExternalRHom.constant A T.left ⋙
        tensorLeft ((ExternalRHom.pull A T.hom).obj K) ≅
      (ExternalRHom.constant A X ⋙ tensorLeft K) ⋙ ExternalRHom.pull A T.hom := by
  letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) T.hom
  exact Functor.isoWhiskerRight (ExternalRHom.constantPullbackIso A T.hom) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.Monoidal.commTensorLeft (ExternalRHom.pull A T.hom) K) ≪≫
    (Functor.associator _ _ _).symm

/-- Global Hom adjunction for the direct image, built from the canonical monoidal and
constant-pullback comparisons. -/
def imageHomIso (K : DerivedCategoryModule A X) (T : Over X) :
    ((ExternalRHom.globalHom A X).obj (op K)).obj (imageValue A M T) ≅
      ((ExternalRHom.globalHom A T.left).obj
        (op ((ExternalRHom.pull A T.hom).obj K))).obj
          ((ExternalRHom.pull A T.hom).obj M) :=
  (conjugateIsoEquiv
    ((ExternalRHom.globalAdjunction A K).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom))
    (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A T.hom).obj K))
    (imageTensorIso A K T)).app ((ExternalRHom.pull A T.hom).obj M)

/-- The derived direct image of a bounded-below pullback stays bounded below. -/
theorem isGE_imageValue (T : Over X) (a : ℤ) [M.IsGE a] : (imageValue A M T).IsGE a := by
  have := (upperStar (ModuleCat.{u + 1} A) T.hom).isGE_mapDerivedCategory_obj M a
  have hK : ((ExternalRHom.pull A T.hom).obj M).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) T.hom).app M).symm a
  let F := lowerStar (ModuleCat.{u + 1} A) T.hom
  let K' : DerivedCategory.Plus (Sheaf T.left.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨(ExternalRHom.pull A T.hom).obj M, ⟨a, hK⟩⟩
  have : K'.IsGE a := (K'.isGE_ι_obj_iff a).1 hK
  refine (DerivedCategory.isGE_iff _ a).2 fun q hq ↦ ?_
  exact (F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE K' a hq).of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso
      (F.rightDerivedFunctorPlusCompatibility.app K')).symm

variable {I : Type (u + 1)} [SmallCategory I]
variable (D : I ⥤ Over X) (c : Cone D)

/-- A strict complex realization of the derived direct-image diagram and cocone.
No continuity assertion is part of this data. -/
structure DerivedImageModel where
  diagram : Iᵒᵖ ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ
  cocone : Cocone diagram
  stage : ∀ i : I, DerivedCategory.Q.obj (diagram.obj (op i)) ≅ imageValue A M (D.obj i)
  apex : DerivedCategory.Q.obj cocone.pt ≅ imageValue A M c.pt
  transition : ∀ {i j : I} (f : i ⟶ j),
    DerivedCategory.Q.map (diagram.map f.op) ≫ (stage i).hom =
      (stage j).hom ≫ imagePullback A M (D.map f)
  leg : ∀ i : I,
    DerivedCategory.Q.map (cocone.ι.app (op i)) ≫ apex.hom =
      (stage i).hom ≫ imagePullback A M (c.π.app i)

end AlgebraicGeometry.Etale.IndEtaleMapping
