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

/-! # The direct-image part of affine ind-etale continuity

The complex diagram here lives on the fixed small etale site of the base. Its
normalization uses the actual derived inverse-image/direct-image adjunction.
Source: Bhatt--Scholze 6.3.16 and Stacks 0GIU
(blueprint: lem-per-ind-etale-derived-image-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (M : DerivedCategoryModule A X)

/-- The actual derived direct image of the pullback of the coefficient complex.
Source: Stacks 0GIU (blueprint: lem-per-ind-etale-derived-image-model). -/
def imageValue (T : Over X) : DerivedCategoryModule A X :=
  ((lowerStar (ModuleCat.{u + 1} A) T.hom).rightDerivedFunctor).obj
    ((ExternalRHom.pull A T.hom).obj M)

/-- The transition is adjoint to pullback of the earlier counit. The two composition
isomorphisms identify iterated inverse images with the specified inverse image.
Source: Stacks 0EYM and Bhatt--Scholze 6.3.16
(blueprint: lem-per-ind-etale-derived-image-model). -/
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
compute global Hom on X and on T.
Source: Stacks 08JA (blueprint: lem-per-ind-etale-derived-image-hom-adjunction). -/
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

/-- Global Hom adjunction for the direct image, constructed by conjugating the
canonical monoidal and constant-pullback comparisons. In particular no witness
of an existence theorem is used to define this isomorphism.
Source: Stacks 08JA (blueprint: lem-per-ind-etale-derived-image-hom-adjunction). -/
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

variable {I : Type (u + 1)} [SmallCategory I]
variable (D : I ⥤ Over X) (c : Cone D)

/-- A strict complex realization of the derived direct-image diagram and cocone.
No continuity assertion is part of this data.
Source: Bhatt--Scholze 6.3.16, proof, direct-image construction
(blueprint: lem-per-ind-etale-derived-image-model). -/
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

/-- The direct-image diagram has uniformly bounded-below strict representatives,
and its actual cocone comparison is a derived isomorphism. This concerns only M;
it makes no assertion about constructible global Hom.

Source: Stacks 0GIU, Bhatt--Scholze 6.3.16, proof, direct-image continuity
(blueprint: lem-per-ind-etale-derived-image-model).

Proof: choose a bounded-below injective representative of M. At an etale stage
its exact inverse image remains injective, since etale extension by zero is an
exact left adjoint. Apply direct image to obtain the stage complexes. Their
transition maps are the adjunction units, with the inverse-image composition
identifications. At the limit resolve the pulled-back complex by a bounded-below
injective complex with the same lower bound, and use the resolution map for the
cocone legs. The unit and counit identities give the displayed normalizations.
Stacks 0GIU gives the colimit isomorphism on every cohomology sheaf; forgetting
coefficient modules preserves the colimit and reflects the isomorphism. Exactness
of filtered colimits identifies these cohomology maps with those of the complex
cocone comparison, so localization inverts it. Construct the strict
representatives on I itself. For the cohomology continuity argument only, take
a directed final index in the opposite of I and adjoin X as an initial stage.
Finality identifies the cohomology cocone comparisons; no strict diagram is
transported backwards along a final functor.
-/
theorem derivedImageModel_exists_continuous [Finite A] [IsAffine X]
    [IsNoetherian X] [IsCofiltered I]
    (hc : IsLimit ((Over.forget X).mapCone c))
    (haffine : ∀ i : I, IsAffine (D.obj i).left)
    (hetale : ∀ i : I, Etale (D.obj i).hom)
    (hfp : ∀ i : I, LocallyOfFinitePresentation (D.obj i).hom)
    (htransition : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left)
    (hM : ∃ a : ℤ, M.IsGE a) :
    ∃ (N : DerivedImageModel A M D c) (a : ℤ),
      (∀ i : I, (DerivedCategory.Q.obj (N.diagram.obj (op i))).IsGE a) ∧
      IsIso (DerivedCategory.Q.map (colimit.desc N.diagram N.cocone)) := by
  sorry

end AlgebraicGeometry.Etale.IndEtaleMapping
