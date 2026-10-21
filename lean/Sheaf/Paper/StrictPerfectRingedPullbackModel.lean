/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients

/-! # Specified strict-perfect models for derived ringed-topos pullback

Source: Stacks Project, Cohomology on Sites, Tag 08H3, lemma-strictly-perfect-pullback;
Tag 06YQ and Section derived-pullback, Tag 06YY
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model).

The finite-free comparison is characterized on all local pure tensors, so its choice
is uniquely determined. The transported splittings are degreewise, with no assertion
that they commute with the differentials.

## Main definitions and statements

- `ringedPullbackFiniteFreeIso`: the uniquely characterized finite-free comparison.
- `ringedPullbackStrictPerfectPackage`: the specified transported degreewise splittings.
- `ringedPullbackComplexComparison`: the given comparison on cochain complexes.
- `strictPerfectRingedPullbackModel`: flatness, K-flatness, bounds and natural comparison.
-/

@[expose] public section
set_option autoImplicit false

-- Avoid repeated multicospan searches: first use size-bounded limits, then the small model.
attribute [local instance 12000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [local instance 11000] CategoryTheory.hasSheafComposeEssentiallySmallSite

universe uC vC uD vD r w
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem flat_finiteFree_retract
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (A : Sheaf J CommRingCat.{r})
    (M : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A))
    (n : ℕ) (i : M ⟶ ∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A))
    (p : (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) ⟶ M)
    (hip : i ≫ p = 𝟙 M) : IsFlatOnSite (J := J) (R := A) M := by
  let := isMonoidal_W_independentCoefficients.{uC, vC, r} A
  let := monoidalCategory.{vC, uC, r} A
  let := symmetricCategory.{vC, uC, r} A
  let := tensorPreadditive.{uC, vC, r} A
  have (M : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) := by
    have := tensorLeft_preservesColimits_independentCoefficients.{uC, vC, r} A M
    exact preservesColimitsOfSize_shrink (MonoidalCategory.tensorLeft M)
  have (M : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have hunit : ObjectProperty.flat
      (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) :=
    ObjectProperty.prop_unit ObjectProperty.flat
  have hfree : ObjectProperty.flat (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) :=
    ObjectProperty.prop_of_isLimit _ (limit.isLimit _) (fun _ ↦ hunit)
  have hM := ObjectProperty.prop_of_retract ObjectProperty.flat
    (show Retract M (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) from
        ⟨i, p, hip⟩) hfree
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso.{uC, vC, r} A M).symm hM.2

-- The resolving-class argument below uses the explicit scalar extension and its
-- identity comparison, as in DerivedPullbackRepresentativeComputation, with
-- independent site and coefficient universes throughout.
section DerivedHelpers
open MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

private noncomputable abbrev moduleUnderlying
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r}) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})

private theorem moduleUnderlying_finiteLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r}) : PreservesFiniteLimits (moduleUnderlying R) := by
  let V := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})
  have : PreservesFiniteLimits (V ⋙ sheafToPresheaf J (Type (r))) :=
    show PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{r} ⋙
      (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{r})) from
        comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits V :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type (r)))
  exact comp_preservesFiniteLimits _ _

private theorem moduleUnderlying_epi
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r}) : (moduleUnderlying R).PreservesEpimorphisms := by
  let V := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})
  have : V.PreservesEpimorphisms := ⟨fun {M N} f hf ↦ by
    have : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{r} f).2 hf
    exact inferInstance⟩
  exact inferInstanceAs ((toSheaf _ ⋙ V).PreservesEpimorphisms)

private theorem algebraicInverseImage_finiteLimits
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {RI : Sheaf JD CommRingCat.{r}}
    (L : Sheaf JC (Type (r)) ⥤ Sheaf JD (Type (r))) [PreservesFiniteLimits L]
    (I : AlgebraicInverseImage L R RI) : PreservesFiniteLimits I.modules := by
  have := moduleUnderlying_finiteLimits R
  have := moduleUnderlying_finiteLimits RI
  have : PreservesFiniteLimits (moduleUnderlying R ⋙ L) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (I.modules ⋙ moduleUnderlying RI) :=
    preservesFiniteLimits_of_natIso I.moduleUnderlying.symm
  exact preservesFiniteLimits_of_reflects_of_preserves I.modules (moduleUnderlying RI)

private theorem algebraicInverseImage_epi
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {RI : Sheaf JD CommRingCat.{r}}
    (L : Sheaf JC (Type (r)) ⥤ Sheaf JD (Type (r)))
    (V : Sheaf JD (Type (r)) ⥤ Sheaf JC (Type (r))) (adj : L ⊣ V)
    (I : AlgebraicInverseImage L R RI) : I.modules.PreservesEpimorphisms := by
  have := moduleUnderlying_epi R
  have := adj.leftAdjoint_preservesColimits
  constructor
  intro M N f hf
  apply (moduleUnderlying RI).epi_of_epi_map
  have : Epi ((moduleUnderlying R ⋙ L).map f) := inferInstance
  have hn := I.moduleUnderlying.hom.naturality f
  have : Epi ((I.modules ⋙ moduleUnderlying RI).map f ≫
      I.moduleUnderlying.hom.app N) := by
    rw [hn]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (I.moduleUnderlying.hom.app N)).1 this

private noncomputable def scalarExtensionPresheaf
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S) :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      PresheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj where
  obj M := changeOfRingsPresheaf.{vC, uC, r} c M
  map {M N} f :=
    { app := fun U ↦ (ModuleCat.extendScalars (c.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality.{vC, uC, r} c M f }
  map_id M := by
    ext U : 1
    simp
    rfl
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars (c.hom.app U).hom).map_comp _ _

private theorem scalarExtensionPresheaf_additive
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S) :
    (scalarExtensionPresheaf c).Additive where
  map_add {M N} f g := by
    ext U : 1
    have : (ModuleCat.extendScalars (c.hom.app U).hom).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (c.hom.app U).hom).left_adjoint_additive
    simpa only [scalarExtensionPresheaf, add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (c.hom.app U).hom).map_add
        (f := f.val.app U) (g := g.val.app U)

private noncomputable def scalarExtension
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S) :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S) :=
  scalarExtensionPresheaf c ⋙ PresheafOfModules.sheafification.{r, vC, r, uC}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)

private theorem scalarExtension_additive
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S) :
    (scalarExtension c).Additive := by
  have hsheaf : (PresheafOfModules.sheafification.{r, vC, r, uC}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction.{r, vC, r, uC} (𝟙 _)).left_adjoint_additive
  have := scalarExtensionPresheaf_additive c
  dsimp only [scalarExtension]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarExtensionPresheafIdIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r})
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    M.val ≅ (scalarExtensionPresheaf (𝟙 R)).obj M := by
  refine PresheafOfModules.isoMk
    (fun U ↦ ((ModuleCat.extendScalarsId (R.obj.obj U)).app (M.val.obj U)).symm) ?_
  intro U V i
  ext m
  change (ModuleCat.extendScalarsId (R.obj.obj V)).inv.app (M.val.obj V)
      (M.val.map i m) =
    changeOfRingsMap (𝟙 R) M i
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m)
  rw [ModuleCat.extendScalarsId_inv_app_apply, ModuleCat.extendScalarsId_inv_app_apply]
  simpa [changeOfRingsMap] using
    (Classical.choose_spec (exists_changeOfRingsMap (𝟙 R) M i)
      (1 : R.obj.obj U) m).symm

private noncomputable def scalarExtensionIdIsoApp
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r})
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    (scalarExtension (𝟙 R)).obj M ≅ M :=
  (PresheafOfModules.sheafification.{r, vC, r, uC} (𝟙 _)).mapIso
      (scalarExtensionPresheafIdIso R M).symm ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction.{r, vC, r, uC} (𝟙 _)).counit.app M)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarExtensionIdIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{r}) : scalarExtension (𝟙 R) ≅ 𝟭 _ := by
  refine NatIso.ofComponents (scalarExtensionIdIsoApp R) ?_
  intro M N a
  let F := PresheafOfModules.sheafification.{r, vC, r, uC}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)
  let ψ := (scalarExtensionPresheaf (𝟙 R)).map a
  have hp : (scalarExtensionPresheafIdIso R M).hom ≫ ψ =
      a.val ≫ (scalarExtensionPresheafIdIso R N).hom := by
    ext U m
    change (ModuleCat.extendScalars (RingHom.id (R.obj.obj U))).map (a.val.app U)
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m) =
        (ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (N.val.obj U) (a.val.app U m)
    exact ConcreteCategory.congr_hom ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.naturality
      (a.val.app U)) m
  have hp' : (scalarExtensionPresheafIdIso R M).inv ≫ a.val =
      ψ ≫ (scalarExtensionPresheafIdIso R N).inv := by
    rw [← cancel_epi (scalarExtensionPresheafIdIso R M).hom]
    simp only [← Category.assoc, hp]
    simp
  symm
  change F.map (scalarExtensionPresheafIdIso R M).inv ≫
      (PresheafOfModules.sheafificationAdjunction.{r, vC, r, uC} (𝟙 _)).counit.app M ≫ a =
    F.map ψ ≫ F.map (scalarExtensionPresheafIdIso R N).inv ≫
      (PresheafOfModules.sheafificationAdjunction.{r, vC, r, uC} (𝟙 _)).counit.app N
  rw [← (PresheafOfModules.sheafificationAdjunction.{r, vC, r, uC} (𝟙 _)).counit_naturality a]
  change F.map (scalarExtensionPresheafIdIso R M).inv ≫ F.map a.val ≫ _ = _
  rw [← F.map_comp_assoc, hp', F.map_comp_assoc]

set_option synthInstance.maxSize 256 in
private theorem isKFlat_of_iso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{r}}
    {P Q : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (e : P ≅ Q) (hP : P.IsKFlatIndependentCoefficients) : Q.IsKFlatIndependentCoefficients := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro A hA n
  let F := (MonoidalCategory.curriedTensor (SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let e' : CochainComplex.mapBifunctor A P (curriedTensor _) ≅
      CochainComplex.mapBifunctor A Q (curriedTensor _) :=
    HomologicalComplex₂.total.mapIso ((F.obj A).mapIso e) (ComplexShape.up ℤ)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hP A hA n)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso e').symm |>
      (HomologicalComplex.exactAt_iff_isZero_homology _ n).2

private theorem isKFlat_inverseImage
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {RI : Sheaf JD CommRingCat.{r}}
    (L : Sheaf JC (Type (r)) ⥤ Sheaf JD (Type (r)))
    (V : Sheaf JD (Type (r)) ⥤ Sheaf JC (Type (r))) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (I : AlgebraicInverseImage L R RI) [I.modules.Additive]
    (P : CochainComplex (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((I.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  have := algebraicInverseImage_finiteLimits L I
  have : I.modules.Additive := Functor.additive_of_preserves_binary_products I.modules
  have := scalarExtension_additive (𝟙 RI)
  let U := I.modules ⋙ scalarExtension (𝟙 RI)
  have hobj (M) : U.obj M = changeOfRings (𝟙 RI) (I.modules.obj M) := rfl
  have hmap {M N} (a : M ⟶ N) : U.map a = eqToHom (hobj M) ≫
      changeOfRingsHom (𝟙 RI) (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hk := (isKFlat_ringedToposPullback L V adj I (𝟙 RI) U hobj hmap P hP hf).1
  let e : U ≅ I.modules :=
    Functor.isoWhiskerLeft I.modules (scalarExtensionIdIso RI) ≪≫ I.modules.rightUnitor
  exact isKFlat_of_iso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app P)
    hk

end DerivedHelpers

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {R : Sheaf JC CommRingCat.{r}} {RI S : Sheaf JD CommRingCat.{r}}
  (uInv : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (uStar : ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    ringedSiteModules.{r} ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
  (hobj : ∀ M : ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R),
    uStar.obj M = changeOfRings c (I.modules.obj M))

private noncomputable abbrev moduleSets
    {E : Type uC} [Category.{vC} E] [EssentiallySmall.{r} E]
    {J : GrothendieckTopology E} (A : Sheaf J CommRingCat.{r}) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})

set_option maxHeartbeats 600000 in
-- Recover the rank-one module comparison from the transported scalar action.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverseImage_unit_iso :
    ∃ e : I.modules.obj
        (unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≅
        unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RI),
      (moduleSets RI).map e.hom = I.moduleUnderlying.hom.app
        (unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≫
          I.ringUnderlying.hom := by
  let U := unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let Z := (moduleSets R).obj U
  let one : Z ⟶ Z := ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : R.obj.obj W))
                        naturality := by
                          intro W V f
                          ext x
                          exact (map_one (R.obj.map f).hom).symm }⟩
  let e : (moduleSets RI).obj (I.modules.obj U) ≅
      (sheafCompose JD (CategoryTheory.forget CommRingCat.{r})).obj RI :=
    I.moduleUnderlying.app U ≪≫ I.ringUnderlying
  let g (W : Dᵒᵖ) (a : RI.obj.obj W) : (I.modules.obj U).val.obj W :=
    e.inv.hom.app W a
  have hf (W : Dᵒᵖ) (a : RI.obj.obj W) : g W a = a • g W 1 := by
    let t := I.ringUnderlying.inv.hom.app W a
    have ht : I.ringUnderlying.hom.hom.app W t = a :=
      congrArg (fun f ↦ f.hom.app W a) I.ringUnderlying.inv_hom_id
    have ho := I.ringOne Z one (fun _ _ ↦ rfl) W t
    have hi := congrArg (I.ringUnderlying.inv.hom.app W) ho
    have hc (x : (uInv.obj Z).obj.obj W) :
        I.ringUnderlying.inv.hom.app W (I.ringUnderlying.hom.hom.app W x) = x :=
      congrArg (fun f ↦ f.hom.app W x) I.ringUnderlying.hom_inv_id
    simp only [id_eq] at hi
    rw [hc] at hi
    let m (x : (uInv.obj Z).obj.obj W) : (I.modules.obj U).val.obj W :=
      (I.moduleUnderlying.inv.app U).hom.app W x
    have hm : m t = (I.ringUnderlying.hom.hom.app W t : RI.obj.obj W) •
        m ((uInv.map one).hom.app W t) := by
      have h := I.moduleSMul U Z (𝟙 Z) one (𝟙 Z)
        (fun W x ↦ (mul_one (show R.obj.obj W from x)).symm) W t
      erw [uInv.map_id] at h
      exact h
    erw [ht, hi] at hm
    exact hm
  let eW (W : Dᵒᵖ) : RI.obj.obj W ≃ₗ[RI.obj.obj W] (I.modules.obj U).val.obj W :=
    { toEquiv := (((sheafToPresheaf JD (Type r)).mapIso e).app W).toEquiv.symm
      map_add' := by
        intro a b
        change g W (a + b) = g W a + g W b
        rw [hf W (a + b), hf W a, hf W b, add_smul]
      map_smul' := by
        intro a b
        change g W (a * b) = a • g W b
        rw [hf W (a * b), hf W b, mul_smul] }
  let ep : (unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RI)).val ≅
      (I.modules.obj U).val :=
    PresheafOfModules.isoMk (fun W ↦ (eW W).toModuleIso) (by
      intro W V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact congrArg (fun k ↦ k a) (e.inv.hom.naturality f))
  refine ⟨(fullyFaithfulForget _).preimageIso ep.symm, ?_⟩
  rfl

/-- The local pure tensor `s ⊗ x` in ordinary ringed-topos pullback, followed by the
module-sheafification unit. This is real tensor and sheafification data.
Source: Stacks Project, Modules on Sites, Tag 03DF, lemma-global-pullback
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model). -/
noncomputable def ringedPullbackTensorSection
    (M : ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (V : Dᵒᵖ) (s : S.obj.obj V)
    (x : (uInv.obj ((toSheaf _ ⋙
      sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{r})).obj M)).obj.obj V) :
    (uStar.obj M).val.obj V :=
  (eqToHom (hobj M).symm).val.app V
    (((PresheafOfModules.sheafificationAdjunction.{r, vD, r, uD}
      (R := (sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
      (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).unit.app
        (changeOfRingsPresheaf.{vD, uD, r} (J := JD) c (I.modules.obj M))).app V
      (s ⊗ₜ[RI.obj.obj V, (c.hom.app V).hom]
        (@id ((I.modules.obj M).val.obj V)
          ((I.moduleUnderlying.inv.app M).hom.app V x))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_unit_iso :
    ∃ e : uStar.obj
        (unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≅
        unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S),
      ∀ (V : Dᵒᵖ) (s : S.obj.obj V)
        (x : (uInv.obj ((moduleSets R).obj
          (unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))).obj.obj V),
        e.hom.val.app V (ringedPullbackTensorSection uInv I c uStar hobj _ V s x) =
          s * c.hom.app V (I.ringUnderlying.hom.hom.app V x) := by
  let U := unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let A := (sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RI
  let B := (sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S
  obtain ⟨eI, heI⟩ := inverseImage_unit_iso uInv I
  let F := PresheafOfModules.sheafification.{r, vD, r, uD} (𝟙 B.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{r, vD, r, uD} (𝟙 B.obj)
  let eW (V : Dᵒᵖ) : (changeOfRingsPresheaf.{vD, uD, r} c (I.modules.obj U)).obj V ≅
      (unit B).val.obj V := by
    let := (c.hom.app V).hom.toAlgebra
    exact (ModuleCat.extendScalars (c.hom.app V).hom).mapIso
      ((evaluation A V).mapIso eI) ≪≫
        (TensorProduct.AlgebraTensorModule.rid (RI.obj.obj V)
          (S.obj.obj V) (S.obj.obj V)).toModuleIso
  have heW (V : Dᵒᵖ) (s : S.obj.obj V) (x : (I.modules.obj U).val.obj V) :
      (eW V).hom (s ⊗ₜ[RI.obj.obj V, (c.hom.app V).hom] x) =
        s * c.hom.app V (eI.hom.val.app V x) := by
    change c.hom.app V (eI.hom.val.app V x) * s = _
    exact mul_comm _ _
  let ep : changeOfRingsPresheaf.{vD, uD, r} c (I.modules.obj U) ≅ (unit B).val :=
    PresheafOfModules.isoMk eW (by
      intro V W f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul s x =>
        change (eW W).hom ((changeOfRingsPresheaf.{vD, uD, r} c (I.modules.obj U)).map f
          (s ⊗ₜ[RI.obj.obj V, (c.hom.app V).hom] x)) =
            S.obj.map f ((eW V).hom (s ⊗ₜ[RI.obj.obj V, (c.hom.app V).hom] x))
        erw [Classical.choose_spec (exists_changeOfRingsMap.{vD, uD, r}
          (J := JD) c (I.modules.obj U) f) s x, heW, heW, map_mul]
        rw [PresheafOfModules.naturality_apply eI.hom.val]
        congr 1
        exact congrArg (fun k ↦ k (eI.hom.val.app V x)) (c.hom.naturality f))
  let e : changeOfRings.{vD, uD, r} (J := JD) c (I.modules.obj U) ≅ unit B :=
    F.mapIso ep ≪≫ asIso (adj.counit.app (unit B))
  refine ⟨eqToIso (hobj U) ≪≫ e, ?_⟩
  intro V s x
  have heI' := congrArg (fun f ↦ f.hom.app V
    ((I.moduleUnderlying.inv.app U).hom.app V x)) heI
  have hcancel : (I.moduleUnderlying.hom.app U).hom.app V
      ((I.moduleUnderlying.inv.app U).hom.app V x) = x :=
    congrArg (fun f ↦ f.hom.app V x) (I.moduleUnderlying.app U).inv_hom_id
  change eI.hom.val.app V ((I.moduleUnderlying.inv.app U).hom.app V x) =
    I.ringUnderlying.hom.hom.app V ((I.moduleUnderlying.hom.app U).hom.app V
      ((I.moduleUnderlying.inv.app U).hom.app V x)) at heI'
  rw [hcancel] at heI'
  let v := s ⊗ₜ[RI.obj.obj V, (c.hom.app V).hom]
    (@id ((I.modules.obj U).val.obj V) ((I.moduleUnderlying.inv.app U).hom.app V x))
  have hn := adj.unit.naturality ep.hom
  have hh := congrArg (fun f ↦ f.app V v) hn
  have ht := congrArg (fun f ↦ f.app V
    (s * c.hom.app V (I.ringUnderlying.hom.hom.app V x)))
      (adj.right_triangle_components (unit B))
  change (eqToHom (hobj U) ≫ e.hom).val.app V
    ((eqToHom (hobj U).symm).val.app V ((adj.unit.app _).app V v)) = _
  have hc : eqToHom (hobj U).symm ≫ eqToHom (hobj U) = 𝟙 _ := by simp
  change ((eqToHom (hobj U).symm ≫ eqToHom (hobj U)) ≫ e.hom).val.app V
    ((adj.unit.app _).app V v) = _
  rw [hc, Category.id_comp]
  change (adj.counit.app (unit B)).val.app V
    ((F.map ep.hom).val.app V ((adj.unit.app _).app V v)) = _
  erw [← hh]
  have hv : ep.hom.app V v = s * c.hom.app V
      (I.ringUnderlying.hom.hom.app V x) := by
    change (eW V).hom v = _
    erw [heW]
    exact congrArg (fun y ↦ s * c.hom.app V y) heI'
  change (adj.counit.app (unit B)).val.app V
    ((adj.unit.app (unit B).val).app V (ep.hom.app V v)) = _
  erw [hv]
  exact ht

/-- The coordinate formula specifying the canonical finite-free pullback comparison.
It tests arbitrary local sections of the inverse image, not just global sections.
Source: Stacks Project, Modules on Sites, Tag 03DF, lemma-global-pullback
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model). -/
def IsRingedPullbackFiniteFreeComparison (n : ℕ)
    (gamma : uStar.obj (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≅
      ∏ᶜ fun _ : Fin n ↦
        unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) : Prop :=
  ∀ (V : Dᵒᵖ) (s : S.obj.obj V)
    (x : (uInv.obj ((toSheaf _ ⋙
      sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{r})).obj
        (∏ᶜ fun _ : Fin n ↦
          unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))).obj.obj V)
    (k : Fin n),
    ((gamma.hom ≫ Pi.π _ k).val.app V)
      (ringedPullbackTensorSection (uInv := uInv) (I := I) (c := c)
        (uStar := uStar) (hobj := hobj) _ V s x) =
        s * c.hom.app V (I.ringUnderlying.hom.hom.app V
          ((uInv.map ((toSheaf _ ⋙
            sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{r})).map
              (Pi.π (fun _ : Fin n ↦
            unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) k))).hom.app V x))

variable (uPush : Sheaf JD (Type r) ⥤ Sheaf JC (Type r))
  (adj : uInv ⊣ uPush) [hlim : PreservesFiniteLimits uInv]
  (hmap : ∀ {M N : ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)} (a : M ⟶ N),
    uStar.map a = eqToHom (hobj M) ≫
      changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
  [hadd : uStar.Additive]

include adj hmap hlim hadd

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit adj hlim hadd in
private theorem tensorSection_naturality
    {M N : ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (f : M ⟶ N) (V : Dᵒᵖ) (s : S.obj.obj V)
    (x : (uInv.obj ((moduleSets R).obj M)).obj.obj V) :
    (uStar.map f).val.app V (ringedPullbackTensorSection uInv I c uStar hobj M V s x) =
      ringedPullbackTensorSection uInv I c uStar hobj N V s
        ((uInv.map ((moduleSets R).map f)).hom.app V x) := by
  let B := (sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S
  let adjS := PresheafOfModules.sheafificationAdjunction.{r, vD, r, uD} (𝟙 B.obj)
  let f' : changeOfRingsPresheaf.{vD, uD, r} c (I.modules.obj M) ⟶
      changeOfRingsPresheaf.{vD, uD, r} c (I.modules.obj N) :=
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map
        ((I.modules.map f).val.app W)
      naturality := changeOfRingsHom_naturality.{vD, uD, r} c (I.modules.obj M) (I.modules.map f) }
  have hh := congrArg (fun k ↦ k.app V
    (s ⊗ₜ[RI.obj.obj V, (c.hom.app V).hom]
      (@id ((I.modules.obj M).val.obj V) ((I.moduleUnderlying.inv.app M).hom.app V x))))
        (adjS.unit.naturality f')
  have hn := congrArg (fun k ↦ k.hom.app V x) (I.moduleUnderlying.inv.naturality f)
  have he : eqToHom (hobj M).symm ≫ uStar.map f =
      changeOfRingsHom.{vD, uD, r} c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm := by
    rw [hmap]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  change ((eqToHom (hobj M).symm ≫ uStar.map f).val.app V)
    ((adjS.unit.app _).app V _) = _
  rw [he]
  change (eqToHom (hobj N).symm).val.app V
    ((changeOfRingsHom.{vD, uD, r} c (I.modules.obj M) (I.modules.map f)).val.app V
      ((adjS.unit.app _).app V _)) = _
  apply congrArg ((eqToHom (hobj N).symm).val.app V)
  change _ = (adjS.unit.app _).app V _
  erw [← hh]
  change (adjS.unit.app (changeOfRingsPresheaf.{vD, uD, r}
    (J := JD) c (I.modules.obj N))).app V
    ((ModuleCat.extendScalars (c.hom.app V).hom).map ((I.modules.map f).val.app V)
      (s ⊗ₜ[RI.obj.obj V, (c.hom.app V).hom] _)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  exact congrArg (fun y ↦ (adjS.unit.app (changeOfRingsPresheaf.{vD, uD, r}
    (J := JD) c (I.modules.obj N))).app V
    (s ⊗ₜ[RI.obj.obj V, (c.hom.app V).hom] y)) hn.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit adj hmap hlim hadd in
private theorem tensorSection_hom_ext
    (M : ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (H : ringedSiteModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    (f g : uStar.obj M ⟶ H)
    (h : ∀ (V : Dᵒᵖ) (s : S.obj.obj V)
      (x : (uInv.obj ((moduleSets R).obj M)).obj.obj V),
      f.val.app V (ringedPullbackTensorSection uInv I c uStar hobj M V s x) =
        g.val.app V (ringedPullbackTensorSection uInv I c uStar hobj M V s x)) : f = g := by
  apply (cancel_epi (eqToHom (hobj M).symm)).1
  let adjS := PresheafOfModules.sheafificationAdjunction.{r, vD, r, uD} (𝟙
    ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)
  apply (adjS.homEquiv _ H).injective
  simp only [Adjunction.homEquiv_unit]
  ext V : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let x := (I.moduleUnderlying.hom.app M).hom.app V m
  have hx : (I.moduleUnderlying.inv.app M).hom.app V x = m :=
    congrArg (fun k ↦ k.hom.app V m) (I.moduleUnderlying.app M).hom_inv_id
  have ht := h V 1 x
  change f.val.app V ((eqToHom (hobj M).symm).val.app V _) =
    g.val.app V ((eqToHom (hobj M).symm).val.app V _)
  change f.val.app V ((eqToHom (hobj M).symm).val.app V _) =
    g.val.app V ((eqToHom (hobj M).symm).val.app V _) at ht
  dsimp only [ringedPullbackTensorSection, id] at ht
  erw [hx] at ht
  exact ht

-- Preserve the existing public parameters for the ringed-topos presentation.
set_option linter.unusedSectionVars false in
/-- The canonical finite-free comparison exists uniquely, including rank zero.
Source: Stacks Project, Tag 08H3 and Modules on Sites, Tag 03DF
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model).

Proof: finite-limit preservation identifies inverse image of the finite tuple sheaf
with tuples over the inverse-image ring, respecting the coordinate projections.
Send `s ⊗ (a_j)` to `(s c(a_j))`. The inverse sends `(s_j)` to the finite sum of
`s_j ⊗ e_j`. The balanced tensor relations prove both inverse equations. These maps
respect restrictions and pass through sheafification. Pure tensors locally generate
the sheafified module, so the coordinate formula determines the map uniquely.
The empty tuple gives the unique isomorphism of zero objects. -/
theorem existsUnique_ringedPullbackFiniteFreeIso (n : ℕ) :
    ∃! gamma : uStar.obj (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≅
      ∏ᶜ fun _ : Fin n ↦
        unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S),
      IsRingedPullbackFiniteFreeComparison (uInv := uInv) (I := I) (c := c)
        (uStar := uStar) (hobj := hobj) n gamma := by
  obtain ⟨e, he⟩ := pullback_unit_iso uInv I c uStar hobj
  let U := unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let V := unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
  let gamma : uStar.obj (∏ᶜ fun _ : Fin n ↦ U) ≅ ∏ᶜ fun _ : Fin n ↦ V :=
    PreservesProduct.iso uStar (fun _ : Fin n ↦ U) ≪≫
      Pi.mapIso (fun _ : Fin n ↦ e)
  have hgamma (k : Fin n) : gamma.hom ≫ Pi.π _ k =
      uStar.map (Pi.π (fun _ : Fin n ↦ U) k) ≫ e.hom := by
    simp [gamma]
  have hcoord : IsRingedPullbackFiniteFreeComparison uInv I c uStar hobj n gamma := by
    intro W s x k
    rw [hgamma]
    change e.hom.val.app W ((uStar.map (Pi.π _ k)).val.app W
      (ringedPullbackTensorSection uInv I c uStar hobj _ W s x)) = _
    rw [tensorSection_naturality uInv I c uStar hobj hmap]
    exact he W s _
  refine ⟨gamma, hcoord, ?_⟩
  intro delta hdelta
  apply Iso.ext
  apply Pi.hom_ext
  intro k
  apply tensorSection_hom_ext uInv I c uStar hobj _ _
  intro W s x
  exact (hdelta W s x k).trans (hcoord W s x k).symm

/-- The unique finite-free comparison fixed by the local pure-tensor coordinate formula.
The named theorem determines this object up to equality, so the choice carries no
unspecified mathematical data. Source: Stacks Project, Tag 08H3 and Tag 03DF
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model). -/
noncomputable def ringedPullbackFiniteFreeIso (n : ℕ) :
    uStar.obj (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≅
      ∏ᶜ fun _ : Fin n ↦
        unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S) :=
  Classical.choose (existsUnique_ringedPullbackFiniteFreeIso
    (uInv := uInv) (I := I) (c := c) (uStar := uStar) (hobj := hobj)
    (uPush := uPush) (adj := adj) (hmap := hmap) n)

/-- The transported degreewise splittings still split after canonical finite-free
identification. Source: Stacks Project, Tag 08H3
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model).

Proof: cancel gamma followed by its inverse, combine the two images by functoriality,
then use the given splitting and preservation of identity morphisms. No splitting
is required to commute with the differentials. -/
theorem ringedPullback_strictPerfect_splitting
    (F : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (package : StrictPerfectCoefficientPackageOnSite _ F) (n : ℤ) :
    (uStar.map (package.i n) ≫
      (ringedPullbackFiniteFreeIso uInv I c uStar hobj uPush adj hmap (package.N n)).hom) ≫
      ((ringedPullbackFiniteFreeIso uInv I c uStar hobj uPush adj hmap (package.N n)).inv ≫
        uStar.map (package.p n)) = 𝟙 (uStar.obj (F.X n)) := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
    package.splitting]
  exact uStar.map_id _

/-- The specified termwise strict-perfect package after ordinary pullback, with the
same finite ranks and the canonically transported inclusion and retraction maps.
Source: Stacks Project, Tag 08H3
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model). -/
noncomputable def ringedPullbackStrictPerfectPackage
    (F : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (package : StrictPerfectCoefficientPackageOnSite _ F) :
    StrictPerfectCoefficientPackageOnSite
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) where
  N := package.N
  i n := uStar.map (package.i n) ≫
    (ringedPullbackFiniteFreeIso uInv I c uStar hobj uPush adj hmap (package.N n)).hom
  p n := (ringedPullbackFiniteFreeIso uInv I c uStar hobj uPush adj hmap (package.N n)).inv ≫
    uStar.map (package.p n)
  splitting n := ringedPullback_strictPerfect_splitting
    uInv I c uStar hobj uPush adj hmap F package n

variable [HasDerivedCategory.{w} (ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
  [HasDerivedCategory.{w} (ringedSiteModules.{r}
    ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))]
  (LF : DerivedCategory (ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
    DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
  (epsilon : DerivedCategory.Qh ⋙ LF ⟶
    uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

/-- The given homotopy-category comparison, transported along the canonical quotient
factorizations to cochain complexes. No comparison map is chosen anew.
Source: Stacks Project, Tag 06YY, lemma-derived-base-change
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model). -/
noncomputable def ringedPullbackComplexComparison :
    DerivedCategory.Q ⋙ LF ⟶
      uStar.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv LF ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) epsilon ≫
    Functor.whiskerRight (uStar.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (uStar.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
private theorem pullback_comparison_iso
    [LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ))]
    (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    IsIso ((ringedPullbackComplexComparison uStar LF epsilon).app P) := by
  classical
  let A := SheafOfModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let B := SheafOfModules.{r}
    ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
  let T := uStar.mapHomologicalComplex (.up ℤ)
  let H := HomotopyCategory.quotient A (.up ℤ)
  let F := uStar.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hpres : ∀ {P Q : CochainComplex A ℤ} (a : P ⟶ Q),
      P.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
      Q.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (Q.X n)) →
      QuasiIso a → QuasiIso (T.map a) := by
    have := algebraicInverseImage_finiteLimits uInv I
    have : I.modules.Additive := Functor.additive_of_preserves_binary_products I.modules
    have := algebraicInverseImage_epi uInv uPush adj I
    have : I.modules.PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels I.modules
    let A' := SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RI)
    let := HasDerivedCategory.standard A'
    let := HasDerivedCategory.standard B
    obtain ⟨E, heobj, hemap, headd, hepres, _⟩ :=
      derivedChangeOfRingsIndependentCoefficients c
    have := headd
    intro P Q a hp hf hq hqf ha
    have := ha
    have hkP := isKFlat_inverseImage uInv uPush adj I P hp hf
    have hkQ := isKFlat_inverseImage uInv uPush adj I Q hq hqf
    have ht := hepres ((I.modules.mapHomologicalComplex (.up ℤ)).map a) hkP hkQ
      (by infer_instance)
    let e : uStar ≅ I.modules ⋙ E := NatIso.ofComponents
      (fun M ↦ eqToIso ((hobj M).trans (heobj (I.modules.obj M)).symm)) (by
        intro M N a
        simp only [Functor.comp_map]
        rw [hmap, hemap]
        simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc])
    let e' : T ≅ I.modules.mapHomologicalComplex (.up ℤ) ⋙
        E.mapHomologicalComplex (.up ℤ) :=
      NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (I.modules ⋙ E)) (.up ℤ)).symm
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e'.app P) (e'.app Q) (e'.hom.naturality a).symm)).2 ht
  let K : Set (HomotopyCategory A (.up ℤ)) :=
    {X | ∃ P : CochainComplex A ℤ, H.obj P = X ∧
      P.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)}
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (a : X' ⟶ X),
        X' ∈ K ∧ HomotopyCategory.quasiIso A (.up ℤ) a := by
    intro X
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, a, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
    have hflat : ∀ n, IsFlatOnSite (J := JC) (R := R) (P.X n) := fun n ↦
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm (hf n)
    exact ⟨H.obj P, H.map a, ⟨P, rfl, hp, hflat⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff a).2 hq⟩
  have hinv : ∀ (X X' : HomotopyCategory A (.up ℤ)) (a : X ⟶ X'),
      X ∈ K → X' ∈ K → HomotopyCategory.quasiIso A (.up ℤ) a →
        IsIso (F.map a) := by
    intro X X' a hX hX' ha
    obtain ⟨P, rfl, hp, hf⟩ := hX
    obtain ⟨P', rfl, hp', hf'⟩ := hX'
    obtain ⟨a, rfl⟩ := H.map_surjective a
    have ht := hpres a hp hf hp' hf'
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 ha)
    change IsIso (DerivedCategory.Qh.map
      ((uStar.mapHomotopyCategory (.up ℤ)).map (H.map a)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff (T.map a)).2 ht)
  obtain ⟨_, LF', ε', hLF', _, hε'⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F K hres hinv
  have := hLF'
  let e := Functor.leftDerivedNatIso LF' LF ε' epsilon
    (HomotopyCategory.quasiIso A (.up ℤ)) (Iso.refl F)
  have he (P : CochainComplex A ℤ) (hp : P.IsKFlatIndependentCoefficients)
      (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
      IsIso ((ringedPullbackComplexComparison uStar LF epsilon).app P) := by
    have : IsIso (ε'.app (H.obj P)) := hε' (H.obj P) ⟨P, rfl, hp, hf⟩
    have hfac : e.hom.app (DerivedCategory.Qh.obj (H.obj P)) ≫
        epsilon.app (H.obj P) = ε'.app (H.obj P) := by
      simp [e, Functor.leftDerivedNatIso, Functor.leftDerivedNatTrans_app]
    have heps : IsIso (epsilon.app (H.obj P)) := by
      have : IsIso (e.hom.app (DerivedCategory.Qh.obj (H.obj P)) ≫
          epsilon.app (H.obj P)) := by rw [hfac]; infer_instance
      exact IsIso.of_isIso_comp_left (e.hom.app (DerivedCategory.Qh.obj (H.obj P)))
        (epsilon.app (H.obj P))
    dsimp only [ringedPullbackComplexComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  exact he P hP hflat

/-- Every bounded specified strict-perfect complex computes derived ringed-topos
pullback, with its specified termwise package and canonical natural comparison.
Source: Stacks Project, Tag 08H3; Tag 06YQ; Tag 06YY
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model).

Proof:
1. For each degree use the specified finite-free retraction. The coordinate tensor
   isomorphism identifies tensor with the finite free sheaf with a finite direct sum.
   Finite sums are exact and exactness passes to retracts, so every term is flat.
   This includes rank zero; projectivity as a categorical sheaf object is not used.
2. Boundedness above and lem-weil-pbc-independent-bounded-flat-kflat give K-flatness.
3. Ordinary pullback preserves zero objects. The finite-free comparison is fixed by
   its pure-tensor coordinate formula; functoriality transports each splitting to
   the maps in ringedPullbackStrictPerfectPackage, with exactly the original ranks.
4. The same retract argument over S gives flat terms in the pulled complex, and
   its unchanged upper bound and the bounded-flat theorem give its K-flatness.
5. The canonical comparison of lem-weil-pbc-ringed-topoi-derived-pullback is invertible
   on these K-flat flat-term complexes. Uniqueness of a left derived functor identifies
   it with the supplied LF and epsilon, respecting epsilon. The quotient isomorphisms
   give exactly ringedPullbackComplexComparison. Composing with LF(e inverse) gives
   the model of LF(P). Naturality of epsilon gives the displayed chain-map equation.
   Neither coefficient-map flatness nor exactness of ordinary pullback is needed. -/
theorem strictPerfectRingedPullbackModel
    [LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (ComplexShape.up ℤ))]
    (F : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (package : StrictPerfectCoefficientPackageOnSite _ F)
    (a b : ℤ) (hbounded : ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) :
    (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (F.X n)) ∧
    F.IsKFlatIndependentCoefficients ∧
    (∀ n : ℤ, n < a ∨ b < n →
      IsZero (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X n)) ∧
    (∀ n : ℤ, IsFlatOnSite (J := JD) (R := S)
      (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X n)) ∧
    CochainComplex.IsKFlatIndependentCoefficients
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ∧
    IsIso ((ringedPullbackComplexComparison uStar LF epsilon).app F) ∧
    (∀ (P : DerivedCategory (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
      (e : DerivedCategory.Q.obj F ≅ P),
      IsIso (LF.map e.inv ≫ (ringedPullbackComplexComparison uStar LF epsilon).app F)) ∧
    (∀ (G : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (_ : StrictPerfectCoefficientPackageOnSite _ G) (a' b' : ℤ)
      (_ : ∀ n : ℤ, n < a' ∨ b' < n → IsZero (G.X n)) (v : F ⟶ G),
      (ringedPullbackComplexComparison uStar LF epsilon).app F ≫
          DerivedCategory.Q.map ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map v) =
        LF.map (DerivedCategory.Q.map v) ≫
          (ringedPullbackComplexComparison uStar LF epsilon).app G) := by
  have hflat : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (F.X n) := fun n ↦
    flat_finiteFree_retract R (F.X n) (package.N n) (package.i n) (package.p n)
      (package.splitting n)
  have : F.IsStrictlyLE b :=
    (F.isStrictlyLE_iff b).2 (fun n hn ↦ hbounded n (Or.inr hn))
  have hk := isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R F b hflat
  have hpull := isKFlat_ringedToposPullback uInv uPush adj I c uStar hobj hmap F hk hflat
  have hcomp := pullback_comparison_iso uInv I c uStar hobj uPush adj hmap LF epsilon
    F hk hflat
  refine ⟨hflat, hk, ?_, hpull.2, hpull.1, hcomp, ?_, ?_⟩
  · intro n hn
    exact uStar.map_isZero (hbounded n hn)
  · intro P e
    infer_instance
  · intro G _ a' b' _ v
    exact ((ringedPullbackComplexComparison uStar LF epsilon).naturality v).symm

end SheafOfModules
