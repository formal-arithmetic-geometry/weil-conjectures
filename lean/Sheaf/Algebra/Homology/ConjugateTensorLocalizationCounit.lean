module

public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Sheaf.Algebra.Homology.SiteDerivedTensorResolvingData
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.CochainTensorModelRigidity

/-! # Conjugate tensor comparison and localization counits

Source: Stacks Project, sites-cohomology.tex, Tags 06YS and 06YU, and the exact-equivalence
conjugation calculation (blueprint: lem-pd-conjugate-tensor-localization-counit).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 11000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

attribute [local irreducible] SheafOfModules.siteDerivedTensorIndependentCoefficients
  CategoryTheory.Functor.mapDerivedCategory
  SheafOfModules.SiteDerivedTensorResolvingData.counit

attribute [local instance 12000]
  SheafOfModules.SiteDerivedTensorResolvingData.sheafCompose
  SheafOfModules.SiteDerivedTensorResolvingData.moduleAbelian
  SheafOfModules.SiteDerivedTensorResolvingData.moduleMonoidal
  SheafOfModules.SiteDerivedTensorResolvingData.moduleAdditive
  SheafOfModules.SiteDerivedTensorResolvingData.moduleSymmetric
  SheafOfModules.SiteDerivedTensorResolvingData.moduleColimits
  SheafOfModules.SiteDerivedTensorResolvingData.complexMonoidal
  SheafOfModules.SiteDerivedTensorResolvingData.complexMonoidalStruct

universe u v u' v' uC vC r w w'

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.ConjugateTensor

/-- Conjugation of the fixed bifunctor by the fixed equivalence.
Source: Stacks 06YU, exact-equivalence comparison
(blueprint: lem-pd-conjugate-tensor-localization-counit). -/
def conjugate {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (e : A ≌ B) (T : A × A ⥤ A) : B × B ⥤ B :=
  e.inverse.prod e.inverse ⋙ T ⋙ e.functor

/-- The comparison theta-zero is induced by the equivalence unit on both inputs.
Source: Stacks 06YU, exact-equivalence comparison
(blueprint: lem-pd-conjugate-tensor-localization-counit). -/
def comparison {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (e : A ≌ B) (T : A × A ⥤ A) :
    T ⋙ e.functor ≅ e.functor.prod e.functor ⋙ conjugate e T :=
  Functor.isoWhiskerRight (NatIso.prod e.unitIso e.unitIso) (T ⋙ e.functor)

/-- Extend a transformation on equivalence images by the fixed equivalence counit.
Source: Stacks 06YU, counit-conjugation formula
(blueprint: lem-pd-conjugate-tensor-localization-counit). -/
def extend {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    {D : Type w} [Category.{w'} D] (e : A ≌ B) (U V : B × B ⥤ D)
    (a : e.functor.prod e.functor ⋙ U ⟶ e.functor.prod e.functor ⋙ V) : U ⟶ V :=
  (Functor.isoWhiskerRight (NatIso.prod e.counitIso e.counitIso) U).inv ≫
    Functor.whiskerLeft (e.inverse.prod e.inverse) a ≫
      (Functor.isoWhiskerRight (NatIso.prod e.counitIso e.counitIso) V).hom

private theorem extend_image {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] {D : Type w} [Category.{w'} D]
    (e : A ≌ B) (U V : B × B ⥤ D)
    (a : e.functor.prod e.functor ⋙ U ⟶ e.functor.prod e.functor ⋙ V) :
    Functor.whiskerLeft (e.functor.prod e.functor) (extend e U V a) = a := by
  ext X
  dsimp [extend]
  have h := a.naturality (X := X)
    (Y := (e.inverse.obj (e.functor.obj X.1), e.inverse.obj (e.functor.obj X.2)))
    (e.unitIso.hom.app X.1, e.unitIso.hom.app X.2)
  dsimp at h
  simp only [← e.counitInv_app_functor] at h
  change U.map (X := (e.functor.obj X.1, e.functor.obj X.2))
      (Y := (e.functor.obj (e.inverse.obj (e.functor.obj X.1)),
        e.functor.obj (e.inverse.obj (e.functor.obj X.2))))
      (e.counitIso.inv.app _, e.counitIso.inv.app _) ≫ _ ≫
    V.map (X := (e.functor.obj (e.inverse.obj (e.functor.obj X.1)),
        e.functor.obj (e.inverse.obj (e.functor.obj X.2))))
      (Y := (e.functor.obj X.1, e.functor.obj X.2))
      (e.counitIso.hom.app _, e.counitIso.hom.app _) = _
  rw [← Category.assoc, h]
  rw [Category.assoc, ← V.map_comp]
  change a.app X ≫ V.map ((e.prod e).counitIso.inv.app _ ≫
    (e.prod e).counitIso.hom.app _) = _
  simp

private theorem extend_whisker {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] {D : Type w} [Category.{w'} D]
    (e : A ≌ B) (U V : B × B ⥤ D) (a : U ⟶ V) :
    extend e U V (Functor.whiskerLeft (e.functor.prod e.functor) a) = a := by
  ext X
  dsimp only [extend, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  change U.map ((e.prod e).counitIso.inv.app X) ≫
    (a.app ((e.prod e).functor.obj ((e.prod e).inverse.obj X)) ≫
      V.map ((e.prod e).counitIso.hom.app X)) = _
  rw [← a.naturality, ← Category.assoc, ← U.map_comp]
  simp

private theorem normalization_square
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (U V : C ⥤ D) (a : U ⟶ V) {X Y : C} (k : X ≅ Y)
    {Z W : D} (t : Z ≅ U.obj X) (r : W ≅ V.obj Y) (d : Z ⟶ W) :
    t.hom ≫ a.app X = d ≫ r.hom ≫ V.map k.inv ↔
      a.app Y ≫ r.inv = U.map k.inv ≫ t.inv ≫ d := by
  constructor
  · intro h
    apply (cancel_epi (U.map k.hom)).mp
    apply (cancel_epi t.hom).mp
    calc
      t.hom ≫ U.map k.hom ≫ (a.app Y ≫ r.inv) =
          (t.hom ≫ a.app X) ≫ V.map k.hom ≫ r.inv := by
        rw [← Category.assoc _ (a.app Y), a.naturality]
        simp only [Category.assoc]
      _ = d ≫ r.hom ≫ V.map k.inv ≫ V.map k.hom ≫ r.inv := by
        rw [h]
        simp only [Category.assoc]
      _ = d := by simp
      _ = t.hom ≫ U.map k.hom ≫ (U.map k.inv ≫ t.inv ≫ d) := by
        simp [← U.map_comp, ← Category.assoc]
  · intro h
    apply (cancel_mono (V.map k.hom)).mp
    apply (cancel_mono r.inv).mp
    simp only [Category.assoc]
    calc
      t.hom ≫ a.app X ≫ V.map k.hom ≫ r.inv =
          t.hom ≫ U.map k.hom ≫ (a.app Y ≫ r.inv) := by
        rw [← Category.assoc (a.app X), ← a.naturality]
        simp only [Category.assoc]
      _ = t.hom ≫ U.map k.hom ≫ (U.map k.inv ≫ t.inv ≫ d) := by rw [h]
      _ = d := by simp [← U.map_comp, ← Category.assoc]
      _ = d ≫ r.hom ≫ V.map k.inv ≫ V.map k.hom ≫ r.inv := by simp

end CategoryTheory.ConjugateTensor

namespace CategoryTheory.ConjugateTensor

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [SymmetricCategory A]
  [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory.{w'} A]

/-- The native internal derived-to-ordinary tensor transformation on every complex pair.
Source: blueprint lem-sfb-derived-monoidal, resolution maps making localization lax monoidal
(blueprint: lem-pd-conjugate-tensor-localization-counit). -/
def internalCounit :
    ((DerivedCategory.Q (C := A)).prod DerivedCategory.Q) ⋙ tensor (DerivedCategory A) ⟶
      tensor (CochainComplex A ℤ) ⋙ DerivedCategory.Q :=
  { app := fun X ↦ Functor.LaxMonoidal.μ DerivedCategory.Q X.1 X.2
    naturality := fun _ _ f ↦ Functor.LaxMonoidal.μ_natural DerivedCategory.Q f.1 f.2 }

private abbrev nativeDerivedMonoidal : MonoidalCategory (DerivedCategory A) := inferInstance

private theorem internalCounit_isIso (P Q : CochainComplex A ℤ)
    (hp : P.IsKFlatForTotalTensor) : IsIso ((internalCounit A).app (P, Q)) := by
  let := nativeDerivedMonoidal A
  have hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P := hp
  have hK := (HomotopyCategory.kFlat_quotient_obj_iff P).2 hP
  have : (curriedTensor (DerivedCategory A)).IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans (DerivedCategory.Qh (C := A)))
      (HomotopyCategory.quasiIso A (.up ℤ))
      (HomotopyCategory.quasiIso A (.up ℤ)) := inferInstance
  have hμ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)
      ((HomotopyCategory.quotient A (.up ℤ)).obj Q)) := by
    exact (MorphismProperty.kFlat_prod_id_derives_curriedTensor
      (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh).isIso_of_isLeftDerivabilityStructure
        (LF := curriedTensor (DerivedCategory A))
        (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh) ⟨_, hK⟩ _
  change IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)
  change IsIso ((tensorHom ((DerivedCategory.quotientCompQhIso A).inv.app P)
      ((DerivedCategory.quotientCompQhIso A).inv.app Q)) ≫
    Functor.LaxMonoidal.μ ((HomotopyCategory.quotient A (.up ℤ)) ⋙ DerivedCategory.Qh) P Q ≫
      (DerivedCategory.quotientCompQhIso A).hom.app (P ⊗ Q))
  have : IsIso (Functor.LaxMonoidal.μ
      ((HomotopyCategory.quotient A (.up ℤ)) ⋙ DerivedCategory.Qh) P Q) := by
    rw [Functor.LaxMonoidal.comp_μ]
    infer_instance
  infer_instance

end CategoryTheory.ConjugateTensor

namespace SheafOfModules.ConjugateTensorLocalization

open SiteDerivedTensorResolvingData CategoryTheory.ConjugateTensor

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{w} (Modules R)]
  {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [SymmetricCategory A]
  [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory.{w'} A]
  (e : A ≌ Modules R) [e.functor.Additive] [e.inverse.Additive] [e.functor.Braided]

/-- The internal tensor conjugated by the actual localized equivalence.
Source: Stacks 06YU, conjugation calculation
(blueprint: lem-pd-conjugate-tensor-localization-counit). -/
abbrev conjugateTensor := conjugate e.mapDerivedCategory (tensor (DerivedCategory A))

/-- The specified total comparison induced by the ordinary strong monoidal functor.
Source: Stacks 06YU, signed direct-sum total comparison
(blueprint: lem-pd-conjugate-tensor-localization-counit). -/
def totalComparison :
    tensor (CochainComplex A ℤ) ⋙ e.functor.mapHomologicalComplex (.up ℤ) ≅
      (e.functor.mapHomologicalComplex (.up ℤ)).prod
        (e.functor.mapHomologicalComplex (.up ℤ)) ⋙ tensor (Complexes R) :=
  (Functor.Monoidal.μNatIso (e.functor.mapHomologicalComplex (.up ℤ))).symm

/-- The defining all-image equation for the conjugate localization transformation.
Read the composite from left to right: undo kappa, undo theta-zero, apply the native
counit, apply kappa on the total tensor, then localize the termwise total comparison.
Source: Stacks 06YU, exact-equivalence conjugation calculation
(blueprint: lem-pd-conjugate-tensor-localization-counit). -/
def imageCounit :
    (e.functor.mapHomologicalComplex (.up ℤ)).prod
        (e.functor.mapHomologicalComplex (.up ℤ)) ⋙
      ((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) ⋙ conjugateTensor R e ⟶
    (e.functor.mapHomologicalComplex (.up ℤ)).prod
        (e.functor.mapHomologicalComplex (.up ℤ)) ⋙
      tensor (Complexes R) ⋙ DerivedCategory.Q :=
  (Functor.isoWhiskerRight
    (NatIso.prod e.functor.mapDerivedCategoryFactors e.functor.mapDerivedCategoryFactors)
    (conjugateTensor R e)).inv ≫
  (Functor.isoWhiskerLeft ((DerivedCategory.Q (C := A)).prod DerivedCategory.Q)
    (comparison e.mapDerivedCategory (tensor (DerivedCategory A)))).inv ≫
  Functor.whiskerRight (internalCounit A) e.functor.mapDerivedCategory ≫
  Functor.whiskerLeft (tensor (CochainComplex A ℤ))
    e.functor.mapDerivedCategoryFactors.hom ≫
  (Functor.isoWhiskerRight (totalComparison R e) DerivedCategory.Q).hom

/-- Extension from E-images to arbitrary complexes by the termwise equivalence counit.
The construction uses the fixed quasi-inverse and counit, without choosing resolutions.
Source: Stacks 06YU, counit-conjugation calculation
(blueprint: lem-pd-conjugate-tensor-localization-counit). -/
def conjugateCounit :
    ((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) ⋙ conjugateTensor R e ⟶
      tensor (Complexes R) ⋙ DerivedCategory.Q :=
  extend (e.mapHomologicalComplex (.up ℤ))
    (((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) ⋙ conjugateTensor R e)
    (tensor (Complexes R) ⋙ DerivedCategory.Q) (imageCounit R e)

end SheafOfModules.ConjugateTensorLocalization

namespace SheafOfModules.ConjugateTensorLocalization

open SiteDerivedTensorResolvingData CategoryTheory.ConjugateTensor

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{w} (Modules R)]
  {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [SymmetricCategory A]
  [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory.{w'} A]
  (e : A ≌ Modules R) [e.functor.Additive] [e.inverse.Additive] [e.functor.Braided]

private theorem counit_model (P Q : Complexes R)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hpf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hqf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)) :
    (counit R).app (P, Q) = (model R P Q hp hq hpf hqf).inv := by
  unfold counit
  exact (Classical.choose_spec (counit_existsUnique R).exists) P Q hp hq hpf hqf

private theorem imageCounit_isIso (P Q : CochainComplex A ℤ)
    (hp : P.IsKFlatForTotalTensor) : IsIso ((imageCounit R e).app (P, Q)) := by
  let := CategoryTheory.ConjugateTensor.nativeDerivedMonoidal A
  have := internalCounit_isIso A P Q hp
  unfold imageCounit
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

private theorem conjugateCounit_isIso
    (hkflatInv : ∀ P : Complexes R, P.IsKFlatIndependentCoefficients →
      CochainComplex.IsKFlatForTotalTensor
        ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P))
    (P Q : Complexes R) (hp : P.IsKFlatIndependentCoefficients) :
    IsIso ((conjugateCounit R e).app (P, Q)) := by
  let := CategoryTheory.ConjugateTensor.nativeDerivedMonoidal A
  have := imageCounit_isIso R e
    ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P)
    ((e.inverse.mapHomologicalComplex (.up ℤ)).obj Q) (hkflatInv P hp)
  unfold conjugateCounit extend
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  have h : IsIso ((imageCounit R e).app
      (((e.mapHomologicalComplex (.up ℤ)).inverse.prod
        (e.mapHomologicalComplex (.up ℤ)).inverse).obj (P, Q))) := by
    change IsIso ((imageCounit R e).app
      (((e.inverse.mapHomologicalComplex (.up ℤ)).obj P),
        ((e.inverse.mapHomologicalComplex (.up ℤ)).obj Q)))
    exact imageCounit_isIso R e _ _ (hkflatInv P hp)
  infer_instance

private theorem conjugateCounit_image :
    Functor.whiskerLeft ((e.functor.mapHomologicalComplex (.up ℤ)).prod
        (e.functor.mapHomologicalComplex (.up ℤ))) (conjugateCounit R e) =
      imageCounit R e :=
  extend_image (e.mapHomologicalComplex (.up ℤ)) _ _ _

private theorem counit_comparison_exists
    (hkflatInv : ∀ P : Complexes R, P.IsKFlatIndependentCoefficients →
      CochainComplex.IsKFlatForTotalTensor
        ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ v : conjugateTensor R e ≅ siteDerivedTensorIndependentCoefficients J R,
      ∀ U V : Complexes R,
        v.hom.app (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V) ≫
          (counit R).app (U, V) = (conjugateCounit R e).app (U, V) := by
  let := CategoryTheory.ConjugateTensor.nativeDerivedMonoidal A
  classical
  let P := cochainTensorFlatRepresentatives.{uC, vC, r} J R
  let L := cochainTensorRepresentativeLocalization.{uC, vC, r, w} J R
  let i := P.ι.prod P.ι
  let a := Functor.whiskerLeft i (conjugateCounit R e)
  let b := Functor.whiskerLeft i (counit R)
  have ha (X : P.FullSubcategory × P.FullSubcategory) : IsIso (a.app X) :=
    conjugateCounit_isIso R e hkflatInv X.1.obj X.2.obj X.1.property.1
  have hb (X : P.FullSubcategory × P.FullSubcategory) : IsIso (b.app X) := by
    change IsIso ((counit R).app (X.1.obj, X.2.obj))
    rw [counit_model R _ _ X.1.property.1 X.2.property.1
      X.1.property.2 X.2.property.2]
    infer_instance
  have : IsIso a := NatIso.isIso_of_isIso_app a
  have : IsIso b := NatIso.isIso_of_isIso_app b
  let F := (Functor.whiskeringLeft _ _ (DerivedCategory (Modules R))).obj (L.prod L)
  have hF : F.FullyFaithful :=
    ((Functor.FullyFaithful.nonempty_iff_map_bijective F).2
      ((cochain_tensor_model_rigidity J R).choose_spec.2.2
        (DerivedCategory (Modules R)) inferInstance)).some
  let v : conjugateTensor R e ≅ siteDerivedTensorIndependentCoefficients J R :=
    hF.preimageIso (asIso a ≪≫ (asIso b).symm)
  have hv (X : P.FullSubcategory × P.FullSubcategory) :
      v.hom.app (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj X.2.obj) ≫
        (counit R).app (X.1.obj, X.2.obj) =
          (conjugateCounit R e).app (X.1.obj, X.2.obj) := by
    have hvmap : F.map v.hom = (asIso a ≪≫ (asIso b).symm).hom :=
      hF.map_preimage _
    have h := congrArg (fun t ↦ t.app X) hvmap
    simp only [F, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
      Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, NatTrans.comp_app,
      NatIso.isIso_inv_app] at h
    change v.hom.app (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj X.2.obj) =
      a.app X ≫ inv (b.app X) at h
    exact (congrArg (· ≫ b.app X) h).trans (by simp; rfl)
  let ε : ((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) ⋙
      siteDerivedTensorIndependentCoefficients J R ⟶
      tensor (Complexes R) ⋙ DerivedCategory.Q := by
    exact Functor.whiskerLeft (C := Complexes R × Complexes R)
      ((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) v.inv ≫
        conjugateCounit R e
  -- The existing counit uniqueness theorem already contains the all-complex resolution
  -- argument, so it suffices to compare the two transformations on resolving pairs.
  have he : ε = counit R := by
    refine (counit_existsUnique R).unique ?_ (counit_model R)
    intro U V hU hV hfU hfV
    change v.inv.app (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V) ≫
      (conjugateCounit R e).app (U, V) = _
    rw [← hv (⟨U, hU, hfU⟩, ⟨V, hV, hfV⟩)]
    simp only [Iso.inv_hom_id_app_assoc]
    exact counit_model R U V hU hV hfU hfV
  refine ⟨v, fun U V ↦ ?_⟩
  have h := congrArg (fun t ↦ t.app (U, V)) he
  change v.inv.app (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V) ≫
      (conjugateCounit R e).app (U, V) = _ at h
  rw [← h, Iso.hom_inv_id_app_assoc]

/-- The precise representative formula, with the inverse model maps r in the node.
`internalCounit` is the inverse of r-A on these pairs, and `model` is r-R.
Source: Stacks 06YU, exact-equivalence comparison formula
(blueprint: lem-pd-conjugate-tensor-localization-counit). -/
def Normalized
    (θ : tensor (DerivedCategory A) ⋙ e.functor.mapDerivedCategory ≅
      e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory ⋙
        siteDerivedTensorIndependentCoefficients J R)
    (hflat : ∀ X : A, ObjectProperty.flat X →
      IsFlatOnSite (J := J) (R := R) (e.functor.obj X))
    (hkflat : ∀ P : CochainComplex A ℤ, P.IsKFlatForTotalTensor →
      CochainComplex.IsKFlatIndependentCoefficients
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)) : Prop :=
  ∀ (P Q : CochainComplex A ℤ)
    (hp : P.IsKFlatForTotalTensor) (hq : Q.IsKFlatForTotalTensor)
    (hpf : ∀ n : ℤ, ObjectProperty.flat (P.X n))
    (hqf : ∀ n : ℤ, ObjectProperty.flat (Q.X n)),
    θ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      e.functor.mapDerivedCategory.map ((internalCounit A).app (P, Q)) ≫
        e.functor.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
        DerivedCategory.Q.map ((totalComparison R e).hom.app (P, Q)) ≫
        (model R ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)
          ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)
          (hkflat P hp) (hkflat Q hq)
          (fun n ↦ hflat (P.X n) (hpf n)) (fun n ↦ hflat (Q.X n) (hqf n))).hom ≫
        (siteDerivedTensorIndependentCoefficients J R).map
          (X := (DerivedCategory.Q.obj ((e.functor.mapHomologicalComplex (.up ℤ)).obj P),
            DerivedCategory.Q.obj ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)))
          (Y := (e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
            e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)))
          (e.functor.mapDerivedCategoryFactors.inv.app P,
            e.functor.mapDerivedCategoryFactors.inv.app Q)

/-- The isomorphism v specified by v at (D(E)M,D(E)N) after theta-zero equals theta.
It is computed by the fixed derived equivalence counit on arbitrary derived objects.
Source: Stacks 06YU, exact-equivalence conjugation formula
(blueprint: lem-pd-conjugate-tensor-localization-counit). -/
def comparisonOnSection
    (θ : tensor (DerivedCategory A) ⋙ e.functor.mapDerivedCategory ≅
      e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory ⋙
        siteDerivedTensorIndependentCoefficients J R) :
    conjugateTensor R e ≅ siteDerivedTensorIndependentCoefficients J R :=
  (Functor.isoWhiskerRight
    (NatIso.prod e.mapDerivedCategory.counitIso e.mapDerivedCategory.counitIso)
    (conjugateTensor R e)).symm ≪≫
  Functor.isoWhiskerLeft
    (e.mapDerivedCategory.inverse.prod e.mapDerivedCategory.inverse)
    ((comparison e.mapDerivedCategory (tensor (DerivedCategory A))).symm ≪≫ θ) ≪≫
  Functor.isoWhiskerRight
    (NatIso.prod e.mapDerivedCategory.counitIso e.mapDerivedCategory.counitIso)
    (siteDerivedTensorIndependentCoefficients J R)

omit [e.functor.Braided] in
private theorem comparisonOnSection_image
    (θ : tensor (DerivedCategory A) ⋙ e.functor.mapDerivedCategory ≅
      e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory ⋙
        siteDerivedTensorIndependentCoefficients J R) :
    (comparison e.mapDerivedCategory (tensor (DerivedCategory A))).hom ≫
      Functor.whiskerLeft
        (e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory)
        (comparisonOnSection R e θ).hom = θ.hom := by
  let := CategoryTheory.ConjugateTensor.nativeDerivedMonoidal A
  have h := extend_image e.mapDerivedCategory (conjugateTensor R e)
    (siteDerivedTensorIndependentCoefficients J R)
    ((comparison e.mapDerivedCategory (tensor (DerivedCategory A))).inv ≫ θ.hom)
  change (comparison e.mapDerivedCategory (tensor (DerivedCategory A))).hom ≫
    Functor.whiskerLeft
      (e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory)
      (extend e.mapDerivedCategory (conjugateTensor R e)
        (siteDerivedTensorIndependentCoefficients J R)
        ((comparison e.mapDerivedCategory (tensor (DerivedCategory A))).inv ≫ θ.hom)) = _
  change Functor.whiskerLeft
      (e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory)
      (extend e.mapDerivedCategory (conjugateTensor R e)
        (siteDerivedTensorIndependentCoefficients J R)
        ((comparison e.mapDerivedCategory (tensor (DerivedCategory A))).inv ≫ θ.hom)) = _ at h
  rw [h]
  simp only [Iso.hom_inv_id_assoc]

omit [e.functor.Braided] in
private theorem comparisonOnSection_of_iso
    (v : conjugateTensor R e ≅ siteDerivedTensorIndependentCoefficients J R) :
    comparisonOnSection R e
      (comparison e.mapDerivedCategory (tensor (DerivedCategory A)) ≪≫
        Functor.isoWhiskerLeft
          (e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory) v) = v := by
  let := CategoryTheory.ConjugateTensor.nativeDerivedMonoidal A
  apply Iso.ext
  change extend _ _ _ (_ ≫ _ ≫ _) = _
  simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]
  exact extend_whisker _ _ _ _

attribute [local irreducible] comparisonOnSection imageCounit conjugateCounit
  totalComparison CategoryTheory.ConjugateTensor.internalCounit

private theorem normalized_iff
    (θ : tensor (DerivedCategory A) ⋙ e.functor.mapDerivedCategory ≅
      e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory ⋙
        siteDerivedTensorIndependentCoefficients J R)
    (hflat : ∀ X : A, ObjectProperty.flat X →
      IsFlatOnSite (J := J) (R := R) (e.functor.obj X))
    (hkflat : ∀ P : CochainComplex A ℤ, P.IsKFlatForTotalTensor →
      CochainComplex.IsKFlatIndependentCoefficients
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)) :
    Normalized R e θ hflat hkflat ↔
      ∀ (P Q : CochainComplex A ℤ)
        (_hp : P.IsKFlatForTotalTensor) (_hq : Q.IsKFlatForTotalTensor)
        (_hpf : ∀ n : ℤ, ObjectProperty.flat (P.X n))
        (_hqf : ∀ n : ℤ, ObjectProperty.flat (Q.X n)),
        (comparisonOnSection R e θ).hom.app
            (DerivedCategory.Q.obj ((e.functor.mapHomologicalComplex (.up ℤ)).obj P),
              DerivedCategory.Q.obj ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)) ≫
          (counit R).app
            (((e.functor.mapHomologicalComplex (.up ℤ)).obj P),
              ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)) =
          (imageCounit R e).app (P, Q) := by
  let := CategoryTheory.ConjugateTensor.nativeDerivedMonoidal A
  have hθ (P Q : CochainComplex A ℤ) := congrArg
    (fun t ↦ t.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (comparisonOnSection_image R e θ)
  unfold Normalized
  constructor <;> intro h P Q hp hq hpf hqf
  all_goals
    have hr := counit_model R
      ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)
      ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)
      (hkflat P hp) (hkflat Q hq)
      (fun n ↦ hflat (P.X n) (hpf n)) (fun n ↦ hflat (Q.X n) (hqf n))
    let k := Iso.prod (e.functor.mapDerivedCategoryFactors.app P)
      (e.functor.mapDerivedCategoryFactors.app Q)
    let t := (comparison e.mapDerivedCategory (tensor (DerivedCategory A))).app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
    let r := model R
      ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)
      ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)
      (hkflat P hp) (hkflat Q hq)
      (fun n ↦ hflat (P.X n) (hpf n)) (fun n ↦ hflat (Q.X n) (hqf n))
    let d := e.functor.mapDerivedCategory.map ((internalCounit A).app (P, Q)) ≫
      e.functor.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
      DerivedCategory.Q.map ((totalComparison R e).hom.app (P, Q))
    have hs := normalization_square (conjugateTensor R e)
      (siteDerivedTensorIndependentCoefficients J R) (comparisonOnSection R e θ).hom k t r d
    have htθ : t.hom ≫ (comparisonOnSection R e θ).hom.app
        (e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
          e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) =
        θ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := hθ P Q
    have hi : (imageCounit R e).app (P, Q) =
        (conjugateTensor R e).map k.inv ≫ t.inv ≫ d := by
      unfold imageCounit
      rfl
  · rw [hr, hi]
    apply hs.mp
    exact htθ.trans (by
      simpa only [d, r, k, Iso.prod_inv, CategoryTheory.Prod.mkHom, Iso.app_inv,
        Category.assoc] using h P Q hp hq hpf hqf)
  · have hh := h P Q hp hq hpf hqf
    rw [hr, hi] at hh
    have hh' := hs.mpr hh
    change t.hom ≫ (comparisonOnSection R e θ).hom.app
        (e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
          e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) = _ at hh'
    exact htθ.symm.trans (by
      simpa only [d, r, k, Iso.prod_inv, CategoryTheory.Prod.mkHom, Iso.app_inv,
        Category.assoc] using hh')

private theorem normalized_counit_resolving
    (θ : tensor (DerivedCategory A) ⋙ e.functor.mapDerivedCategory ≅
      e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory ⋙
        siteDerivedTensorIndependentCoefficients J R)
    (hflat : ∀ X : A, ObjectProperty.flat X →
      IsFlatOnSite (J := J) (R := R) (e.functor.obj X))
    (hflatInv : ∀ X : Modules R, IsFlatOnSite (J := J) (R := R) X →
      ObjectProperty.flat (e.inverse.obj X))
    (hkflat : ∀ P : CochainComplex A ℤ, P.IsKFlatForTotalTensor →
      CochainComplex.IsKFlatIndependentCoefficients
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj P))
    (hkflatInv : ∀ P : Complexes R, P.IsKFlatIndependentCoefficients →
      CochainComplex.IsKFlatForTotalTensor
        ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P))
    (hθ : Normalized R e θ hflat hkflat)
    (P Q : Complexes R)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hpf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hqf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)) :
    (comparisonOnSection R e θ).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (counit R).app (P, Q) = (conjugateCounit R e).app (P, Q) := by
  let := CategoryTheory.ConjugateTensor.nativeDerivedMonoidal A
  let ε : ((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) ⋙
      conjugateTensor R e ⟶ tensor (Complexes R) ⋙ DerivedCategory.Q := by
    exact Functor.whiskerLeft (C := Complexes R × Complexes R)
      ((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q)
      (comparisonOnSection R e θ).hom ≫ counit R
  let δ := conjugateCounit R e
  let H := e.inverse.mapHomologicalComplex (.up ℤ)
  let E := e.functor.mapHomologicalComplex (.up ℤ)
  have hi : ε.app (E.obj (H.obj P), E.obj (H.obj Q)) =
      δ.app (E.obj (H.obj P), E.obj (H.obj Q)) := by
    have h := (normalized_iff R e θ hflat hkflat).mp hθ
      (H.obj P) (H.obj Q) (hkflatInv P hp) (hkflatInv Q hq)
      (fun n ↦ hflatInv (P.X n) (hpf n)) (fun n ↦ hflatInv (Q.X n) (hqf n))
    have hc := congrArg (fun t ↦ t.app (H.obj P, H.obj Q)) (conjugateCounit_image R e)
    exact h.trans hc.symm
  let c := (e.mapHomologicalComplex (.up ℤ)).counitIso
  let f : (E.obj (H.obj P), E.obj (H.obj Q)) ⟶ (P, Q) :=
    (c.hom.app P, c.hom.app Q)
  have hε := ε.naturality (X := (E.obj (H.obj P), E.obj (H.obj Q)))
    (Y := (P, Q)) f
  have hδ := δ.naturality (X := (E.obj (H.obj P), E.obj (H.obj Q)))
    (Y := (P, Q)) f
  let S := ((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) ⋙
    conjugateTensor R e
  have hS : S.map f = (S.mapIso (Iso.prod (c.app P) (c.app Q))).hom := rfl
  have hmap : IsIso (S.map f) := by rw [hS]; infer_instance
  change ε.app (P, Q) = δ.app (P, Q)
  apply (cancel_epi (S.map f)).mp
  exact hε.trans ((congrArg (· ≫ (tensor (Complexes R) ⋙ DerivedCategory.Q).map f) hi).trans
    hδ.symm)

omit [e.functor.Braided] in
private theorem comparison_unique
    (v v' : conjugateTensor R e ≅ siteDerivedTensorIndependentCoefficients J R)
    (h : ∀ (P Q : Complexes R)
      (_hp : P.IsKFlatIndependentCoefficients) (_hq : Q.IsKFlatIndependentCoefficients)
      (_hpf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
      (_hqf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
      v.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (counit R).app (P, Q) =
      v'.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (counit R).app (P, Q)) : v = v' := by
  let := CategoryTheory.ConjugateTensor.nativeDerivedMonoidal A
  apply Iso.ext
  have hf := (cochain_tensor_model_rigidity J R).choose_spec.2.2
    (DerivedCategory (Modules R)) inferInstance (conjugateTensor R e)
    (siteDerivedTensorIndependentCoefficients J R)
  apply hf.injective
  ext X
  have hh := h X.1.obj X.2.obj X.1.property.1 X.2.property.1
    X.1.property.2 X.2.property.2
  rw [counit_model R _ _ X.1.property.1 X.2.property.1
    X.1.property.2 X.2.property.2] at hh
  exact (cancel_mono _).mp hh

/-- There is exactly one representative-normalized tensor comparison, and its conjugate
identifies the canonical localization transformations on every pair of complexes.
The final universal quantifier has no K-flatness, flatness or boundedness assumptions.

Source: Stacks Project, sites-cohomology.tex, Tags 06YS and 06YU, and the exact-equivalence
conjugation calculation (blueprint: lem-pd-conjugate-tensor-localization-counit).

Proof, following the node's five steps:
1. For flat-term K-flat U,V, the inverse equivalence gives flat-term K-flat HU,HV.
   The defining imageCounit composite is invertible on EHU,EHV. Naturality for
   the termwise counit EHU→U gives invertibility of conjugateCounit at U,V.
2. On resolving pairs set b to the conjugate counit followed by the inverse native
   counit. Naturality of both counits proves naturality of b and its inverse.
   Extend both using lem-weil-pbc-site-derived-tensor-descent. Unique extension
   makes their composites identities, giving the isomorphism v.
3. Compose v on E-images with theta-zero. Substitute imageCounit's defining
   equation and cancel the kappa maps to obtain precisely Normalized.
4. Every other normalized theta induces comparisonOnSection by the displayed
   counit formula. Triangle identities give its E-image equation. Apply its
   normalization to HU,HV and naturality along EHU→U to see its restriction is b.
   Unique extension makes it v, proving uniqueness of theta and v.
5. For arbitrary U,V choose resolving quasi-isomorphisms P→U and Q→V by
   lem-pc-kflat-resolution. Naturality of v and of both counits yields equality
   after precomposition with the conjugate derived tensor of these maps. That
   map is invertible by localization, so cancel it. Neither the ordinary tensor
   of the resolution maps nor the counits at U,V are inverted.
-/
theorem conjugate_tensor_localization_counit
    (hflat : ∀ X : A, ObjectProperty.flat X →
      IsFlatOnSite (J := J) (R := R) (e.functor.obj X))
    (hflatInv : ∀ X : Modules R, IsFlatOnSite (J := J) (R := R) X →
      ObjectProperty.flat (e.inverse.obj X))
    (hacyclic : ∀ P : CochainComplex A ℤ, P.Acyclic →
      ((e.functor.mapHomologicalComplex (.up ℤ)).obj P).Acyclic)
    (hacyclicInv : ∀ P : Complexes R, P.Acyclic →
      ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P).Acyclic)
    (hkflat : ∀ P : CochainComplex A ℤ, P.IsKFlatForTotalTensor →
      CochainComplex.IsKFlatIndependentCoefficients
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj P))
    (hkflatInv : ∀ P : Complexes R, P.IsKFlatIndependentCoefficients →
      CochainComplex.IsKFlatForTotalTensor
        ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P)) :
    (∃! θ : tensor (DerivedCategory A) ⋙ e.functor.mapDerivedCategory ≅
        e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory ⋙
          siteDerivedTensorIndependentCoefficients J R,
      Normalized R e θ hflat hkflat) ∧
    (∀ θ : tensor (DerivedCategory A) ⋙ e.functor.mapDerivedCategory ≅
        e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory ⋙
          siteDerivedTensorIndependentCoefficients J R,
      Normalized R e θ hflat hkflat →
        (∀ M N : DerivedCategory A,
          (comparison e.mapDerivedCategory (tensor (DerivedCategory A))).hom.app (M, N) ≫
            (comparisonOnSection R e θ).hom.app
              (e.functor.mapDerivedCategory.obj M, e.functor.mapDerivedCategory.obj N) =
            θ.hom.app (M, N)) ∧
        (∀ U V : Complexes R,
          (comparisonOnSection R e θ).hom.app
              (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V) ≫
            (counit R).app (U, V) = (conjugateCounit R e).app (U, V))) := by
  let := CategoryTheory.ConjugateTensor.nativeDerivedMonoidal A
  have _ := hacyclic
  have _ := hacyclicInv
  obtain ⟨v, hv⟩ := counit_comparison_exists R e hkflatInv
  let θ := comparison e.mapDerivedCategory (tensor (DerivedCategory A)) ≪≫
    Functor.isoWhiskerLeft
      (e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory) v
  have hθ : Normalized R e θ hflat hkflat := by
    apply (normalized_iff R e θ hflat hkflat).mpr
    intro P Q hp hq hpf hqf
    rw [comparisonOnSection_of_iso R e v]
    have h := hv ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)
      ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)
    have hc := congrArg (fun t ↦ t.app (P, Q)) (conjugateCounit_image R e)
    exact h.trans hc
  have huv (θ' : tensor (DerivedCategory A) ⋙ e.functor.mapDerivedCategory ≅
      e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory ⋙
        siteDerivedTensorIndependentCoefficients J R)
      (hθ' : Normalized R e θ' hflat hkflat) : comparisonOnSection R e θ' = v := by
    apply comparison_unique R e
    intro P Q hp hq hpf hqf
    exact (normalized_counit_resolving R e θ' hflat hflatInv hkflat hkflatInv
      hθ' P Q hp hq hpf hqf).trans (hv P Q).symm
  constructor
  · refine ⟨θ, hθ, fun θ' hθ' ↦ ?_⟩
    apply Iso.ext
    have h := comparisonOnSection_image R e θ'
    rw [huv θ' hθ'] at h
    exact h.symm
  · intro θ' hθ'
    constructor
    · intro M N
      exact congrArg (fun t ↦ t.app (M, N)) (comparisonOnSection_image R e θ')
    · rw [huv θ' hθ']
      exact hv

end SheafOfModules.ConjugateTensorLocalization
