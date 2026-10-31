/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CoherentCechImageModel
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.ElementSiteDescent
import WeilConjectures.CategoryTheory.ElementModulePresheafExtension
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.ContinuousCocontinuousRingedRestriction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Compatible injective columns of the ringed-topos Cech nerve

Source: Stacks Project, sites-cohomology.tex, Tags 03FC, 08FI and section-unbounded;
sites-modules.tex, Tags 04IE and 04J4
(blueprint: lem-sfb-cech-injective-column-model).

The derived functors and their units are supplied together with their defining universal
properties. This retains their normalization without choosing an arbitrary object
isomorphism. The natural isomorphism of cosimplicial diagrams records every operator.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u wX wY wSlice

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Apply the existing canonical element-site restriction to an integer-indexed complex.
Additivity is obtained from its given adjunction using the existing biproduct lemmas;
all objects, morphisms and differentials are the sectionwise restriction itself.

Source: Stacks 04IE, 04J4 and 08FI
(blueprint: lem-sfb-cech-injective-column-model). -/
def cechColumnRestrictComplex
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (D : CoherentCechImageModel R)
    (A : Sheaf J (Type u)) :
    CochainComplex (ringedSiteModules.{u} R) ℤ ⥤
      CochainComplex (ringedSiteModules.{u} (elementRing R A)) ℤ :=
  letI := (D.adj A).isLeftAdjoint
  letI : HasBinaryBiproducts (ringedSiteModules.{u} R) := Abelian.hasBinaryBiproducts
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (elementModulePullback R A)
  letI : (elementModulePullback R A).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  (elementModulePullback R A).mapHomologicalComplex (.up ℤ)

set_option maxRecDepth 500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace CechColumnAux

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

private theorem restriction_leftAdjoint (A : Sheaf J (Type u)) :
    (elementModulePullback.{u, u} R A : ringedSiteModules.{u} R ⥤
      ringedSiteModules.{u} (elementRing R A)).IsLeftAdjoint := by
  have := (element_site_descent A).2.1
  obtain ⟨f, _, _, ⟨adj⟩⟩ := continuous_cocontinuous_ringed_restriction
    (elementTopology A) J (elementProjection A) R
  exact adj.isLeftAdjoint

@[irreducible] private noncomputable def push (A : Sheaf J (Type u)) :
    ringedSiteModules.{u} (elementRing R A) ⥤ ringedSiteModules.{u} R :=
  have := restriction_leftAdjoint R A
  (elementModulePullback.{u, u} R A).rightAdjoint

@[irreducible] private noncomputable def adj (A : Sheaf J (Type u)) :
    elementModulePullback.{u, u} R A ⊣ push R A := by
  unfold push
  have := restriction_leftAdjoint R A
  exact Adjunction.ofIsLeftAdjoint (elementModulePullback.{u, u} R A)

private theorem continuous {A B : Sheaf J (Type u)} (b : B ⟶ A) :
    Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A) :=
  (element_site_descent A).2.2.2 B b

@[irreducible] private noncomputable def restrictHom
    {A B : Sheaf J (Type u)} (b : B ⟶ A) {M N : ringedSiteModules.{u} R}
    (t : (elementModulePullback.{u, u} R A).obj M ⟶
      (elementModulePullback.{u, u} R A).obj N) :
    (elementModulePullback.{u, u} R B).obj M ⟶
      (elementModulePullback.{u, u} R B).obj N :=
  (elementModulePullbackOver.{u, u} R b (continuous b)).map t

private theorem restrictHom_comp {A B : Sheaf J (Type u)} (b : B ⟶ A)
    {M N P : ringedSiteModules.{u} R}
    (t : (elementModulePullback.{u, u} R A).obj M ⟶
      (elementModulePullback.{u, u} R A).obj N)
    (v : (elementModulePullback.{u, u} R A).obj N ⟶
      (elementModulePullback.{u, u} R A).obj P) :
    restrictHom R b (t ≫ v) = restrictHom R b t ≫ restrictHom R b v := by
  unfold restrictHom
  apply SheafOfModules.hom_ext
  rfl

private theorem restrictHom_map {A B : Sheaf J (Type u)} (b : B ⟶ A)
    {M N : ringedSiteModules.{u} R} (t : M ⟶ N) :
    restrictHom R b ((elementModulePullback.{u, u} R A).map t) =
      (elementModulePullback.{u, u} R B).map t := by
  unfold restrictHom
  apply SheafOfModules.hom_ext
  rfl

private theorem restrictHom_idMap (A : Sheaf J (Type u))
    {M N : ringedSiteModules.{u} R}
    (t : (elementModulePullback.{u, u} R A).obj M ⟶
      (elementModulePullback.{u, u} R A).obj N) : restrictHom R (𝟙 A) t = t := by
  unfold restrictHom
  apply SheafOfModules.hom_ext
  rfl

private theorem restrictHom_trans {A B E : Sheaf J (Type u)} (b : B ⟶ A) (c : E ⟶ B)
    {M N : ringedSiteModules.{u} R}
    (t : (elementModulePullback.{u, u} R A).obj M ⟶
      (elementModulePullback.{u, u} R A).obj N) :
    restrictHom R c (restrictHom R b t) = restrictHom R (c ≫ b) t := by
  unfold restrictHom
  apply SheafOfModules.hom_ext
  rfl

private noncomputable def restriction {A B : Sheaf J (Type u)} (b : B ⟶ A)
    (M : ringedSiteModules.{u} R) :
    (push R A).obj ((elementModulePullback.{u, u} R A).obj M) ⟶
      (push R B).obj ((elementModulePullback.{u, u} R B).obj M) :=
  (adj R B).homEquiv _ _
    (restrictHom R b ((adj R A).counit.app ((elementModulePullback.{u, u} R A).obj M)))

private theorem restriction_transpose {A B : Sheaf J (Type u)} (b : B ⟶ A)
    (M : ringedSiteModules.{u} R) :
    ((adj R B).homEquiv _ _).symm (restriction R b M) =
      restrictHom R b ((adj R A).counit.app ((elementModulePullback.{u, u} R A).obj M)) :=
  Equiv.symm_apply_apply _ _

private theorem restriction_naturality {A B : Sheaf J (Type u)} (b : B ⟶ A)
    {M N : ringedSiteModules.{u} R} (f : M ⟶ N) :
    (push R A).map ((elementModulePullback.{u, u} R A).map f) ≫ restriction R b N =
      restriction R b M ≫ (push R B).map ((elementModulePullback.{u, u} R B).map f) := by
  apply ((adj R B).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, restriction_transpose,
    restriction_transpose, ← restrictHom_map R b, ← restrictHom_map R b,
    ← restrictHom_comp, ← restrictHom_comp]
  exact congrArg (restrictHom R b)
    ((adj R A).counit.naturality ((elementModulePullback.{u, u} R A).map f))

private theorem restriction_id (A : Sheaf J (Type u)) (M : ringedSiteModules.{u} R) :
    restriction R (𝟙 A) M = 𝟙 _ := by
  apply ((adj R A).homEquiv _ _).symm.injective
  rw [restriction_transpose, Adjunction.homEquiv_symm_id, restrictHom_idMap]

private theorem restriction_comp {A B E : Sheaf J (Type u)} (b : B ⟶ A) (c : E ⟶ B)
    (M : ringedSiteModules.{u} R) :
    restriction R b M ≫ restriction R c M = restriction R (c ≫ b) M := by
  apply ((adj R E).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, restriction_transpose,
    restriction_transpose, ← restrictHom_map R c, ← restrictHom_comp]
  have h := restriction_transpose R b M
  rw [Adjunction.homEquiv_counit] at h
  exact (congrArg (restrictHom R c) h).trans (restrictHom_trans R b c _)

private noncomputable def image :
    (Sheaf J (Type u))ᵒᵖ ⥤ ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} R where
  obj A := elementModulePullback.{u, u} R A.unop ⋙ push R A.unop
  map b := { app := restriction R b.unop
             naturality := fun _ _ f ↦ restriction_naturality R b.unop f }
  map_id A := by
    apply NatTrans.ext
    funext M
    exact restriction_id R A.unop M
  map_comp b c := by
    apply NatTrans.ext
    funext M
    exact (restriction_comp R b.unop c.unop M).symm

private theorem unit_restriction {A B : Sheaf J (Type u)} (b : B ⟶ A)
    (M : ringedSiteModules.{u} R) :
    (adj R A).unit.app M ≫ restriction R b M = (adj R B).unit.app M := by
  apply ((adj R B).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  simp only [Functor.id_obj, Functor.comp_obj]
  rw [Adjunction.homEquiv_symm_unit, restriction_transpose, ← restrictHom_map R b,
    ← restrictHom_comp,
    (adj R A).left_triangle_components]
  simpa only [Functor.map_id] using restrictHom_map R b (𝟙 M)

private noncomputable def model : CoherentCechImageModel R where
  push := push R
  pushAdditive A := by
    have := (adj R A).isRightAdjoint
    have : PreservesBinaryBiproducts (push R A) :=
      preservesBinaryBiproducts_of_preservesBinaryProducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  adj := adj R
  continuous := continuous
  image := image R
  imageIso A := Iso.refl _
  restriction b M := by
    simpa only [image, Functor.comp_obj, Functor.op_obj, unop_op,
      Iso.refl_hom, NatTrans.id_app, Category.comp_id, Adjunction.homEquiv_symm_id,
      Quiver.Hom.unop_op, restrictHom]
      using restriction_transpose R b M
  augmentation A := (adj R A).unit
  unit A M := by simp
  augmentation_naturality b := by
    apply NatTrans.ext
    funext M
    exact unit_restriction R b M
  additive V := by
    constructor
    intro M N f g
    apply HomologicalComplex.Hom.ext
    funext n
    have : HasBinaryBiproducts (ringedSiteModules.{u} R) := Abelian.hasBinaryBiproducts
    have := (adj R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).isLeftAdjoint
    have := (adj R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).isRightAdjoint
    have : PreservesBinaryBiproducts
        (elementModulePullback.{u, u} R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    have : (elementModulePullback.{u, u} R
        ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).Additive :=
      Functor.additive_of_preservesBinaryBiproducts _
    have : PreservesBinaryBiproducts
        (push R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))) :=
      preservesBinaryBiproducts_of_preservesBinaryProducts _
    have : (push R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).Additive :=
      Functor.additive_of_preservesBinaryBiproducts _
    change (push R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).map
      ((elementModulePullback.{u, u} R
          ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).map (f + g)) =
      (push R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).map
      ((elementModulePullback.{u, u} R
          ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).map f) +
        (push R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).map
      ((elementModulePullback.{u, u} R
          ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).map g)
    calc
      _ = (push R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).map
          ((elementModulePullback.{u, u} R
          ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).map f +
            (elementModulePullback.{u, u} R
          ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).map g) :=
        congrArg (push R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).map
          (Functor.map_add _)
      _ = _ := Functor.map_add _



private theorem extension_leftExact (A : Sheaf J (Type u)) :
    PreservesFiniteLimits (elementModuleExtension.{u} R A) := by
  have := (element_module_presheaf_extension R A).1
  let e := SheafOfModules.pullbackIso (F := elementProjection A) (𝟙 (elementRing R A))
  have : PreservesFiniteLimits
      (SheafOfModules.forget (elementRing R A) ⋙
        PresheafOfModules.pullback.{u} (F := elementProjection A)
          (𝟙 (elementRing R A).obj) ⋙
        PresheafOfModules.sheafification (𝟙 R.obj)) := by
    have : PreservesFiniteLimits
        (PresheafOfModules.pullback.{u} (F := elementProjection A)
          (𝟙 (elementRing R A).obj) ⋙
          PresheafOfModules.sheafification (𝟙 R.obj)) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  have he : (SheafOfModules.forget (elementRing R A) ⋙
      PresheafOfModules.pullback.{u} (F := elementProjection A)
        (𝟙 (elementRing R A).obj) ⋙ PresheafOfModules.sheafification (𝟙 R.obj)) ≅
        elementModuleExtension.{u} R A := e.symm
  exact preservesFiniteLimits_of_natIso he

private theorem restriction_injectives (A : Sheaf J (Type u)) :
    (elementModulePullback.{u, u} R A).PreservesInjectiveObjects := by
  have := extension_leftExact R A
  obtain ⟨a⟩ := elementModuleExtension_adjunction R A
  exact a.preservesInjectiveObjects_of_preservesFiniteLimits

private theorem restricted_resolution {M : ringedSiteModules.{u} R}
    (I : InjectiveResolution M) (D : CoherentCechImageModel R)
    (A : Sheaf J (Type u)) :
    CochainComplex.IsKInjective
        ((cechColumnRestrictComplex D A).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat)) ∧
      QuasiIso ((cechColumnRestrictComplex D A).map
        (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)) := by
  have := (D.adj A).isLeftAdjoint
  have : PreservesBinaryBiproducts (elementModulePullback.{u, u} R A) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (elementModulePullback.{u, u} R A).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have := restriction_injectives R A
  obtain ⟨extAdj⟩ := elementModuleExtension_adjunction R A
  have := extAdj.isRightAdjoint
  constructor
  · have : ∀ q : ℕ,
        Injective (((elementModulePullback.{u, u} R A).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex |>.X q) := fun q ↦
          Functor.injective_obj (elementModulePullback.{u, u} R A) (I.cocomplex.X q)
    exact CochainComplex.isKInjective_of_iso
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
        (elementModulePullback.{u, u} R A)).symm
  · change QuasiIso (((elementModulePullback.{u, u} R A).mapHomologicalComplex (.up ℤ)).map _)
    infer_instance


section Diagram

variable {Y : Type u} [SmallCategory Y] {L : GrothendieckTopology Y}
  {S : Sheaf L RingCat.{u}} (D : CoherentCechImageModel R)
  (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
  (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ)

private theorem image_additive (A : Sheaf J (Type u)) : (D.image.obj (op A)).Additive := by
  have := (D.adj A).isLeftAdjoint
  have : PreservesBinaryBiproducts (elementModulePullback.{u, u} R A) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (elementModulePullback.{u, u} R A).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  exact Functor.additive_of_iso (D.imageIso A).symm

private noncomputable def diagram :
    CosimplicialObject (CochainComplex (ringedSiteModules.{u} S) ℕ) where
  obj n := (D.bicomplex G V I).X n.len
  map {n m} θ :=
    { f q := G.map ((D.image.map (((sheafCoverNerve V).map θ.op).op)).app (I.X q))
      comm' i j _ := by
        change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
        rw [← G.map_comp, ← G.map_comp]
        exact congrArg G.map
          ((D.image.map (((sheafCoverNerve V).map θ.op).op)).naturality (I.d i j)).symm }
  map_id n := by
    apply HomologicalComplex.Hom.ext
    funext q
    simp only [op_id, Functor.map_id, NatTrans.id_app, HomologicalComplex.id_f]
    exact G.map_id _
  map_comp θ ψ := by
    apply HomologicalComplex.Hom.ext
    funext q
    change G.map ((D.image.map (((sheafCoverNerve V).map (θ ≫ ψ).op).op)).app (I.X q)) =
      G.map ((D.image.map (((sheafCoverNerve V).map θ.op).op)).app (I.X q)) ≫
        G.map ((D.image.map (((sheafCoverNerve V).map ψ.op).op)).app (I.X q))
    rw [op_comp, Functor.map_comp, op_comp, Functor.map_comp, NatTrans.comp_app,
      G.map_comp]

private noncomputable def augmentation :
    (Functor.const SimplexCategory).obj ((G.mapHomologicalComplex (.up ℕ)).obj I) ⟶
      diagram R D G V I where
  app n :=
    { f q := G.map ((D.augmentation ((sheafCoverNerve V).obj (op n))).app (I.X q))
      comm' i j _ := by
        change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
        rw [← G.map_comp, ← G.map_comp]
        exact congrArg G.map
          ((D.augmentation ((sheafCoverNerve V).obj (op n))).naturality (I.d i j)).symm }
  naturality n m θ := by
    apply HomologicalComplex.Hom.ext
    funext q
    change 𝟙 _ ≫ _ = G.map _ ≫ G.map _
    rw [Category.id_comp, ← G.map_comp]
    exact congrArg G.map (NatTrans.congr_app
      (D.augmentation_naturality ((sheafCoverNerve V).map θ.op)) (I.X q)).symm

private theorem augmentation_d :
    (augmentation R D G V I).app (SimplexCategory.mk 0) ≫
      (D.bicomplex G V I).d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  change G.map _ ≫ G.map _ = 0
  rw [← G.map_comp]
  change G.map (_ ≫ AlgebraicTopology.AlternatingCofaceMapComplex.objD
    (((sheafCoverNerve V).rightOp ⋙ D.image).flip.obj (I.X q)) 0) = 0
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Fin.sum_univ_two]
  simp only [
    Fin.val_zero, pow_zero, Fin.val_one, pow_one, neg_smul, one_smul,
    Preadditive.comp_add, Preadditive.comp_neg]
  have h (i : Fin 2) :
      (D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).app (I.X q) ≫
        (D.image.map (((sheafCoverNerve V).map (SimplexCategory.δ i).op).op)).app (I.X q) =
      (D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 1)))).app (I.X q) :=
    NatTrans.congr_app (D.augmentation_naturality
      ((sheafCoverNerve V).map (SimplexCategory.δ i).op)) (I.X q)
  have h' (i : Fin 2) :
      (D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).app (I.X q) ≫
        CosimplicialObject.δ (((sheafCoverNerve V).rightOp ⋙ D.image).flip.obj (I.X q)) i =
      (D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 1)))).app (I.X q) :=
    h i
  rw [h' 0, h' 1, add_neg_cancel, G.map_zero]

private noncomputable def totalAugmentation :
    (G.mapHomologicalComplex (.up ℕ)).obj I ⟶ (D.bicomplex G V I).total (.up ℕ) where
  f q := ((augmentation R D G V I).app (SimplexCategory.mk 0)).f q ≫
    (D.bicomplex G V I).ιTotal (.up ℕ) 0 q q (zero_add q)
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      Category.assoc, Category.assoc, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℕ).Rel 0 1 by rfl) _ _
        (by dsimp; omega),
      HomologicalComplex₂.d₂_eq _ _ _ (show (ComplexShape.up ℕ).Rel i (i + 1) by rfl) _
        (by dsimp; omega)]
    have hz := congrArg (fun f ↦ f.f i) (augmentation_d R D G V I)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
    change _ ≫ ((1 : ℤˣ) • _) + _ ≫ ((1 : ℤˣ) • _) = _
    simp only [one_smul]
    rw [← Category.assoc, hz, zero_comp, zero_add]
    have hc := ((augmentation R D G V I).app (SimplexCategory.mk 0)).comm i (i + 1)
    change ((augmentation R D G V I).app (SimplexCategory.mk 0)).f i ≫
      ((D.bicomplex G V I).X 0).d i (i + 1) =
        ((G.mapHomologicalComplex (.up ℕ)).obj I).d i (i + 1) ≫
          ((augmentation R D G V I).app (SimplexCategory.mk 0)).f (i + 1) at hc
    simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ (D.bicomplex G V I).ιTotal (.up ℕ) 0 (i + 1) (i + 1)
        (zero_add (i + 1)))
      hc

private theorem mapExtendIso_inv_f
    {A E : Type*} [Category* A] [Abelian A] [Category* E] [Abelian E]
    (F : A ⥤ E) [F.Additive] (K : CochainComplex A ℕ) (n : ℕ) :
    (K.mapExtendIso ComplexShape.embeddingUpNat F).inv.f (n : ℤ) =
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
        ComplexShape.embeddingUpNat (i := n) rfl).hom ≫
      F.map (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).inv := by
  simp only [HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.hom, eqToIso.inv,
    eqToHom_map, eqToHom_trans]
  rw [HomologicalComplex.mapExtendX_hom_eq K F
    (ComplexShape.embeddingUpNat.r_eq_some (i := n) (i' := (n : ℤ)) rfl)]
  rfl

private theorem column_normalization
    {A E : Type*} [Category* A] [Abelian A] [Category* E] [Abelian E]
    (F H : A ⥤ E) [F.Additive] [H.Additive] (t : F ≅ H)
    (K : CochainComplex A ℕ) (q : ℕ) :
    (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
      ComplexShape.embeddingUpNat (i := q) rfl).inv ≫
        ((K.mapExtendIso ComplexShape.embeddingUpNat F).symm ≪≫
          (NatIso.mapHomologicalComplex t (.up ℤ)).app
            (K.extend ComplexShape.embeddingUpNat)).hom.f (q : ℤ) ≫
              H.map (K.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom =
      t.hom.app (K.X q) := by
  change _ ≫ ((K.mapExtendIso ComplexShape.embeddingUpNat F).inv.f (q : ℤ) ≫
    t.hom.app ((K.extend ComplexShape.embeddingUpNat).X (q : ℤ))) ≫ _ = _
  rw [mapExtendIso_inv_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (congrArg (fun z ↦ F.map
    (K.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv ≫ z)
      (t.hom.naturality
        (K.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom).symm).trans
    (by simp only [← Category.assoc, ← F.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.id_comp])

end Diagram



section Derived

private noncomputable def factors
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions A]
  (F : A ⥤ E) [F.Additive] :
    HomotopyCategory.quotient A (.up ℤ) ⋙
      (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso E)

private noncomputable def derivedUnit
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions A]
  (F : A ⥤ E) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (factors F).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) F.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom F.rightDerivedFunctor

private theorem full_whiskering_kan
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    (L : A ⥤ B) (G : B ⥤ E)
    [((Functor.whiskeringLeft A B E).obj L).Full]
    [((Functor.whiskeringLeft A B E).obj L).Faithful]
    {H : A ⥤ E} (e : H ≅ L ⋙ G) : G.IsLeftKanExtension e.hom := by
  let W := (Functor.whiskeringLeft A B E).obj L
  refine ⟨⟨IsInitial.ofUniqueHom
    (fun Y ↦ StructuredArrow.homMk (W.preimage (e.inv ≫ Y.hom)) ?_) ?_⟩⟩
  · change e.hom ≫ W.map (W.preimage (e.inv ≫ Y.hom)) = Y.hom
    rw [W.map_preimage]
    simp
  · intro Y m
    apply StructuredArrow.hom_ext
    apply W.map_injective
    change W.map m.right = W.map (W.preimage (e.inv ≫ Y.hom))
    rw [W.map_preimage]
    have h := m.w
    change e.hom ≫ W.map m.right = Y.hom at h
    rw [← h]
    simp

private theorem derivedUnit_universal
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions A]
  (F : A ⥤ E) [F.Additive] :
    F.rightDerivedFunctor.IsRightDerivedFunctor (derivedUnit F)
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
  have : (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).IsLeftKanExtension
      (factors F).inv := full_whiskering_kan _ _ (factors F).symm
  have : F.rightDerivedFunctor.IsLeftKanExtension F.rightDerivedFunctorUnit :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension _ _
      (HomotopyCategory.quasiIso A (.up ℤ))
  constructor
  exact (Functor.isLeftKanExtension_iff_postcompose (factors F).inv DerivedCategory.Q
    (DerivedCategory.quotientCompQhIso A) F.rightDerivedFunctorUnit (derivedUnit F)
    (by rfl)).mp inferInstance

private theorem derivedUnit_isIso
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions A]
  (F : A ⥤ E) [F.Additive] (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((derivedUnit F).app I) := by
  dsimp only [derivedUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app]
  infer_instance

private noncomputable def comparison
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions A]
  (F : A ⥤ E) [F.Additive] {K I : CochainComplex A ℤ}
    [I.IsKInjective] (s : K ⟶ I) [QuasiIso s] :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  have := derivedUnit_isIso F I
  asIso ((derivedUnit F).app I) ≪≫
    (F.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map s))).symm

private theorem comparison_normalization
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions A]
  (F : A ⥤ E) [F.Additive] {K I : CochainComplex A ℤ}
    [I.IsKInjective] (s : K ⟶ I) [QuasiIso s] :
    (comparison F s).hom ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map s) =
      (derivedUnit F).app I := by
  simp [comparison]

private noncomputable def transport
    {A E : Type*} [Category A] [Category E] (F : A ⥤ E)
    (X : A → E) (e : ∀ a, F.obj a ≅ X a) : A ⥤ E where
  obj := X
  map {a b} f := (e a).inv ≫ F.map f ≫ (e b).hom
  map_id a := by rw [F.map_id]; simp only [Category.id_comp, Iso.inv_hom_id]
  map_comp f g := by rw [F.map_comp]; simp only [Category.assoc, Iso.hom_inv_id_assoc]

private noncomputable def transportIso
    {A E : Type*} [Category A] [Category E] (F : A ⥤ E)
    (X : A → E) (e : ∀ a, F.obj a ≅ X a) : F ≅ transport F X e :=
  NatIso.ofComponents e (fun f ↦ by
    dsimp only [transport]
    simp only [Iso.hom_inv_id_assoc])

end Derived


end CechColumnAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- A single ordinary injective resolution supplies the actual augmented cosimplicial
complex, its signed finite total, and all unit-normalized derived column comparisons.
`σ` identifies its columns with the recorded bicomplex, and `κ` identifies them with
`(f v_n)_* v_n^* I`. Their component equations fix the actual localization maps.
`e` is a natural isomorphism of whole cosimplicial diagrams; `hT` fixes its target objects
to the derived direct images. Thus the coherence includes degeneracies and augmentation.

Source: Stacks 03FC, 08FI, 07A5, 04IE and 04J4
(blueprint: lem-sfb-cech-injective-column-model).

Proof plan, following the nine DAG steps:
1. Module sheaves are Grothendieck (lem-weil-pbc-ring-sheaves-grothendieck), hence have
   enough injectives (lem-sp-grothendieck-enough-injectives). Apply the degree-zero
   resolution existence clause of lem-weil-pbc-left-exact-injective-resolution-degree-zero.
2. The exact extension-by-zero adjoint of lem-weil-pbc-ringed-sheaf-slice-adjunction
   makes element-site restriction preserve injectives by
   lem-sp-right-adjoint-preserves-injectives. Exact restriction preserves the resolution
   quasi-isomorphism, its differential and its zero terms in negative degrees.
3. Apply lem-weil-pbc-bounded-below-injectives-kinjective to I and its restrictions.
4. The continuous-cocontinuous restriction theorem constructs the localization right
   adjoints. For b:B→A the element projection satisfies p_A p_b=p_B. Induced covering
   sieves give both continuity and cover lifting. Transpose the restricted counit to
   construct the actual arrow E_A→E_B (def-sfb-element-site-localization).
5. Counit naturality and the triangle identities prove identity, composition, unit
   compatibility and additivity (def-sfb-coherent-cech-image-model).
6. Apply f_* to the actual nerve diagram. Coordinate deletion and repetition satisfy
   the simplicial identities. Naturality makes the alternating cofaces commute with d_I;
   pairing the two coface composites with opposite signs gives d_Cech squared zero.
7. Use f_*(u_V) for a. Its first Cech differential vanishes since both restrictions of
   the unit agree. Insert a in (0,q) for b. The vertical sign there is +1 and the
   horizontal contribution is zero. The total's cross terms cancel with signs
   (-1)^(n+1) and (-1)^n (def-sp-double-complex-total).
8. Grothendieck categories have K-injective resolutions (lem-sfb-grothendieck-k-injective).
   Apply lem-weil-pbc-kinjective-total-derived to f_* and j_n* followed by f_*.
   Their units are invertible on the complexes from step 3. Define each comparison
   as that unit followed by the inverse of the derived image of the resolution map.
   The equations below are precisely these definitions (def-sfb-right-derived-functor).
9. Transport the one strict diagram through these comparisons: c_m Q(r) c_n inverse.
   Adjacent comparison inverses cancel, so identities, compositions and the augmentation
   remain coherent. This produces T, e and the displayed natural augmentation β. -/
theorem cech_injective_column_model
    {C X : Type u} [SmallCategory C] [SmallCategory X]
    {J : GrothendieckTopology C} {L : GrothendieckTopology X}
    (R : Sheaf J RingCat.{u}) (S : Sheaf L RingCat.{u})
    (_hR : ∀ (U : Cᵒᵖ) (x y : R.obj.obj U), x * y = y * x)
    (_hS : ∀ (U : Xᵒᵖ) (x y : S.obj.obj U), x * y = y * x)
    [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wY} (ringedSiteModules.{u} S)]
    [∀ A : Sheaf J (Type u),
      HasDerivedCategory.{wSlice} (ringedSiteModules.{u} (elementRing R A))]
    (f : RingedToposMorphism R S) [IsIso f.ringMap]
    (fInverse : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R)
    [fInverse.Additive] [PreservesFiniteLimits fInverse] [PreservesFiniteColimits fInverse]
    (_adj : fInverse ⊣ f.modules)
    (V : Sheaf J (Type u)) [Epi (terminal.from V)] (M : ringedSiteModules.{u} R) :
    Nonempty (InjectiveResolution M) ∧ Nonempty (CoherentCechImageModel R) ∧
    ∀ (I : InjectiveResolution M) (D : CoherentCechImageModel R),
      CochainComplex.IsKInjective (I.cocomplex.extend ComplexShape.embeddingUpNat) ∧
      (∀ n : SimplexCategory,
        CochainComplex.IsKInjective
          ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).obj
            (I.cocomplex.extend ComplexShape.embeddingUpNat)) ∧
        QuasiIso ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).map
          (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat))) ∧
      ∃ (B : CosimplicialObject (CochainComplex (ringedSiteModules.{u} S) ℕ))
        (σ : ∀ n : SimplexCategory, B.obj n ≅ (D.bicomplex f.modules V I.cocomplex).X n.len)
        (α : (Functor.const SimplexCategory).obj
          ((f.modules.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) ⟶ B)
        (a : (f.modules.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
          (D.bicomplex f.modules V I.cocomplex).X 0)
        (b : (f.modules.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
          (D.bicomplex f.modules V I.cocomplex).total (.up ℕ))
        (RF : DerivedCategory (ringedSiteModules.{u} R) ⥤
          DerivedCategory (ringedSiteModules.{u} S))
        (η : f.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
          DerivedCategory.Q ⋙ RF)
        (RFslice : ∀ n : SimplexCategory,
          DerivedCategory (ringedSiteModules.{u}
            (elementRing R ((sheafCoverNerve V).obj (op n)))) ⥤
              DerivedCategory (ringedSiteModules.{u} S))
        (ηslice : ∀ n : SimplexCategory,
          ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).mapHomologicalComplex
            (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RFslice n)
        (κ : ∀ n : SimplexCategory,
          (B.obj n).extend ComplexShape.embeddingUpNat ≅
            ((((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).mapHomologicalComplex
              (.up ℤ)).obj ((cechColumnRestrictComplex D
                ((sheafCoverNerve V).obj (op n))).obj
                  (I.cocomplex.extend ComplexShape.embeddingUpNat))))
        (c : DerivedCategory.Q.obj
          (((f.modules.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extend
            ComplexShape.embeddingUpNat) ≅
          RF.obj (DerivedCategory.Q.obj
            (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat)))
        (T : CosimplicialObject (DerivedCategory (ringedSiteModules.{u} S)))
        (hT : ∀ n : SimplexCategory, T.obj n = (RFslice n).obj
          (DerivedCategory.Q.obj ((cechColumnRestrictComplex D
            ((sheafCoverNerve V).obj (op n))).obj
              (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat))))
        (e : B ⋙ ComplexShape.embeddingUpNat.extendFunctor (ringedSiteModules.{u} S) ⋙
          DerivedCategory.Q ≅ T)
        (β : (Functor.const SimplexCategory).obj (RF.obj (DerivedCategory.Q.obj
          (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat))) ⟶ T),
        (∀ (n m : SimplexCategory) (θ : n ⟶ m) (q : ℕ),
          (σ n).inv.f q ≫ (B.map θ).f q ≫ (σ m).hom.f q =
            f.modules.map ((D.image.map (((sheafCoverNerve V).map θ.op).op)).app
              (I.cocomplex.X q))) ∧
        (∀ (n : SimplexCategory) (q : ℕ),
          (α.app n).f q ≫ (σ n).hom.f q = f.modules.map
            ((D.augmentation ((sheafCoverNerve V).obj (op n))).app (I.cocomplex.X q))) ∧
        α.app (SimplexCategory.mk 0) ≫ (σ (SimplexCategory.mk 0)).hom = a ∧
        a ≫ (D.bicomplex f.modules V I.cocomplex).d 0 1 = 0 ∧
        (∀ q : ℕ, b.f q = a.f q ≫
          (D.bicomplex f.modules V I.cocomplex).ιTotal (.up ℕ) 0 q q (zero_add q)) ∧
        RF.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (ringedSiteModules.{u} R) (.up ℤ)) ∧
        (∀ n : SimplexCategory, (RFslice n).IsRightDerivedFunctor (ηslice n)
          (HomologicalComplex.quasiIso (ringedSiteModules.{u}
            (elementRing R ((sheafCoverNerve V).obj (op n)))) (.up ℤ))) ∧
        (∀ (n : SimplexCategory) (q : ℕ),
          ((B.obj n).extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv ≫
            (κ n).hom.f (q : ℤ) ≫
              ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).map
                ((elementModulePullback R ((sheafCoverNerve V).obj (op n))).map
                  (I.cocomplex.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom) =
            (σ n).hom.f q ≫ f.modules.map
              ((D.imageIso ((sheafCoverNerve V).obj (op n))).hom.app (I.cocomplex.X q))) ∧
        c.hom ≫ RF.map (DerivedCategory.Q.map
          (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)) =
          DerivedCategory.Q.map (I.cocomplex.mapExtendIso
            ComplexShape.embeddingUpNat f.modules).inv ≫
              η.app (I.cocomplex.extend ComplexShape.embeddingUpNat) ∧
        (∀ n : SimplexCategory,
          (e.app n).hom ≫ eqToHom (hT n) ≫
            (RFslice n).map (DerivedCategory.Q.map
              ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).map
                (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat))) =
            DerivedCategory.Q.map (κ n).hom ≫ (ηslice n).app
              ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).obj
                (I.cocomplex.extend ComplexShape.embeddingUpNat))) ∧
        (∀ n : SimplexCategory,
          β.app n = c.inv ≫ DerivedCategory.Q.map
            (HomologicalComplex.extendMap (α.app n) ComplexShape.embeddingUpNat) ≫
              (e.app n).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
    classical
    have : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
      SheafOfModules.isGrothendieckAbelianOfUniverses J R
    have : ∀ A : Sheaf J (Type u),
        IsGrothendieckAbelian.{u} (ringedSiteModules.{u} (elementRing R A)) :=
      fun A ↦ SheafOfModules.isGrothendieckAbelianOfUniverses (elementTopology A) (elementRing R A)
    refine ⟨⟨InjectiveResolution.of M⟩, ⟨CechColumnAux.model R⟩, ?_⟩
    intro I D
    have hI : CochainComplex.IsKInjective
        (I.cocomplex.extend ComplexShape.embeddingUpNat) := inferInstance
    have hres := CechColumnAux.restricted_resolution R I D
    refine ⟨hI, fun n ↦ hres ((sheafCoverNerve V).obj (op n)), ?_⟩
    have hadd (A : Sheaf J (Type u)) : (elementModulePullback.{u, u} R A).Additive := by
      have := (D.adj A).isLeftAdjoint
      have : PreservesBinaryBiproducts (elementModulePullback.{u, u} R A) :=
        preservesBinaryBiproducts_of_preservesBinaryCoproducts _
      exact Functor.additive_of_preservesBinaryBiproducts _
    have himage (A : Sheaf J (Type u)) : (D.image.obj (op A)).Additive :=
      CechColumnAux.image_additive R D A
    let B := CechColumnAux.diagram R D f.modules V I.cocomplex
    let α := CechColumnAux.augmentation R D f.modules V I.cocomplex
    let a := α.app (SimplexCategory.mk 0)
    let b := CechColumnAux.totalAugmentation R D f.modules V I.cocomplex
    let s := HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat
    let RF := f.modules.rightDerivedFunctor
    let η := CechColumnAux.derivedUnit f.modules
    let RFslice := fun n : SimplexCategory ↦
      ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).rightDerivedFunctor
    let ηslice := fun n : SimplexCategory ↦
      CechColumnAux.derivedUnit ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules)
    let κ : ∀ n : SimplexCategory,
        (B.obj n).extend ComplexShape.embeddingUpNat ≅
          ((((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).mapHomologicalComplex
            (.up ℤ)).obj ((cechColumnRestrictComplex D
              ((sheafCoverNerve V).obj (op n))).obj
                (I.cocomplex.extend ComplexShape.embeddingUpNat))) := fun n ↦
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
        (D.image.obj (op ((sheafCoverNerve V).obj (op n))) ⋙ f.modules)).symm ≪≫
          (NatIso.mapHomologicalComplex
            (Functor.isoWhiskerRight (D.imageIso ((sheafCoverNerve V).obj (op n))) f.modules)
            (.up ℤ)).app (I.cocomplex.extend ComplexShape.embeddingUpNat)
    let c := (DerivedCategory.Q.mapIso
        (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat f.modules)).symm ≪≫
      CechColumnAux.comparison f.modules s
    let v := fun n : SimplexCategory ↦
      (cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).map s
    have hv (n : SimplexCategory) : QuasiIso (v n) := (hres _).2
    have hk (n : SimplexCategory) :
        ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat)).IsKInjective := (hres _).1
    let cn := fun n : SimplexCategory ↦ DerivedCategory.Q.mapIso (κ n) ≪≫
      CechColumnAux.comparison ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules) (v n)
    let Q (B' : CosimplicialObject (CochainComplex (ringedSiteModules.{u} S) ℕ)) :
        CosimplicialObject (DerivedCategory (ringedSiteModules.{u} S)) :=
      B' ⋙ ComplexShape.embeddingUpNat.extendFunctor (ringedSiteModules.{u} S) ⋙
      DerivedCategory.Q
    let T := CechColumnAux.transport (Q B)
      (fun n ↦ (RFslice n).obj (DerivedCategory.Q.obj
        ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).obj
          (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat)))) cn
    let e : Q B ≅ T := CechColumnAux.transportIso (Q B) _ cn
    let β : (Functor.const SimplexCategory).obj
        (RF.obj (DerivedCategory.Q.obj
          (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat))) ⟶ T :=
      (Functor.const SimplexCategory).map c.inv ≫
        (Functor.constComp SimplexCategory
          ((f.modules.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
          (ComplexShape.embeddingUpNat.extendFunctor (ringedSiteModules.{u} S) ⋙
            DerivedCategory.Q)).inv ≫ Functor.whiskerRight α
          (ComplexShape.embeddingUpNat.extendFunctor (ringedSiteModules.{u} S) ⋙
            DerivedCategory.Q) ≫ e.hom
    refine ⟨B, (fun _ ↦ Iso.refl _), α, a, b, RF, η, RFslice, ηslice, κ, c, T,
      (fun _ ↦ rfl), e, β, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n m θ q
      simp only [Iso.refl_inv, Iso.refl_hom, HomologicalComplex.id_f,
        Category.comp_id]
      rfl
    · intro n q
      simp only [Iso.refl_hom, HomologicalComplex.id_f, Category.comp_id]
      rfl
    · simp [a]
    · exact CechColumnAux.augmentation_d R D f.modules V I.cocomplex
    · intro q
      rfl
    · exact CechColumnAux.derivedUnit_universal f.modules
    · intro n
      exact CechColumnAux.derivedUnit_universal _
    · intro n q
      rcases n with ⟨n⟩
      simpa only [κ, B, CechColumnAux.diagram, CoherentCechImageModel.bicomplex,
        HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
        CoherentCechImageModel.cochains, Functor.comp_map, Functor.comp_obj,
        Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        Iso.refl_hom, HomologicalComplex.id_f, Category.id_comp] using
        CechColumnAux.column_normalization
          (D.image.obj (op ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))) ⋙ f.modules)
          (elementModulePullback.{u, u} R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n))) ⋙
            D.push ((sheafCoverNerve V).obj (op (SimplexCategory.mk n))) ⋙ f.modules)
          (Functor.isoWhiskerRight
            (D.imageIso ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))) f.modules)
          I.cocomplex q
    · dsimp only [c, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, η, RF]
      rw [Category.assoc, CechColumnAux.comparison_normalization]
    · intro n
      change (cn n).hom ≫ 𝟙 _ ≫ (RFslice n).map (DerivedCategory.Q.map (v n)) = _
      dsimp only [cn, Iso.trans_hom]
      rw [Category.id_comp, Category.assoc, CechColumnAux.comparison_normalization]
      rfl
    · intro n
      change c.inv ≫ 𝟙 _ ≫ DerivedCategory.Q.map
        (HomologicalComplex.extendMap (α.app n) ComplexShape.embeddingUpNat) ≫
          (e.app n).hom = _
      rw [Category.id_comp]

end CategoryTheory
