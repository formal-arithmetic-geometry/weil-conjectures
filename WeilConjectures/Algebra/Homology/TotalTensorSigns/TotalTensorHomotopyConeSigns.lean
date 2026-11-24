/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Signed tensor homotopies and mapping cones

Signed homotopy, mapping cone and interchange formulas for the total tensor product of complexes
of sheaves of modules.

## Implementation details

All sheaf tensor maps used here are the localization tensor maps induced by balanced presheaf
tensor maps, rather than arbitrary maps on the associated sheaves.

## References

* Stacks Project, Tags 06YM, 06YP, 0G6E, 0FNH and 0GWR
* Stacks Project, Modules on Sites, Section 03DA, and Tag 03EK
-/

@[expose] public noncomputable section

set_option autoImplicit false
attribute [local instance 10000] CategoryTheory.functorCategoryPreadditive
attribute [local instance 10000] SheafOfModules.instPreadditive
attribute [local instance 10000] HomologicalComplex.instPreadditive
attribute [local instance 10000] HomologicalComplex.instLinear
attribute [local instance 10000] CategoryTheory.Functor.preservesZeroMorphisms_of_additive
set_option synthInstance.maxSize 4096

universe u v r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CochainComplex HomologicalComplex

attribute [local irreducible] SheafOfModules.monoidalCategory

namespace SheafOfModules.TotalTensorSigns

/-- Coefficient composition on an independently small site. -/
local instance coefficientCompose {C : Type u} [Category.{v} C]
    [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := by
  let KJ := (equivSmallModel.{r} C).inverse.inducedTopology J
  have : KJ.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) :=
    hasSheafCompose_of_preservesLimitsOfSize KJ
  exact hasSheafComposeEssentiallySmallSite J CommRingCat.{r} RingCat.{r}
    (forget₂ CommRingCat.{r} RingCat.{r})

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

attribute [local instance 10000] coefficientCompose
  SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- The existing category of module sheaves. -/
abbrev Modules := CategoryTheory.ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The existing Abelian structure with its pointwise additive field exposed.
The finite-product, kernel, cokernel and normality fields are the native ones; the
additive field is the same pointwise structure, named directly for specialization. -/
local instance modulesAbelian : Abelian (Modules R) := by
  let native : Abelian (Modules R) := inferInstance
  exact { native with toPreadditive := SheafOfModules.instPreadditive _ }

attribute [local instance 20000] modulesAbelian

namespace Generic

universe d e

variable (D : Type d) [Category.{e} D] [Abelian D] [HasBinaryBiproducts D]
  [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
  [HasCoproducts.{0} D]

/-- Countable coproducts supply the generic total tensor. -/
local instance genericTotalExists (A B : CochainComplex D ℤ) :
    HomologicalComplex.HasMapBifunctor A B (curriedTensor D) (.up ℤ) := inferInstance

end Generic

attribute [local instance] Generic.genericTotalExists

/-- The existing sheafified balanced tensor. -/
def tensor := curriedTensor (Modules R)

/-- The sheaf tensor is additive in both variables. -/
instance tensorAdditive : (tensor R).Additive := by
  unfold tensor
  infer_instance

/-- Tensoring with one module sheaf is additive. -/
instance tensorObjAdditive (M : Modules R) : ((tensor R).obj M).Additive := by
  unfold tensor
  infer_instance

/-- Countable total tensor sums exist for these module sheaves. -/
instance totalExists (A B : CochainComplex (Modules R) ℤ) :
    HomologicalComplex.HasMapBifunctor A B (tensor R) (.up ℤ) := by
  unfold tensor
  exact Generic.genericTotalExists (Modules R) A B

/-- The direct-sum total tensor bifunctor, with differential d tensor 1 + (-1)^p 1 tensor d. -/
def total := (tensor R).map₂CochainComplex

/-- The total tensor is additive in its second argument. -/
instance totalObjAdditive (A : CochainComplex (Modules R) ℤ) :
    ((total R).obj A).Additive := by
  unfold total
  infer_instance

/-- The total tensor is additive in its first argument. -/
instance totalFlipObjAdditive (A : CochainComplex (Modules R) ℤ) :
    ((total R).flip.obj A).Additive := by
  unfold total
  infer_instance

/-- The same bifunctor modulo homotopies, with the inherited coherent integer shifts. -/
abbrev homotopyTensor := (tensor R).bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)

/-- The canonical signed comparison A tensor Cone(u) to Cone(A tensor u). -/
def coneLeft (A : CochainComplex (Modules R) ℤ)
    {X Y : CochainComplex (Modules R) ℤ} (f : X ⟶ Y) :
    ((total R).obj A).obj (mappingCone f) ≅ mappingCone (((total R).obj A).map f) :=
  CochainComplex.mapBifunctorMappingCone₂Iso A f (tensor R)

/-- The canonical unsigned comparison Cone(u) tensor A to Cone(u tensor A). -/
def coneRight (A : CochainComplex (Modules R) ℤ)
    {X Y : CochainComplex (Modules R) ℤ} (f : X ⟶ Y) :
    ((total R).flip.obj A).obj (mappingCone f) ≅
      mappingCone (((total R).flip.obj A).map f) :=
  CochainComplex.mapBifunctorMappingCone₁Iso f A (tensor R)

/-- The existing signed total flip after the presheaf-induced sheaf symmetry, without
requesting the unused associativity data of the monoidal structure on all complexes. -/
def swap (B A : CochainComplex (Modules R) ℤ) :
    ((total R).obj B).obj A ≅ ((total R).obj A).obj B :=
  HomologicalComplex₂.total.mapIso (CochainComplex.Monoidal.braidingBicomplexIso B A)
    (.up ℤ) ≪≫ HomologicalComplex.mapBifunctorFlipIso A B (tensor R) (.up ℤ)

/-- The existing inclusion of a total-tensor summand, with its endpoint type exposed. -/
def ι (A B : CochainComplex (Modules R) ℤ) (p q n : ℤ) (hpq : p + q = n) :
    A.X p ⊗ B.X q ⟶ (((total R).obj A).obj B).X n :=
  CochainComplex.ιMapBifunctor A B (tensor R) p q n hpq

/-- The existing second-variable tensor homotopy, with its endpoints exposed. -/
def homotopyLeft (A : CochainComplex (Modules R) ℤ)
    {X Y : CochainComplex (Modules R) ℤ} {f g : X ⟶ Y} (h : Homotopy f g) :
    Homotopy (((total R).obj A).map f) (((total R).obj A).map g) :=
  HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 A) h (tensor R) (.up ℤ)

/-- The existing first-variable tensor homotopy, with its endpoints exposed. -/
def homotopyRight (A : CochainComplex (Modules R) ℤ)
    {X Y : CochainComplex (Modules R) ℤ} {f g : X ⟶ Y} (h : Homotopy f g) :
    Homotopy (((total R).flip.obj A).map f) (((total R).flip.obj A).map g) :=
  HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 A) (tensor R) (.up ℤ)

/-- The existing coherent second-factor shift, with its endpoints exposed. -/
def shiftLeft (A X : CochainComplex (Modules R) ℤ) (n : ℤ) :
    ((total R).obj A).obj (X⟦n⟧) ≅ (((total R).obj A).obj X)⟦n⟧ :=
  CochainComplex.mapBifunctorShift₂Iso A X (tensor R) n

/-- The existing coherent first-factor shift, with its endpoints exposed. -/
def shiftRight (A X : CochainComplex (Modules R) ℤ) (n : ℤ) :
    ((total R).flip.obj A).obj (X⟦n⟧) ≅ (((total R).flip.obj A).obj X)⟦n⟧ :=
  CochainComplex.mapBifunctorShift₁Iso X A (tensor R) n

attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex

namespace Generic

universe d e

variable (D : Type d) [Category.{e} D] [Abelian D] [HasBinaryBiproducts D]
  [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]

private abbrev tensor := curriedTensor D

variable [HasCoproducts.{0} D]

private abbrev total := (tensor D).map₂CochainComplex

private abbrev coneLeft (A : CochainComplex (D) ℤ)
    {X Y : CochainComplex (D) ℤ} (f : X ⟶ Y) :
    ((total D).obj A).obj (mappingCone f) ≅ mappingCone (((total D).obj A).map f) :=
  CochainComplex.mapBifunctorMappingCone₂Iso A f (tensor D)

private abbrev coneRight (A : CochainComplex (D) ℤ)
    {X Y : CochainComplex (D) ℤ} (f : X ⟶ Y) :
    ((total D).flip.obj A).obj (mappingCone f) ≅
      mappingCone (((total D).flip.obj A).map f) :=
  CochainComplex.mapBifunctorMappingCone₁Iso f A (tensor D)

private abbrev swap (B A : CochainComplex (D) ℤ) :
    ((total D).obj B).obj A ≅ ((total D).obj A).obj B :=
  HomologicalComplex₂.total.mapIso (CochainComplex.Monoidal.braidingBicomplexIso B A)
    (.up ℤ) ≪≫ HomologicalComplex.mapBifunctorFlipIso A B (tensor D) (.up ℤ)

private abbrev ι (A B : CochainComplex (D) ℤ) (p q n : ℤ) (hpq : p + q = n) :
    A.X p ⊗ B.X q ⟶ (((total D).obj A).obj B).X n :=
  CochainComplex.ιMapBifunctor A B (tensor D) p q n hpq

private abbrev shiftLeft (A X : CochainComplex (D) ℤ) (n : ℤ) :
    ((total D).obj A).obj (X⟦n⟧) ≅ (((total D).obj A).obj X)⟦n⟧ :=
  CochainComplex.mapBifunctorShift₂Iso A X (tensor D) n

private abbrev shiftRight (A X : CochainComplex (D) ℤ) (n : ℤ) :
    ((total D).flip.obj A).obj (X⟦n⟧) ≅ (((total D).flip.obj A).obj X)⟦n⟧ :=
  CochainComplex.mapBifunctorShift₁Iso X A (tensor D) n

omit [HasBinaryBiproducts D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem swap_ι (B A : CochainComplex (D) ℤ)
    (i j n : ℤ) (hij : i + j = n) :
    ι D B A i j n hij ≫ (swap D B A).hom.f n =
      (i * j).negOnePow • ((β_ (B.X i) (A.X j)).hom ≫
        ι D A B j i n (by omega)) := by
  dsimp only [ι]
  have h : HomologicalComplex.ιMapBifunctor B A (tensor D) (.up ℤ) i j n hij ≫
      (HomologicalComplex₂.total.map
        (CochainComplex.Monoidal.braidingBicomplexIso B A).hom (.up ℤ)).f n =
      (β_ (B.X i) (A.X j)).hom ≫
        HomologicalComplex.ιMapBifunctor B A (tensor D).flip (.up ℤ) i j n hij := by
    erw [HomologicalComplex₂.ιTotal_map]
    rfl
  dsimp only [swap, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso_hom]
  rw [← Category.assoc, h, Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom,
    Units.smul_def, Preadditive.comp_zsmul]
  change (j * i).negOnePow • ((β_ (B.X i) (A.X j)).hom ≫
    ι D A B j i n (by omega)) = _
  rw [mul_comm j i]

omit [HasBinaryBiproducts D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem swap_naturality
    (A A' B B' : CochainComplex (D) ℤ) (a : A ⟶ A') (b : B ⟶ B') :
    HomologicalComplex.mapBifunctorMap b a (tensor D) (.up ℤ) ≫
        (swap D B' A').hom =
      (swap D B A).hom ≫ HomologicalComplex.mapBifunctorMap a b (tensor D) (.up ℤ) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  dsimp at hij
  simp only [HomologicalComplex.comp_f]
  have e₁ := swap_ι D B' A' i j n hij
  have e₂ := swap_ι_assoc D B A i j n hij
    ((HomologicalComplex.mapBifunctorMap a b (tensor D) (.up ℤ)).f n)
  dsimp only [ι] at e₁ e₂
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, e₁, e₂]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap]
  change (i * j).negOnePow •
    (b.f i ▷ A.X j ≫ B'.X i ◁ a.f j ≫ (β_ (B'.X i) (A'.X j)).hom ≫ _) =
      (i * j).negOnePow • ((β_ (B.X i) (A.X j)).hom ≫
        a.f j ▷ B.X i ≫ A'.X j ◁ b.f i ≫ _)
  congr 1
  simpa only [ι, tensorHom_def, Category.assoc] using
    (BraidedCategory.braiding_naturality_assoc (b.f i) (a.f j)
      (ι D A' B' j i n (by omega)))

omit [SymmetricCategory D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coneLeft_ι (A : CochainComplex (D) ℤ)
    {X Y : CochainComplex (D) ℤ} (f : X ⟶ Y)
    (p q n : ℤ) (hpq : p + q = n) :
    A.X p ◁ (mappingCone.inl f).v (q + 1) q (by omega) ≫
        ι D A (mappingCone f) p q n hpq ≫ (coneLeft D A f).hom.f n =
      p.negOnePow • (ι D A X p (q + 1) (n + 1) (by omega) ≫
        (mappingCone.inl (((total D).obj A).map f)).v (n + 1) n (by omega)) := by
  apply (cancel_mono ((coneLeft D A f).inv.f n)).1
  have hc := HomComplex.Cochain.congr_v
    (CochainComplex.mapBifunctorMappingCone₂Iso.inl_inv A f (tensor D))
    (n + 1) n (by omega)
  simp only [HomComplex.Cochain.comp_zero_cochain_v, HomComplex.Cochain.ofHom_v] at hc
  simp only [Category.assoc, Linear.units_smul_comp]
  rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
    Category.comp_id]
  dsimp only [ι, coneLeft, total, CategoryTheory.Functor.map₂CochainComplex,
    CategoryTheory.Functor.map₂HomologicalComplex, CochainComplex.mapBifunctorMappingCone₂Iso]
  rw [hc, CochainComplex.mapBifunctorMappingCone₂Iso.ι_ι₁
      A f (tensor D) p (q + 1) (n + 1) (by omega) n (by omega) q rfl]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  rfl

omit [SymmetricCategory D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coneRight_ι (A : CochainComplex (D) ℤ)
    {X Y : CochainComplex (D) ℤ} (f : X ⟶ Y)
    (p q n : ℤ) (hpq : q + p = n) :
    (mappingCone.inl f).v (q + 1) q (by omega) ▷ A.X p ≫
        ι D (mappingCone f) A q p n hpq ≫ (coneRight D A f).hom.f n =
      ι D X A (q + 1) p (n + 1) (by omega) ≫
        (mappingCone.inl (((total D).flip.obj A).map f)).v (n + 1) n (by omega) := by
  apply (cancel_mono ((coneRight D A f).inv.f n)).1
  have hc := HomComplex.Cochain.congr_v
    (CochainComplex.mapBifunctorMappingCone₁Iso.inl_inv f A (tensor D))
    (n + 1) n (by omega)
  simp only [HomComplex.Cochain.comp_zero_cochain_v, HomComplex.Cochain.ofHom_v] at hc
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
    ]
  dsimp only [ι, coneRight, total, CategoryTheory.Functor.map₂CochainComplex,
    CategoryTheory.Functor.map₂HomologicalComplex, CategoryTheory.Functor.flip,
    CochainComplex.mapBifunctorMappingCone₁Iso]
  rw [Category.comp_id, hc, CochainComplex.mapBifunctorMappingCone₁Iso.ι_ι₁
      f A (tensor D) (q + 1) p (n + 1) (by omega) n (by omega) q rfl]
  rfl

omit [SymmetricCategory D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coneLeft_inr_ι (A : CochainComplex (D) ℤ)
    {X Y : CochainComplex (D) ℤ} (f : X ⟶ Y)
    (p q n : ℤ) (hpq : p + q = n) :
    A.X p ◁ (mappingCone.inr f).f q ≫
        ι D A (mappingCone f) p q n hpq ≫ (coneLeft D A f).hom.f n =
      ι D A Y p q n hpq ≫ (mappingCone.inr (((total D).obj A).map f)).f n := by
  have e := congrArg (fun t ↦ ι D A Y p q n hpq ≫ t.f n)
    (CochainComplex.mapBifunctorMap_inr_mapBifunctorMappingCone₂Iso_hom A f (tensor D))
  simpa only [ι, CochainComplex.ιMapBifunctor, coneLeft, coneRight, total,
    CochainComplex.mapBifunctorMappingCone₁Iso_hom,
    CochainComplex.mapBifunctorMappingCone₂Iso_hom, tensor, curriedTensor,
    id_whiskerRight, whiskerLeft_id,
    CategoryTheory.Functor.map₂CochainComplex,
    CategoryTheory.Functor.map₂HomologicalComplex, CategoryTheory.Functor.flip,
    HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] using e

omit [SymmetricCategory D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coneRight_inr_ι (A : CochainComplex (D) ℤ)
    {X Y : CochainComplex (D) ℤ} (f : X ⟶ Y)
    (p q n : ℤ) (hpq : q + p = n) :
    (mappingCone.inr f).f q ▷ A.X p ≫
        ι D (mappingCone f) A q p n hpq ≫ (coneRight D A f).hom.f n =
      ι D Y A q p n hpq ≫ (mappingCone.inr (((total D).flip.obj A).map f)).f n := by
  have e := congrArg (fun t ↦ ι D Y A q p n hpq ≫ t.f n)
    (CochainComplex.mapBifunctorMap_inr_mapBifunctorMappingCone₁Iso_hom f A (tensor D))
  simpa only [ι, CochainComplex.ιMapBifunctor, coneLeft, coneRight, total,
    CochainComplex.mapBifunctorMappingCone₁Iso_hom,
    CochainComplex.mapBifunctorMappingCone₂Iso_hom, tensor, curriedTensor,
    id_whiskerRight, whiskerLeft_id,
    CategoryTheory.Functor.map₂CochainComplex,
    CategoryTheory.Functor.map₂HomologicalComplex, CategoryTheory.Functor.flip,
    HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc] using e

omit [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
  [HasCoproducts.{0} D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mapCone_ext (T : D ⥤ D) [T.Additive]
    {X Y : CochainComplex (D) ℤ} (f : X ⟶ Y) (q : ℤ)
    {Z : D} {a b : T.obj ((mappingCone f).X q) ⟶ Z}
    (hl : T.map ((mappingCone.inl f).v (q + 1) q (by omega)) ≫ a =
      T.map ((mappingCone.inl f).v (q + 1) q (by omega)) ≫ b)
    (hr : T.map ((mappingCone.inr f).f q) ≫ a =
      T.map ((mappingCone.inr f).f q) ≫ b) : a = b := by
  have e := congrArg T.map (mappingCone.id_X f q (q + 1) rfl)
  rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at e
  calc
    a = (T.map ((mappingCone.fst f).1.v q (q + 1) rfl) ≫
        T.map ((mappingCone.inl f).v (q + 1) q (by omega)) +
      T.map ((mappingCone.snd f).v q q (add_zero q)) ≫
        T.map ((mappingCone.inr f).f q)) ≫ a := by rw [e, Category.id_comp]
    _ = (T.map ((mappingCone.fst f).1.v q (q + 1) rfl) ≫
        T.map ((mappingCone.inl f).v (q + 1) q (by omega)) +
      T.map ((mappingCone.snd f).v q q (add_zero q)) ≫
        T.map ((mappingCone.inr f).f q)) ≫ b := by
      simp only [Preadditive.add_comp, Category.assoc, hl, hr]
    _ = b := by rw [e, Category.id_comp]

omit [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
  [HasCoproducts.{0} D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coneMap_inl
    {X Y X' Y' : CochainComplex (D) ℤ} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f') (q : ℤ) :
    (mappingCone.inl f).v (q + 1) q (by omega) ≫
        (mappingCone.map f f' a b comm).f q =
      a.f (q + 1) ≫ (mappingCone.inl f').v (q + 1) q (by omega) := by
  simp only [mappingCone.map, mappingCone.inl_v_desc_f,
    HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v]

omit [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
  [HasCoproducts.{0} D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coneMap_inr
    {X Y X' Y' : CochainComplex (D) ℤ} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f') (q : ℤ) :
    (mappingCone.inr f).f q ≫ (mappingCone.map f f' a b comm).f q =
      b.f q ≫ (mappingCone.inr f').f q := by
  simp only [mappingCone.map, mappingCone.inr_f_desc_f, HomologicalComplex.comp_f]

omit [SymmetricCategory D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coneLeft_δ (A : CochainComplex (D) ℤ)
    {X Y : CochainComplex (D) ℤ} (f : X ⟶ Y) :
    (coneLeft D A f).hom ≫ (mappingCone.triangle (((total D).obj A).map f)).mor₃ =
      ((total D).obj A).map (mappingCone.triangle f).mor₃ ≫
        (shiftLeft D A X 1).hom := by
  have e := (CochainComplex.bifunctorMapCochainComplexObjMapMappingConeTriangleIso
    (tensor D) A f).hom.comm₃
  dsimp only [CochainComplex.bifunctorMapCochainComplexObjMapMappingConeTriangleIso,
    Triangle.isoMk, Triangle.homMk, Functor.mapTriangle, Triangle.mk,
    Iso.refl_hom] at e
  simp only [CochainComplex.map₂CochainComplex_obj_commShiftIso_hom_app] at e
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id, coneLeft, coneRight,
    total, CategoryTheory.Functor.map₂CochainComplex,
    CategoryTheory.Functor.map₂HomologicalComplex, CategoryTheory.Functor.flip,
    mappingCone.triangle_obj₁, mappingCone.triangle_obj₃, shiftLeft, shiftRight,
    CochainComplex.map₂CochainComplex_obj_commShiftIso_hom_app,
    CochainComplex.map₂CochainComplex_flip_obj_commShiftIso_hom_app] using e.symm

omit [SymmetricCategory D] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coneRight_δ (A : CochainComplex (D) ℤ)
    {X Y : CochainComplex (D) ℤ} (f : X ⟶ Y) :
    (coneRight D A f).hom ≫ (mappingCone.triangle (((total D).flip.obj A).map f)).mor₃ =
      ((total D).flip.obj A).map (mappingCone.triangle f).mor₃ ≫
        (shiftRight D A X 1).hom := by
  have e := (CochainComplex.map₂CochainComplexFlipObjMapMappingConeTriangleIso
    (tensor D) f A).hom.comm₃
  dsimp only [CochainComplex.map₂CochainComplexFlipObjMapMappingConeTriangleIso,
    Triangle.isoMk, Triangle.homMk, Functor.mapTriangle, Triangle.mk,
    Iso.refl_hom] at e
  simp only [CochainComplex.map₂CochainComplex_flip_obj_commShiftIso_hom_app] at e
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id, coneLeft, coneRight,
    total, CategoryTheory.Functor.map₂CochainComplex,
    CategoryTheory.Functor.map₂HomologicalComplex, CategoryTheory.Functor.flip,
    mappingCone.triangle_obj₁, mappingCone.triangle_obj₃, shiftLeft, shiftRight,
    CochainComplex.map₂CochainComplex_obj_commShiftIso_hom_app,
    CochainComplex.map₂CochainComplex_flip_obj_commShiftIso_hom_app] using e.symm

omit [HasBinaryBiproducts D] [SymmetricCategory D] in
private theorem homotopy_components
    (A X Y : CochainComplex D ℤ) (f g : X ⟶ Y) (h : Homotopy f g)
    (p q n : ℤ) (hpq : p + q = n) :
    (ι D A X p q n hpq ≫
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 A) h (tensor D) (.up ℤ)).hom
        n (n - 1) = p.negOnePow • (A.X p ◁ h.hom q (q - 1) ≫
          ι D A Y p (q - 1) (n - 1) (by omega))) ∧
    (ι D X A q p n (by omega) ≫
      (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 A) (tensor D) (.up ℤ)).hom
        n (n - 1) = h.hom q (q - 1) ▷ A.X p ≫
          ι D Y A (q - 1) p (n - 1) (by omega)) := by
  constructor
  · change CochainComplex.ιMapBifunctor A X (tensor D) p q n hpq ≫
        HomologicalComplex.mapBifunctorMapHomotopy.hom₂ (𝟙 A) h (tensor D)
          (.up ℤ) n (n - 1) = _
    rw [HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₂
      (𝟙 A) h (tensor D) (.up ℤ) p (q - 1) q n (n - 1) hpq
        ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (q - 1) q by
          change q - 1 + 1 = q
          omega)),
      HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ (by dsimp; omega)]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp]
    rfl
  · change CochainComplex.ιMapBifunctor X A (tensor D) q p n (by omega) ≫
        HomologicalComplex.mapBifunctorMapHomotopy.hom₁ h (𝟙 A) (tensor D)
          (.up ℤ) n (n - 1) = _
    rw [HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₁
      h (𝟙 A) (tensor D) (.up ℤ) (q - 1) q p n (n - 1)
        (by dsimp; omega)
        ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (q - 1) q by
          change q - 1 + 1 = q
          omega)),
      HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ (by dsimp; omega)]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp]
    change (1 : ℤˣ) • _ = _
    simp only [one_smul]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [SymmetricCategory D] in
private theorem cone_naturality
    (A X Y X' Y' : CochainComplex D ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f') :
    (((total D).obj A).map (mappingCone.map f f' a b comm) ≫ (coneLeft D A f').hom =
      (coneLeft D A f).hom ≫ mappingCone.map (((total D).obj A).map f)
        (((total D).obj A).map f') (((total D).obj A).map a) (((total D).obj A).map b)
        (by rw [← CategoryTheory.Functor.map_comp, comm, CategoryTheory.Functor.map_comp])) ∧
    (((total D).flip.obj A).map (mappingCone.map f f' a b comm) ≫
      (coneRight D A f').hom = (coneRight D A f).hom ≫
        mappingCone.map (((total D).flip.obj A).map f) (((total D).flip.obj A).map f')
          (((total D).flip.obj A).map a) (((total D).flip.obj A).map b)
          (by rw [← CategoryTheory.Functor.map_comp, comm, CategoryTheory.Functor.map_comp])) := by
  dsimp only [total, CategoryTheory.Functor.map₂CochainComplex,
    CategoryTheory.Functor.map₂HomologicalComplex, CategoryTheory.Functor.flip, coneLeft, coneRight,
    CochainComplex.mapBifunctorMappingCone₁Iso, CochainComplex.mapBifunctorMappingCone₂Iso]
  constructor
  · ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    dsimp at hpq
    simp only [HomologicalComplex.comp_f]
    apply mapCone_ext (D) ((tensor D).obj (A.X p)) f q
    · simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, curriedTensor, id_whiskerRight,
      HomologicalComplex.id_f, Category.id_comp]
      have e₁ := coneLeft_ι D A f' p q n hpq
      have e₂ := coneLeft_ι D A f p q n hpq
      dsimp only [ι, coneLeft, coneRight, total,
        CategoryTheory.Functor.map₂CochainComplex,
        CategoryTheory.Functor.map₂HomologicalComplex, CategoryTheory.Functor.flip,
        CochainComplex.mapBifunctorMappingCone₁Iso,
        CochainComplex.mapBifunctorMappingCone₂Iso] at e₁ e₂
      dsimp only [tensor, curriedTensor, CochainComplex.ιMapBifunctor] at e₁ e₂ ⊢
      rw [← whiskerLeft_comp_assoc, coneMap_inl D f f' a b comm q, whiskerLeft_comp]
      simp only [Category.assoc]
      rw [e₁, reassoc_of% e₂]
      simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc, coneMap_inl,
        HomologicalComplex.ι_mapBifunctorMap_assoc, id_whiskerRight, HomologicalComplex.id_f,
        Category.id_comp]
    · simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, curriedTensor, id_whiskerRight,
      HomologicalComplex.id_f, Category.id_comp]
      have e₁ := coneLeft_inr_ι D A f' p q n hpq
      have e₂ := coneLeft_inr_ι D A f p q n hpq
      dsimp only [ι, coneLeft, coneRight, total,
        CategoryTheory.Functor.map₂CochainComplex,
        CategoryTheory.Functor.map₂HomologicalComplex, CategoryTheory.Functor.flip,
        CochainComplex.mapBifunctorMappingCone₁Iso,
        CochainComplex.mapBifunctorMappingCone₂Iso] at e₁ e₂
      dsimp only [tensor, curriedTensor, CochainComplex.ιMapBifunctor] at e₁ e₂ ⊢
      rw [← whiskerLeft_comp_assoc, coneMap_inr D f f' a b comm q, whiskerLeft_comp]
      simp only [Category.assoc]
      rw [e₁, reassoc_of% e₂]
      simp only [coneMap_inr, HomologicalComplex.ι_mapBifunctorMap_assoc, id_whiskerRight,
        HomologicalComplex.id_f, Category.id_comp]
  · ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro q p hpq
    dsimp at hpq
    simp only [HomologicalComplex.comp_f]
    apply mapCone_ext (D) ((tensor D).flip.obj (A.X p)) f q
    all_goals dsimp only [CategoryTheory.Functor.flip]
    · simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, curriedTensor,
        whiskerLeft_id, HomologicalComplex.id_f, Category.id_comp]
      have e₁ := coneRight_ι D A f' p q n hpq
      have e₂ := coneRight_ι D A f p q n hpq
      dsimp only [ι, coneLeft, coneRight, total,
        CategoryTheory.Functor.map₂CochainComplex,
        CategoryTheory.Functor.map₂HomologicalComplex, CategoryTheory.Functor.flip,
        CochainComplex.mapBifunctorMappingCone₁Iso,
        CochainComplex.mapBifunctorMappingCone₂Iso] at e₁ e₂
      dsimp only [tensor, curriedTensor, CochainComplex.ιMapBifunctor] at e₁ e₂ ⊢
      rw [← comp_whiskerRight_assoc, coneMap_inl D f f' a b comm q,
        comp_whiskerRight, Category.assoc]
      rw [e₁, reassoc_of% e₂]
      simp only [coneMap_inl, HomologicalComplex.ι_mapBifunctorMap_assoc, whiskerLeft_id,
        HomologicalComplex.id_f, Category.id_comp]
    · simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, curriedTensor, whiskerLeft_id,
      HomologicalComplex.id_f, Category.id_comp]
      have e₁ := coneRight_inr_ι D A f' p q n hpq
      have e₂ := coneRight_inr_ι D A f p q n hpq
      dsimp only [ι, coneLeft, coneRight, total,
        CategoryTheory.Functor.map₂CochainComplex,
        CategoryTheory.Functor.map₂HomologicalComplex, CategoryTheory.Functor.flip,
        CochainComplex.mapBifunctorMappingCone₁Iso,
        CochainComplex.mapBifunctorMappingCone₂Iso] at e₁ e₂
      dsimp only [tensor, curriedTensor, CochainComplex.ιMapBifunctor] at e₁ e₂ ⊢
      rw [← comp_whiskerRight_assoc, coneMap_inr D f f' a b comm q,
        comp_whiskerRight, Category.assoc]
      rw [e₁, reassoc_of% e₂]
      simp only [coneMap_inr, HomologicalComplex.ι_mapBifunctorMap_assoc, whiskerLeft_id,
        HomologicalComplex.id_f, Category.id_comp]

private theorem kflat (A : CochainComplex D ℤ)
    (hA : ∀ F : CochainComplex D ℤ,
      F.Acyclic → (((total D).flip.obj A).obj F).Acyclic) :
    (∀ (X Y : CochainComplex D ℤ) (f : X ⟶ Y),
      QuasiIso f → QuasiIso (((total D).obj A).map f) ∧
        QuasiIso (((total D).flip.obj A).map f)) ∧
    ∀ n : ℤ, ∀ F : CochainComplex D ℤ,
      F.Acyclic → (((total D).flip.obj (A⟦n⟧)).obj F).Acyclic := by
  constructor
  · intro X Y f hf
    have hcone := hA (mappingCone f) ((mappingCone.quasiIso_iff_acyclic f).1 hf)
    have hright : QuasiIso (((total D).flip.obj A).map f) := by
      apply (mappingCone.quasiIso_iff_acyclic _).2
      intro n
      exact (hcone n).of_iso (coneRight D A f)
    refine ⟨?_, hright⟩
    apply (quasiIso_iff_of_arrow_mk_iso (((total D).obj A).map f)
      (((total D).flip.obj A).map f)
      (Arrow.isoMk (swap D A X) (swap D A Y) ?_)).2 hright
    exact (swap_naturality D X Y A A f (𝟙 A)).symm
  · intro n F hF i
    have h := hA F hF
    apply HomologicalComplex.ExactAt.of_iso
      (K := (((total D).obj F).obj A)⟦n⟧) (i := i) ?_ (shiftLeft D F A n).symm
    exact ShortComplex.exact_of_iso
      ((CochainComplex.shiftShortComplexFunctorIso D n i (n + i) rfl).app
        (((total D).obj F).obj A)).symm (h (n + i))

omit [HasBinaryBiproducts D] in
private theorem signed_swap :
    (∀ (A B : CochainComplex (D) ℤ),
      (swap D B A).inv = (swap D A B).hom ∧
      ∀ (i j n : ℤ) (hij : i + j = n),
        ι D B A i j n hij ≫
            (swap D B A).hom.f n =
          (i * j).negOnePow • ((β_ (B.X i) (A.X j)).hom ≫
            ι D A B j i n (by omega))) := by
  intro A B
  refine ⟨?_, fun i j n hij ↦ swap_ι (D) B A i j n hij⟩
  apply (cancel_mono (swap D B A).hom).1
  rw [Iso.inv_hom_id]
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  dsimp at hij
  simp only [HomologicalComplex.id_f, HomologicalComplex.comp_f]
  have e₁ := swap_ι_assoc (D) A B i j n hij ((swap D B A).hom.f n)
  have e₂ := swap_ι (D) B A j i n (by omega)
  dsimp only [ι, swap] at e₁ e₂
  rw [e₁]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [e₂]
  simp only [Linear.comp_units_smul, smul_smul, mul_comm i j, Int.units_mul_self, one_smul]
  simp only [SymmetricCategory.symmetry_assoc]
  exact Category.comp_id _

end Generic

/-- The signed homotopy, cone and interchange formulas for total sheaf tensor, its exactness
on K(R), preservation of arbitrary quasi-isomorphisms by K-flat factors, and shift stability.
The two cone isomorphisms and the swap are existing canonical constructions, so their
existence, inverses and chain identities are included in their types. -/
theorem totalTensorHomotopyConeSigns :
    (∀ A : CochainComplex (Modules R) ℤ,
      ((total R).obj A).Additive ∧ ((total R).flip.obj A).Additive ∧
      (((homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj A)).Additive ∧
        ((homotopyTensor R).flip.obj ((HomotopyCategory.quotient _ _).obj A)).Additive) ∧
      (((homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj A)).IsTriangulated ∧
        ((homotopyTensor R).flip.obj ((HomotopyCategory.quotient _ _).obj A)).IsTriangulated) ∧
      (NatTrans.CommShift ((tensor R).quotientCompBifunctorMapHomotopyObjIso
        (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ ∧
        NatTrans.CommShift ((tensor R).quotientCompBifunctorMapHomotopyFlipObjIso
          (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ)) ∧
    (∀ (A X Y : CochainComplex (Modules R) ℤ) (f g : X ⟶ Y) (h : Homotopy f g)
        (p q n : ℤ) (hpq : p + q = n),
      (ι R A X p q n hpq ≫
        (homotopyLeft R A h).hom n (n - 1) =
        p.negOnePow • (A.X p ◁ h.hom q (q - 1) ≫
          ι R A Y p (q - 1) (n - 1) (by omega))) ∧
      (ι R X A q p n (by omega) ≫
        (homotopyRight R A h).hom n (n - 1) =
        h.hom q (q - 1) ▷ A.X p ≫
          ι R Y A (q - 1) p (n - 1) (by omega))) ∧
    (∀ (A X Y : CochainComplex (Modules R) ℤ) (f : X ⟶ Y),
      (((total R).obj A).map (mappingCone.inr f) ≫ (coneLeft R A f).hom =
        mappingCone.inr (((total R).obj A).map f)) ∧
      (((total R).flip.obj A).map (mappingCone.inr f) ≫ (coneRight R A f).hom =
        mappingCone.inr (((total R).flip.obj A).map f)) ∧
      (∀ (p q n : ℤ) (hpq : p + q = n),
        (A.X p ◁ (mappingCone.inl f).v (q + 1) q (by omega) ≫
            ι R A (mappingCone f) p q n hpq ≫
            (coneLeft R A f).hom.f n =
          p.negOnePow • (ι R A X
            p (q + 1) (n + 1) (by omega) ≫
              (mappingCone.inl (((total R).obj A).map f)).v (n + 1) n (by omega))) ∧
        ((mappingCone.inl f).v (q + 1) q (by omega) ▷ A.X p ≫
            ι R (mappingCone f) A q p n (by omega) ≫
            (coneRight R A f).hom.f n =
          ι R X A (q + 1) p (n + 1) (by omega) ≫
            (mappingCone.inl (((total R).flip.obj A).map f)).v (n + 1) n (by omega))) ∧
      ((coneLeft R A f).hom ≫ (-(mappingCone.triangle (((total R).obj A).map f)).mor₃) =
        ((total R).obj A).map (-(mappingCone.triangle f).mor₃) ≫
          (shiftLeft R A X 1).hom) ∧
      ((coneRight R A f).hom ≫ (-(mappingCone.triangle (((total R).flip.obj A).map f)).mor₃) =
        ((total R).flip.obj A).map (-(mappingCone.triangle f).mor₃) ≫
          (shiftRight R A X 1).hom) ∧
      ((coneLeft R A f).hom ≫ (mappingCone.triangle (((total R).obj A).map f)).mor₃ =
        ((total R).obj A).map (mappingCone.triangle f).mor₃ ≫
          (shiftLeft R A X 1).hom) ∧
      ((coneRight R A f).hom ≫ (mappingCone.triangle (((total R).flip.obj A).map f)).mor₃ =
        ((total R).flip.obj A).map (mappingCone.triangle f).mor₃ ≫
          (shiftRight R A X 1).hom)) ∧
    (∀ (A X Y X' Y' : CochainComplex (Modules R) ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y')
        (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f'),
      (((total R).obj A).map (mappingCone.map f f' a b comm) ≫ (coneLeft R A f').hom =
        (coneLeft R A f).hom ≫ mappingCone.map (((total R).obj A).map f) (((total R).obj A).map f')
          (((total R).obj A).map a) (((total R).obj A).map b)
          (by rw [← Functor.map_comp, comm, Functor.map_comp])) ∧
      (((total R).flip.obj A).map (mappingCone.map f f' a b comm) ≫ (coneRight R A f').hom =
        (coneRight R A f).hom ≫
          mappingCone.map (((total R).flip.obj A).map f) (((total R).flip.obj A).map f')
          (((total R).flip.obj A).map a) (((total R).flip.obj A).map b)
          (by rw [← Functor.map_comp, comm, Functor.map_comp]))) ∧
    (∀ (A B : CochainComplex (Modules R) ℤ),
      (swap R B A).inv = (swap R A B).hom ∧
      ∀ (i j n : ℤ) (hij : i + j = n),
        ι R B A i j n hij ≫
            (swap R B A).hom.f n =
          (i * j).negOnePow • ((β_ (B.X i) (A.X j)).hom ≫
            ι R A B j i n (by omega))) ∧
    (∀ (A A' B B' : CochainComplex (Modules R) ℤ) (a : A ⟶ A') (b : B ⟶ B'),
      HomologicalComplex.mapBifunctorMap b a (tensor R) (.up ℤ) ≫
          (swap R B' A').hom =
        (swap R B A).hom ≫
          HomologicalComplex.mapBifunctorMap a b (tensor R) (.up ℤ)) ∧
    (∀ (A : CochainComplex (Modules R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients A →
        (∀ (X Y : CochainComplex (Modules R) ℤ) (f : X ⟶ Y),
          QuasiIso f → QuasiIso (((total R).obj A).map f) ∧
            QuasiIso (((total R).flip.obj A).map f)) ∧
        ∀ n : ℤ, CochainComplex.IsKFlatIndependentCoefficients (A⟦n⟧)) ∧
    (∀ (A : CochainComplex (Modules R) ℤ),
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (A.X i)) →
        ∀ n i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) ((A⟦n⟧).X i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    refine ⟨?_, ?_, ⟨inferInstance, inferInstance⟩,
      ⟨inferInstance, inferInstance⟩, inferInstance, inferInstance⟩
    · infer_instance
    · infer_instance
  · exact Generic.homotopy_components (Modules R)
  · intro A X Y f
    have hL : (coneLeft R A f).hom ≫
        (mappingCone.triangle (((total R).obj A).map f)).mor₃ =
        ((total R).obj A).map (mappingCone.triangle f).mor₃ ≫
          (shiftLeft R A X 1).hom := Generic.coneLeft_δ (Modules R) A f
    have hR : (coneRight R A f).hom ≫
        (mappingCone.triangle (((total R).flip.obj A).map f)).mor₃ =
        ((total R).flip.obj A).map (mappingCone.triangle f).mor₃ ≫
          (shiftRight R A X 1).hom := Generic.coneRight_δ (Modules R) A f
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact CochainComplex.mapBifunctorMap_inr_mapBifunctorMappingCone₂Iso_hom A f
        (tensor R)
    · exact CochainComplex.mapBifunctorMap_inr_mapBifunctorMappingCone₁Iso_hom f A
        (tensor R)
    · intro p q n hpq
      constructor
      · exact Generic.coneLeft_ι (Modules R) A f p q n hpq
      · exact Generic.coneRight_ι (Modules R) A f p q n (by omega)
    · simpa only [CategoryTheory.Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp]
        using congrArg Neg.neg hL
    · simpa only [CategoryTheory.Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp]
        using congrArg Neg.neg hR
    · exact hL
    · exact hR
  · exact Generic.cone_naturality (Modules R)
  · exact Generic.signed_swap (Modules R)
  · exact Generic.swap_naturality (Modules R)
  · exact Generic.kflat (Modules R)
  · intro A h n i
    exact h (i + n)

end SheafOfModules.TotalTensorSigns
