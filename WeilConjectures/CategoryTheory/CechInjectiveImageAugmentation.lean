/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CoherentCechImageModel
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.RingedSheafSliceAdjunction
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleNerveAcyclic
import WeilConjectures.CategoryTheory.Sites.PresheafCechComplex
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.RegularEpi
import WeilConjectures.CategoryTheory.ElementModulePresheafExtension
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.CategoryTheory.ElementSiteDescent
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Yoneda

/-! # Injective Čech rows and their direct-image total augmentation

Source: Stacks Project, sites-cohomology.tex, Tag 03FC; sites-modules.tex,
Tags 04IE and 04J4; homology.tex, Tag 0133, second-variable variant.
(blueprint: lem-sfb-cech-injective-image-augmentation).

The existing coherent localization model fixes all restriction maps and units.
The section comparison below is characterized on free generators by the actual
module adjunction, after sheafification, Yoneda and the geometric adjunction.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CechInjectiveImage

variable {C X : Type u} [SmallCategory C] [SmallCategory X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}

/-- The inverse image of the sheafified representable of a target site object.
Source: Stacks 03FC, evaluation adjunctions
(blueprint: lem-sfb-cech-injective-image-augmentation). -/
def testObject {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (W : X) : Sheaf J (Type u) :=
  f.inverse.obj ((presheafToSheaf K (Type u)).obj (yoneda.obj W))

/-- Evaluation of the underlying abelian sheaf of a module.
Source: Stacks 03FC (blueprint: lem-sfb-cech-injective-image-augmentation). -/
def evaluate (S : Sheaf K RingCat.{u}) (W : X) :
    ringedSiteModules.{u} S ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf S ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
    (evaluation Xᵒᵖ AddCommGrpCat.{u}).obj (op W)

/-- Free abelian presheaves on sheaves of sets, using Mathlib's free functor.
Source: Stacks 03FC, free-abelian interpretation of sections
(blueprint: lem-sfb-cech-injective-image-augmentation). -/
def freeAbelian : Sheaf J (Type u) ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf J (Type u) ⋙
    (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free

/-- Sections over an arbitrary sheaf object, encoded by free abelian adjunction.
These are maps from that sheaf to the underlying set sheaf of the module.
Source: Stacks 03FC (blueprint: lem-sfb-cech-injective-image-augmentation). -/
def sections (R : Sheaf J RingCat.{u}) (M : ringedSiteModules.{u} R) :
    (Sheaf J (Type u))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  freeAbelian.op ⋙ preadditiveYoneda.obj M.val.presheaf

/-- Postcomposition on sections, induced by the actual module morphism.
Source: Stacks 03FC (blueprint: lem-sfb-cech-injective-image-augmentation). -/
def sectionsMap {R : Sheaf J RingCat.{u}} {M N : ringedSiteModules.{u} R}
    (g : M ⟶ N) : sections R M ⟶ sections R N :=
  Functor.whiskerLeft freeAbelian.op
    (preadditiveYoneda.map ((PresheafOfModules.toPresheaf R.obj).map g.val))

/-- The free module sheaf on a sheaf object, by the existing free and sheafification functors.
Source: Stacks 03FC (blueprint: lem-sfb-cech-injective-image-augmentation). -/
def freeModule (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) :
    ringedSiteModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj A.obj)

/-- The universal generator in the free module sheaf, including its sheafification unit.
Source: Stacks 03FC (blueprint: lem-sfb-cech-injective-image-augmentation). -/
def generator (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    (U : Cᵒᵖ) (a : A.obj.obj U) : (freeModule R A).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
    ((PresheafOfModules.free R.obj).obj A.obj)).app U (ModuleCat.freeMk a)

/-- Linearization through the free-module and module-sheafification adjunctions.
Source: Stacks 03FC (blueprint: lem-sfb-cech-injective-image-augmentation). -/
def linearize (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    (M : ringedSiteModules.{u} R)
    (z : A ⟶ (sheafCompose J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M)) : freeModule R A ⟶ M :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
    (PresheafOfModules.freeObjDesc z.hom)

/-- A target section transposed by sheafification, Yoneda and the geometric adjunction.
Source: Stacks 03FC and 001P (blueprint: lem-sfb-cech-injective-image-augmentation). -/
def transpose {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (W : X) (M : ringedSiteModules.{u} R)
    (x : (f.modules.obj M).val.obj (op W)) :
    testObject f W ⟶ (sheafCompose J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M) :=
  (f.adj.homEquiv _ _).symm
    (((sheafificationAdjunction K (Type u)).homEquiv (yoneda.obj W)
      ((sheafCompose K (forget AddCommGrpCat)).obj
        ((SheafOfModules.toSheaf S).obj (f.modules.obj M)))).symm
      (yonedaEquiv.symm x) ≫ f.underlying.hom.app M)

/-- The actual cosimplicial row evaluated at a target site object.
Source: Stacks 03FC (blueprint: lem-sfb-cech-injective-image-augmentation). -/
def row {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R) :
    CosimplicialObject AddCommGrpCat.{u} :=
  (((sheafCoverNerve V).rightOp ⋙ D.image).flip.obj M) ⋙ f.modules ⋙ evaluate S W

/-- Sections of the restricted module over the powers of `V × A → A` in the slice.
Relocalization identifies these with sections of `M` over `A × V_n` in the original topos.
Source: Stacks 03FC, 04IE and 04J4
(blueprint: lem-sfb-cech-injective-image-augmentation). -/
def sliceRow {R : Sheaf J RingCat.{u}} (V A : Sheaf J (Type u))
    (M : ringedSiteModules.{u} R) : CosimplicialObject AddCommGrpCat.{u} :=
  (sheafCoverNerve V ⋙ prod.functor.obj A).rightOp ⋙ sections R M

/-- The alternating evaluated row, using the specified Čech cofaces.
Source: Stacks 03FC (blueprint: lem-sfb-cech-injective-image-augmentation). -/
def rowComplex {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (row f D V W M)

/-- The degree-zero localization unit on target sections.
Source: Stacks 03FC (blueprint: lem-sfb-cech-injective-image-augmentation). -/
def augment {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R) :
    (evaluate S W).obj (f.modules.obj M) ⟶ (rowComplex f D V W M).X 0 :=
  (evaluate S W).map
    (f.modules.map ((D.augmentation ((sheafCoverNerve V).obj (op (.mk 0)))).app M))

/-- A section of a Čech direct-image term, transposed through the localization adjunction.
The result is evaluated on the universal generator; this fixes the section comparison
uniquely, rather than allowing an arbitrary equivalence of cochain groups.
Source: Stacks 03FC and 04IE (blueprint: lem-sfb-cech-injective-image-augmentation). -/
def localizedTranspose {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R) (n : ℕ)
    (x : (row f D V W M).obj (.mk n))
    (U : Cᵒᵖ)
    (z : ((testObject f W) ⨯ ((sheafCoverNerve V).obj (op (.mk n)))).obj.obj U) :
    M.val.obj U :=
  (((D.adj ((sheafCoverNerve V).obj (op (.mk n)))).homEquiv _ _).symm
    (linearize R (testObject f W) _ (transpose f W _ x) ≫
      (D.imageIso ((sheafCoverNerve V).obj (op (.mk n)))).hom.app M)).val.app
        (elementObj ((sheafCoverNerve V).obj (op (.mk n))) U
          ((prod.snd : (testObject f W) ⨯
            ((sheafCoverNerve V).obj (op (.mk n))) ⟶ _).hom.app U z))
        (generator R (testObject f W) U
          ((prod.fst : (testObject f W) ⨯
            ((sheafCoverNerve V).obj (op (.mk n))) ⟶ _).hom.app U z))

/-- The complete row, total-augmentation and transpose-sign assertions.
Source: Stacks 03FC, 04IE, 04J4 and 0133
(blueprint: lem-sfb-cech-injective-image-augmentation). -/
structure ExactAugmentation {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [HasDerivedCategory.{w} (ringedSiteModules.{u} S)]
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ) : Prop where
  /-- Restriction of every injective term to each evaluation slice is injective. -/
  injective_slice : ∀ (W : X) (q : ℕ),
    Injective ((elementModulePullback R (testObject f W)).obj (I.X q))
  /-- The adjunction-induced section identifications, including every face and degeneracy. -/
  sections_identification : ∀ W : X,
    ∃ e : ∀ q : ℕ, row f D V W (I.X q) ≅ sliceRow V (testObject f W) (I.X q),
      (∀ (q n : ℕ) (x : (row f D V W (I.X q)).obj (.mk n)) (U : Cᵒᵖ)
        (z : ((testObject f W) ⨯ ((sheafCoverNerve V).obj (op (.mk n)))).obj.obj U),
        (((e q).hom.app (.mk n)) x).app U (FreeAbelianGroup.of z) =
          localizedTranspose f D V W (I.X q) n x U z) ∧
      (∀ (q r n : ℕ) (x : (row f D V W (I.X q)).obj (.mk n)),
        (e r).hom.app (.mk n)
          ((f.modules.map ((D.image.obj (op ((sheafCoverNerve V).obj (op (.mk n))))).map
            (I.d q r))).val.app (op W) x) =
          (sectionsMap (I.d q r)).app
            (op ((testObject f W) ⨯ ((sheafCoverNerve V).obj (op (.mk n)))))
              ((e q).hom.app (.mk n) x)) ∧
      (∀ (q : ℕ) (x : (f.modules.obj (I.X q)).val.obj (op W)) (U : Cᵒᵖ)
        (z : ((testObject f W) ⨯ ((sheafCoverNerve V).obj (op (.mk 0)))).obj.obj U),
        (((e q).hom.app (.mk 0)) (augment f D V W (I.X q) x)).app U
          (FreeAbelianGroup.of z) =
            (transpose f W (I.X q) x).hom.app U
              ((prod.fst : (testObject f W) ⨯
                ((sheafCoverNerve V).obj (op (.mk 0))) ⟶ _).hom.app U z))
  /-- Injectivity at the left, the degree-zero kernel/image, and higher row vanishing. -/
  sectionwise_exact : ∀ (W : X) (q : ℕ),
    Function.Injective (augment f D V W (I.X q)) ∧
    Function.Exact (augment f D V W (I.X q)) ((rowComplex f D V W (I.X q)).d 0 1) ∧
    ∀ n : ℕ, IsZero ((rowComplex f D V W (I.X q)).homology (n + 1))
  /-- Exact augmented rows in the abelian category of module sheaves. -/
  sheaf_rows : ∀ q : ℕ,
    ∃ a : (CochainComplex.single₀ (ringedSiteModules.{u} S)).obj
        (f.modules.obj (I.X q)) ⟶
          (f.modules.mapHomologicalComplex (.up ℕ)).obj ((D.cochains V).obj (I.X q)),
      a.f 0 = f.modules.map
        ((D.augmentation ((sheafCoverNerve V).obj (op (.mk 0)))).app (I.X q)) ∧ QuasiIso a
  /-- The specified unit total augmentation and its ordinary derived localization. -/
  total_augmentation :
    ∃ b : (f.modules.mapHomologicalComplex (.up ℕ)).obj I ⟶
        (D.bicomplex f.modules V I).total (.up ℕ),
      D.IsAugmentation f.modules V I b ∧ QuasiIso b ∧
      IsIso (DerivedCategory.Q.map (HomologicalComplex.extendMap b ComplexShape.embeddingUpNat))
  /-- The canonical chain isomorphism has the sign (-1)^(nq) on every summand. -/
  transpose_sign : ∀ n q : ℕ,
    (D.bicomplex f.modules V I).ιTotal (.up ℕ) n q (n + q) rfl ≫
        ((D.bicomplex f.modules V I).totalFlipIso (.up ℕ)).inv.f (n + q) =
      (-1 : ℤ) ^ (n * q) •
        (D.bicomplex f.modules V I).flip.ιTotal (.up ℕ) q n (n + q) (Nat.add_comm q n)
  /-- On every augmentation summand the transpose is the identity. -/
  transpose_augmentation : ∀ q : ℕ,
    (D.bicomplex f.modules V I).ιTotal (.up ℕ) 0 q q (zero_add q) ≫
        ((D.bicomplex f.modules V I).totalFlipIso (.up ℕ)).inv.f q =
      (D.bicomplex f.modules V I).flip.ιTotal (.up ℕ) q 0 q (add_zero q)

private theorem moduleFiniteLimits (R : Sheaf J RingCat.{u}) :
    HasFiniteLimits (ringedSiteModules.{u} R) := inferInstance

private theorem moduleFiniteColimits (R : Sheaf J RingCat.{u}) :
    HasFiniteColimits (ringedSiteModules.{u} R) := inferInstance

private theorem sheafFiniteLimits : HasFiniteLimits (Sheaf J (Type u)) := inferInstance

attribute [local instance] moduleFiniteLimits moduleFiniteColimits sheafFiniteLimits

private theorem moduleShortHomology (R : Sheaf J RingCat.{u})
    (S : ShortComplex (ringedSiteModules.{u} R)) : S.HasHomology := inferInstance

private theorem abelianShortHomology (S : ShortComplex AddCommGrpCat.{u}) :
    S.HasHomology := inferInstance

private theorem moduleNatTotal (R : Sheaf J RingCat.{u})
    (B : HomologicalComplex₂ (ringedSiteModules.{u} R) (.up ℕ) (.up ℕ)) :
    B.HasTotal (.up ℕ) := inferInstance

attribute [local instance] moduleShortHomology abelianShortHomology moduleNatTotal

private instance evaluate_additive (S : Sheaf K RingCat.{u}) (W : X) :
    (evaluate S W).Additive := by
  dsimp only [evaluate]
  infer_instance

private theorem natural_map_add {E : Type*} [Category E] [Preadditive E]
    [HasBinaryBiproducts E] (F G : E ⥤ AddCommGrpCat.{u}) [F.Additive] [G.Additive]
    (t : ∀ M : E, F.obj M → G.obj M)
    (ht : ∀ {M N : E} (g : M ⟶ N) (x : F.obj M),
      t N (F.map g x) = G.map g (t M x))
    (M : E) (x y : F.obj M) : t M (x + y) = t M x + t M y := by
  let z : F.obj (M ⊞ M) := F.map biprod.inl x + F.map biprod.inr y
  have hfst : F.map (biprod.fst : M ⊞ M ⟶ M) z = x := by
    simp [z, ← ConcreteCategory.comp_apply, ← F.map_comp]
  have hsnd : F.map (biprod.snd : M ⊞ M ⟶ M) z = y := by
    simp [z, ← ConcreteCategory.comp_apply, ← F.map_comp]
  have hsum : F.map (biprod.fst + biprod.snd : M ⊞ M ⟶ M) z = x + y := by
    rw [F.map_add]
    exact congrArg₂ (· + ·) hfst hsnd
  rw [← hsum, ht, G.map_add]
  change G.map biprod.fst (t (M ⊞ M) z) + G.map biprod.snd (t (M ⊞ M) z) = _
  rw [← ht, ← ht, hfst, hsnd]

private def sectionProductIso (A B : Sheaf J (Type u)) (U : Cᵒᵖ) :
    (A ⨯ B).obj.obj U ≅ A.obj.obj U × B.obj.obj U :=
  (PreservesLimitPair.iso
    (sheafToPresheaf J (Type u) ⋙ (evaluation Cᵒᵖ (Type u)).obj U) A B) ≪≫
      Types.binaryProductIso _ _

private theorem sectionProductIso_fst (A B : Sheaf J (Type u)) (U : Cᵒᵖ) :
    (sectionProductIso A B U).hom ≫ ↾_root_.Prod.fst =
      (prod.fst : A ⨯ B ⟶ A).hom.app U := by
  simp only [sectionProductIso, Iso.trans_hom, Category.assoc,
    PreservesLimitPair.iso_hom]
  exact prodComparison_fst _ _ _

private theorem sectionProductIso_snd (A B : Sheaf J (Type u)) (U : Cᵒᵖ) :
    (sectionProductIso A B U).hom ≫ ↾_root_.Prod.snd =
      (prod.snd : A ⨯ B ⟶ B).hom.app U := by
  simp only [sectionProductIso, Iso.trans_hom, Category.assoc,
    PreservesLimitPair.iso_hom]
  exact prodComparison_snd _ _ _

attribute [irreducible] sectionProductIso

private def sectionPair (A B : Sheaf J (Type u)) (U : Cᵒᵖ)
    (a : A.obj.obj U) (b : B.obj.obj U) : (A ⨯ B).obj.obj U :=
  (sectionProductIso A B U).inv (a, b)

private theorem sectionPair_fst (A B : Sheaf J (Type u)) (U : Cᵒᵖ)
    (a : A.obj.obj U) (b : B.obj.obj U) :
    (prod.fst : A ⨯ B ⟶ A).hom.app U (sectionPair A B U a b) = a := by
  change ((sectionProductIso A B U).inv ≫ (prod.fst : A ⨯ B ⟶ A).hom.app U) (a, b) = a
  rw [← sectionProductIso_fst, Iso.inv_hom_id_assoc]
  rfl

private theorem sectionPair_snd (A B : Sheaf J (Type u)) (U : Cᵒᵖ)
    (a : A.obj.obj U) (b : B.obj.obj U) :
    (prod.snd : A ⨯ B ⟶ B).hom.app U (sectionPair A B U a b) = b := by
  change ((sectionProductIso A B U).inv ≫ (prod.snd : A ⨯ B ⟶ B).hom.app U) (a, b) = b
  rw [← sectionProductIso_snd, Iso.inv_hom_id_assoc]
  rfl

private theorem sectionPair_eta (A B : Sheaf J (Type u)) (U : Cᵒᵖ)
    (z : (A ⨯ B).obj.obj U) :
    sectionPair A B U ((prod.fst : A ⨯ B ⟶ A).hom.app U z)
      ((prod.snd : A ⨯ B ⟶ B).hom.app U z) = z := by
  have he : (sectionProductIso A B U).hom z =
      ((prod.fst : A ⨯ B ⟶ A).hom.app U z,
        (prod.snd : A ⨯ B ⟶ B).hom.app U z) := by
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (sectionProductIso_fst A B U) z
    · exact ConcreteCategory.congr_hom (sectionProductIso_snd A B U) z
  change (sectionProductIso A B U).inv _ = z
  rw [← he]
  exact ConcreteCategory.congr_hom (sectionProductIso A B U).hom_inv_id z

private theorem sectionPair_map (A B : Sheaf J (Type u)) {U T : Cᵒᵖ}
    (g : U ⟶ T) (a : A.obj.obj U) (b : B.obj.obj U) :
    (A ⨯ B).obj.map g (sectionPair A B U a b) =
      sectionPair A B T (A.obj.map g a) (B.obj.map g b) := by
  rw [← sectionPair_eta A B T ((A ⨯ B).obj.map g (sectionPair A B U a b))]
  congr 1
  · rw [NatTrans.naturality_apply, sectionPair_fst]
  · rw [NatTrans.naturality_apply, sectionPair_snd]

attribute [irreducible] sectionPair

private def restrictedFreeUnit (R : Sheaf J RingCat.{u})
    (A B : Sheaf J (Type u)) :
    (PresheafOfModules.free (elementRing R B).obj).obj
      ((elementProjection B).op ⋙ A.obj) ⟶
        ((elementModulePullback R B).obj (freeModule R A)).val :=
  (PresheafOfModules.pushforward (F := elementProjection B)
    (𝟙 (elementRing R B).obj)).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
        ((PresheafOfModules.free R.obj).obj A.obj))

private theorem restrictedFreeUnit_locallyInjective (R : Sheaf J RingCat.{u})
    (A B : Sheaf J (Type u)) :
    PresheafOfModules.IsLocallyInjective (elementTopology B) (restrictedFreeUnit R A B) := by
  have := (element_site_descent B).2.1
  exact Presheaf.isLocallyInjective_whisker (elementTopology B) J
    (elementProjection B) (toSheafify J ((PresheafOfModules.free R.obj).obj A.obj).presheaf)

private theorem restrictedFreeUnit_locallySurjective (R : Sheaf J RingCat.{u})
    (A B : Sheaf J (Type u)) :
    PresheafOfModules.IsLocallySurjective (elementTopology B) (restrictedFreeUnit R A B) := by
  have := (element_site_descent B).2.1
  exact Presheaf.isLocallySurjective_whisker (elementTopology B) J
    (elementProjection B) (toSheafify J ((PresheafOfModules.free R.obj).obj A.obj).presheaf)

private def elementProductEquiv (A B F : Sheaf J (Type u)) :
    (((elementProjection B).op ⋙ A.obj) ⟶ (elementProjection B).op ⋙ F.obj) ≃
      (A ⨯ B ⟶ F) where
  toFun h := ⟨{
    app U := ↾fun z ↦ h.app (elementObj B U ((prod.snd : A ⨯ B ⟶ B).hom.app U z))
      ((prod.fst : A ⨯ B ⟶ A).hom.app U z)
    naturality U T g := by
      ext z
      change h.app (elementObj B T ((prod.snd : A ⨯ B ⟶ B).hom.app T
          ((A ⨯ B).obj.map g z)))
          ((prod.fst : A ⨯ B ⟶ A).hom.app T ((A ⨯ B).obj.map g z)) =
        F.obj.map g (h.app
          (elementObj B U ((prod.snd : A ⨯ B ⟶ B).hom.app U z))
          ((prod.fst : A ⨯ B ⟶ A).hom.app U z))
      erw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact NatTrans.naturality_apply h (elementObjMap B g
        ((prod.snd : A ⨯ B ⟶ B).hom.app U z))
          ((prod.fst : A ⨯ B ⟶ A).hom.app U z) }⟩
  invFun z := {
    app e := ↾fun a ↦ z.hom.app e.unop.unop.1
      (sectionPair A B e.unop.unop.1 a e.unop.unop.2)
    naturality e d g := by
      ext a
      change z.hom.app d.unop.unop.1
        (sectionPair A B d.unop.unop.1 (A.obj.map g.unop.unop.1 a) d.unop.unop.2) =
          F.obj.map g.unop.unop.1
            (z.hom.app e.unop.unop.1 (sectionPair A B e.unop.unop.1 a e.unop.unop.2))
      erw [← NatTrans.naturality_apply z.hom, sectionPair_map]
      exact congrArg (fun b ↦ z.hom.app d.unop.unop.1
        (sectionPair A B d.unop.unop.1 (A.obj.map g.unop.unop.1 a) b))
          g.unop.unop.2.symm }
  left_inv h := by
    ext e a
    change h.app (elementObj B e.unop.unop.1
      ((prod.snd : A ⨯ B ⟶ B).hom.app e.unop.unop.1
        (sectionPair A B e.unop.unop.1 a e.unop.unop.2)))
      ((prod.fst : A ⨯ B ⟶ A).hom.app e.unop.unop.1
        (sectionPair A B e.unop.unop.1 a e.unop.unop.2)) = h.app e a
    rw [sectionPair_snd, sectionPair_fst]
    rfl
  right_inv z := by
    ext U t
    change z.hom.app U (sectionPair A B U _ _) = z.hom.app U t
    rw [sectionPair_eta]

private def restrictedSectionEquiv (R : Sheaf J RingCat.{u})
    (A B : Sheaf J (Type u)) (M : ringedSiteModules.{u} R) :
    (((elementProjection B).op ⋙ A.obj) ⟶
      ((elementModulePullback R B).obj M).val.presheaf ⋙ forget AddCommGrpCat) ≃
    (A ⨯ B ⟶ (sheafCompose J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M)) :=
  elementProductEquiv A B ((sheafCompose J (forget AddCommGrpCat)).obj
    ((SheafOfModules.toSheaf R).obj M))

private theorem restrictedSectionEquiv_apply (R : Sheaf J RingCat.{u})
    (A B : Sheaf J (Type u)) (M : ringedSiteModules.{u} R)
    (h : ((elementProjection B).op ⋙ A.obj) ⟶
      ((elementModulePullback R B).obj M).val.presheaf ⋙ forget AddCommGrpCat)
    (U : Cᵒᵖ) (z : (A ⨯ B).obj.obj U) :
    (restrictedSectionEquiv R A B M h).hom.app U z =
      h.app (elementObj B U ((prod.snd : A ⨯ B ⟶ B).hom.app U z))
        ((prod.fst : A ⨯ B ⟶ A).hom.app U z) := rfl

attribute [irreducible] restrictedSectionEquiv

private def localizedSectionEquiv (R : Sheaf J RingCat.{u})
    (D : CoherentCechImageModel R) (A B : Sheaf J (Type u))
    (M : ringedSiteModules.{u} R) :
    (freeModule R A ⟶ (D.image.obj (op B)).obj M) ≃
      (sections R M).obj (op (A ⨯ B)) := by
  have := restrictedFreeUnit_locallyInjective R A B
  have := restrictedFreeUnit_locallySurjective R A B
  exact (Iso.homCongr (Iso.refl _) ((D.imageIso B).app M)).trans
    (((D.adj B).homEquiv _ _).symm.trans
      ((SheafOfModules.fullyFaithfulForget _).homEquiv.trans
        ((PresheafOfModules.homEquivOfIsLocallyBijective
          (restrictedFreeUnit R A B) ((elementModulePullback R B).obj M).isSheaf).trans
          (PresheafOfModules.freeHomEquiv.trans
            ((restrictedSectionEquiv R A B M).trans
              (((fullyFaithfulSheafToPresheaf J (Type u)).homEquiv).trans
                ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).symm))))))

private theorem localizedSectionEquiv_apply (R : Sheaf J RingCat.{u})
    (D : CoherentCechImageModel R) (A B : Sheaf J (Type u))
    (M : ringedSiteModules.{u} R) (t : freeModule R A ⟶ (D.image.obj (op B)).obj M)
    (U : Cᵒᵖ) (z : (A ⨯ B).obj.obj U) :
    (localizedSectionEquiv R D A B M t).app U (FreeAbelianGroup.of z) =
      (((D.adj B).homEquiv _ _).symm (t ≫ (D.imageIso B).hom.app M)).val.app
        (elementObj B U ((prod.snd : A ⨯ B ⟶ B).hom.app U z))
        (generator R A U ((prod.fst : A ⨯ B ⟶ A).hom.app U z)) := by
  have h := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv
    (A ⨯ B).obj M.val.presheaf).apply_symm_apply
    (((restrictedSectionEquiv R A B M)
      (PresheafOfModules.freeHomEquiv
        (restrictedFreeUnit R A B ≫
          (((D.adj B).homEquiv _ _).symm
            (t ≫ (D.imageIso B).hom.app M)).val))).hom)
  rw [Adjunction.homEquiv_unit] at h
  have he := congrArg (fun k ↦ k.app U z) h
  exact he.trans (restrictedSectionEquiv_apply R A B M _ U z)

attribute [irreducible] localizedSectionEquiv

private def localizedSectionAddEquiv (R : Sheaf J RingCat.{u})
    (D : CoherentCechImageModel R) (A B : Sheaf J (Type u))
    (M : ringedSiteModules.{u} R) :
    (freeModule R A ⟶ (D.image.obj (op B)).obj M) ≃+
      (sections R M).obj (op (A ⨯ B)) where
  toEquiv := localizedSectionEquiv R D A B M
  map_add' t s := by
    have : (elementModulePullback.{u, u} R B).Additive := ⟨by intros; rfl⟩
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro z
    change (localizedSectionEquiv R D A B M (t + s)).app U (FreeAbelianGroup.of z) =
      (localizedSectionEquiv R D A B M t).app U (FreeAbelianGroup.of z) +
        (localizedSectionEquiv R D A B M s).app U (FreeAbelianGroup.of z)
    refine (localizedSectionEquiv_apply R D A B M (t + s) U z).trans ?_
    refine Eq.trans ?_ (congrArg₂ (fun x y ↦ x + y)
      (localizedSectionEquiv_apply R D A B M t U z).symm
      (localizedSectionEquiv_apply R D A B M s U z).symm)
    rw [Preadditive.add_comp, Adjunction.homAddEquiv_symm_add]
    rfl

set_option backward.isDefEq.respectTransparency true in
private theorem localizedSectionEquiv_naturality
    (R : Sheaf J RingCat.{u}) (D : CoherentCechImageModel R)
    (A B : Sheaf J (Type u)) {M N : ringedSiteModules.{u} R}
    (g : M ⟶ N) (t : freeModule R A ⟶ (D.image.obj (op B)).obj M) :
    localizedSectionEquiv R D A B N (t ≫ (D.image.obj (op B)).map g) =
      (sectionsMap g).app (op (A ⨯ B)) (localizedSectionEquiv R D A B M t) := by
  have : (elementModulePullback.{u, u} R B).Additive := ⟨by intros; rfl⟩
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro z
  change (localizedSectionEquiv R D A B N (t ≫ (D.image.obj (op B)).map g)).app U
    (FreeAbelianGroup.of z) =
      g.val.app U ((localizedSectionEquiv R D A B M t).app U (FreeAbelianGroup.of z))
  refine (localizedSectionEquiv_apply R D A B N
    (t ≫ (D.image.obj (op B)).map g) U z).trans ?_
  refine Eq.trans ?_ (congrArg (fun x ↦ g.val.app U x)
    (localizedSectionEquiv_apply R D A B M t U z).symm)
  have h : (((D.image.obj (op B)).map g) ≫ (D.imageIso B).hom.app N) =
      (D.imageIso B).hom.app M ≫ (D.push B).map ((elementModulePullback R B).map g) :=
    (D.imageIso B).hom.naturality g
  have ht : ((D.adj B).homEquiv _ _).symm
      ((t ≫ (D.image.obj (op B)).map g) ≫ (D.imageIso B).hom.app N) =
      ((D.adj B).homEquiv _ _).symm (t ≫ (D.imageIso B).hom.app M) ≫
        (elementModulePullback R B).map g := by
    rw [Category.assoc, h, ← Category.assoc, (D.adj B).homEquiv_naturality_right_symm]
  exact congrArg (fun k ↦ k.val.app
    (elementObj B U ((prod.snd : A ⨯ B ⟶ B).hom.app U z))
    (generator R A U ((prod.fst : A ⨯ B ⟶ A).hom.app U z))) ht

set_option backward.isDefEq.respectTransparency true in
private theorem localizedSectionEquiv_restriction
    (R : Sheaf J RingCat.{u}) (D : CoherentCechImageModel R)
    (A : Sheaf J (Type u)) {B B' : Sheaf J (Type u)} (b : B' ⟶ B)
    (M : ringedSiteModules.{u} R) (t : freeModule R A ⟶ (D.image.obj (op B)).obj M) :
    localizedSectionEquiv R D A B' M (t ≫ (D.image.map b.op).app M) =
      (sections R M).map (prod.map (𝟙 A) b).op
        (localizedSectionEquiv R D A B M t) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro z
  change (localizedSectionEquiv R D A B' M (t ≫ (D.image.map b.op).app M)).app U
    (FreeAbelianGroup.of z) =
      (localizedSectionEquiv R D A B M t).app U
        ((AddCommGrpCat.free.map ((prod.map (𝟙 A) b).hom.app U)) (FreeAbelianGroup.of z))
  rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of]
  refine (localizedSectionEquiv_apply R D A B' M
    (t ≫ (D.image.map b.op).app M) U z).trans ?_
  refine Eq.trans ?_ (localizedSectionEquiv_apply R D A B M t U
    ((prod.map (𝟙 A) b).hom.app U z)).symm
  rw [Category.assoc, (D.adj B').homEquiv_naturality_left_symm, D.restriction]
  rw [(D.adj B).homEquiv_naturality_left_symm]
  have hfst : (prod.fst : A ⨯ B ⟶ A).hom.app U ((prod.map (𝟙 A) b).hom.app U z) =
      (prod.fst : A ⨯ B' ⟶ A).hom.app U z := by
    exact congrArg (fun k ↦ k.hom.app U z) (by simp :
      prod.map (𝟙 A) b ≫ prod.fst = (prod.fst : A ⨯ B' ⟶ A))
  have hsnd : (prod.snd : A ⨯ B ⟶ B).hom.app U ((prod.map (𝟙 A) b).hom.app U z) =
      b.hom.app U ((prod.snd : A ⨯ B' ⟶ B').hom.app U z) := by
    exact congrArg (fun k ↦ k.hom.app U z) (prod.map_snd (𝟙 A) b)
  rw [hfst, hsnd]
  rfl

private def freeModuleHomEquiv (R : Sheaf J RingCat.{u})
    (A : Sheaf J (Type u)) (M : ringedSiteModules.{u} R) :
    (freeModule R A ⟶ M) ≃
      (A ⟶ (sheafCompose J (forget AddCommGrpCat)).obj
        ((SheafOfModules.toSheaf R).obj M)) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    (PresheafOfModules.freeHomEquiv.trans
      { toFun := fun h ↦ ⟨h⟩
        invFun := fun h ↦ h.hom
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })

private theorem freeModuleHomEquiv_symm_apply (R : Sheaf J RingCat.{u})
    (A : Sheaf J (Type u)) (M : ringedSiteModules.{u} R)
    (z : A ⟶ (sheafCompose J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M)) :
    (freeModuleHomEquiv R A M).symm z = linearize R A M z := rfl

private theorem linearize_generator (R : Sheaf J RingCat.{u})
    (A : Sheaf J (Type u)) (M : ringedSiteModules.{u} R)
    (z : A ⟶ (sheafCompose J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M)) (U : Cᵒᵖ) (a : A.obj.obj U) :
    (linearize R A M z).val.app U (generator R A U a) = z.hom.app U a := by
  have h := (freeModuleHomEquiv R A M).apply_symm_apply z
  exact congrArg (fun t ↦ t.hom.app U a) h

private theorem freeModuleHomEquiv_apply (R : Sheaf J RingCat.{u})
    (A : Sheaf J (Type u)) (M : ringedSiteModules.{u} R) (t : freeModule R A ⟶ M)
    (U : Cᵒᵖ) (a : A.obj.obj U) :
    (freeModuleHomEquiv R A M t).hom.app U a =
      t.val.app U (generator R A U a) := rfl

attribute [irreducible] freeModuleHomEquiv

private def transposeEquiv {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (W : X) (M : ringedSiteModules.{u} R) :
    ((evaluate S W).obj (f.modules.obj M)) ≃
      (testObject f W ⟶ (sheafCompose J (forget AddCommGrpCat)).obj
        ((SheafOfModules.toSheaf R).obj M)) :=
  yonedaEquiv.symm.trans
    (((sheafificationAdjunction K (Type u)).homEquiv _ _).symm.trans
      ((Iso.homCongr (Iso.refl _) (f.underlying.app M)).trans
        (f.adj.homEquiv _ _).symm))

private theorem transposeEquiv_apply
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (W : X) (M : ringedSiteModules.{u} R)
    (x : (evaluate S W).obj (f.modules.obj M)) :
    transposeEquiv f W M x = transpose f W M x := rfl

attribute [irreducible] transposeEquiv

private def transposeLinearEquiv {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (W : X) (M : ringedSiteModules.{u} R) :
    ((evaluate S W).obj (f.modules.obj M)) ≃ (freeModule R (testObject f W) ⟶ M) :=
  (transposeEquiv f W M).trans (freeModuleHomEquiv R (testObject f W) M).symm

private theorem transposeLinearEquiv_apply
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (W : X) (M : ringedSiteModules.{u} R)
    (x : (evaluate S W).obj (f.modules.obj M)) :
    transposeLinearEquiv f W M x = linearize R (testObject f W) M (transpose f W M x) := by
  change (freeModuleHomEquiv R (testObject f W) M).symm (transposeEquiv f W M x) = _
  rw [transposeEquiv_apply, freeModuleHomEquiv_symm_apply]

attribute [irreducible] transposeLinearEquiv

private theorem transpose_naturality
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (W : X) {M N : ringedSiteModules.{u} R}
    (g : M ⟶ N) (x : (f.modules.obj M).val.obj (op W)) :
    transpose f W N ((f.modules.map g).val.app (op W) x) =
      transpose f W M x ≫
        (SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)).map g := by
  let U := SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)
  let U' := SheafOfModules.toSheaf S ⋙ sheafCompose K (forget AddCommGrpCat)
  have hu : U'.map (f.modules.map g) ≫ f.underlying.hom.app N =
      f.underlying.hom.app M ≫ f.direct.map (U.map g) :=
    f.underlying.hom.naturality g
  dsimp only [transpose]
  rw [← f.adj.homEquiv_naturality_right_symm]
  congr 1
  conv_rhs => rw [Category.assoc, ← hu, ← Category.assoc]
  congr 1
  rw [← (sheafificationAdjunction K (Type u)).homEquiv_naturality_right_symm]
  congr 1
  exact (yonedaEquiv_symm_naturality_right W
    ((sheafToPresheaf K (Type u)).map (U'.map (f.modules.map g))) x).symm

set_option backward.isDefEq.respectTransparency true in
private theorem linearize_naturality (R : Sheaf J RingCat.{u})
    (A : Sheaf J (Type u)) {M N : ringedSiteModules.{u} R}
    (g : M ⟶ N)
    (z : A ⟶ (sheafCompose J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M)) :
    linearize R A N (z ≫
      (SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)).map g) =
      linearize R A M z ≫ g := by
  apply (freeModuleHomEquiv R A N).injective
  apply Sheaf.hom_ext
  ext U a
  change (freeModuleHomEquiv R A N (linearize R A N
    (z ≫ (SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)).map g))).hom.app
      U a = (freeModuleHomEquiv R A N (linearize R A M z ≫ g)).hom.app U a
  rw [freeModuleHomEquiv_apply, freeModuleHomEquiv_apply, linearize_generator]
  change _ = g.val.app U ((linearize R A M z).val.app U (generator R A U a))
  rw [linearize_generator]
  rfl

private theorem transposeLinearEquiv_naturality
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (W : X) {M N : ringedSiteModules.{u} R}
    (g : M ⟶ N) (x : (evaluate S W).obj (f.modules.obj M)) :
    transposeLinearEquiv f W N ((f.modules ⋙ evaluate S W).map g x) =
      transposeLinearEquiv f W M x ≫ g := by
  rw [transposeLinearEquiv_apply, transposeLinearEquiv_apply]
  change linearize R _ N (transpose f W N ((f.modules.map g).val.app (op W) x)) = _
  rw [transpose_naturality, linearize_naturality]

private def transposeLinearAddEquiv
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (W : X) (M : ringedSiteModules.{u} R) :
    ((evaluate S W).obj (f.modules.obj M)) ≃+ (freeModule R (testObject f W) ⟶ M) where
  toEquiv := transposeLinearEquiv f W M
  map_add' x y := natural_map_add (f.modules ⋙ evaluate S W)
    (preadditiveCoyoneda.obj (op (freeModule R (testObject f W))))
    (fun N x ↦ transposeLinearEquiv f W N x)
    (fun g x ↦ transposeLinearEquiv_naturality f W g x) M x y

private def sectionEquiv {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (A : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R) :
    ((evaluate S W).obj (f.modules.obj ((D.image.obj (op A)).obj M))) ≃+
      (sections R M).obj (op ((testObject f W) ⨯ A)) :=
  (transposeLinearAddEquiv f W _).trans
    (localizedSectionAddEquiv R D (testObject f W) A M)

private theorem sectionEquiv_apply
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (A : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R)
    (x : (evaluate S W).obj (f.modules.obj ((D.image.obj (op A)).obj M))) :
    sectionEquiv f D A W M x = localizedSectionEquiv R D (testObject f W) A M
      (transposeLinearEquiv f W _ x) := rfl

attribute [irreducible] sectionEquiv localizedSectionAddEquiv transposeLinearAddEquiv

private def sectionIso {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R) :
    row f D V W M ≅ sliceRow V (testObject f W) M :=
  NatIso.ofComponents (fun n ↦ (sectionEquiv f D
    ((sheafCoverNerve V).obj (op n)) W M).toAddCommGrpIso) (by
      intro n m g
      apply AddCommGrpCat.hom_ext
      ext x
      change sectionEquiv f D _ W M
        ((f.modules ⋙ evaluate S W).map ((D.image.map
          ((sheafCoverNerve V).map g.op).op).app M) x) = _
      change sectionEquiv f D _ W M _ =
        (sections R M).map (prod.map (𝟙 (testObject f W))
          ((sheafCoverNerve V).map g.op)).op (sectionEquiv f D _ W M x)
      rw [sectionEquiv_apply, sectionEquiv_apply]
      erw [transposeLinearEquiv_naturality, localizedSectionEquiv_restriction])

private theorem sectionIso_apply
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R) (n : ℕ)
    (x : (row f D V W M).obj (.mk n)) (U : Cᵒᵖ)
    (z : ((testObject f W) ⨯ ((sheafCoverNerve V).obj (op (.mk n)))).obj.obj U) :
    (((sectionIso f D V W M).hom.app (.mk n)) x).app U (FreeAbelianGroup.of z) =
      localizedTranspose f D V W M n x U z := by
  change (sectionEquiv f D _ W M x).app U (FreeAbelianGroup.of z) = _
  rw [sectionEquiv_apply]
  rw [localizedSectionEquiv_apply, transposeLinearEquiv_apply]
  rfl

private theorem sectionIso_naturality
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (W : X) {M N : ringedSiteModules.{u} R}
    (g : M ⟶ N) (n : ℕ) (x : (row f D V W M).obj (.mk n)) :
    (sectionIso f D V W N).hom.app (.mk n)
      ((f.modules.map ((D.image.obj (op ((sheafCoverNerve V).obj (op (.mk n))))).map
        g)).val.app (op W) x) =
      (sectionsMap g).app
        (op ((testObject f W) ⨯ ((sheafCoverNerve V).obj (op (.mk n)))))
          ((sectionIso f D V W M).hom.app (.mk n) x) := by
  change sectionEquiv f D _ W N ((f.modules ⋙ evaluate S W).map
    ((D.image.obj _).map g) x) =
      (sectionsMap g).app _ (sectionEquiv f D _ W M x)
  rw [sectionEquiv_apply, sectionEquiv_apply]
  rw [transposeLinearEquiv_naturality, localizedSectionEquiv_naturality]

private theorem sectionIso_augmentation
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R)
    (x : (f.modules.obj M).val.obj (op W)) (U : Cᵒᵖ)
    (z : ((testObject f W) ⨯ ((sheafCoverNerve V).obj (op (.mk 0)))).obj.obj U) :
    (((sectionIso f D V W M).hom.app (.mk 0)) (augment f D V W M x)).app U
      (FreeAbelianGroup.of z) =
        (transpose f W M x).hom.app U
          ((prod.fst : (testObject f W) ⨯
            ((sheafCoverNerve V).obj (op (.mk 0))) ⟶ _).hom.app U z) := by
  change (sectionEquiv f D _ W M ((f.modules ⋙ evaluate S W).map
    ((D.augmentation _).app M) x)).app U (FreeAbelianGroup.of z) = _
  rw [sectionEquiv_apply]
  rw [transposeLinearEquiv_naturality, localizedSectionEquiv_apply]
  rw [Category.assoc, (D.adj _).homEquiv_naturality_left_symm, D.unit,
    transposeLinearEquiv_apply]
  change (linearize R (testObject f W) M (transpose f W M x)).val.app U
    (generator R (testObject f W) U _) = _
  exact linearize_generator R (testObject f W) M (transpose f W M x) U _


attribute [irreducible] sectionIso

private def nerveMapIso
    {D E : Type*} [Category D] [Category E] [HasFiniteLimits D] [HasFiniteLimits E]
    (F : D ⥤ E) [PreservesFiniteLimits F] (f : Arrow D) :
    f.cechNerve ⋙ F ≅ (Arrow.mk (F.map f.hom)).cechNerve := by
  let L (n : SimplexCategoryᵒᵖ) :=
    WidePullbackShape.wideCospan f.right (fun _ : Fin (n.unop.len + 1) ↦ f.left)
      (fun _ ↦ f.hom)
  let R (n : SimplexCategoryᵒᵖ) :=
    WidePullbackShape.wideCospan (F.obj f.right)
      (fun _ : Fin (n.unop.len + 1) ↦ F.obj f.left) (fun _ ↦ F.map f.hom)
  let eD (n : SimplexCategoryᵒᵖ) : L n ⋙ F ≅ R n :=
    NatIso.ofComponents (fun j ↦ match j with
      | none => Iso.refl _
      | some _ => Iso.refl _)
      (by intro j k α; cases α with
          | id j =>
              change F.map ((L n).map (𝟙 j)) ≫ _ = _ ≫ (R n).map (𝟙 j)
              rw [(L n).map_id, (R n).map_id, F.map_id]
              simp
          | term j => simp [L, R])
  let e (n : SimplexCategoryᵒᵖ) : F.obj (limit (L n)) ≅ limit (R n) :=
    preservesLimitIso F (L n) ≪≫ HasLimit.isoOfNatIso (eD n)
  have hπ (n : SimplexCategoryᵒᵖ) (j : Fin (n.unop.len + 1)) :
      (e n).hom ≫ WidePullback.π (fun _ ↦ F.map f.hom) j =
        F.map (WidePullback.π (fun _ ↦ f.hom) j) := by
    change (e n).hom ≫ limit.π (R n) (some j) = F.map (limit.π (L n) (some j))
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    simp [eD]
  have hb (n : SimplexCategoryᵒᵖ) :
      (e n).hom ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ F.map f.hom) =
        F.map (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f.hom)) := by
    change (e n).hom ≫ limit.π (R n) none = F.map (limit.π (L n) none)
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    simp [eD]
  refine NatIso.ofComponents e ?_
  intro n m α
  apply WidePullback.hom_ext
  · intro j
    dsimp only [Arrow.mk, Functor.comp_map]
    rw [Category.assoc, hπ]
    simp only [← F.map_comp]
    simp [Arrow.cechNerve, Category.assoc, hπ]
  · dsimp only [Arrow.mk, Functor.comp_map]
    rw [Category.assoc, hb]
    simp only [← F.map_comp]
    simp [Arrow.cechNerve, Category.assoc, hb]

attribute [irreducible] nerveMapIso

private def productWidePullbackIso {E : Type*} [Category E] [HasFiniteLimits E]
    (A V : E) (n : ℕ) :
    A ⨯ widePullback (⊤_ E) (fun _ : Fin (n + 1) ↦ V) (fun _ ↦ terminal.from V) ≅
      widePullback A (fun _ : Fin (n + 1) ↦ A ⨯ V) (fun _ ↦ prod.fst) where
  hom := WidePullback.lift prod.fst
    (fun i ↦ prod.lift prod.fst (prod.snd ≫ WidePullback.π _ i)) (by simp)
  inv := prod.lift (WidePullback.base _) (WidePullback.lift (terminal.from _)
    (fun i ↦ WidePullback.π _ i ≫ prod.snd) (by simp))
  hom_inv_id := by
    apply prod.hom_ext
    · simp
    · apply WidePullback.hom_ext
      · intro i
        simp
      · apply terminal.hom_ext
  inv_hom_id := by
    apply WidePullback.hom_ext
    · intro i
      apply prod.hom_ext
      · simp
      · simp
    · simp

private theorem productWidePullbackIso_π {E : Type*} [Category E] [HasFiniteLimits E]
    (A V : E) (n : ℕ) (i : Fin (n + 1)) :
    (productWidePullbackIso A V n).hom ≫ WidePullback.π _ i =
      prod.lift prod.fst (prod.snd ≫ WidePullback.π (fun _ : Fin (n + 1) ↦ terminal.from V) i) :=
  WidePullback.lift_π _ _ _ _ i

private theorem productWidePullbackIso_base {E : Type*} [Category E] [HasFiniteLimits E]
    (A V : E) (n : ℕ) :
    (productWidePullbackIso A V n).hom ≫ WidePullback.base _ = prod.fst :=
  WidePullback.lift_base _ _ _ _

attribute [irreducible] productWidePullbackIso

private def productNerveIso {E : Type*} [Category E] [HasFiniteLimits E] (A V : E) :
    (Arrow.mk (terminal.from V)).cechNerve ⋙ prod.functor.obj A ≅
      (Arrow.mk (prod.fst : A ⨯ V ⟶ A)).cechNerve := by
  refine NatIso.ofComponents (fun n ↦ productWidePullbackIso A V n.unop.len) ?_
  intro n m g
  apply WidePullback.hom_ext
  · intro i
    apply prod.hom_ext <;>
      simp [Category.assoc, productWidePullbackIso_π, Arrow.cechNerve]
  · simp [Category.assoc, productWidePullbackIso_base, Arrow.cechNerve]

attribute [irreducible] productNerveIso

private def nerveComparison (A V : Sheaf J (Type u)) :
    sheafCoverNerve V ⋙ prod.functor.obj A ⋙ sheafToPresheaf J (Type u) ≅
      (Arrow.mk ((prod.fst : A ⨯ V ⟶ A).hom)).cechNerve :=
  Functor.isoWhiskerRight (productNerveIso A V) (sheafToPresheaf J (Type u)) ≪≫
    nerveMapIso (sheafToPresheaf J (Type u)) (Arrow.mk (prod.fst : A ⨯ V ⟶ A))

attribute [irreducible] nerveComparison

private def freeNerveHomIso {E : Type*} [Category E]
    (F G : Eᵒᵖ ⥤ Cᵒᵖ ⥤ Type u) (e : F ≅ G) (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (F ⋙ (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free).rightOp ⋙ preadditiveYoneda.obj P ≅
    (G ⋙ (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free).rightOp ⋙ preadditiveYoneda.obj P :=
  Functor.isoWhiskerRight
    (((Functor.leftOpRightOpEquiv E (Cᵒᵖ ⥤ AddCommGrpCat.{u})).functor.mapIso
      (Functor.isoWhiskerRight e
        ((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj
          AddCommGrpCat.free)).op).symm)
    (preadditiveYoneda.obj P)

attribute [irreducible] freeNerveHomIso

private def sliceNerveIso (R : Sheaf J RingCat.{u})
    (A V : Sheaf J (Type u)) (M : ringedSiteModules.{u} R) :
    sliceRow V A M ≅
      ((Arrow.mk ((prod.fst : A ⨯ V ⟶ A).hom)).cechNerve ⋙
        (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).rightOp ⋙
          preadditiveYoneda.obj M.val.presheaf :=
  freeNerveHomIso _ _ (nerveComparison A V) M.val.presheaf

attribute [irreducible] sliceNerveIso

private theorem sliceHigherExact (R : Sheaf J RingCat.{u})
    (A V : Sheaf J (Type u)) (M : ringedSiteModules.{u} R) [Injective M] (n : ℕ) :
    IsZero (((AlgebraicTopology.alternatingCofaceMapComplex _).obj
      (sliceRow V A M)).homology (n + 1)) := by
  have : Injective M.val := injective_module_sheaf_injective_presheaf R M
  have h := injective_presheaf_module_nerve_acyclic R.obj M.val
    (Arrow.mk ((prod.fst : A ⨯ V ⟶ A).hom)) (n + 1) (by omega)
  let e := (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
    (sliceNerveIso R A V M)
  exact h.of_iso ((HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso e)

private def sectionHomEquiv (R : Sheaf J RingCat.{u}) (M : ringedSiteModules.{u} R)
    (A : Sheaf J (Type u)) :
    (sections R M).obj (op A) ≃
      (A ⟶ (sheafCompose J (forget AddCommGrpCat)).obj
        ((SheafOfModules.toSheaf R).obj M)) :=
  ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv A.obj M.val.presheaf).trans
    { toFun := fun h ↦ ⟨h⟩
      invFun := fun h ↦ h.hom
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

private theorem sectionHomEquiv_map (R : Sheaf J RingCat.{u}) (M : ringedSiteModules.{u} R)
    {A B : Sheaf J (Type u)} (b : A ⟶ B) (c : (sections R M).obj (op B)) :
    sectionHomEquiv R M A ((sections R M).map b.op c) =
      b ≫ sectionHomEquiv R M B c := by
  apply Sheaf.hom_ext
  exact (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left b.hom c

private def nerveZeroIso {E : Type*} [Category E] [HasFiniteLimits E] (V : E) :
    (Arrow.mk (terminal.from V)).cechNerve.obj (op (.mk 0)) ≅ V where
  hom := WidePullback.π _ 0
  inv := WidePullback.lift (terminal.from V) (fun _ ↦ 𝟙 V) (by simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro i
      have : i = 0 := Fin.eq_zero i
      subst i
      simp
    · apply terminal.hom_ext
  inv_hom_id := by simp

private theorem product_epi (A V : Sheaf J (Type u)) [Epi (terminal.from V)] :
    Epi (prod.fst : A ⨯ V ⟶ A) := by
  have hv : Sheaf.IsLocallySurjective (terminal.from V) :=
    (Sheaf.isLocallySurjective_iff_epi _).2 inferInstance
  have hp : Sheaf.IsLocallySurjective (prod.fst : A ⨯ V ⟶ A) := by
    constructor
    intro U a
    have h := Presheaf.imageSieve_mem J (terminal.from V).hom
      ((terminal.from A).hom.app (op U) a)
    apply J.superset_covering _ h
    intro T k hk
    obtain ⟨v, _⟩ := hk
    refine ⟨sectionPair A V (op T) (A.obj.map k.op a) v, ?_⟩
    exact sectionPair_fst A V (op T) _ _
  exact (Sheaf.isLocallySurjective_iff_epi _).1 hp

private theorem sliceAugment_injective (R : Sheaf J RingCat.{u})
    (A V : Sheaf J (Type u)) [Epi (terminal.from V)] (M : ringedSiteModules.{u} R) :
    Function.Injective ((sections R M).map
      (prod.fst : A ⨯ ((sheafCoverNerve V).obj (op (.mk 0))) ⟶ A).op) := by
  have : Epi (terminal.from ((sheafCoverNerve V).obj (op (.mk 0)))) := by
    have he : (nerveZeroIso V).hom ≫ terminal.from V =
        terminal.from ((sheafCoverNerve V).obj (op (.mk 0))) := terminal.hom_ext _ _
    rw [← he]
    infer_instance
  have := product_epi A ((sheafCoverNerve V).obj (op (.mk 0)))
  intro x y h
  apply (sectionHomEquiv R M A).injective
  apply (cancel_epi (prod.fst : A ⨯ ((sheafCoverNerve V).obj (op (.mk 0))) ⟶ A)).1
  simpa only [sectionHomEquiv_map] using congrArg (sectionHomEquiv R M _) h

private theorem productNerve_descent {E : Type*} [Category E] [HasFiniteLimits E]
    [IsRegularEpiCategory E] (A V F : E)
    [Epi (prod.fst : A ⨯ (Arrow.mk (terminal.from V)).cechNerve.obj (op (.mk 0)) ⟶ A)]
    (b : A ⨯ (Arrow.mk (terminal.from V)).cechNerve.obj (op (.mk 0)) ⟶ F)
    (heq : prod.map (𝟙 A)
        ((Arrow.mk (terminal.from V)).cechNerve.map (SimplexCategory.δ 0).op) ≫ b =
      prod.map (𝟙 A)
        ((Arrow.mk (terminal.from V)).cechNerve.map (SimplexCategory.δ 1).op) ≫ b) :
    ∃ a : A ⟶ F, prod.fst ≫ a = b := by
  let N := (Arrow.mk (terminal.from V)).cechNerve
  change prod.map (𝟙 A) (N.map (SimplexCategory.δ 0).op) ≫ b =
    prod.map (𝟙 A) (N.map (SimplexCategory.δ 1).op) ≫ b at heq
  have hdesc : ∀ {T : E}
      (g h : T ⟶ A ⨯ N.obj (op (.mk 0))),
      g ≫ prod.fst = h ≫ prod.fst → g ≫ b = h ≫ b := by
    intro T g h hgh
    let t : T ⟶ N.obj (op (.mk 1)) := WidePullback.lift (terminal.from T)
      (fun i ↦ if i = 0 then h ≫ prod.snd ≫ (nerveZeroIso V).hom
        else g ≫ prod.snd ≫ (nerveZeroIso V).hom) (by intro i; apply terminal.hom_ext)
    have hd0 : (SimplexCategory.δ (0 : Fin 2)).toOrderHom 0 ≠ 0 := by decide
    have hd1 : (SimplexCategory.δ (1 : Fin 2)).toOrderHom 0 = 0 := by decide
    have h0 : prod.lift (g ≫ prod.fst) t ≫
        prod.map (𝟙 A) (N.map (SimplexCategory.δ 0).op) = g := by
      apply prod.hom_ext
      · simp
      · simp only [Category.assoc, prod.map_snd, prod.lift_snd_assoc]
        apply (cancel_mono (nerveZeroIso V).hom).1
        simp [t, N, Arrow.cechNerve, nerveZeroIso, hd0]
    have h1 : prod.lift (g ≫ prod.fst) t ≫
        prod.map (𝟙 A) (N.map (SimplexCategory.δ 1).op) = h := by
      apply prod.hom_ext
      · simpa using hgh
      · apply (cancel_mono (nerveZeroIso V).hom).1
        simp [t, N, Arrow.cechNerve, nerveZeroIso, hd1]
    simpa only [← Category.assoc, h0, h1] using
      congrArg (fun k ↦ prod.lift (g ≫ prod.fst) t ≫ k) heq
  have : IsRegularEpi (prod.fst : A ⨯ N.obj (op (.mk 0)) ⟶ A) :=
    IsRegularEpiCategory.regularEpiOfEpi _
  exact ⟨EffectiveEpi.desc (prod.fst : A ⨯ N.obj (op (.mk 0)) ⟶ A) b hdesc,
    EffectiveEpi.fac _ b hdesc⟩

private theorem sliceAugment_exact (R : Sheaf J RingCat.{u})
    (A V : Sheaf J (Type u)) [Epi (terminal.from V)] (M : ringedSiteModules.{u} R) :
    ∀ c : (sliceRow V A M).obj (.mk 0),
      ((AlgebraicTopology.alternatingCofaceMapComplex _).obj (sliceRow V A M)).d 0 1 c = 0 →
      ∃ x : (sections R M).obj (op A),
        (sections R M).map
          (prod.fst : A ⨯ ((sheafCoverNerve V).obj (op (.mk 0))) ⟶ A).op x = c := by
  intro c hc
  let N := sheafCoverNerve V
  let F := (sheafCompose J (forget AddCommGrpCat)).obj ((SheafOfModules.toSheaf R).obj M)
  let b : A ⨯ N.obj (op (.mk 0)) ⟶ F := sectionHomEquiv R M _ c
  have heq : prod.map (𝟙 A) (N.map (SimplexCategory.δ 0).op) ≫ b =
      prod.map (𝟙 A) (N.map (SimplexCategory.δ 1).op) ≫ b := by
    have hz : (sliceRow V A M).map (SimplexCategory.δ 0) c =
        (sliceRow V A M).map (SimplexCategory.δ 1) c := by
      change (AlgebraicTopology.AlternatingCofaceMapComplex.objD (sliceRow V A M) 0) c = 0 at hc
      dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD] at hc
      rw [Fin.sum_univ_two] at hc
      change (1 : ℤ) • ((sliceRow V A M).map (SimplexCategory.δ 0) c) +
        (-1 : ℤ) • ((sliceRow V A M).map (SimplexCategory.δ 1) c) = 0 at hc
      simpa only [one_zsmul, neg_one_zsmul, add_neg_eq_zero] using hc
    exact (sectionHomEquiv_map R M _ _).symm.trans
      ((congrArg (sectionHomEquiv R M _) hz).trans (sectionHomEquiv_map R M _ _))
  have hepi : Epi (prod.fst : A ⨯ N.obj (op (.mk 0)) ⟶ A) := by
    have : Epi (terminal.from (N.obj (op (.mk 0)))) := by
      have he : (nerveZeroIso V).hom ≫ terminal.from V = terminal.from (N.obj (op (.mk 0))) :=
        terminal.hom_ext _ _
      rw [← he]
      infer_instance
    exact product_epi A _
  have : Epi (prod.fst :
      A ⨯ (Arrow.mk (terminal.from V)).cechNerve.obj (op (.mk 0)) ⟶ A) := hepi
  obtain ⟨a, ha⟩ := productNerve_descent A V F b heq
  refine ⟨(sectionHomEquiv R M A).symm a, ?_⟩
  apply (sectionHomEquiv R M _).injective
  rw [sectionHomEquiv_map, Equiv.apply_symm_apply]
  exact ha

private theorem unit_closed {R : Sheaf J RingCat.{u}}
    (D : CoherentCechImageModel R) (V : Sheaf J (Type u))
    (M : ringedSiteModules.{u} R) :
    (D.augmentation ((sheafCoverNerve V).obj (op (.mk 0)))).app M ≫
      ((D.cochains V).obj M).d 0 1 = 0 := by
  change (D.augmentation ((sheafCoverNerve V).obj (op (.mk 0)))).app M ≫
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
      ((((sheafCoverNerve V).rightOp ⋙ D.image).flip.obj M)) 0 = 0
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  change _ ≫ (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
    (CosimplicialObject.δ
      (((sheafCoverNerve V).rightOp ⋙ D.image).flip.obj M) i)) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Preadditive.comp_add, Preadditive.comp_neg]
  change _ ≫ (D.image.map _).app M + -(_ ≫ (D.image.map _).app M) = 0
  change _ ≫ (D.image.map ((sheafCoverNerve V).map (SimplexCategory.δ 0).op).op).app M +
    -(_ ≫ (D.image.map ((sheafCoverNerve V).map (SimplexCategory.δ 1).op).op).app M) = 0
  rw [← NatTrans.comp_app, D.augmentation_naturality,
    ← NatTrans.comp_app, D.augmentation_naturality]
  exact add_neg_cancel _

private def baseAugmentation {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ) :
    (f.modules.mapHomologicalComplex (.up ℕ)).obj I ⟶
      (D.bicomplex f.modules V I).X 0 where
  f q := f.modules.map
    ((D.augmentation ((sheafCoverNerve V).obj (op (.mk 0)))).app (I.X q))
  comm' q r h := by
    symm
    change f.modules.map (I.d q r) ≫ f.modules.map _ =
      f.modules.map _ ≫ f.modules.map ((D.image.obj _).map (I.d q r))
    rw [← f.modules.map_comp, ← f.modules.map_comp]
    exact congrArg f.modules.map ((D.augmentation _).naturality (I.d q r))

private theorem baseAugmentation_closed
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ) :
    baseAugmentation f D V I ≫ (D.bicomplex f.modules V I).d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  change f.modules.map _ ≫ f.modules.map (((D.cochains V).obj (I.X q)).d 0 1) = 0
  rw [← f.modules.map_comp, unit_closed, f.modules.map_zero]

private def columnAugmentation {E : Type*} [Category E] [Abelian E]
    (B : HomologicalComplex₂ E (.up ℕ) (.up ℕ)) (A : CochainComplex E ℕ)
    (a : A ⟶ B.X 0) (ha : a ≫ B.d 0 1 = 0) : A ⟶ B.total (.up ℕ) where
  f q := a.f q ≫ B.ιTotal (.up ℕ) 0 q q (zero_add q)
  comm' q r h := by
    obtain rfl : r = q + 1 := h.symm
    simp only [HomologicalComplex₂.total_d, Category.assoc, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [B.d₁_eq (.up ℕ) (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
      q (q + 1) (by change 1 + q = q + 1; omega),
      B.d₂_eq (.up ℕ) 0 (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl)
        (q + 1) (by simp)]
    have hz := congrArg (fun g ↦ g.f q) ha
    change a.f q ≫ (B.d 0 1).f q = 0 at hz
    have he₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := rfl
    have he₂ : ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := by
      change (-1 : ℤˣ) ^ 0 = 1
      exact pow_zero _
    simp only [← Category.assoc, he₁, he₂, one_smul]
    rw [hz, zero_comp, zero_add]
    exact a.comm q (q + 1) =≫ _

private theorem columnAugmentation_f {E : Type*} [Category E] [Abelian E]
    (B : HomologicalComplex₂ E (.up ℕ) (.up ℕ)) (A : CochainComplex E ℕ)
    (a : A ⟶ B.X 0) (ha : a ≫ B.d 0 1 = 0) (q : ℕ) :
    (columnAugmentation B A a ha).f q = a.f q ≫
      B.ιTotal (.up ℕ) 0 q q (zero_add q) := rfl

attribute [irreducible] columnAugmentation

private def totalAugmentation
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ) :
    (f.modules.mapHomologicalComplex (.up ℕ)).obj I ⟶
      (D.bicomplex f.modules V I).total (.up ℕ) :=
  columnAugmentation (D.bicomplex f.modules V I) _ (baseAugmentation f D V I)
    (baseAugmentation_closed f D V I)

private theorem totalAugmentation_f
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ) (q : ℕ) :
    (totalAugmentation f D V I).f q = (baseAugmentation f D V I).f q ≫
      (D.bicomplex f.modules V I).ιTotal (.up ℕ) 0 q q (zero_add q) :=
  columnAugmentation_f _ _ _ _ q

attribute [irreducible] totalAugmentation

private theorem columnAugmentation_quasiIso {E : Type*} [Category E] [Abelian E]
    (B : HomologicalComplex₂ E (.up ℕ) (.up ℕ)) (A : CochainComplex E ℕ)
    (a : A ⟶ B.X 0) (ha : a ≫ B.d 0 1 = 0)
    (b : A ⟶ B.total (.up ℕ))
    (hb : ∀ q, b.f q = a.f q ≫ B.ιTotal (.up ℕ) 0 q q (zero_add q))
    (hrows : ∀ q : ℕ, ∃ r : (CochainComplex.single₀ E).obj (A.X q) ⟶ B.flip.X q,
      r.f 0 = a.f q ∧ QuasiIso r) : QuasiIso b := by
  apply HomologicalComplex₂.quasiIso_of_column_augmentation B A a ha b hb
  intro q
  obtain ⟨r, hr, hqr⟩ := hrows q
  have he : r = (CochainComplex.fromSingle₀Equiv (B.flip.X q) (A.X q)).symm
      ⟨a.f q, by simpa using congrArg (fun g ↦ g.f q) ha⟩ := by
    apply HomologicalComplex.hom_ext
    intro p
    cases p with
    | zero => simpa only [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero] using hr
    | succ p =>
      exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0
        (A.X q) (p + 1) (by omega)).eq_of_src _ _
  simpa only [← he] using hqr

private theorem total_augmentation_of_rows
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [HasDerivedCategory.{w} (ringedSiteModules.{u} S)]
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (hrows : ∀ q : ℕ,
      ∃ a : (CochainComplex.single₀ (ringedSiteModules.{u} S)).obj
          (f.modules.obj (I.X q)) ⟶
            (f.modules.mapHomologicalComplex (.up ℕ)).obj ((D.cochains V).obj (I.X q)),
        a.f 0 = f.modules.map
          ((D.augmentation ((sheafCoverNerve V).obj (op (.mk 0)))).app (I.X q)) ∧
          QuasiIso a) :
    ∃ b : (f.modules.mapHomologicalComplex (.up ℕ)).obj I ⟶
        (D.bicomplex f.modules V I).total (.up ℕ),
      D.IsAugmentation f.modules V I b ∧ QuasiIso b ∧
      IsIso (DerivedCategory.Q.map
        (HomologicalComplex.extendMap b ComplexShape.embeddingUpNat)) := by
  let b := totalAugmentation f D V I
  have hb : QuasiIso b := columnAugmentation_quasiIso
    (D.bicomplex f.modules V I) _ (baseAugmentation f D V I)
    (baseAugmentation_closed f D V I) b (totalAugmentation_f f D V I) hrows
  have := hb
  refine ⟨b, totalAugmentation_f f D V I, hb, ?_⟩
  infer_instance


private theorem restrict_injective (R : Sheaf J RingCat.{u})
    (A : Sheaf J (Type u)) (M : ringedSiteModules.{u} R) [Injective M] :
    Injective ((elementModulePullback R A).obj M) := by
  obtain ⟨extAdj⟩ := elementModuleExtension_adjunction R A
  have := extAdj.isLeftAdjoint
  obtain ⟨hpreserves, _⟩ := element_module_presheaf_extension R A
  have := hpreserves
  have hleft : PreservesFiniteLimits (elementModuleExtension R A) := by
    let e := SheafOfModules.pullbackIso.{u} (R := R) (S := elementRing R A)
      (F := elementProjection A) (𝟙 (elementRing R A))
    have hcomp : PreservesFiniteLimits
        (SheafOfModules.forget (elementRing R A) ⋙
          PresheafOfModules.pullback.{u} (F := elementProjection A)
            (𝟙 (elementRing R A) : elementRing R A ⟶ elementRing R A).hom ⋙
          PresheafOfModules.sheafification (R := R) (𝟙 R.obj)) := by
      change PreservesFiniteLimits
        (SheafOfModules.forget (elementRing R A) ⋙
          PresheafOfModules.pullback.{u} (F := elementProjection A)
            (𝟙 (elementRing R A).obj) ⋙
          PresheafOfModules.sheafification (R := R) (𝟙 R.obj))
      have : PreservesFiniteLimits
          (PresheafOfModules.pullback.{u} (F := elementProjection A)
            (𝟙 (elementRing R A).obj) ⋙ PresheafOfModules.sheafification (R := R) (𝟙 R.obj)) :=
        @comp_preservesFiniteLimits _ _ _ _ _ _
          (PresheafOfModules.pullback.{u} (F := elementProjection A)
            (𝟙 (elementRing R A).obj))
          (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)) hpreserves inferInstance
      exact comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_natIso e.symm
  have := hleft
  exact extAdj.map_injective M inferInstance

private theorem row_d_eval
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R) (n : ℕ) :
    (evaluate S W).map (f.modules.map (((D.cochains V).obj M).d n (n + 1))) =
      (rowComplex f D V W M).d n (n + 1) := by
  let A : CosimplicialObject (ringedSiteModules.{u} R) :=
    (((sheafCoverNerve V).rightOp ⋙ D.image).flip.obj M)
  let F := f.modules ⋙ evaluate S W
  change F.map (CochainComplex.of.d (fun i ↦ A.obj (.mk i))
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD A) n (n + 1)) =
      CochainComplex.of.d (fun i ↦ F.obj (A.obj (.mk i)))
        (AlgebraicTopology.AlternatingCofaceMapComplex.objD (A ⋙ F)) n (n + 1)
  rw [CochainComplex.of_d, CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Functor.map_sum,
    Functor.map_zsmul]
  rfl

private def rowEvalIso
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R) :
    ((f.modules ⋙ evaluate S W).mapHomologicalComplex (.up ℕ)).obj
      ((D.cochains V).obj M) ≅ rowComplex f D V W M :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    change 𝟙 _ ≫ _ = (evaluate S W).map (f.modules.map _) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, row_d_eval])

private def baseSectionEquiv {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (W : X) (M : ringedSiteModules.{u} R) :
    ((evaluate S W).obj (f.modules.obj M)) ≃
      (sections R M).obj (op (testObject f W)) :=
  (transposeEquiv f W M).trans (sectionHomEquiv R M (testObject f W)).symm

private theorem sectionIso_augment_eq
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) (W : X) (M : ringedSiteModules.{u} R)
    (x : (f.modules.obj M).val.obj (op W)) :
    (sectionIso f D V W M).hom.app (.mk 0) (augment f D V W M x) =
      (sections R M).map (prod.fst : (testObject f W) ⨯
        ((sheafCoverNerve V).obj (op (.mk 0))) ⟶ _).op (baseSectionEquiv f W M x) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro z
  change (((sectionIso f D V W M).hom.app (.mk 0))
    (augment f D V W M x)).app U (FreeAbelianGroup.of z) = _
  rw [sectionIso_augmentation]
  change _ = ((sectionHomEquiv R M _).symm
    (transposeEquiv f W M x)).app U
      (FreeAbelianGroup.of ((prod.fst : (testObject f W) ⨯
        ((sheafCoverNerve V).obj (op (.mk 0))) ⟶ _).hom.app U z))
  rw [transposeEquiv_apply]
  have h := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv
    (testObject f W).obj M.val.presheaf).apply_symm_apply (transpose f W M x).hom
  rw [Adjunction.homEquiv_unit] at h
  exact (congrArg (fun t ↦ t.app U
    ((prod.fst : (testObject f W) ⨯
      ((sheafCoverNerve V).obj (op (.mk 0))) ⟶ _).hom.app U z)) h).symm

attribute [irreducible] sectionHomEquiv baseSectionEquiv

private theorem row_sectionwise_exact
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) [Epi (terminal.from V)] (W : X)
    (M : ringedSiteModules.{u} R) [Injective M] :
    Function.Injective (augment f D V W M) ∧
    Function.Exact (augment f D V W M) ((rowComplex f D V W M).d 0 1) ∧
    ∀ n : ℕ, IsZero ((rowComplex f D V W M).homology (n + 1)) := by
  let e := (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
    (sectionIso f D V W M)
  have hd (x : (rowComplex f D V W M).X 0) :
      e.hom.f 1 ((rowComplex f D V W M).d 0 1 x) =
      (((AlgebraicTopology.alternatingCofaceMapComplex _).obj
        (sliceRow V (testObject f W) M)).d 0 1) (e.hom.f 0 x) :=
    ConcreteCategory.congr_hom (e.hom.comm 0 1).symm x
  refine ⟨?_, ?_, fun n ↦ (sliceHigherExact R (testObject f W) V M n).of_iso
    ((HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso e)⟩
  · intro x y h
    apply (baseSectionEquiv f W M).injective
    apply sliceAugment_injective R (testObject f W) V M
    have he := congrArg ((sectionIso f D V W M).hom.app (.mk 0)) h
    rw [sectionIso_augment_eq, sectionIso_augment_eq] at he
    exact he
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := sliceAugment_exact R (testObject f W) V M (e.hom.f 0 x)
        (by rw [← hd, hx]; exact map_zero _)
      refine ⟨(baseSectionEquiv f W M).symm y, ?_⟩
      apply (AddCommGrpCat.mono_iff_injective
        ((sectionIso f D V W M).hom.app (.mk 0))).1 inferInstance
      rw [sectionIso_augment_eq, Equiv.apply_symm_apply]
      exact hy
    · rintro ⟨y, rfl⟩
      have hz := congrArg (fun t ↦ (evaluate S W).map (f.modules.map t) y)
        (unit_closed D V M)
      simp only [Functor.map_comp, Functor.map_zero, ConcreteCategory.comp_apply,
        AddCommGrpCat.zero_apply, row_d_eval] at hz
      exact hz

attribute [irreducible] rowEvalIso

private theorem singleAugmentation_quasiIso {E : Type*} [Category E] [Abelian E]
    (L : CochainComplex E ℕ) (M : E) (u : M ⟶ L.X 0) (hu : u ≫ L.d 0 1 = 0)
    (hzero : (ShortComplex.mk u (L.d 0 1) hu).Exact) (hmono : Mono u)
    (hpositive : ∀ n : ℕ, L.ExactAt (n + 1)) :
    ∃ a : (CochainComplex.single₀ E).obj M ⟶ L, a.f 0 = u ∧ QuasiIso a := by
  let a := (CochainComplex.fromSingle₀Equiv L M).symm ⟨u, hu⟩
  refine ⟨a, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _, ⟨fun n ↦ ?_⟩⟩
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · change (ShortComplex.mk (a.f 0) (L.d 0 1) _).Exact ∧ Mono (a.f 0)
      simpa only [a, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero] using
        And.intro hzero hmono
    · rfl
    · rfl
    · exact L.shape 0 0 (by simp)
  | succ n =>
    exact (quasiIsoAt_iff_exactAt a (n + 1)
      (CochainComplex.exactAt_succ_single_obj _ _)).2 (hpositive n)

private theorem augmentation_quasiIso_of_sections
    {E Y : Type*} [Category E] [Abelian E] [Category Y]
    (G : E ⥤ Y ⥤ AddCommGrpCat.{u}) [G.Faithful] [G.Additive]
    (L : CochainComplex E ℕ) (M : E) (u : M ⟶ L.X 0) (hu : u ≫ L.d 0 1 = 0)
    (hinj : ∀ W : Y, Function.Injective ((G.map u).app W))
    (hex : ∀ W : Y, Function.Exact ((G.map u).app W) ((G.map (L.d 0 1)).app W))
    (hpos : ∀ (W : Y) (n : ℕ),
      (((G ⋙ (evaluation Y AddCommGrpCat.{u}).obj W).mapHomologicalComplex (.up ℕ)).obj L).ExactAt
        (n + 1)) :
    ∃ a : (CochainComplex.single₀ E).obj M ⟶ L, a.f 0 = u ∧ QuasiIso a := by
  have hzero : (ShortComplex.mk u (L.d 0 1) hu).Exact := by
    apply G.reflects_exact_of_faithful
    rw [ShortComplex.exact_iff_evaluation]
    intro W
    exact (ShortComplex.ab_exact_iff_function_exact _).2 (hex W)
  have hmono : Mono u := by
    apply G.mono_of_mono_map
    have hmonoapp (W : Y) : Mono ((G.map u).app W) :=
      (AddCommGrpCat.mono_iff_injective _).2 (hinj W)
    exact NatTrans.mono_of_mono_app _
  have hpositive (n : ℕ) : L.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
    apply G.reflects_exact_of_faithful
    rw [ShortComplex.exact_iff_evaluation]
    intro W
    exact (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
      (by simp) (by simp)).1 (hpos W n)
  exact singleAugmentation_quasiIso L M u hu hzero hmono hpositive

private theorem sheaf_row_quasiIso
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) [Epi (terminal.from V)]
    (M : ringedSiteModules.{u} R) [Injective M] :
    ∃ a : (CochainComplex.single₀ (ringedSiteModules.{u} S)).obj (f.modules.obj M) ⟶
        (f.modules.mapHomologicalComplex (.up ℕ)).obj ((D.cochains V).obj M),
      a.f 0 = f.modules.map
        ((D.augmentation ((sheafCoverNerve V).obj (op (.mk 0)))).app M) ∧ QuasiIso a := by
  let L := (f.modules.mapHomologicalComplex (.up ℕ)).obj ((D.cochains V).obj M)
  let u := f.modules.map
    ((D.augmentation ((sheafCoverNerve V).obj (op (.mk 0)))).app M)
  have hu : u ≫ L.d 0 1 = 0 := by
    change f.modules.map _ ≫ f.modules.map _ = 0
    rw [← f.modules.map_comp, unit_closed, f.modules.map_zero]
  let G := SheafOfModules.toSheaf S ⋙ sheafToPresheaf K AddCommGrpCat.{u}
  have hG : G.Additive := by dsimp [G]; infer_instance
  apply augmentation_quasiIso_of_sections G L (f.modules.obj M) u hu
  · intro W
    exact (row_sectionwise_exact f D V W.unop M).1
  · intro W
    change Function.Exact (augment f D V W.unop M)
      ((evaluate S W.unop).map (f.modules.map (((D.cochains V).obj M).d 0 1)))
    rw [row_d_eval]
    exact (row_sectionwise_exact f D V W.unop M).2.1
  · intro W n
    have hz := (row_sectionwise_exact f D V W.unop M).2.2 n
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ (n + 1)).2 hz).of_iso
      (rowEvalIso f D V W.unop M).symm

/-- Exact injective Čech rows, the specified direct-image total augmentation, and its signs.

Source: Stacks Project, sites-cohomology.tex, Tag 03FC, including degree-zero gluing;
sites-modules.tex, Tags 04IE and 04J4; homology.tex, Tag 0133, second-variable variant.
(blueprint: lem-sfb-cech-injective-image-augmentation).

Proof, following the seven DAG steps.
1. Present the slice at A = f⁻¹(h_W#) by its element site. Restriction has an exact
   left adjoint, the canonical elementModuleExtension, by its module adjunction
   and the exact presheaf-extension theorem.
   Transpose a lifting problem along that adjunction and use injectivity of I^q;
   restriction of I^q is injective. No representability of A is used.
2. Sheafification and Yoneda identify target sections with maps from h_W#. Transpose
   through f⁻¹ ⊣ f_* and then through the localization module adjunction. Evaluation
   on the free-module generators gives localizedTranspose. The free-abelian adjunction
   identifies it with sections over A × V_n, hence with sections on the slice over the
   powers of V_A. All bijections preserve addition. Counit naturality gives every face,
   degeneracy and I-differential; the triangle identity gives the stated augmentation.
3. On the original site, the underlying module presheaf of I^q is injective by
   lem-weil-pbc-ringed-site-injective-module-injective-presheaf. Identify the nerve
   of A × V → A with A × V_n, using preservation of finite limits by sheaf forget.
   Apply lem-sc-injective-presheaf-module-nerve-acyclic and transport the resulting
   positive homology vanishing through the section comparison.
4. Local surjectivity of V → 1 makes A × V_0 → A epimorphic.
   In the regular epi category of set sheaves it is therefore an effective epimorphism.
   A degree-zero cocycle
   agrees on its two nerve projections, hence descends uniquely to A. This proves
   injectivity and the kernel/image equation for the specified unit.
5. Sectionwise exactness implies exactness of abelian presheaves. The faithful
   additive forget functor reflects exactness, giving exact module-sheaf rows.
   The degree-zero short-complex criterion and positive exactness prove the stated
   quasi-isomorphism from the single object in degree zero.
6. Units commute with d_I; their horizontal differential is zero because the two
   restrictions agree. They define b with precisely the (0,q) components. Apply
   lem-sc-first-quadrant-column-augmentation to this first-quadrant bicomplex and
   the row quasi-isomorphisms. Each total diagonal is finite, so b is a quasi-isomorphism.
7. Extension by zero preserves quasi-isomorphisms, and Q inverts them. The canonical
   transpose multiplies the (n,q) summand by (-1)^(nq). For horizontal arrows the two
   exponents are (n+1)q and nq+q; for vertical arrows they are n+n(q+1) and nq,
   equal modulo two. The square of the multiplier is one. At n=0 it is one, so the
   transpose is the identity on all augmentation summands. -/
theorem cech_injective_image_augmentation
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [HasDerivedCategory.{w} (ringedSiteModules.{u} S)]
    (f : RingedToposMorphism R S)
    (fInverse : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R)
    [fInverse.Additive] [PreservesFiniteLimits fInverse] [PreservesFiniteColimits fInverse]
    (_fAdj : fInverse ⊣ f.modules)
    (_commR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_commS : ∀ (U : Xᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    (D : CoherentCechImageModel R) (V : Sheaf J (Type u)) [Epi (terminal.from V)]
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (_injective : ∀ q : ℕ, Injective (I.X q)) : ExactAugmentation f D V I := by
  have hrows (q : ℕ) : ∃ a :
      (CochainComplex.single₀ (ringedSiteModules.{u} S)).obj (f.modules.obj (I.X q)) ⟶
        (f.modules.mapHomologicalComplex (.up ℕ)).obj ((D.cochains V).obj (I.X q)),
      a.f 0 = f.modules.map
        ((D.augmentation ((sheafCoverNerve V).obj (op (.mk 0)))).app (I.X q)) ∧
        QuasiIso a := by
    have := _injective q
    exact sheaf_row_quasiIso f D V (I.X q)
  refine {
    injective_slice := ?_
    sections_identification := ?_
    sectionwise_exact := ?_
    sheaf_rows := ?_
    total_augmentation := ?_
    transpose_sign := ?_
    transpose_augmentation := ?_ }
  · intro W q
    have := _injective q
    exact restrict_injective R (testObject f W) (I.X q)
  · intro W
    refine ⟨fun q ↦ sectionIso f D V W (I.X q), ?_, ?_, ?_⟩
    · intro q n x U z
      exact sectionIso_apply f D V W (I.X q) n x U z
    · intro q r n x
      exact sectionIso_naturality f D V W (I.d q r) n x
    · intro q x U z
      exact sectionIso_augmentation f D V W (I.X q) x U z
  · intro W q
    have := _injective q
    exact row_sectionwise_exact f D V W (I.X q)
  · exact hrows
  · exact total_augmentation_of_rows f D V I hrows
  · intro n q
    rw [HomologicalComplex₂.ιTotal_totalFlipIso_f_inv]
    rfl
  · intro q
    rw [HomologicalComplex₂.ιTotal_totalFlipIso_f_inv]
    change ((-1 : ℤˣ) ^ (0 * q)) • _ = _
    simp

end CategoryTheory.CechInjectiveImage
