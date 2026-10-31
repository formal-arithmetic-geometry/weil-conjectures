/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CoherentCechImageModel
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
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
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives

/-! # Normalized Čech augmentation and resolution/refinement naturality

Source: Stacks Project, derived.tex, Tags 013S, 070I and 09T5; sites-modules.tex,
Tags 04IE and 04J4. The signed-total specialization is the ten-step proof of
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096


universe u wX wY wA

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CechAugmentationNormalized

attribute [local implicit_reducible] CoherentCechImageModel.bicomplex
  CoherentCechImageModel.totalFunctor CoherentCechImageModel.total
  HomologicalComplex₂.flipFunctor HomologicalComplex₂.totalFunctor
  Functor.mapHomologicalComplex HomologicalComplex₂.flip


variable {C X : Type u} [SmallCategory C] [SmallCategory X]
  {J : GrothendieckTopology C} {L : GrothendieckTopology X}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J RingCat.{u}} {S : Sheaf L RingCat.{u}}

/-- Localization of nonnegative complexes after extension by zero.
Source: Stacks 05RU (blueprint: lem-sfb-cech-augmentation-normalized-naturality). -/
def QN (A : Type (u + 1)) [Category.{u} A] [Abelian A] [HasDerivedCategory.{wA} A] :
    CochainComplex A ℕ ⥤ DerivedCategory A :=
  ComplexShape.embeddingUpNat.extendFunctor A ⋙ DerivedCategory.Q

/-- The actual total map on a chain map, with the signed finite-diagonal total unchanged.
Source: Stacks 0133 (blueprint: lem-sfb-cech-augmentation-normalized-naturality). -/
def totalMap (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) {I I' : CochainComplex (ringedSiteModules.{u} R) ℕ}
    (t : I ⟶ I') : D.total G V I ⟶ D.total G V I' :=
  HomologicalComplex.extendMap ((D.totalFunctor G V).map t) ComplexShape.embeddingUpNat

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem augmentation_chain_naturality (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) {I I' : CochainComplex (ringedSiteModules.{u} R) ℕ}
    (t : I ⟶ I')
    (b : (G.mapHomologicalComplex (.up ℕ)).obj I ⟶ (D.totalFunctor G V).obj I)
    (b' : (G.mapHomologicalComplex (.up ℕ)).obj I' ⟶ (D.totalFunctor G V).obj I')
    (hb : D.IsAugmentation G V I b) (hb' : D.IsAugmentation G V I' b') :
    (G.mapHomologicalComplex (.up ℕ)).map t ≫ b' =
      b ≫ (D.totalFunctor G V).map t := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hb q, hb' q]
  change G.map (t.f q) ≫ _ ≫ _ = (_ ≫ _) ≫
    (HomologicalComplex₂.total.map _ (.up ℕ)).f q
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
  change G.map (t.f q) ≫ G.map _ ≫ _ =
    G.map _ ≫ G.map (((D.cochains V).map (t.f q)).f 0) ≫ _
  rw [← Category.assoc, ← Category.assoc, ← G.map_comp, ← G.map_comp]
  exact congrArg (fun z ↦ G.map z ≫
    (D.bicomplex G V I').ιTotal (.up ℕ) 0 q q (zero_add q))
      ((D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).naturality
        (t.f q))

section Derived

variable [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
  [HasDerivedCategory.{wY} (ringedSiteModules.{u} S)]
  [Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} R)]

/-- The canonical inverse of e_I: first apply RF to the resolution, then the inverse
right-derived unit on the K-injective resolution, then commute extension with G.
Source: Stacks 070I (blueprint: lem-sfb-cech-augmentation-normalized-naturality). -/
def comparison (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    {K : ringedSiteModules.{u} R} (I : InjectiveResolution K) :
    G.rightDerivedFunctor.obj ((QN (ringedSiteModules.{u} R)).obj
      ((CochainComplex.single₀ _).obj K)) ≅
      (QN (ringedSiteModules.{u} S)).obj
        ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) :=
  G.rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map
        (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat))) ≪≫
    G.rightDerivedFunctorObjQIso (I.cocomplex.extend ComplexShape.embeddingUpNat) ≪≫
    DerivedCategory.Q.mapIso (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat G)

private theorem comparison_naturality
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    {K K' : ringedSiteModules.{u} R} (I : InjectiveResolution K)
    (I' : InjectiveResolution K') (u : K ⟶ K') (t : I.cocomplex ⟶ I'.cocomplex)
    (ht : I.ι ≫ t = (CochainComplex.single₀ _).map u ≫ I'.ι) :
    (comparison G I).hom ≫
        (QN (ringedSiteModules.{u} S)).map ((G.mapHomologicalComplex (.up ℕ)).map t) =
      G.rightDerivedFunctor.map ((QN (ringedSiteModules.{u} R)).map
        ((CochainComplex.single₀ _).map u)) ≫ (comparison G I').hom := by
  let a := HomologicalComplex.extendMap t ComplexShape.embeddingUpNat
  have hn := G.rightDerivedFunctorUnitQ_naturality a
  rw [G.rightDerivedFunctorUnitQ_eq, G.rightDerivedFunctorUnitQ_eq] at hn
  have hi : G.rightDerivedFunctor.map (DerivedCategory.Q.map a) ≫
        (G.rightDerivedFunctorObjQIso
          (I'.cocomplex.extend ComplexShape.embeddingUpNat)).hom =
      (G.rightDerivedFunctorObjQIso
          (I.cocomplex.extend ComplexShape.embeddingUpNat)).hom ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map a) := by
    rw [← cancel_epi (G.rightDerivedFunctorObjQIso
      (I.cocomplex.extend ComplexShape.embeddingUpNat)).inv]
    rw [Iso.inv_hom_id_assoc, ← Category.assoc, ← hn, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have he : (G.mapHomologicalComplex (.up ℤ)).map a ≫
        (I'.cocomplex.mapExtendIso ComplexShape.embeddingUpNat G).hom =
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat G).hom ≫
        HomologicalComplex.extendMap ((G.mapHomologicalComplex (.up ℕ)).map t)
          ComplexShape.embeddingUpNat := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact HomologicalComplex.mapExtensIso_hom_f_naturality t ComplexShape.embeddingUpNat G i
  have hl := congrArg (fun z ↦ G.rightDerivedFunctor.map
    ((QN (ringedSiteModules.{u} R)).map z)) ht
  simp only [Functor.map_comp] at hl
  change G.rightDerivedFunctor.map (DerivedCategory.Q.map
      (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)) ≫
        G.rightDerivedFunctor.map (DerivedCategory.Q.map a) =
    G.rightDerivedFunctor.map (DerivedCategory.Q.map
      (HomologicalComplex.extendMap ((CochainComplex.single₀ _).map u)
        ComplexShape.embeddingUpNat)) ≫
      G.rightDerivedFunctor.map (DerivedCategory.Q.map
        (HomologicalComplex.extendMap I'.ι ComplexShape.embeddingUpNat)) at hl
  dsimp only [comparison, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  change (G.rightDerivedFunctor.map (DerivedCategory.Q.map
      (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)) ≫
        (G.rightDerivedFunctorObjQIso
          (I.cocomplex.extend ComplexShape.embeddingUpNat)).hom ≫
        DerivedCategory.Q.map
          (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat G).hom) ≫
      DerivedCategory.Q.map
        (HomologicalComplex.extendMap ((G.mapHomologicalComplex (.up ℕ)).map t)
          ComplexShape.embeddingUpNat) = _
  rw [Category.assoc, Category.assoc, ← DerivedCategory.Q.map_comp, ← he,
    DerivedCategory.Q.map_comp]
  simp only [← Category.assoc]
  exact (congrArg (fun z ↦ z ≫ DerivedCategory.Q.map
      (I'.cocomplex.mapExtendIso ComplexShape.embeddingUpNat G).hom)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ G.rightDerivedFunctor.map (DerivedCategory.Q.map
        (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)) ≫ z)
          hi.symm).trans (Category.assoc _ _ _).symm))).trans
      ((congrArg (fun z ↦ (z ≫
        (G.rightDerivedFunctorObjQIso
          (I'.cocomplex.extend ComplexShape.embeddingUpNat)).hom) ≫
          DerivedCategory.Q.map
            (I'.cocomplex.mapExtendIso ComplexShape.embeddingUpNat G).hom) hl).trans
              (by simp only [Category.assoc]; rfl))

/-- The displayed augmentation alpha = e_I inverse followed by Q(b). The input b is
fixed termwise by IsAugmentation; no arbitrary derived arrow is introduced.
Source: Stacks 070I (blueprint: lem-sfb-cech-augmentation-normalized-naturality). -/
def alpha (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) {K : ringedSiteModules.{u} R} (I : InjectiveResolution K)
    (b : (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      (D.totalFunctor G V).obj I.cocomplex) :
    G.rightDerivedFunctor.obj ((QN (ringedSiteModules.{u} R)).obj
      ((CochainComplex.single₀ _).obj K)) ⟶
      DerivedCategory.Q.obj (D.total G V I.cocomplex) :=
  (comparison G I).hom ≫ (QN (ringedSiteModules.{u} S)).map b

/-- Existence of chain lifts and naturality of every lift under the canonical
resolution comparisons, including the augmentation square before localization.
Source: Stacks 013S and 070I
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).

Proof: steps 1--3 and 5 of the node. Extend u to injective resolutions using injectivity
and exactness, giving t with I.ι t = u[0] I'.ι. Naturality of the localization units gives
the chain augmentation square on every (0,q) summand; all other summands vanish.
Naturality of the right-derived unit gives e_J Q(Gt) = RF(u[0]) e_I. Multiplication
by the inverse comparisons and the chain square gives the displayed derived square.
The column-model and lift-existence nodes supply these computing resolutions. -/
theorem cech_augmentation_normalized_naturality
    (f : RingedToposMorphism R S) [IsIso f.ringMap]
    (_hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hS : ∀ (U : Xᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    (fInverse : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R)
    [fInverse.Additive] [PreservesFiniteLimits fInverse] [PreservesFiniteColimits fInverse]
    (_fAdj : fInverse ⊣ f.modules)
    (D : CoherentCechImageModel R) (V : Sheaf J (Type u)) [Epi (terminal.from V)]
    {K K' : ringedSiteModules.{u} R} (I : InjectiveResolution K)
    (I' : InjectiveResolution K') (u : K ⟶ K') :
    (∃ t : I.cocomplex ⟶ I'.cocomplex,
      I.ι ≫ t = (CochainComplex.single₀ _).map u ≫ I'.ι) ∧
    ∀ (t : I.cocomplex ⟶ I'.cocomplex)
      (_ht : I.ι ≫ t = (CochainComplex.single₀ _).map u ≫ I'.ι)
      (b : (f.modules.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
        (D.totalFunctor f.modules V).obj I.cocomplex)
      (b' : (f.modules.mapHomologicalComplex (.up ℕ)).obj I'.cocomplex ⟶
        (D.totalFunctor f.modules V).obj I'.cocomplex),
      D.IsAugmentation f.modules V I.cocomplex b →
      D.IsAugmentation f.modules V I'.cocomplex b' →
      ((f.modules.mapHomologicalComplex (.up ℕ)).map t ≫ b' =
        b ≫ (D.totalFunctor f.modules V).map t) ∧
      (alpha D f.modules V I b ≫ DerivedCategory.Q.map (totalMap D f.modules V t) =
        f.modules.rightDerivedFunctor.map ((QN (ringedSiteModules.{u} R)).map
          ((CochainComplex.single₀ _).map u)) ≫ alpha D f.modules V I' b') := by
  refine ⟨⟨InjectiveResolution.desc u I' I, InjectiveResolution.desc_commutes u I' I⟩, ?_⟩
  intro t ht b b' hb hb'
  have h := augmentation_chain_naturality D f.modules V t b b' hb hb'
  refine ⟨h, ?_⟩
  change ((comparison f.modules I).hom ≫ (QN _).map b) ≫
      (QN _).map ((D.totalFunctor f.modules V).map t) = _
  rw [Category.assoc, ← Functor.map_comp, ← h, Functor.map_comp,
    ← Category.assoc, comparison_naturality f.modules I I' u t ht]
  exact Category.assoc _ _ _

end Derived

private def cochainFunctors (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) :
    CochainComplex (ringedSiteModules.{u} R ⥤+ ringedSiteModules.{u} S) ℕ where
  X n := AdditiveFunctor.of
    (D.cochains V ⋙ HomologicalComplex.eval _ _ n ⋙ G)
  d n m := ⟨{
    app M := G.map (((D.cochains V).obj M).d n m)
    naturality M N f := by
      dsimp
      rw [← G.map_comp, ← G.map_comp]
      exact congrArg G.map (((D.cochains V).map f).comm n m) }⟩
  shape n m h := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext M
    change G.map (((D.cochains V).obj M).d n m) = 0
    rw [HomologicalComplex.shape _ _ _ h, G.map_zero]
  d_comp_d' n m k _ _ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext M
    change G.map (((D.cochains V).obj M).d n m) ≫
      G.map (((D.cochains V).obj M).d m k) = 0
    rw [← G.map_comp, HomologicalComplex.d_comp_d, G.map_zero]

attribute [local implicit_reducible] cochainFunctors
  AdditiveFunctor.of Functor.mapBifunctorHomologicalComplex
  Functor.mapBifunctorHomologicalComplexObj HomologicalComplex₂.ofGradedObject
  GradedObject.mapBifunctor

set_option linter.unusedSectionVars false in
/-- The signed total homotopy has component (-1)^n F_n(s); the bottom resolution
row is zero. This specifies the entire map on every diagonal summand.
Source: Stacks 05RU and 0133, node proof step 4
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).

Proof: put H = (-1)^n G(E_n(s)) on the (n,q) summand into (n,q-1), and zero on q=0.
The two vertical signs multiply to 1, yielding G(E_n(ds+sd)). Horizontal terms cancel
because their signs are (-1)^n and (-1)^(n+1) and restrictions are natural in s.
The diagonals are finite, so these maps define a homotopy of the actual totals. -/
theorem signed_total_homotopy (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) {I I' : CochainComplex (ringedSiteModules.{u} R) ℕ}
    {t₀ t₁ : I ⟶ I'} (s : Homotopy t₀ t₁) :
    ∃ H : Homotopy ((D.totalFunctor G V).map t₀) ((D.totalFunctor G V).map t₁),
      (∀ n q : ℕ,
        (D.bicomplex G V I).ιTotal (.up ℕ) n (q + 1) (n + (q + 1)) rfl ≫
          H.hom (n + (q + 1)) (n + q) =
        ((-1 : ℤ) ^ n) • G.map (((D.cochains V).map (s.hom (q + 1) q)).f n) ≫
          (D.bicomplex G V I').ιTotal (.up ℕ) n q (n + q) rfl) ∧
      (∀ n m : ℕ, (D.bicomplex G V I).ιTotal (.up ℕ) n 0 n (add_zero n) ≫
        H.hom n m = 0) := by
  let m (t : I ⟶ I') : (D.bicomplex G V I).total (.up ℕ) ⟶
      (D.bicomplex G V I').total (.up ℕ) :=
    HomologicalComplex₂.total.map
      ((HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)).map
        (((D.cochains V ⋙ G.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex
          (.up ℕ)).map t)) (.up ℕ)
  change ∃ H : Homotopy (m t₀) (m t₁), _
  let E := cochainFunctors D G V
  let F := AdditiveFunctor.forget (ringedSiteModules.{u} R) (ringedSiteModules.{u} S)
  have : ∀ E : ringedSiteModules.{u} R ⥤+ ringedSiteModules.{u} S,
      (F.obj E).Additive := fun E ↦ E.property
  have : ∀ E : ringedSiteModules.{u} R ⥤+ ringedSiteModules.{u} S,
      (F.obj E).PreservesZeroMorphisms := fun E ↦ inferInstance
  let e (A : CochainComplex (ringedSiteModules.{u} R) ℕ) :
      (((F.mapBifunctorHomologicalComplex (.up ℕ) (.up ℕ)).obj E).obj A) ≅
        D.bicomplex G V A :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ Iso.refl (G.obj (((D.cochains V).obj (A.X q)).X n))) (by
        intros
        change 𝟙 _ ≫ G.map _ = G.map _ ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]
        rfl)) (by
          intros
          apply HomologicalComplex.Hom.ext
          funext q
          change 𝟙 _ ≫ G.map _ = G.map _ ≫ 𝟙 _
          simp only [Category.id_comp, Category.comp_id])
  let et (A : CochainComplex (ringedSiteModules.{u} R) ℕ) :=
    HomologicalComplex₂.total.mapIso (e A) (.up ℕ)
  have hm (t : I ⟶ I') :
      (et I).inv ≫ HomologicalComplex.mapBifunctorMap (𝟙 E) t F (.up ℕ) ≫ (et I').hom =
        m t := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply HomologicalComplex₂.total.hom_ext
    intro n q h
    change _ ≫ ((HomologicalComplex₂.total.map (e I).inv _).f k ≫ _ ≫
      (HomologicalComplex₂.total.map (e I').hom _).f k) =
      _ ≫ (HomologicalComplex₂.total.map _ _).f k
    rw [HomologicalComplex₂.ιTotal_map_assoc,
      HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex₂.ιTotal_map,
      HomologicalComplex₂.ιTotal_map]
    dsimp [e, E, F, cochainFunctors]
    exact Category.id_comp _
  let H₀ := ((HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 E) s F (.up ℕ)).compLeft
    (et I).inv).compRight (et I').hom
  have hm' (t : I ⟶ I') :
      ((et I).inv ≫ HomologicalComplex.mapBifunctorMap (𝟙 E) t F (.up ℕ)) ≫
        (et I').hom = m t := (Category.assoc _ _ _).trans (hm t)
  let H : Homotopy (m t₀) (m t₁) :=
    { hom := H₀.hom
      zero := H₀.zero
      comm i := by
        rw [← hm' t₀, ← hm' t₁]
        exact H₀.comm i }
  refine ⟨H, ?_, ?_⟩
  · intro n q
    dsimp only [H, H₀, Homotopy.compLeft_hom, Homotopy.compRight_hom]
    simp only [Category.assoc]
    change _ ≫ (HomologicalComplex₂.total.map (e I).inv (.up ℕ)).f _ ≫ _ ≫
      (HomologicalComplex₂.total.map (e I').hom (.up ℕ)).f _ = _
    rw [HomologicalComplex₂.ιTotal_map_assoc]
    dsimp only [e, HomologicalComplex.Hom.isoOfComponents_inv_f, Iso.refl_inv]
    erw [Category.id_comp]
    dsimp only [HomologicalComplex.mapBifunctorMapHomotopy₂]
    erw [HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₂_assoc
      (𝟙 E) s F (.up ℕ) n q (q + 1) (n + (q + 1)) (n + q) rfl (by simp)]
    erw [HomologicalComplex.ιMapBifunctorOrZero_eq E I' F (.up ℕ) n q (n + q) rfl]
    rw [Linear.units_smul_comp]
    simp only [Category.assoc]
    erw [HomologicalComplex₂.ιTotal_map]
    dsimp only [e, HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.refl_hom]
    erw [Category.id_comp]
    change ((-1 : ℤˣ) ^ n) • (𝟙 _ ≫ G.map _ ≫ _) = _
    erw [Category.id_comp]
    simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  · intro n m
    dsimp only [H, H₀, Homotopy.compLeft_hom, Homotopy.compRight_hom]
    simp only [Category.assoc]
    change _ ≫ (HomologicalComplex₂.total.map (e I).inv (.up ℕ)).f _ ≫ _ ≫
      (HomologicalComplex₂.total.map (e I').hom (.up ℕ)).f _ = _
    rw [HomologicalComplex₂.ιTotal_map_assoc]
    dsimp only [e, HomologicalComplex.Hom.isoOfComponents_inv_f, Iso.refl_inv]
    erw [Category.id_comp]
    dsimp only [HomologicalComplex.mapBifunctorMapHomotopy₂]
    erw [HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₂_assoc
      (𝟙 E) s F (.up ℕ) n 0 0 n m (add_zero n) (by simp)]
    simp [s.zero 0 0 (by simp [ComplexShape.up_Rel])]

/-- Homotopic lifts induce the same map in the ordinary unbounded derived category.
Source: Stacks 013S and 05RU
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).

Proof: step 4 supplies the signed total homotopy. Extend it by zero and use that Q
factors through the homotopy category. For two lifts of u, step 2 supplies the input
homotopy by injective-resolution uniqueness. -/
theorem lift_independence [HasDerivedCategory.{wY} (ringedSiteModules.{u} S)]
    (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) {K K' : ringedSiteModules.{u} R}
    (I : InjectiveResolution K) (I' : InjectiveResolution K') (u : K ⟶ K')
    (t₀ t₁ : I.cocomplex ⟶ I'.cocomplex)
    (h₀ : I.ι ≫ t₀ = (CochainComplex.single₀ _).map u ≫ I'.ι)
    (h₁ : I.ι ≫ t₁ = (CochainComplex.single₀ _).map u ≫ I'.ι) :
    DerivedCategory.Q.map (totalMap D G V t₀) =
      DerivedCategory.Q.map (totalMap D G V t₁) := by
  obtain ⟨H, _⟩ := signed_total_homotopy D G V
    (InjectiveResolution.descHomotopy u t₀ t₁ h₀ h₁)
  exact DerivedCategory.Q_map_eq_of_homotopy (C := ringedSiteModules.{u} S)
    (H.extend ComplexShape.embeddingUpNat)

/-- Identity comparisons are invertible and total maps obey identities and composition.
Source: Stacks 013S, node proof step 6
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).

Proof: choose a reverse lift of the identity. Uniqueness makes both composites homotopic
to identities, and the signed total homotopy makes their localized maps inverses.
Identity and composition laws follow from strict functoriality of totalization. -/
theorem resolution_comparison_laws [HasDerivedCategory.{wY} (ringedSiteModules.{u} S)]
    (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) {K : ringedSiteModules.{u} R}
    (I I' : InjectiveResolution K) (t : I.cocomplex ⟶ I'.cocomplex)
    (ht : I.ι ≫ t = I'.ι) :
    IsIso (DerivedCategory.Q.map (totalMap D G V t)) ∧
    (∀ A : CochainComplex (ringedSiteModules.{u} R) ℕ, totalMap D G V (𝟙 A) = 𝟙 _) ∧
    (∀ (A B E : CochainComplex (ringedSiteModules.{u} R) ℕ)
      (a : A ⟶ B) (b : B ⟶ E),
      totalMap D G V (a ≫ b) = totalMap D G V a ≫ totalMap D G V b) := by
  have hid : ∀ A : CochainComplex (ringedSiteModules.{u} R) ℕ,
      totalMap D G V (𝟙 A) = 𝟙 _ := by
    intro A
    change (ComplexShape.embeddingUpNat.extendFunctor _).map
      ((D.totalFunctor G V).map (𝟙 A)) = _
    simp only [Functor.map_id]
    rfl
  have hcomp : ∀ (A B E : CochainComplex (ringedSiteModules.{u} R) ℕ)
      (a : A ⟶ B) (b : B ⟶ E),
      totalMap D G V (a ≫ b) = totalMap D G V a ≫ totalMap D G V b := by
    intros A B E a b
    change (ComplexShape.embeddingUpNat.extendFunctor _).map
      ((D.totalFunctor G V).map (a ≫ b)) = _
    simp only [Functor.map_comp]
    rfl
  let t' := InjectiveResolution.desc (𝟙 K) I I'
  have ht' : I'.ι ≫ t' = I.ι := by simp [t']
  have hleft : DerivedCategory.Q.map (totalMap D G V t) ≫
      DerivedCategory.Q.map (totalMap D G V t') = 𝟙 _ := by
    rw [← Functor.map_comp, ← hcomp]
    rw [lift_independence D G V I I (𝟙 K) (t ≫ t') (𝟙 _) (by
      simp [← Category.assoc, ht, ht']) (by simp), hid, Functor.map_id]
  have hright : DerivedCategory.Q.map (totalMap D G V t') ≫
      DerivedCategory.Q.map (totalMap D G V t) = 𝟙 _ := by
    rw [← Functor.map_comp, ← hcomp]
    rw [lift_independence D G V I' I' (𝟙 K) (t' ≫ t) (𝟙 _) (by
      simp [← Category.assoc, ht, ht']) (by simp), hid, Functor.map_id]
  exact ⟨⟨⟨DerivedCategory.Q.map (totalMap D G V t'), hleft, hright⟩⟩, hid, hcomp⟩

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem refinement_cochains_id (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) : D.refinement (𝟙 V) = 𝟙 _ := by
  have hn : Arrow.mapCechNerve
      (show Arrow.mk (terminal.from V) ⟶ Arrow.mk (terminal.from V) from
        Arrow.homMk (𝟙 V) (𝟙 _) (terminal.hom_ext _ _)) = 𝟙 _ := by
    apply NatTrans.ext
    funext n
    apply WidePullback.hom_ext <;> simp
  dsimp only [CoherentCechImageModel.refinement]
  rw [hn, NatTrans.rightOp_id]
  rw [Functor.whiskerRight_id', Functor.map_id, Functor.whiskerRight_id']
  rfl

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem refinement_cochains_comp (D : CoherentCechImageModel R)
    {V W Z : Sheaf J (Type u)} (r : W ⟶ V) (r' : Z ⟶ W) :
    D.refinement (r' ≫ r) = D.refinement r ≫ D.refinement r' := by
  have hn : Arrow.mapCechNerve
      (show Arrow.mk (terminal.from Z) ⟶ Arrow.mk (terminal.from V) from
        Arrow.homMk (r' ≫ r) (𝟙 _) (terminal.hom_ext _ _)) =
      Arrow.mapCechNerve
        (show Arrow.mk (terminal.from Z) ⟶ Arrow.mk (terminal.from W) from
          Arrow.homMk r' (𝟙 _) (terminal.hom_ext _ _)) ≫
      Arrow.mapCechNerve
        (show Arrow.mk (terminal.from W) ⟶ Arrow.mk (terminal.from V) from
          Arrow.homMk r (𝟙 _) (terminal.hom_ext _ _)) := by
    apply NatTrans.ext
    funext n
    apply WidePullback.hom_ext <;> simp [Category.assoc]
  dsimp only [CoherentCechImageModel.refinement]
  rw [hn, NatTrans.rightOp_comp]
  simp only [Functor.whiskerRight_comp, Functor.map_comp]

set_option linter.unusedSectionVars false in
/-- Actual refinement maps commute with augmentations, are strictly functorial, and
commute with every resolution chain map. The first equality gives Q(rho) alpha = alpha'.
Source: Stacks 04J4, node proof steps 7--8
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).

Proof: maps of fibre powers commute with all cofaces. D.restriction fixes their actual
maps by counit transposition. D.augmentation_naturality gives the square on (0,q),
and hence on the total. Functoriality of D.image gives identity and composition, and
naturality at each t^q gives the commuting resolution/refinement square. -/
theorem refinement_laws (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    {V W Z : Sheaf J (Type u)} (r : W ⟶ V) (r' : Z ⟶ W)
    (I I' : CochainComplex (ringedSiteModules.{u} R) ℕ) (t : I ⟶ I')
    (b : (G.mapHomologicalComplex (.up ℕ)).obj I ⟶ (D.totalFunctor G V).obj I)
    (b' : (G.mapHomologicalComplex (.up ℕ)).obj I ⟶ (D.totalFunctor G W).obj I)
    (hb : D.IsAugmentation G V I b) (hb' : D.IsAugmentation G W I b') :
    (b ≫ D.totalRefinement G r I = b') ∧
    (D.totalRefinement G (𝟙 V) I = 𝟙 _) ∧
    (D.totalRefinement G (r' ≫ r) I =
      D.totalRefinement G r I ≫ D.totalRefinement G r' I) ∧
    ((D.totalFunctor G V).map t ≫ D.totalRefinement G r I' =
      D.totalRefinement G r I ≫ (D.totalFunctor G W).map t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply HomologicalComplex.Hom.ext
    funext q
    simp only [HomologicalComplex.comp_f, hb q, hb' q, Category.assoc]
    change _ ≫ _ ≫ (HomologicalComplex₂.total.map _ _).f q = _
    rw [HomologicalComplex₂.ιTotal_map]
    change G.map _ ≫ G.map _ ≫ _ = _
    rw [← Category.assoc, ← G.map_comp]
    congr 1
    exact congrArg G.map (NatTrans.congr_app
      (D.augmentation_naturality ((Arrow.mapCechNerve
        (show Arrow.mk (terminal.from W) ⟶ Arrow.mk (terminal.from V) from
          Arrow.homMk r (𝟙 _) (terminal.hom_ext _ _))).app
            (op (SimplexCategory.mk 0)))) (I.X q))
  · dsimp only [CoherentCechImageModel.totalRefinement]
    rw [refinement_cochains_id]
    simp
    rfl
  · dsimp only [CoherentCechImageModel.totalRefinement]
    rw [refinement_cochains_comp]
    simp only [Functor.whiskerRight_comp, NatTrans.mapHomologicalComplex_comp,
      NatTrans.comp_app, Functor.map_comp, HomologicalComplex₂.total.map_comp]
  · exact (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (Functor.whiskerRight (D.refinement r)
        (G.mapHomologicalComplex (.up ℕ))) (.up ℕ))
      (HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ) ⋙
        HomologicalComplex₂.totalFunctor _ (.up ℕ) (.up ℕ) (.up ℕ))).naturality t

/-- Refinement naturality with exactly the canonical resolution comparison used in alpha.
Source: Stacks 04J4 and 070I
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).

Proof: localize the augmentation equality of step 7 and precompose by e_I inverse.
Step 8 gives identity, composition and commutation with every resolution comparison. -/
theorem alpha_refinement [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wY} (ringedSiteModules.{u} S)]
    [Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} R)]
    (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    {V W : Sheaf J (Type u)} [Epi (terminal.from V)] [Epi (terminal.from W)]
    (r : W ⟶ V) {K : ringedSiteModules.{u} R} (I : InjectiveResolution K)
    (b : (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      (D.totalFunctor G V).obj I.cocomplex)
    (b' : (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      (D.totalFunctor G W).obj I.cocomplex)
    (hb : D.IsAugmentation G V I.cocomplex b)
    (hb' : D.IsAugmentation G W I.cocomplex b') :
    alpha D G V I b ≫ (QN (ringedSiteModules.{u} S)).map (D.totalRefinement G r I.cocomplex) =
      alpha D G W I b' := by
  have h := (refinement_laws D G r (𝟙 _) I.cocomplex I.cocomplex
    (𝟙 _) b b' hb hb').1
  dsimp only [alpha]
  rw [Category.assoc, ← Functor.map_comp, h]

set_option linter.unusedSectionVars false in
/-- The localization unit commutes with the zero-column differential.
Source: Stacks 04IE, node proof step 9
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).

Proof: the zero-column differential is G of the endofunctor applied to I.d.
Naturality of D.augmentation gives the square before G, and G preserves its
composition. In Cech degree zero the vertical sign is 1. -/
theorem columnUnit_comm (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (i j : ℕ) (_h : (ComplexShape.up ℕ).Rel i j) :
    G.map (I.d i j) ≫
        G.map ((D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).app
          (I.X j)) =
      G.map ((D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).app
          (I.X i)) ≫ ((D.bicomplex G V I).X 0).d i j := by
  simpa [CoherentCechImageModel.bicomplex, CoherentCechImageModel.cochains,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.map] using congrArg G.map
    ((D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).naturality
      (I.d i j))

/-- The actual chain map giving the zero-column localization unit before inclusion
in the total. Source: Stacks 04IE
(blueprint: lem-sfb-cech-augmentation-normalized-naturality). -/
def columnUnit (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ) :
    (G.mapHomologicalComplex (.up ℕ)).obj I ⟶ (D.bicomplex G V I).X 0 where
  f q := G.map
    ((D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).app (I.X q))
  comm' i j h := (columnUnit_comm D G V I i j h).symm

/-- The unique localization-unit augmentation. Its data are fixed on every degree,
so existence does not choose an unspecified chain map.
Source: Stacks 04IE and 0133, node proof steps 1 and 3
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).

Proof: insert G of the localization unit in (0,q), and zero in all other summands.
The two cofaces agree on the unit, so its horizontal differential vanishes. Naturality
of the unit gives compatibility with the vertical differential. These facts give the
chain map. IsAugmentation specifies every component and hence gives uniqueness. -/
theorem augmentation_exists (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ) :
    ∃! b : (G.mapHomologicalComplex (.up ℕ)).obj I ⟶ (D.totalFunctor G V).obj I,
      D.IsAugmentation G V I b := by
  have hz : columnUnit D G V I ≫ (D.bicomplex G V I).d 0 1 = 0 := by
    apply HomologicalComplex.Hom.ext
    funext q
    change G.map _ ≫ G.map _ = 0
    rw [← G.map_comp]
    change G.map (_ ≫ AlgebraicTopology.AlternatingCofaceMapComplex.objD
      (((sheafCoverNerve V).rightOp ⋙ D.image).flip.obj (I.X q)) 0) = 0
    dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one, neg_smul, one_smul,
      Preadditive.comp_add, Preadditive.comp_neg]
    have h (i : Fin 2) :
        (D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).app (I.X q) ≫
          CosimplicialObject.δ (((sheafCoverNerve V).rightOp ⋙ D.image).flip.obj (I.X q)) i =
        (D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 1)))).app (I.X q) :=
      NatTrans.congr_app (D.augmentation_naturality
        ((sheafCoverNerve V).map (SimplexCategory.δ i).op)) (I.X q)
    rw [h 0, h 1, add_neg_cancel, G.map_zero]
  let b : (G.mapHomologicalComplex (.up ℕ)).obj I ⟶ (D.bicomplex G V I).total (.up ℕ) :=
    { f q := (columnUnit D G V I).f q ≫
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
        have hz' := congrArg (fun f ↦ f.f i) hz
        simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz'
        change _ ≫ ((1 : ℤˣ) • _) + _ ≫ ((1 : ℤˣ) • _) = _
        simp only [one_smul]
        rw [← Category.assoc, hz', zero_comp, zero_add]
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun z ↦ z ≫
            (D.bicomplex G V I).ιTotal (.up ℕ) 0 (i + 1) (i + 1) (zero_add (i + 1)))
              ((columnUnit D G V I).comm i (i + 1))) }
  refine ⟨b, fun _ ↦ rfl, ?_⟩
  intro b' hb'
  apply HomologicalComplex.Hom.ext
  funext q
  exact hb' q

private def projectionComponent {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) (k : ℕ) :
    (K.total (.up ℕ)).X k ⟶ (K.X 0).X k :=
  K.totalDesc fun n q h ↦ if hn : n = 0 then
    eqToHom (by
      have hq : q = k := by simpa [hn] using h
      rw [hn, hq])
    else 0

private theorem ι_projectionComponent_zero {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) (q : ℕ) :
    K.ιTotal (.up ℕ) 0 q q (zero_add q) ≫ projectionComponent K q = 𝟙 _ := by
  simp [projectionComponent]

private theorem ι_projectionComponent_ne {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) (n q k : ℕ)
    (h : n + q = k) (hn : n ≠ 0) :
    K.ιTotal (.up ℕ) n q k h ≫ projectionComponent K k = 0 := by
  simp [projectionComponent, hn]

private def zeroColumnProjection {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) : K.total (.up ℕ) ⟶ K.X 0 where
  f := projectionComponent K
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    apply HomologicalComplex₂.total.hom_ext
    intro n q h
    change n + q = i at h
    cases n with
    | zero =>
      have hi : q = i := by omega
      rcases hi with rfl
      rw [HomologicalComplex₂.total_d, Preadditive.add_comp,
        Preadditive.comp_add, HomologicalComplex₂.ι_D₁_assoc,
        HomologicalComplex₂.ι_D₂_assoc,
        HomologicalComplex₂.d₁_eq _ _
          (show (ComplexShape.up ℕ).Rel 0 (0 + 1) by rfl) _ _ (by dsimp; omega),
        HomologicalComplex₂.d₂_eq _ _ _
          (show (ComplexShape.up ℕ).Rel q (q + 1) by rfl) _ (by dsimp; omega)]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [ι_projectionComponent_ne K (0 + 1) q (q + 1) (by omega) (by omega)]
      simp only [comp_zero, smul_zero, zero_add]
      change K.ιTotal (.up ℕ) 0 q q (zero_add q) ≫ projectionComponent K q ≫
        (K.X 0).d q (q + 1) =
          (1 : ℤˣ) • (K.X 0).d q (q + 1) ≫
            K.ιTotal (.up ℕ) 0 (q + 1) (q + 1) (zero_add _) ≫
              projectionComponent K (q + 1)
      rw [← Category.assoc, ι_projectionComponent_zero, Category.id_comp, one_smul,
        ι_projectionComponent_zero, Category.comp_id]
    | succ n =>
      subst i
      rw [HomologicalComplex₂.total_d, Preadditive.add_comp,
        Preadditive.comp_add, HomologicalComplex₂.ι_D₁_assoc,
        HomologicalComplex₂.ι_D₂_assoc,
        HomologicalComplex₂.d₁_eq _ _
          (show (ComplexShape.up ℕ).Rel (n + 1) ((n + 1) + 1) by rfl) _ _ (by dsimp; omega),
        HomologicalComplex₂.d₂_eq _ _ _
          (show (ComplexShape.up ℕ).Rel q (q + 1) by rfl) _ (by dsimp; omega)]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [ι_projectionComponent_ne K ((n + 1) + 1) q (n + 1 + q + 1) (by omega) (by omega)]
      simp only [comp_zero, smul_zero, zero_add]
      rw [← Category.assoc, ι_projectionComponent_ne K (n + 1) q (n + 1 + q)
        rfl (by omega), zero_comp,
        ι_projectionComponent_ne K (n + 1) (q + 1) (n + 1 + q + 1) (by omega) (by omega)]
      simp only [comp_zero, smul_zero]

/-- Projection to the zero Cech column, its unit representative, and its ordinary
adjoint transpose and counit normalization before applying G.
Source: Stacks 04IE, node proof step 9
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).

Proof: project each finite diagonal to its (0,q) summand. The horizontal differential
only increases Cech degree, and the vertical sign in column zero is 1, so projection
is a chain map. The component formula for b gives b followed by projection = columnUnit.
D.unit identifies its transpose with the identity. The adjunction triangle gives
pull(unit) followed by counit = identity, term by term. -/
theorem projection_normalization (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (b : (G.mapHomologicalComplex (.up ℕ)).obj I ⟶ (D.totalFunctor G V).obj I)
    (hb : D.IsAugmentation G V I b) :
    ∃ π : (D.totalFunctor G V).obj I ⟶ (D.bicomplex G V I).X 0,
      (∀ q : ℕ, (D.bicomplex G V I).ιTotal (.up ℕ) 0 q q (zero_add q) ≫ π.f q = 𝟙 _) ∧
      (∀ (n q k : ℕ) (h : n + q = k), n ≠ 0 →
        (D.bicomplex G V I).ιTotal (.up ℕ) n q k h ≫ π.f k = 0) ∧
      b ≫ π = columnUnit D G V I ∧
      (∀ q : ℕ,
        (columnUnit D G V I).f q ≫ G.map
          ((D.imageIso ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).hom.app
            (I.X q)) =
        G.map ((D.adj ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).unit.app
          (I.X q))) ∧
      (∀ q : ℕ,
        ((D.adj ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).homEquiv _ _).symm
          (((D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).app
            (I.X q)) ≫
            (D.imageIso ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).hom.app
              (I.X q)) = 𝟙 _) ∧
      (∀ q : ℕ,
        (elementModulePullback R
          ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).map
          ((D.adj ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).unit.app (I.X q)) ≫
        (D.adj ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).counit.app
          ((elementModulePullback R
            ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).obj (I.X q)) = 𝟙 _) := by
  let π := zeroColumnProjection (D.bicomplex G V I)
  refine ⟨π, ι_projectionComponent_zero _, ι_projectionComponent_ne _, ?_, ?_, ?_, ?_⟩
  · apply HomologicalComplex.Hom.ext
    funext q
    change b.f q ≫ projectionComponent (D.bicomplex G V I) q = _
    rw [hb q, Category.assoc, ι_projectionComponent_zero]
    exact Category.comp_id _
  · intro q
    change G.map _ ≫ G.map _ = _
    rw [← G.map_comp]
    congr 1
    apply ((D.adj _).homEquiv _ _).symm.injective
    exact (D.unit _ _).trans (by simp)
  · intro q
    exact D.unit _ _
  · intro q
    exact (D.adj _).left_triangle_components _

/-- The projected derived augmentation retains exactly the zero-column unit, under e_I.
Source: Stacks 070I and 04IE, node proof steps 9--10
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).

Proof: use projection_normalization and apply Q after extension by zero; then
precompose by the canonical inverse resolution comparison. This is precisely alpha,
so no claim about a transpose of a map on the target topos is made. -/
theorem alpha_projection [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wY} (ringedSiteModules.{u} S)]
    [Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} R)]
    (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) {K : ringedSiteModules.{u} R} (I : InjectiveResolution K)
    (b : (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      (D.totalFunctor G V).obj I.cocomplex)
    (hb : D.IsAugmentation G V I.cocomplex b) :
    ∃ π : (D.totalFunctor G V).obj I.cocomplex ⟶ (D.bicomplex G V I.cocomplex).X 0,
      (∀ q : ℕ, (D.bicomplex G V I.cocomplex).ιTotal (.up ℕ) 0 q q (zero_add q) ≫
        π.f q = 𝟙 _) ∧
      (∀ (n q k : ℕ) (h : n + q = k), n ≠ 0 →
        (D.bicomplex G V I.cocomplex).ιTotal (.up ℕ) n q k h ≫ π.f k = 0) ∧
      b ≫ π = columnUnit D G V I.cocomplex ∧
      alpha D G V I b ≫ (QN (ringedSiteModules.{u} S)).map π =
        (comparison G I).hom ≫
          (QN (ringedSiteModules.{u} S)).map (columnUnit D G V I.cocomplex) := by
  obtain ⟨π, hπ, hzero, hbπ, _⟩ := projection_normalization D G V I.cocomplex b hb
  refine ⟨π, hπ, hzero, hbπ, ?_⟩
  dsimp only [alpha]
  rw [Category.assoc, ← Functor.map_comp, hbπ]

-- Use Mathlib's small-site instances directly; the generic small-model transport
-- otherwise expands inside the derived-category structures during kernel checking.
attribute [-instance] CategoryTheory.siteAbelianHasSheafify
  CategoryTheory.siteAbelianWEqualsLocallyBijective in
/-- The derived slice adjunction with its termwise representatives. Exactness,
additivity and existence of slice resolutions are conclusions of the existence theorem,
not additional assumptions on the ringed topos. The Hom formula fixes the adjunction.
Source: Stacks 04IE, 070I and 09T5
(blueprint: lem-sfb-cech-augmentation-normalized-naturality). -/
structure SliceNormalization [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
    (D : CoherentCechImageModel R) (A : Sheaf J (Type u))
    [HasDerivedCategory.{wA} (ringedSiteModules.{u} (elementRing R A))] where
  [pullAdditive : (elementModulePullback R A).Additive]
  [pullLimits : PreservesFiniteLimits (elementModulePullback R A)]
  [pullColimits : PreservesFiniteColimits (elementModulePullback R A)]
  [sliceResolutions : Abelian.HasKInjectiveResolutions
    (ringedSiteModules.{u} (elementRing R A))]
  derivedAdj : (elementModulePullback R A).mapDerivedCategory ⊣ (D.push A).rightDerivedFunctor
  hom_formula : ∀ (I : CochainComplex (ringedSiteModules.{u} R) ℤ)
    (M : CochainComplex (ringedSiteModules.{u} (elementRing R A)) ℤ)
    (a : ((elementModulePullback R A).mapHomologicalComplex (.up ℤ)).obj I ⟶ M),
    derivedAdj.homEquiv (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj M)
      ((elementModulePullback R A).mapDerivedCategoryFactors.hom.app I ≫
        DerivedCategory.Q.map a) =
      DerivedCategory.Q.map (((D.adj A).mapHomologicalComplex (.up ℤ)).homEquiv I M a) ≫
        (D.push A).rightDerivedFunctorUnitQ M
  restricted_injective : ∀ (K : ringedSiteModules.{u} R) (I : InjectiveResolution K),
    CochainComplex.IsKInjective
      (((elementModulePullback R A).mapHomologicalComplex (.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat))
  unit_formula : ∀ I : CochainComplex (ringedSiteModules.{u} R) ℤ,
    derivedAdj.unit.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map (((D.adj A).mapHomologicalComplex (.up ℤ)).unit.app I) ≫
        (D.push A).rightDerivedFunctorUnitQ
          (((elementModulePullback R A).mapHomologicalComplex (.up ℤ)).obj I) ≫
        (D.push A).rightDerivedFunctor.map
          ((elementModulePullback R A).mapDerivedCategoryFactors.inv.app I)
  counit_formula : ∀ M : CochainComplex (ringedSiteModules.{u} (elementRing R A)) ℤ,
    (elementModulePullback R A).mapDerivedCategory.map
        ((D.push A).rightDerivedFunctorUnitQ M) ≫
      derivedAdj.counit.app (DerivedCategory.Q.obj M) =
    (elementModulePullback R A).mapDerivedCategoryFactors.hom.app
        (((D.push A).mapHomologicalComplex (.up ℤ)).obj M) ≫
      DerivedCategory.Q.map (((D.adj A).mapHomologicalComplex (.up ℤ)).counit.app M)
  triangle : ∀ I : CochainComplex (ringedSiteModules.{u} R) ℤ,
    (elementModulePullback R A).mapDerivedCategory.map
        (derivedAdj.unit.app (DerivedCategory.Q.obj I)) ≫
      derivedAdj.counit.app
        ((elementModulePullback R A).mapDerivedCategory.obj (DerivedCategory.Q.obj I)) = 𝟙 _

private theorem derivesOnComplexes
    {B : Type*} {E : Type*} [Category* B] [Category* E]
    [Abelian B] [Abelian E] [HasDerivedCategory E]
    (F : B ⥤ E) [F.Additive] :
    (CochainComplex.KInjectives.localizerMorphism B).Derives
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro I I' f hf
  have : I.obj.IsKInjective := I.property
  have : I'.obj.IsKInjective := I'.property
  have hq : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    erw [← he]
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

/-- The ordinary localization normalization survives the canonical right-derived
comparisons in the unbounded derived category.
Source: Stacks 04IE, 04J4, 070I and 09T5, node proof step 10
(blueprint: lem-sfb-cech-augmentation-normalized-naturality).

Proof: the exact additive left adjoint j_! of j^* implies that j^* preserves injectives,
so j^*I is a nonnegative complex of injectives and is K-injective. The small element
site has K-injective resolutions. Apply resolving-derived-adjunction normalization
with the whole homotopy category as resolving class, since j^* is exact. Its Hom
formula is hom_formula. Transpose the identity of j^*I to obtain unit_formula, and
transpose the ordinary counit to obtain counit_formula. The derived comparison on
j^*I is invertible by K-injectivity, so these are termwise representatives. The
ordinary triangle from step 9 then yields the displayed derived triangle. Finally
alpha_projection transports precisely this normalization to the projected alpha. -/
theorem slice_normalization [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
    (D : CoherentCechImageModel R) (A : Sheaf J (Type u))
    [HasDerivedCategory.{wA} (ringedSiteModules.{u} (elementRing R A))] :
    Nonempty (SliceNormalization D A) := by
  classical
  have : (elementModulePullback.{u, u} R A).IsLeftAdjoint := (D.adj A).isLeftAdjoint
  obtain ⟨extAdj⟩ := elementModuleExtension_adjunction R A
  have : (elementModulePullback.{u, u} R A).IsRightAdjoint := extAdj.isRightAdjoint
  have : PreservesFiniteLimits (elementModulePullback.{u, u} R A) := inferInstance
  have : PreservesFiniteColimits (elementModulePullback.{u, u} R A) := inferInstance
  have : PreservesBinaryBiproducts (elementModulePullback.{u, u} R A) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (elementModulePullback.{u, u} R A).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} (elementRing R A)) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses (elementTopology A) (elementRing R A)
  have : Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} (elementRing R A)) :=
    inferInstance
  let G := elementModulePullback.{u, u} R A
  let F := D.push A
  let β : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    { app := F.rightDerivedFunctorUnitQ
      naturality _ _ f := F.rightDerivedFunctorUnitQ_naturality f }
  have hβ : F.rightDerivedFunctor.IsRightDerivedFunctor β
      (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    apply (derivesOnComplexes F).isRightDerivedFunctor_of_isIso β
    intro I
    have : I.obj.IsKInjective := I.property
    change IsIso (F.rightDerivedFunctorUnitQ I.obj)
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  let := hβ
  have hLG : G.mapDerivedCategory.IsLeftDerivedFunctor G.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso _ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ G.mapDerivedCategoryFactors
  let := hLG
  have hLGRF : (G.mapDerivedCategory ⋙ F.rightDerivedFunctor).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight G.mapDerivedCategoryFactors.hom F.rightDerivedFunctor)
      (HomologicalComplex.quasiIso _ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight G.mapDerivedCategoryFactors F.rightDerivedFunctor)
  let := hLGRF
  have hRFLG : (F.rightDerivedFunctor ⋙ G.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight β G.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    have hd : (CochainComplex.KInjectives.localizerMorphism _).Derives
        (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ G.mapDerivedCategory) := by
      intro I I' f hf
      have : IsIso (DerivedCategory.Q.map
          ((F.mapHomologicalComplex _).map f.hom)) := (derivesOnComplexes F) f hf
      change IsIso (G.mapDerivedCategory.map
        (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.hom)))
      infer_instance
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have : IsIso (β.app I.obj) :=
      (derivesOnComplexes F).isIso_of_isRightDerivedFunctor β I
    change IsIso (G.mapDerivedCategory.map (β.app I.obj) ≫ 𝟙 _)
    infer_instance
  let := hRFLG
  let ac := (D.adj A).mapHomologicalComplex (.up ℤ)
  let d := ac.derived (HomologicalComplex.quasiIso _ (.up ℤ))
    (HomologicalComplex.quasiIso _ (.up ℤ)) G.mapDerivedCategoryFactors.hom β
  refine ⟨{
    derivedAdj := d
    hom_formula := ?_
    restricted_injective := ?_
    unit_formula := ?_
    counit_formula := ?_
    triangle := ?_ }⟩
  · intro I M a
    change d.unit.app _ ≫ F.rightDerivedFunctor.map
      (G.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map a) =
        DerivedCategory.Q.map (ac.homEquiv I M a) ≫ β.app M
    rw [Functor.map_comp, ← Category.assoc]
    have hu := ac.derivedη_fac_app (HomologicalComplex.quasiIso _ (.up ℤ))
      G.mapDerivedCategoryFactors.hom β I
    change d.unit.app _ ≫ F.rightDerivedFunctor.map
      (G.mapDerivedCategoryFactors.hom.app I) = _ at hu
    have hn := β.naturality a
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) ≫ β.app M =
      β.app _ ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map a) at hn
    rw [hu, Category.assoc, ← hn, ← DerivedCategory.Q.map_comp_assoc]
    rfl
  · intro K I
    have := (element_module_presheaf_extension R A).1
    let e := SheafOfModules.pullbackIso (F := elementProjection A) (𝟙 (elementRing R A))
    have : PreservesFiniteLimits
        (PresheafOfModules.pullback.{u} (F := elementProjection A)
          (𝟙 (elementRing R A).obj) ⋙ PresheafOfModules.sheafification (𝟙 R.obj)) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteLimits
        (SheafOfModules.forget (elementRing R A) ⋙
          PresheafOfModules.pullback.{u} (F := elementProjection A)
            (𝟙 (elementRing R A).obj) ⋙ PresheafOfModules.sheafification (𝟙 R.obj)) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteLimits (elementModuleExtension.{u} R A) :=
      preservesFiniteLimits_of_natIso
        (show (SheafOfModules.forget (elementRing R A) ⋙
          PresheafOfModules.pullback.{u} (F := elementProjection A)
            (𝟙 (elementRing R A).obj) ⋙
          PresheafOfModules.sheafification (𝟙 R.obj)) ≅
            elementModuleExtension.{u} R A from e.symm)
    have : G.PreservesInjectiveObjects :=
      extAdj.preservesInjectiveObjects_of_preservesFiniteLimits
    have : ∀ q : ℕ, Injective ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex |>.X q) :=
      fun q ↦ G.injective_obj (I.cocomplex.X q)
    exact CochainComplex.isKInjective_of_iso
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat G).symm
  · intro I
    change d.unit.app _ = DerivedCategory.Q.map (ac.unit.app I) ≫ β.app _ ≫
      F.rightDerivedFunctor.map (G.mapDerivedCategoryFactors.inv.app I)
    have hu := ac.derivedη_fac_app (HomologicalComplex.quasiIso _ (.up ℤ))
      G.mapDerivedCategoryFactors.hom β I
    change d.unit.app _ ≫ F.rightDerivedFunctor.map
      (G.mapDerivedCategoryFactors.hom.app I) = _ at hu
    rw [← cancel_mono (F.rightDerivedFunctor.map
      (G.mapDerivedCategoryFactors.hom.app I))]
    change d.unit.app (DerivedCategory.Q.obj I) ≫ F.rightDerivedFunctor.map
      (G.mapDerivedCategoryFactors.hom.app I) = _
    rw [hu]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [Functor.map_id, Category.comp_id]
  · intro M
    exact ac.derivedε_fac_app (HomologicalComplex.quasiIso _ (.up ℤ))
      G.mapDerivedCategoryFactors.hom β M
  · intro I
    exact d.left_triangle_components _

end CategoryTheory.CechAugmentationNormalized
