/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CechInjectiveColumnModel
public import WeilConjectures.CategoryTheory.CechAugmentationNormalizedNaturality
import all WeilConjectures.CategoryTheory.CechAugmentationNormalizedNaturality
import all WeilConjectures.CategoryTheory.CechInjectiveColumnModel
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
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
import WeilConjectures.CategoryTheory.CechInjectiveImageAugmentation

/-! # The coherent augmented Čech model after arbitrary exact-inverse-image pushforward

Source: Stacks Project, sites-cohomology.tex, Tag 03FC; derived.tex, Tags 070J and
09T5; sites-modules.tex, Tags 04IE and 04J4
(blueprint: lem-sfb-cech-pushforward-augmented-model).

The data below retain every cosimplicial operator. Their equations fix the derived
comparisons on a single resolution and the entire chain augmentation. In particular,
the structural ring map of the ringed-topos morphism need not be invertible.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async true
set_option maxRecDepth 1000
set_option synthInstance.maxSize 4096

universe u wX wY wA

open CategoryTheory CategoryTheory.Limits Opposite

-- On these small sites use Mathlib's direct instances, avoiding small-model transport.
attribute [-instance] CategoryTheory.siteAbelianHasSheafify
  CategoryTheory.siteAbelianWEqualsLocallyBijective

namespace CategoryTheory.CechPushforward

variable {C X : Type u} [SmallCategory C] [SmallCategory X]
  {J : GrothendieckTopology C} {L : GrothendieckTopology X}
  {R : Sheaf J RingCat.{u}} {S : Sheaf L RingCat.{u}}

section Models

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}]

private theorem smallSheafify {T : Type u} [SmallCategory T]
    (K : GrothendieckTopology T) : HasSheafify K AddCommGrpCat.{u} := inferInstance

private theorem smallLocallyBijective {T : Type u} [SmallCategory T]
    (K : GrothendieckTopology T) : K.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstance

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem moduleFiniteLimits (R : Sheaf J RingCat.{u}) :
    HasFiniteLimits (ringedSiteModules.{u} R) := inferInstance

private theorem moduleFiniteColimits (R : Sheaf J RingCat.{u}) :
    HasFiniteColimits (ringedSiteModules.{u} R) := inferInstance

private theorem moduleNatTotal (R : Sheaf J RingCat.{u})
    (B : HomologicalComplex₂ (ringedSiteModules.{u} R) (.up ℕ) (.up ℕ)) :
    B.HasTotal (.up ℕ) := inferInstance


/-- The canonical column functor of the existing coherent bicomplex. Its first index
is Čech degree and its second is resolution degree.
Source: Stacks 03FC and 0133 (blueprint: lem-sfb-cech-pushforward-augmented-model). -/
def columnFunctor (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) (n : SimplexCategory) :
    CochainComplex (ringedSiteModules.{u} R) ℕ ⥤
      CochainComplex (ringedSiteModules.{u} S) ℕ :=
  (D.cochains V ⋙ HomologicalComplex.eval _ (.up ℕ) n.len ⋙ G).mapHomologicalComplex
    (.up ℕ)

/-- The actual covering-refinement arrow on a column, before localization.
Source: Stacks 04J4 (blueprint: lem-sfb-cech-pushforward-augmented-model). -/
def columnRefinement (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    {V W : Sheaf J (Type u)} (r : W ⟶ V) (n : SimplexCategory)
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ) :
    (columnFunctor D G V n).obj I ⟶ (columnFunctor D G W n).obj I :=
  (NatTrans.mapHomologicalComplex
    (Functor.whiskerRight (D.refinement r)
      (HomologicalComplex.eval _ (.up ℕ) n.len ⋙ G)) (.up ℕ)).app I

/-- The actual chain transition for a module lift and a covering refinement, on a column.
Source: Stacks 03FC and 04J4 (blueprint: lem-sfb-cech-pushforward-augmented-model). -/
def columnTransition (D : CoherentCechImageModel R)
    (f : RingedToposMorphism R S) {V W : Sheaf J (Type u)} (r : W ⟶ V)
    {I I' : CochainComplex (ringedSiteModules.{u} R) ℕ} (t : I ⟶ I')
    (n : SimplexCategory) :
    (columnFunctor D f.modules V n).obj I ⟶ (columnFunctor D f.modules W n).obj I' :=
  (columnFunctor D f.modules V n).map t ≫ columnRefinement D f.modules r n I'

/-- The actual signed-total transition for a module lift and a covering refinement.
Source: Stacks 0133 and 04J4 (blueprint: lem-sfb-cech-pushforward-augmented-model). -/
def totalTransition (D : CoherentCechImageModel R)
    (f : RingedToposMorphism R S) {V W : Sheaf J (Type u)} (r : W ⟶ V)
    {I I' : CochainComplex (ringedSiteModules.{u} R) ℕ} (t : I ⟶ I') :
    (D.totalFunctor f.modules V).obj I ⟶ (D.totalFunctor f.modules W).obj I' :=
  (D.totalFunctor f.modules V).map t ≫ D.totalRefinement f.modules r I'

/-- All cofaces and codegeneracies are the actual restriction maps in the chosen columns.
Source: Stacks 03FC and 04J4 (blueprint: lem-sfb-cech-pushforward-augmented-model). -/
def IsColumnDiagram (D : CoherentCechImageModel R) (f : RingedToposMorphism R S)
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (B : CosimplicialObject (CochainComplex (ringedSiteModules.{u} S) ℕ))
    (sigma : ∀ n : SimplexCategory, B.obj n ≅ (columnFunctor D f.modules V n).obj I) : Prop :=
  ∀ (n m : SimplexCategory) (θ : n ⟶ m) (q : ℕ),
    (sigma n).inv.f q ≫ (B.map θ).f q ≫ (sigma m).hom.f q =
      f.modules.map ((D.image.map (((sheafCoverNerve V).map θ.op).op)).app (I.X q))

section Helpers



attribute [local instance] moduleFiniteLimits moduleFiniteColimits moduleNatTotal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local implicit_reducible] CoherentCechImageModel.bicomplex
  CoherentCechImageModel.totalFunctor CoherentCechImageModel.total
  HomologicalComplex₂.flipFunctor HomologicalComplex₂.totalFunctor
  Functor.mapHomologicalComplex HomologicalComplex₂.flip


private def identityMorphism (R : Sheaf J RingCat.{u}) : RingedToposMorphism R R where
  inverse := 𝟭 _
  direct := 𝟭 _
  adj := Adjunction.id
  leftExact := inferInstance
  ringMap := 𝟙 _
  ring_zero := by intro T z h U t; exact h U t
  ring_one := by intro T z h U t; exact h U t
  ring_add := by intro T x y z h U t; exact h U t
  ring_mul := by intro T x y z h U t; exact h U t
  modules := 𝟭 _
  additive := inferInstance
  underlying := Iso.refl _
  module_linear := by intro M T a x y z h U t; exact h U t

private instance (R : Sheaf J RingCat.{u}) : IsIso (identityMorphism R).ringMap :=
  inferInstanceAs (IsIso (𝟙 _))

namespace Aux

variable (D : CoherentCechImageModel R)
  (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
  (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ)


private noncomputable def bicomplexIso :
    (AlgebraicTopology.alternatingCofaceMapComplex
      (CochainComplex (ringedSiteModules.{u} S) ℕ)).obj (CechColumnAux.diagram R D G V I) ≅
      D.bicomplex G V I :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro n m h
    have hm : n + 1 = m := h
    subst m
    apply HomologicalComplex.Hom.ext
    funext q
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    symm
    change (((AlgebraicTopology.alternatingCofaceMapComplex
      (CochainComplex (ringedSiteModules.{u} S) ℕ)).obj (CechColumnAux.diagram R D G V I)).d
        n (n + 1)).f q = _
    simp only [AlgebraicTopology.alternatingCofaceMapComplex_obj,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
    change (AlgebraicTopology.AlternatingCofaceMapComplex.objD
      (CechColumnAux.diagram R D G V I) n).f q = G.map
        (((AlgebraicTopology.alternatingCofaceMapComplex
          (ringedSiteModules.{u} R)).obj
            (((sheafCoverNerve V).rightOp ⋙ D.image).flip.obj (I.X q))).d n (n + 1))
    simp only [AlgebraicTopology.alternatingCofaceMapComplex_obj,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD,
      Functor.map_sum, Functor.map_zsmul]
    change (HomologicalComplex.eval (ringedSiteModules.{u} S) (.up ℕ) q).map
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (CechColumnAux.diagram R D G V I).δ i) = _
    simp only [Functor.map_sum, Functor.map_zsmul]
    rfl)


end Aux


omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem columnTransition_f
    (D : CoherentCechImageModel R) (f : RingedToposMorphism R S)
    {V W : Sheaf J (Type u)} (r : W ⟶ V)
    {I I' : CochainComplex (ringedSiteModules.{u} R) ℕ} (t : I ⟶ I')
    (n : SimplexCategory) (q : ℕ) :
    (columnTransition D f r t n).f q =
      f.modules.map ((D.image.obj (op ((sheafCoverNerve V).obj (op n)))).map (t.f q)) ≫
        f.modules.map ((D.image.map ((Arrow.mapCechNerve
          (show Arrow.mk (terminal.from W) ⟶ Arrow.mk (terminal.from V) from
            Arrow.homMk r (𝟙 _) (terminal.hom_ext _ _))).app (op n)).op).app (I'.X q)) := by
  rfl


omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem columnTransition_naturality
    (D : CoherentCechImageModel R) (f : RingedToposMorphism R S)
    {V W : Sheaf J (Type u)} (r : W ⟶ V)
    {I I' : CochainComplex (ringedSiteModules.{u} R) ℕ} (t : I ⟶ I')
    (n m : SimplexCategory) (θ : n ⟶ m) (q : ℕ) :
    f.modules.map ((D.image.map (((sheafCoverNerve V).map θ.op).op)).app (I.X q)) ≫
        (columnTransition D f r t m).f q =
      (columnTransition D f r t n).f q ≫
        f.modules.map ((D.image.map (((sheafCoverNerve W).map θ.op).op)).app (I'.X q)) := by
  let rho := Arrow.mapCechNerve
    (show Arrow.mk (terminal.from W) ⟶ Arrow.mk (terminal.from V) from
      Arrow.homMk r (𝟙 _) (terminal.hom_ext _ _))
  rw [columnTransition_f, columnTransition_f]
  have hn := (D.image.map (((sheafCoverNerve V).map θ.op).op)).naturality (t.f q)
  have hc := rho.naturality θ.op
  have hci := congrArg (fun z ↦ (D.image.map z.op).app (I'.X q)) hc
  simp only [op_comp, Functor.map_comp, NatTrans.comp_app] at hci
  simp only [← f.modules.map_comp, ← Category.assoc]
  rw [← hn]
  simp only [Category.assoc]
  apply congrArg f.modules.map
  exact congrArg (fun z ↦ _ ≫ z) hci.symm

end Helpers


section Derived

variable [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
  [HasDerivedCategory.{wY} (ringedSiteModules.{u} S)]
  [IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R)]
  [IsGrothendieckAbelian.{u} (ringedSiteModules.{u} S)]
  [∀ A : Sheaf J (Type u),
    HasDerivedCategory.{wA} (ringedSiteModules.{u} (elementRing R A))]

/-- The assertion that a coherent augmented model with normalized columns exists.
The composite-unit equation characterizes the canonical composition
comparison by the two right-derived units; by the adjunction-normalization theorem
it is the comparison conjugate to the composite exact inverse image. The column-unit equation
characterizes beta on the restricted injective resolution. Thus neither comparison
is an arbitrary isomorphism. The total comparison is fixed on every diagonal inclusion.
This predicate is written out completely; the theorem below postpones only its proof.

Source: Stacks 03FC, 070J, 09T5 and 04J4
(blueprint: lem-sfb-cech-pushforward-augmented-model). -/
def AugmentedModel (f : RingedToposMorphism R S) (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) {N : ringedSiteModules.{u} R} (I : InjectiveResolution N)
    [sliceResolutions : ∀ A : Sheaf J (Type u),
      Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} (elementRing R A))] : Prop :=
    ∃ (B : CosimplicialObject (CochainComplex (ringedSiteModules.{u} S) ℕ)),
    ∃ (sigma : ∀ n : SimplexCategory, B.obj n ≅ (columnFunctor D f.modules V n).obj I.cocomplex),
    ∃ (augmentation : (Functor.const SimplexCategory).obj
    ((f.modules.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) ⟶ B),
    ∃ (b : (f.modules.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
    (D.totalFunctor f.modules V).obj I.cocomplex),
    ∃ (representative : ∀ n : SimplexCategory,
    (B.obj n).extend ComplexShape.embeddingUpNat ≅
      (((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).mapHomologicalComplex
        (.up ℤ)).obj ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat))),
    ∃ (composition : ∀ n : SimplexCategory,
    ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).rightDerivedFunctor ≅
      (D.push ((sheafCoverNerve V).obj (op n))).rightDerivedFunctor ⋙
        f.modules.rightDerivedFunctor),
    ∃ (columns : CosimplicialObject (DerivedCategory (ringedSiteModules.{u} S))),
    ∃ (columns_obj : ∀ n : SimplexCategory, columns.obj n =
    ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).rightDerivedFunctor.obj
      (DerivedCategory.Q.obj ((cechColumnRestrictComplex D
        ((sheafCoverNerve V).obj (op n))).obj
          (((CochainComplex.single₀ _).obj N).extend ComplexShape.embeddingUpNat)))),
    ∃ (beta : B ⋙ CechAugmentationNormalized.QN (ringedSiteModules.{u} S) ≅ columns),
    ∃ (totalIso : HomologicalComplex₂.total
      ((AlgebraicTopology.alternatingCofaceMapComplex
        (CochainComplex (ringedSiteModules.{u} S) ℕ)).obj B) (.up ℕ) ≅
      (D.totalFunctor f.modules V).obj I.cocomplex),
      (∀ (n q k : ℕ) (h : n + q = k),
        HomologicalComplex₂.ιTotal
          ((AlgebraicTopology.alternatingCofaceMapComplex
            (CochainComplex (ringedSiteModules.{u} S) ℕ)).obj B) (.up ℕ) n q k h ≫
            totalIso.hom.f k =
          (sigma (SimplexCategory.mk n)).hom.f q ≫
            (D.bicomplex f.modules V I.cocomplex).ιTotal (.up ℕ) n q k h) ∧
      (IsColumnDiagram D f V I.cocomplex B sigma) ∧
      (∀ (n : SimplexCategory) (q : ℕ),
    (augmentation.app n).f q ≫ (sigma n).hom.f q =
      f.modules.map ((D.augmentation ((sheafCoverNerve V).obj (op n))).app (I.cocomplex.X q))) ∧
      (D.IsAugmentation f.modules V I.cocomplex b) ∧
      (IsIso (CechAugmentationNormalized.alpha D f.modules V I b ≫
        (CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map totalIso.inv)) ∧
      (∀ (n : SimplexCategory) (q : ℕ),
    ((B.obj n).extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv ≫
      (representative n).hom.f (q : ℤ) ≫
        ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).map
          ((elementModulePullback R ((sheafCoverNerve V).obj (op n))).map
            (I.cocomplex.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom) =
      (sigma n).hom.f q ≫ f.modules.map
        ((D.imageIso ((sheafCoverNerve V).obj (op n))).hom.app (I.cocomplex.X q))) ∧
      (∀ (n : SimplexCategory)
    (K : CochainComplex (ringedSiteModules.{u}
      (elementRing R ((sheafCoverNerve V).obj (op n)))) ℤ),
    ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).rightDerivedFunctorUnitQ K ≫
        (composition n).hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (Iso.refl ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules)) (.up ℤ)).inv.app K) ≫
      f.modules.rightDerivedFunctorUnitQ
        (((D.push ((sheafCoverNerve V).obj (op n))).mapHomologicalComplex (.up ℤ)).obj K) ≫
      f.modules.rightDerivedFunctor.map
        ((D.push ((sheafCoverNerve V).obj (op n))).rightDerivedFunctorUnitQ K)) ∧
      (∀ n : SimplexCategory,
    (beta.app n).hom ≫ eqToHom (columns_obj n) ≫
        ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).rightDerivedFunctor.map
          (DerivedCategory.Q.map
            ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).map
              (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat))) =
      DerivedCategory.Q.map (representative n).hom ≫
        ((D.push ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).rightDerivedFunctorUnitQ
          ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).obj
            (I.cocomplex.extend ComplexShape.embeddingUpNat)))


/-- Naturality of the entire augmented diagrams under module lifts and cover refinements.
The column and total transitions are the actual ones defined above. Every column
component of the coherent diagram map is fixed by restriction and the chain lift.
Derived column comparisons are separately fixed by their right-derived unit equations
in `AugmentedModel`; no freely chosen map between their targets is asserted here.

Source: Stacks 013S, 03FC, 070J and 04J4
(blueprint: lem-sfb-cech-pushforward-augmented-model). -/
def ModelNaturality (f : RingedToposMorphism R S) (D : CoherentCechImageModel R) : Prop :=
  ∀ (V W : Sheaf J (Type u)) (_hV : Epi (terminal.from V))
    (_hW : Epi (terminal.from W)) (r : W ⟶ V)
    (N N' : ringedSiteModules.{u} R) (I : InjectiveResolution N)
    (I' : InjectiveResolution N') (u : N ⟶ N'),
  (∃ t : I.cocomplex ⟶ I'.cocomplex,
    I.ι ≫ t = (CochainComplex.single₀ _).map u ≫ I'.ι) ∧
  ∀ (t : I.cocomplex ⟶ I'.cocomplex)
    (_ht : I.ι ≫ t = (CochainComplex.single₀ _).map u ≫ I'.ι)
    (b : (f.modules.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      (D.totalFunctor f.modules V).obj I.cocomplex)
    (b' : (f.modules.mapHomologicalComplex (.up ℕ)).obj I'.cocomplex ⟶
      (D.totalFunctor f.modules W).obj I'.cocomplex)
    (_hb : D.IsAugmentation f.modules V I.cocomplex b)
    (_hb' : D.IsAugmentation f.modules W I'.cocomplex b'),
  ((f.modules.mapHomologicalComplex (.up ℕ)).map t ≫ b' =
    b ≫ totalTransition D f r t) ∧
  (CechAugmentationNormalized.alpha D f.modules V I b ≫
      (CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map
        (totalTransition D f r t) =
    f.modules.rightDerivedFunctor.map
        ((CechAugmentationNormalized.QN (ringedSiteModules.{u} R)).map
          ((CochainComplex.single₀ _).map u)) ≫
      CechAugmentationNormalized.alpha D f.modules W I' b') ∧
  (∀ (t' : I.cocomplex ⟶ I'.cocomplex)
    (_ht' : I.ι ≫ t' = (CochainComplex.single₀ _).map u ≫ I'.ι),
    (CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map
        (totalTransition D f r t) =
      (CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map
        (totalTransition D f r t') ∧
    ∀ n : SimplexCategory,
      (CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map
          (columnTransition D f r t n) =
        (CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map
          (columnTransition D f r t' n)) ∧
  (∀ (B B' : CosimplicialObject (CochainComplex (ringedSiteModules.{u} S) ℕ))
    (sigma : ∀ n : SimplexCategory,
      B.obj n ≅ (columnFunctor D f.modules V n).obj I.cocomplex)
    (sigma' : ∀ n : SimplexCategory,
      B'.obj n ≅ (columnFunctor D f.modules W n).obj I'.cocomplex),
    IsColumnDiagram D f V I.cocomplex B sigma →
    IsColumnDiagram D f W I'.cocomplex B' sigma' →
    ∃ tau : B ⟶ B',
      (∀ n : SimplexCategory, tau.app n =
        (sigma n).hom ≫ columnTransition D f r t n ≫ (sigma' n).inv) ∧
      (∀ (a : (Functor.const SimplexCategory).obj
          ((f.modules.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) ⟶ B)
        (a' : (Functor.const SimplexCategory).obj
          ((f.modules.mapHomologicalComplex (.up ℕ)).obj I'.cocomplex) ⟶ B'),
        (∀ (n : SimplexCategory) (q : ℕ),
          (a.app n).f q ≫ (sigma n).hom.f q =
            f.modules.map ((D.augmentation ((sheafCoverNerve V).obj (op n))).app
              (I.cocomplex.X q))) →
        (∀ (n : SimplexCategory) (q : ℕ),
          (a'.app n).f q ≫ (sigma' n).hom.f q =
            f.modules.map ((D.augmentation ((sheafCoverNerve W).obj (op n))).app
              (I'.cocomplex.X q))) →
        ∀ n : SimplexCategory,
          (f.modules.mapHomologicalComplex (.up ℕ)).map t ≫ a'.app n =
            a.app n ≫ tau.app n))

/-- Identity and composition of actual coherent transitions, and canonical isomorphisms
for changes of resolution. These laws concern all columns and the whole signed total.

Source: Stacks 013S and 04J4
(blueprint: lem-sfb-cech-pushforward-augmented-model). -/
def ComparisonLaws (f : RingedToposMorphism R S) (D : CoherentCechImageModel R) : Prop :=
  (∀ (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ),
    totalTransition D f (𝟙 V) (𝟙 I) = 𝟙 _ ∧
    ∀ n : SimplexCategory, columnTransition D f (𝟙 V) (𝟙 I) n = 𝟙 _) ∧
  (∀ (V W Z : Sheaf J (Type u)) (r : W ⟶ V) (s : Z ⟶ W)
    (I I' I'' : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (t : I ⟶ I') (t' : I' ⟶ I''),
    totalTransition D f (s ≫ r) (t ≫ t') =
      totalTransition D f r t ≫ totalTransition D f s t' ∧
    ∀ n : SimplexCategory, columnTransition D f (s ≫ r) (t ≫ t') n =
      columnTransition D f r t n ≫ columnTransition D f s t' n) ∧
  (∀ (V : Sheaf J (Type u)) (N : ringedSiteModules.{u} R)
    (I I' : InjectiveResolution N) (t : I.cocomplex ⟶ I'.cocomplex)
    (_ht : I.ι ≫ t = I'.ι),
    IsIso ((CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map
      (totalTransition D f (𝟙 V) t)) ∧
    ∀ n : SimplexCategory,
      IsIso ((CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map
        (columnTransition D f (𝟙 V) t n)))

section Proofs



attribute [local instance] moduleFiniteLimits moduleFiniteColimits moduleNatTotal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local implicit_reducible] CoherentCechImageModel.bicomplex
  CoherentCechImageModel.totalFunctor CoherentCechImageModel.total
  HomologicalComplex₂.flipFunctor HomologicalComplex₂.totalFunctor
  Functor.mapHomologicalComplex HomologicalComplex₂.flip

omit [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
  [IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R)]
  [IsGrothendieckAbelian.{u} (ringedSiteModules.{u} S)]
  [∀ A : Sheaf J (Type u),
    HasDerivedCategory.{wA} (ringedSiteModules.{u} (elementRing R A))] in
omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem column_homotopy
    (D : CoherentCechImageModel R) (f : RingedToposMorphism R S)
    (V : Sheaf J (Type u)) (n : SimplexCategory)
    {I I' : CochainComplex (ringedSiteModules.{u} R) ℕ} {t t' : I ⟶ I'}
    (H : Homotopy t t') :
    (CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map
        ((columnFunctor D f.modules V n).map t) =
      (CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map
        ((columnFunctor D f.modules V n).map t') := by
  have ha : (D.image.obj (op ((sheafCoverNerve V).obj (op n)))).Additive :=
    CechColumnAux.image_additive R D _
  exact DerivedCategory.Q_map_eq_of_homotopy _
    (((D.image.obj (op ((sheafCoverNerve V).obj (op n))) ⋙ f.modules).mapHomotopy H).extend
      ComplexShape.embeddingUpNat)

omit [IsGrothendieckAbelian.{u} (ringedSiteModules.{u} S)]
  [∀ A : Sheaf J (Type u),
    HasDerivedCategory.{wA} (ringedSiteModules.{u} (elementRing R A))] in
private theorem model_naturality
    (f : RingedToposMorphism R S)
    (D : CoherentCechImageModel R) : ModelNaturality f D := by
  intro V W hV hW r N N' I I' u
  have := hV
  have := hW
  refine ⟨⟨InjectiveResolution.desc u I' I, InjectiveResolution.desc_commutes u I' I⟩, ?_⟩
  intro t ht b b' hb hb'
  obtain ⟨bv, hbv, _⟩ := CechAugmentationNormalized.augmentation_exists
    D f.modules V I'.cocomplex
  have hchain := CechAugmentationNormalized.augmentation_chain_naturality
    D f.modules V t b bv hb hbv
  have hderived : CechAugmentationNormalized.alpha D f.modules V I b ≫
      (CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map
        ((D.totalFunctor f.modules V).map t) =
      f.modules.rightDerivedFunctor.map
        ((CechAugmentationNormalized.QN (ringedSiteModules.{u} R)).map
          ((CochainComplex.single₀ _).map u)) ≫
        CechAugmentationNormalized.alpha D f.modules V I' bv := by
    unfold CechAugmentationNormalized.alpha
    rw [Category.assoc, ← Functor.map_comp, ← hchain, Functor.map_comp,
      ← Category.assoc, CechAugmentationNormalized.comparison_naturality f.modules I I' u t ht]
    exact Category.assoc _ _ _
  have h := And.intro hchain hderived
  have hr := (CechAugmentationNormalized.refinement_laws D f.modules r (𝟙 W)
    I'.cocomplex I'.cocomplex (𝟙 _) bv b' hbv hb').1
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold totalTransition
    rw [← Category.assoc, ← h.1, Category.assoc, hr]
  · unfold totalTransition
    rw [Functor.map_comp, ← Category.assoc]
    erw [h.2, Category.assoc,
      CechAugmentationNormalized.alpha_refinement D f.modules r I' bv b' hbv hb']
  · intro t' ht'
    constructor
    · simp only [totalTransition, Functor.map_comp]
      congr 1
      exact CechAugmentationNormalized.lift_independence D f.modules V I I' u t t' ht ht'
    · intro n
      simp only [columnTransition, Functor.map_comp]
      rw [column_homotopy D f V n
        (InjectiveResolution.descHomotopy u t t' ht ht')]
  · intro B B' sigma sigma' hB hB'
    let e : B ≅ CechColumnAux.diagram R D f.modules V I.cocomplex :=
      NatIso.ofComponents sigma (fun {n m} θ ↦ by
        apply HomologicalComplex.Hom.ext
        funext q
        change (B.map θ).f q ≫ (sigma m).hom.f q =
          (sigma n).hom.f q ≫ _
        calc
          _ = (sigma n).hom.f q ≫
              ((sigma n).inv.f q ≫ (B.map θ).f q ≫ (sigma m).hom.f q) := by
            simp only [← Category.assoc, ← HomologicalComplex.comp_f,
              Iso.hom_inv_id, Category.id_comp]
          _ = _ := by rw [hB n m θ q]; rfl)
    let e' : B' ≅ CechColumnAux.diagram R D f.modules W I'.cocomplex :=
      NatIso.ofComponents sigma' (fun {n m} θ ↦ by
        apply HomologicalComplex.Hom.ext
        funext q
        change (B'.map θ).f q ≫ (sigma' m).hom.f q =
          (sigma' n).hom.f q ≫ _
        calc
          _ = (sigma' n).hom.f q ≫
              ((sigma' n).inv.f q ≫ (B'.map θ).f q ≫ (sigma' m).hom.f q) := by
            simp only [← Category.assoc, ← HomologicalComplex.comp_f,
              Iso.hom_inv_id, Category.id_comp]
          _ = _ := by rw [hB' n m θ q]; rfl)
    let z : CechColumnAux.diagram R D f.modules V I.cocomplex ⟶
        CechColumnAux.diagram R D f.modules W I'.cocomplex :=
      { app n := columnTransition D f r t n
        naturality n m θ := by
          apply HomologicalComplex.Hom.ext
          funext q
          exact columnTransition_naturality D f r t n m θ q }
    let tau : B ⟶ B' := e.hom ≫ z ≫ e'.inv
    refine ⟨tau, fun _ ↦ rfl, ?_⟩
    intro a a' ha ha' n
    apply HomologicalComplex.Hom.ext
    funext q
    rw [← cancel_mono ((sigma' n).hom.f q)]
    change (f.modules.map (t.f q) ≫ (a'.app n).f q) ≫ (sigma' n).hom.f q =
      ((a.app n).f q ≫ ((sigma n).hom.f q ≫
        (columnTransition D f r t n).f q ≫ (sigma' n).inv.f q)) ≫
          (sigma' n).hom.f q
    have hcancel : (sigma' n).inv.f q ≫ (sigma' n).hom.f q = 𝟙 _ :=
      congrArg (fun z ↦ z.f q) (sigma' n).inv_hom_id
    simp only [Category.assoc, hcancel, Category.comp_id]
    rw [ha' n q, ← Category.assoc, ha n q, columnTransition_f]
    simp only [← f.modules.map_comp]
    have hn := (D.augmentation ((sheafCoverNerve V).obj (op n))).naturality (t.f q)
    apply congrArg f.modules.map
    simp only [← Category.assoc]
    rw [← hn, Category.assoc]
    exact congrArg (fun z ↦ t.f q ≫ z)
      (NatTrans.congr_app (D.augmentation_naturality _) (I'.cocomplex.X q)).symm


omit [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
  [IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R)]
  [IsGrothendieckAbelian.{u} (ringedSiteModules.{u} S)]
  [∀ A : Sheaf J (Type u),
    HasDerivedCategory.{wA} (ringedSiteModules.{u} (elementRing R A))] in
private theorem comparison_laws (f : RingedToposMorphism R S)
    (D : CoherentCechImageModel R) : ComparisonLaws f D := by
  have hr (V W Z : Sheaf J (Type u)) (r : W ⟶ V) (s : Z ⟶ W)
      (I I' : CochainComplex (ringedSiteModules.{u} R) ℕ) (t : I ⟶ I') :
      D.totalRefinement f.modules (𝟙 V) I = 𝟙 _ ∧
        D.totalRefinement f.modules (s ≫ r) I =
          D.totalRefinement f.modules r I ≫ D.totalRefinement f.modules s I ∧
        (D.totalFunctor f.modules V).map t ≫ D.totalRefinement f.modules r I' =
          D.totalRefinement f.modules r I ≫ (D.totalFunctor f.modules W).map t := by
    obtain ⟨b, hb, _⟩ := CechAugmentationNormalized.augmentation_exists D f.modules V I
    obtain ⟨b', hb', _⟩ := CechAugmentationNormalized.augmentation_exists D f.modules W I
    exact (CechAugmentationNormalized.refinement_laws D f.modules r s I I' t b b' hb hb').2
  have hcId (V : Sheaf J (Type u))
      (I : CochainComplex (ringedSiteModules.{u} R) ℕ) (n : SimplexCategory) :
      columnRefinement D f.modules (𝟙 V) n I = 𝟙 _ := by
    unfold columnRefinement
    rw [CechAugmentationNormalized.refinement_cochains_id]
    simp
    rfl
  have hcComp (V W Z : Sheaf J (Type u)) (r : W ⟶ V) (s : Z ⟶ W)
      (I : CochainComplex (ringedSiteModules.{u} R) ℕ) (n : SimplexCategory) :
      columnRefinement D f.modules (s ≫ r) n I =
        columnRefinement D f.modules r n I ≫ columnRefinement D f.modules s n I := by
    unfold columnRefinement
    rw [CechAugmentationNormalized.refinement_cochains_comp]
    simp only [Functor.whiskerRight_comp, NatTrans.mapHomologicalComplex_comp,
      NatTrans.comp_app]
  have hcNat (V W : Sheaf J (Type u)) (r : W ⟶ V)
      (I I' : CochainComplex (ringedSiteModules.{u} R) ℕ) (t : I ⟶ I')
      (n : SimplexCategory) :
      (columnFunctor D f.modules V n).map t ≫ columnRefinement D f.modules r n I' =
        columnRefinement D f.modules r n I ≫ (columnFunctor D f.modules W n).map t := by
    exact (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (Functor.whiskerRight (D.refinement r)
        (f.modules.mapHomologicalComplex (.up ℕ))) (.up ℕ))
      (HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ) ⋙
        HomologicalComplex.eval _ (.up ℕ) n.len)).naturality t
  refine ⟨?_, ?_, ?_⟩
  · intro V I
    constructor
    · simp only [totalTransition, Functor.map_id, Category.id_comp,
        (hr V V V (𝟙 V) (𝟙 V) I I (𝟙 I)).1]
    · intro n
      simp only [columnTransition, Functor.map_id, Category.id_comp, hcId]
  · intro V W Z r s I I' I'' t t'
    constructor
    · unfold totalTransition
      rw [Functor.map_comp, (hr V W Z r s I'' I'' (𝟙 I'')).2.1]
      simp only [Category.assoc]
      rw [← reassoc_of% (hr V W W r (𝟙 W) I' I'' t').2.2]
    · intro n
      unfold columnTransition
      rw [Functor.map_comp, hcComp]
      simp only [Category.assoc]
      rw [← reassoc_of% hcNat V W r I' I'' t' n]
  · intro V N I I' t ht
    constructor
    · simpa only [totalTransition, (hr V V V (𝟙 V) (𝟙 V) I'.cocomplex
        I'.cocomplex (𝟙 _)).1, Category.comp_id,
        CechAugmentationNormalized.QN, Functor.comp_map,
        CechAugmentationNormalized.totalMap, CoherentCechImageModel.total,
        CoherentCechImageModel.totalFunctor, CoherentCechImageModel.bicomplex,
        ComplexShape.Embedding.extendFunctor_obj,
        ComplexShape.Embedding.extendFunctor_map, Functor.comp_obj] using
        (CechAugmentationNormalized.resolution_comparison_laws D f.modules V I I' t ht).1
    · intro n
      simp only [columnTransition, hcId, Category.comp_id]
      let Q := CechAugmentationNormalized.QN (ringedSiteModules.{u} S)
      let F := columnFunctor D f.modules V n
      let t' := InjectiveResolution.desc (𝟙 N) I I'
      have ht' : I'.ι ≫ t' = I.ι := by simp [t']
      have hl : Q.map (F.map t) ≫ Q.map (F.map t') = 𝟙 _ := by
        rw [← Functor.map_comp, ← Functor.map_comp,
          column_homotopy D f V n (InjectiveResolution.descHomotopy (𝟙 N)
            (t ≫ t') (𝟙 _) (by simp [← Category.assoc, ht, ht']) (by simp)),
          Functor.map_id, Functor.map_id]
      have hr' : Q.map (F.map t') ≫ Q.map (F.map t) = 𝟙 _ := by
        rw [← Functor.map_comp, ← Functor.map_comp,
          column_homotopy D f V n (InjectiveResolution.descHomotopy (𝟙 N)
            (t' ≫ t) (𝟙 _) (by simp [← Category.assoc, ht, ht']) (by simp)),
          Functor.map_id, Functor.map_id]
      exact ⟨⟨Q.map (F.map t'), hl, hr'⟩⟩


private theorem composition_unit
    {A E F : Type*} [Category A] [Category E] [Category F]
    [Abelian A] [Abelian E] [Abelian F]
    [HasDerivedCategory A] [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions E]
    (G : A ⥤ E) (H : E ⥤ F) [G.Additive] [H.Additive]
    [G.PreservesKInjectiveComplexes] (K : CochainComplex A ℤ) :
    (G ⋙ H).rightDerivedFunctorUnitQ K ≫
        (Functor.rightDerivedFunctorCompIso G H).hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (G ⋙ H)) (.up ℤ)).inv.app K) ≫
      H.rightDerivedFunctorUnitQ ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
      H.rightDerivedFunctor.map (G.rightDerivedFunctorUnitQ K) := by
  have hfac : (G ⋙ H).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≫
      (Functor.rightDerivedFunctorCompIso G H).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj K)) =
      (Functor.rightDerivedFunctorCompUnit G H).app
        ((HomotopyCategory.quotient A (.up ℤ)).obj K) := by
    simpa only [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique,
      Functor.rightDerivedNatIso_hom, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp] using
      Functor.rightDerivedNatTrans_app
        (G ⋙ H).rightDerivedFunctor (G.rightDerivedFunctor ⋙ H.rightDerivedFunctor)
        (G ⋙ H).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit G H)
        (HomotopyCategory.quasiIso A (.up ℤ)) (𝟙 _) _
  have hn := (Functor.rightDerivedFunctorCompIso G H).hom.naturality
    ((DerivedCategory.quotientCompQhIso A).hom.app K)
  simp only [Functor.rightDerivedFunctorUnitQ, Functor.map_comp, Category.assoc]
  erw [hn, reassoc_of% hfac]
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ H)) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj K) = 𝟙 _ := by
    erw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (G ⋙ H)) (.up ℤ)).hom.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj K)), Iso.hom_inv_id_app]
  have hj : (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (.up ℤ)).inv.app K =
      𝟙 _ := rfl
  simp only [hi, hj, Functor.map_id, Category.id_comp]
  simp only [← H.rightDerivedFunctor.map_comp_assoc, Iso.hom_inv_id_app_assoc,
    Functor.comp_map]
  rfl

omit [HasDerivedCategory.{wY} (ringedSiteModules.{u} S)]
  [IsGrothendieckAbelian.{u} (ringedSiteModules.{u} S)]
  [IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R)] in
private theorem column_input
    (hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (V : Sheaf J (Type u)) [Epi (terminal.from V)] (N : ringedSiteModules.{u} R) :
    (Nonempty (InjectiveResolution N) ∧ Nonempty (CoherentCechImageModel R)) ∧
      ∀ (I : InjectiveResolution N) (D : CoherentCechImageModel R) (n : SimplexCategory),
        CochainComplex.IsKInjective
            ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).obj
              (I.cocomplex.extend ComplexShape.embeddingUpNat)) ∧
          QuasiIso ((cechColumnRestrictComplex D ((sheafCoverNerve V).obj (op n))).map
            (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)) := by
  have h := cech_injective_column_model R R hR hR (identityMorphism R)
    (𝟭 _) Adjunction.id V N
  exact ⟨⟨h.1, h.2.1⟩, fun I D n ↦ (h.2.2 I D).2.1 n⟩

private theorem augmented_model
    (f : RingedToposMorphism R S)
    (fInverse : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R)
    [fInverse.Additive] [PreservesFiniteLimits fInverse] [PreservesFiniteColimits fInverse]
    (adj : fInverse ⊣ f.modules)
    (hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (hS : ∀ (U : Xᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    (D : CoherentCechImageModel R) (V : Sheaf J (Type u)) [Epi (terminal.from V)]
    {N : ringedSiteModules.{u} R} (I : InjectiveResolution N)
    [hs : ∀ A : Sheaf J (Type u),
      Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} (elementRing R A))] :
    AugmentedModel (sliceResolutions := hs) f D V I := by
  classical
  let A := fun n : SimplexCategory ↦ (sheafCoverNerve V).obj (op n)
  let P := fun n : SimplexCategory ↦ D.push (A n) ⋙ f.modules
  let F := fun n : SimplexCategory ↦ cechColumnRestrictComplex D (A n)
  let K := fun n : SimplexCategory ↦
    (F n).obj (I.cocomplex.extend ComplexShape.embeddingUpNat)
  have hres (n : SimplexCategory) :
      CochainComplex.IsKInjective
          (K n) ∧
        QuasiIso ((F n).map
          (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)) :=
    (column_input hR V N).2 I D n
  have hadd (A : Sheaf J (Type u)) : (elementModulePullback.{u, u} R A).Additive :=
    ⟨by intros; rfl⟩
  have himage (A : Sheaf J (Type u)) : (D.image.obj (op A)).Additive :=
    CechColumnAux.image_additive R D A
  obtain ⟨b, hb, hq, _⟩ := (CechInjectiveImage.cech_injective_image_augmentation
    f fInverse adj hR hS D V I.cocomplex (fun _ ↦ inferInstance)).total_augmentation
  let B := CechColumnAux.diagram R D f.modules V I.cocomplex
  let a := CechColumnAux.augmentation R D f.modules V I.cocomplex
  let representative : ∀ n : SimplexCategory,
      (B.obj n).extend ComplexShape.embeddingUpNat ≅
        ((P n).mapHomologicalComplex
          (.up ℤ)).obj (K n) := fun n ↦
    (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
      (D.image.obj (op ((sheafCoverNerve V).obj (op n))) ⋙ f.modules)).symm ≪≫
      (NatIso.mapHomologicalComplex
        (Functor.isoWhiskerRight (D.imageIso ((sheafCoverNerve V).obj (op n))) f.modules)
        (.up ℤ)).app (I.cocomplex.extend ComplexShape.embeddingUpNat)
  let v := fun n : SimplexCategory ↦
    (F n).map
      (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)
  have hv (n : SimplexCategory) : QuasiIso (v n) := (hres n).2
  have hk (n : SimplexCategory) :
      (K n).IsKInjective := (hres n).1
  have hunit (n : SimplexCategory) : IsIso
      ((P n).rightDerivedFunctorUnitQ
        (K n)) := by
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  let cn := fun n : SimplexCategory ↦ DerivedCategory.Q.mapIso (representative n) ≪≫
    (asIso ((P n).rightDerivedFunctorUnitQ
      (K n))) ≪≫
    ((P n).rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map (v n)))).symm
  let columns := Functor.copyObj (B ⋙ CechAugmentationNormalized.QN (ringedSiteModules.{u} S))
    (fun n ↦ (P n).rightDerivedFunctor.obj
      (DerivedCategory.Q.obj ((F n).obj
          (((CochainComplex.single₀ _).obj N).extend ComplexShape.embeddingUpNat)))) cn
  let beta := Functor.isoCopyObj (B ⋙ CechAugmentationNormalized.QN (ringedSiteModules.{u} S))
    _ cn
  let totalIso := (HomologicalComplex₂.totalFunctor _ (.up ℕ) (.up ℕ) (.up ℕ)).mapIso
    (Aux.bicomplexIso D f.modules V I.cocomplex)
  have hcomp (A : Sheaf J (Type u)) : (D.push A).PreservesKInjectiveComplexes := by
    obtain ⟨extAdj⟩ := elementModuleExtension_adjunction R A
    have := (D.adj A).isLeftAdjoint
    have := extAdj.isRightAdjoint
    exact (D.adj A).preservesKInjectiveComplexes
  let composition := fun n : SimplexCategory ↦
    Functor.rightDerivedFunctorCompIso (D.push ((sheafCoverNerve V).obj (op n))) f.modules
  refine ⟨B, (fun _ ↦ Iso.refl _), a, b, representative, composition, columns,
    (fun _ ↦ rfl), beta, totalIso, ?_, ?_, ?_, hb, ?_, ?_, ?_, ?_⟩
  · intro n q k h
    change _ ≫ (HomologicalComplex₂.total.map
      (Aux.bicomplexIso D f.modules V I.cocomplex).hom (.up ℕ)).f k = _
    rw [HomologicalComplex₂.ιTotal_map]
    rfl
  · intro n m θ q
    simp only [Iso.refl_inv, Iso.refl_hom, HomologicalComplex.id_f, Category.comp_id]
    rfl
  · intro n q
    simp only [Iso.refl_hom, HomologicalComplex.id_f, Category.comp_id]
    rfl
  · have : IsIso ((CechAugmentationNormalized.QN (ringedSiteModules.{u} S)).map b) := by
      change IsIso (DerivedCategory.Q.map
        (HomologicalComplex.extendMap b ComplexShape.embeddingUpNat))
      infer_instance
    unfold CechAugmentationNormalized.alpha
    infer_instance
  · intro n q
    rcases n with ⟨n⟩
    simpa only [representative, B, CechColumnAux.diagram, P, F, K, A,
      CoherentCechImageModel.bicomplex,
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
  · intro n K
    exact composition_unit _ _ K
  · intro n
    change (cn n).hom ≫ 𝟙 _ ≫
      (P n).rightDerivedFunctor.map
        (DerivedCategory.Q.map (v n)) = _
    dsimp only [cn, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_hom, asIso_inv]
    simp only [Category.id_comp, Category.assoc]
    rw [← Functor.map_comp, IsIso.inv_hom_id, Functor.map_id, Category.comp_id]
    rfl


attribute [-instance] moduleFiniteLimits moduleFiniteColimits moduleNatTotal

end Proofs
end Derived
end Models

/-- The pushed-forward coherent augmented model exists for every compatible resolution
and localization presentation, without a Cartesian coefficient hypothesis on f.

Source: Stacks 03FC, 070J, 09T5 and 04J4
(blueprint: lem-sfb-cech-pushforward-augmented-model).

Proof: use the identity specialization of the column-model theorem for restricted
injective resolutions. Construct the strict diagram from the actual restriction maps.
Additivity identifies its alternating-coface bicomplex and total with the coherent
model, on every diagonal inclusion. The exact image-augmentation theorem applies
directly to the arbitrary ringed morphism: its sectionwise proof does not use a
Cartesian ring-map assumption. Thus the normalized augmentation is a quasi-isomorphism.
For each column, commute extension with its image functor, apply the right-derived
unit on the restricted K-injective resolution, and invert the right-derived image of
the restricted resolution map. Transporting the localized strict diagram along these
isomorphisms gives the required derived columns and their unit equations. The exact
slice adjunction makes its pushforward preserve K-injectives; the canonical composition
isomorphism has the displayed composite-unit factorization by its universal property.
Naturality of units and the resolution comparison gives the augmentation squares.
Refinement laws and homotopy uniqueness of resolution lifts give all transition laws,
independence of lifts, and invertibility of identity-cover resolution comparisons. -/
theorem cech_pushforward_augmented_model
    (R : Sheaf J RingCat.{u}) (S : Sheaf L RingCat.{u})
    (_hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hS : ∀ (U : Xᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wY} (ringedSiteModules.{u} S)]
    [IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R)]
    [IsGrothendieckAbelian.{u} (ringedSiteModules.{u} S)]
    [∀ A : Sheaf J (Type u),
      HasDerivedCategory.{wA} (ringedSiteModules.{u} (elementRing R A))]
    (f : RingedToposMorphism R S)
    (fInverse : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R)
    [fInverse.Additive] [PreservesFiniteLimits fInverse] [PreservesFiniteColimits fInverse]
    (_adj : fInverse ⊣ f.modules)
    (V : Sheaf J (Type u)) [Epi (terminal.from V)] (N : ringedSiteModules.{u} R) :
    ∃ hs : ∀ A : Sheaf J (Type u),
      Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} (elementRing R A)),
    Nonempty (InjectiveResolution N) ∧ Nonempty (CoherentCechImageModel R) ∧
      ∀ D : CoherentCechImageModel R,
        (∀ I : InjectiveResolution N, AugmentedModel (sliceResolutions := hs) f D V I) ∧
        ModelNaturality f D ∧ ComparisonLaws f D := by
  classical
  have := smallSheafify J
  have := smallSheafify L
  have := smallLocallyBijective J
  have := smallLocallyBijective L
  have hs : ∀ A : Sheaf J (Type u),
      Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} (elementRing R A)) := by
    intro A
    have : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} (elementRing R A)) :=
      SheafOfModules.isGrothendieckAbelianOfUniverses (elementTopology A) (elementRing R A)
    exact Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have hc : Nonempty (InjectiveResolution N) ∧ Nonempty (CoherentCechImageModel R) :=
    (column_input _hR V N).1
  refine ⟨hs, hc.1, hc.2, ?_⟩
  intro D
  refine ⟨fun I ↦ augmented_model f fInverse _adj _hR _hS D V I,
    model_naturality f D, ?_⟩
  exact comparison_laws f D

end CategoryTheory.CechPushforward
