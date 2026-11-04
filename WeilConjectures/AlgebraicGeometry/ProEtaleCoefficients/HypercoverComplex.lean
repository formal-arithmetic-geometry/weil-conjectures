/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.HypercoverExistence
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWContractibleSectionsDerived
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.EssentiallySmall
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.CategoryTheory.RingedHypercoverInjectiveAugmentationRing
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.Algebra.Exact.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.CategoryTheory.RingedHypercoverFiniteCones
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Data.Fin.VecNotation
import WeilConjectures.Algebra.Homology.BoundedBelowAugmentation
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.BoundedBelowTotalComparison
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Algebra.Homology.KInjectiveResolution
import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverComputesBoundedComplexSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProetaleSiteProperties

/-!
# Derived abelian sections from a weakly contractible hypercover

Source: blueprint main-20261015, sec-proetale-coefficients/sk-prop-pe-hypercover/
det-pe-hypercover-complex.md; Stacks Project, Tag 09A2
(blueprint: det-pe-hypercover-complex).

The helpers realize this node's alternating section total for arbitrary ring sheaves.
The existing `hypercoverTotal` has commutative coefficients and a module-valued target.
Here all values and derived categories use the common larger coefficient universe;
the pro-etale site's object and morphism universes stay different.
-/

@[expose] public section

set_option autoImplicit false

universe t u v wA wB

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

private instance : Preadditive (CosimplicialObject AddCommGrpCat.{u}) :=
  inferInstanceAs (Preadditive (SimplexCategory ⥤ AddCommGrpCat.{u}))

/-- Cosimplicial underlying abelian sections, with the actual sheaf restriction maps.
Source: Stacks Project, Tag 09A2, the construction of `s(E(K))`
(blueprint: det-pe-hypercover-complex). -/
noncomputable def hypercoverAbelianSections (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U)) :
    ringedSiteModules.{max u v (t + 1)} R ⥤
      CosimplicialObject AddCommGrpCat.{max u v (t + 1)} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
    (Functor.whiskeringLeft _ _ _).obj (W ⋙ Over.forget U).rightOp

/-- The alternating section rows, extended by zero in negative simplicial degrees.
The differential from degree r to r+1 is the sum of `(-1)^i` times the i-th
face restriction, for i in `Fin (r+2)`. No hypercover condition enters this data.
Source: Stacks Project, Tag 09A2
(blueprint: det-pe-hypercover-complex). -/
noncomputable def hypercoverAbelianRows (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U)) :
    ringedSiteModules.{max u v (t + 1)} R ⥤
      CochainComplex AddCommGrpCat.{max u v (t + 1)} ℤ :=
  hypercoverAbelianSections X R U W ⋙
    AlgebraicTopology.alternatingCofaceMapComplex _ ⋙
    ComplexShape.embeddingUpNat.extendFunctor _

/-- Additivity needed to apply the alternating section rows to a coefficient complex.
Source: Stacks Project, Tag 09A2, construction of the total complex; step 1 of the
node's proof (blueprint: det-pe-hypercover-complex).
Proof: a coefficient morphism acts by its section map in every degree. Addition of
module-sheaf morphisms, of abelian presheaf morphisms and of complex morphisms is
componentwise. Alternating cofaces do not change these components, and extension
by zero has zero components in the additional degrees. Thus each component of the
image of a sum is the sum of its images. -/
theorem hypercoverAbelianRows_additive (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U)) :
    (hypercoverAbelianRows.{t, u, v} X R U W).Additive := by
  let : (hypercoverAbelianSections.{t, u, v} X R U W).Additive :=
    { map_add := by intros; rfl }
  let : (AlgebraicTopology.alternatingCofaceMapComplex
      AddCommGrpCat.{max u v (t + 1)}).Additive := { map_add := by intros; rfl }
  unfold hypercoverAbelianRows
  infer_instance

attribute [instance] hypercoverAbelianRows_additive

/-- The actual coproduct total of the section bicomplex. Flip puts simplicial degree r
first; Mathlib's total differential is then `delta + (-1)^r d_K`. Its degree q is
the sum over r+b=q, r nonnegative, of K^b(W_r). For a strict lower bound a on K,
all summands outside `0 ≤ r ≤ q-a` are zero; for q<a the entire diagonal is zero.
Coefficient chain maps act componentwise. The definition uses no choice of a complex.
Source: Stacks Project, Tag 09A2; Homology, Tags 0132 and 0133
(blueprint: det-pe-hypercover-complex). -/
noncomputable def hypercoverAbelianTotal (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U)) :
    CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ ⥤
      CochainComplex AddCommGrpCat.{max u v (t + 1)} ℤ :=
  (hypercoverAbelianRows X R U W).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.totalFunctor _ _ _ (ComplexShape.up ℤ)

/-- The additive abelian section functor used for RΓ(U,-).
Source: Stacks Project, Tag 09A2
(blueprint: det-pe-hypercover-complex). -/
noncomputable abbrev hypercoverAbelianEvaluation (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt) :
    ringedSiteModules.{max u v (t + 1)} R ⥤ AddCommGrpCat.{max u v (t + 1)} :=
  SheafOfModules.evaluation R (op U) ⋙ forget₂ _ AddCommGrpCat

variable (X : Scheme.{t}) (R : Sheaf (topology X) RingCat.{u})
  (U : X.ProEt) (W : SimplicialObject (Over U))

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the vertices, with scalars restricted from the augmentation object.
Source: Stacks Project, Tag 09A2.
(blueprint: det-pe-hypercover-complex). -/
private noncomputable def hypercoverAbelianRestrictionZero
    (I : ringedSiteModules.{max u v (t + 1)} R) :
    (hypercoverAbelianEvaluation X R U).obj I ⟶
      ((hypercoverAbelianSections X R U W).obj I).obj ⦋0⦌ :=
  I.val.presheaf.map (W _⦋0⦌).hom.op

/-- Restriction to vertices agrees with ordinary sheaf restriction.
Source: Stacks Project, Tag 09A2.
(blueprint: det-pe-hypercover-complex). -/
@[simp]
private lemma hypercoverAbelianRestrictionZero_apply
    (I : ringedSiteModules.{max u v (t + 1)} R)
    (x : I.val.presheaf.obj (op U)) :
    (hypercoverAbelianRestrictionZero X R U W I).hom x =
      I.val.presheaf.map (W _⦋0⦌).hom.op x := by rfl

private theorem hypercoverAbelianRestrictionZero_naturality
    {I J : ringedSiteModules.{max u v (t + 1)} R}
    (f : I ⟶ J) :
    (hypercoverAbelianEvaluation X R U).map f ≫
      hypercoverAbelianRestrictionZero X R U W J =
      hypercoverAbelianRestrictionZero X R U W I ≫
        ((hypercoverAbelianSections X R U W).map f).app ⦋0⦌ := by
  ext x
  simp only [AddCommGrpCat.comp_apply, hypercoverAbelianRestrictionZero_apply]
  exact ConcreteCategory.congr_hom (f.val.naturality (W _⦋0⦌).hom.op).symm x

/-- The restriction to vertices is killed by the alternating face differential.
Source: Stacks Project, Tag 01GE.
(blueprint: det-pe-hypercover-complex). -/
private theorem hypercoverAbelianRestrictionZero_d
    (I : ringedSiteModules.{max u v (t + 1)} R) :
    hypercoverAbelianRestrictionZero X R U W I ≫
      ((AlgebraicTopology.alternatingCofaceMapComplex _).obj
        ((hypercoverAbelianSections X R U W).obj I)).d 0 1 = 0 := by
  change hypercoverAbelianRestrictionZero X R U W I ≫
    (∑ j : Fin 2, (-1 : ℤ) ^ j.val • ((hypercoverAbelianSections X R U W).obj I).δ j) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    one_smul, ← sub_eq_add_neg, Preadditive.comp_sub, sub_eq_zero]
  ext x
  simp only [AddCommGrpCat.comp_apply, hypercoverAbelianRestrictionZero_apply]
  change I.val.presheaf.map (W.δ 0).left.op (I.val.presheaf.map (W _⦋0⦌).hom.op x) =
    I.val.presheaf.map (W.δ 1).left.op (I.val.presheaf.map (W _⦋0⦌).hom.op x)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  have h : (W _⦋0⦌).hom.op ≫ (W.δ 0).left.op =
      (W _⦋0⦌).hom.op ≫ (W.δ 1).left.op := by
    simpa only [← op_comp] using
      congrArg Quiver.Hom.op ((W.δ 0).w.trans (W.δ 1).w.symm)
  rw [h]

/-- Restriction into degree zero of the alternating section complex.
Source: Stacks Project, Tag 09A2.
(blueprint: det-pe-hypercover-complex). -/
private noncomputable def hypercoverAbelianRowAugmentation
    (I : ringedSiteModules.{max u v (t + 1)} R) :
    (hypercoverAbelianEvaluation X R U).obj I ⟶
      ((hypercoverAbelianRows X R U W).obj I).X 0 :=
  hypercoverAbelianRestrictionZero X R U W I ≫
    (((AlgebraicTopology.alternatingCofaceMapComplex _).obj
      ((hypercoverAbelianSections X R U W).obj I)).extendXIso
        ComplexShape.embeddingUpNat (i := 0) rfl).inv

set_option backward.isDefEq.respectTransparency false in
/-- Restriction into the extended section row is natural in the module sheaf.
Source: Stacks Project, Tag 09A2.
(blueprint: det-pe-hypercover-complex). -/
@[reassoc]
private lemma hypercoverAbelianRowAugmentation_naturality
    {I J : ringedSiteModules.{max u v (t + 1)} R}
    (f : I ⟶ J) :
    (hypercoverAbelianEvaluation X R U).map f ≫
      hypercoverAbelianRowAugmentation X R U W J =
      hypercoverAbelianRowAugmentation X R U W I ≫
        ((hypercoverAbelianRows X R U W).map f).f 0 := by
  dsimp only [hypercoverAbelianRowAugmentation, hypercoverAbelianRows, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc]
  exact congrArg (fun z ↦ z ≫ _)
    (hypercoverAbelianRestrictionZero_naturality X R U W f)

set_option backward.isDefEq.respectTransparency false in
/-- The extended section-row differential kills the augmentation.
Source: Stacks Project, Tag 01GE.
(blueprint: det-pe-hypercover-complex). -/
@[reassoc (attr := simp)]
private lemma hypercoverAbelianRowAugmentation_d
    (I : ringedSiteModules.{max u v (t + 1)} R) :
    hypercoverAbelianRowAugmentation X R U W I ≫
      ((hypercoverAbelianRows X R U W).obj I).d 0 1 = 0 := by
  dsimp only [hypercoverAbelianRowAugmentation, hypercoverAbelianRows, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq _ _ (i := 0) (j := 1) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hypercoverAbelianRestrictionZero_d, zero_comp]

/-- The augmented row, with the augmentation object placed in degree zero.
Source: Stacks Project, Tags 09A2 and 01GE.
(blueprint: det-pe-hypercover-complex). -/
private noncomputable def hypercoverAbelianRowAugmentationComplex
    (I : ringedSiteModules.{max u v (t + 1)} R) :
    (HomologicalComplex.single _ (.up ℤ) 0).obj
      ((hypercoverAbelianEvaluation X R U).obj I) ⟶
        (hypercoverAbelianRows X R U W).obj I :=
  HomologicalComplex.mkHomFromSingle (hypercoverAbelianRowAugmentation X R U W I) (by
    intro k hk
    obtain rfl : k = 1 := by simpa using hk.symm
    exact hypercoverAbelianRowAugmentation_d X R U W I)

set_option maxHeartbeats 800000 in
-- The total augmentation expands the section, extension and total functors.
set_option backward.isDefEq.respectTransparency false in
/-- The canonical augmentation of a coefficient complex into total hypercover sections.
Its degree-n component is restriction into the (0,n) summand.
Source: Stacks Project, Tag 09A2.
(blueprint: det-pe-hypercover-complex). -/
private noncomputable def hypercoverAbelianAugmentation :
    (hypercoverAbelianEvaluation X R U).mapHomologicalComplex
          (ComplexShape.up ℤ) ⟶ hypercoverAbelianTotal X R U W where
  app K := by
    let D := HomologicalComplex₂.flip
      (((hypercoverAbelianRows X R U W).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    refine
      { f := fun n ↦ hypercoverAbelianRowAugmentation X R U W (K.X n) ≫
          D.ιTotal (ComplexShape.up ℤ) 0 n n (by simp)
        comm' := ?_ }
    intro n m h
    have hm : n + 1 = m := h
    subst m
    change (hypercoverAbelianRowAugmentation X R U W (K.X n) ≫
      D.ιTotal (ComplexShape.up ℤ) 0 n n _) ≫ (D.total (ComplexShape.up ℤ)).d n (n + 1) =
        (hypercoverAbelianEvaluation X R U).map (K.d n (n + 1)) ≫ _
    simp only [HomologicalComplex₂.total_d, Category.assoc,
      Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (ComplexShape.up ℤ) (by simp : (ComplexShape.up ℤ).Rel 0 1)
      n (n + 1) (by simp [add_comm]), D.d₂_eq (ComplexShape.up ℤ) 0
      (by simp : (ComplexShape.up ℤ).Rel n (n + 1)) (n + 1) (by simp)]
    have hs₁ : ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (0, n) = 1 := rfl
    have hs₂ : ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (0, n) = 1 := by
      change (-1 : ℤˣ) ^ (0 : ℤ) = 1
      exact zpow_zero _
    simp only [hs₁, hs₂, one_smul, ← Category.assoc]
    change (_ ≫ ((hypercoverAbelianRows X R U W).obj (K.X n)).d 0 1) ≫ _ + _ = _
    rw [hypercoverAbelianRowAugmentation_d, zero_comp, zero_add]
    exact congrArg (fun z ↦ z ≫ D.ιTotal (ComplexShape.up ℤ) 0 (n + 1) (n + 1)
      (by simp)) (hypercoverAbelianRowAugmentation_naturality X R U W (K.d n (n + 1))).symm
  naturality K L f := by
    apply HomologicalComplex.hom_ext
    intro n
    dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    let D := HomologicalComplex₂.flip
      (((hypercoverAbelianRows X R U W).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    let D' := HomologicalComplex₂.flip
      (((hypercoverAbelianRows X R U W).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    let g := (HomologicalComplex₂.flipFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      (((hypercoverAbelianRows X R U W).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
    change (hypercoverAbelianEvaluation X R U).map (f.f n) ≫
      (hypercoverAbelianRowAugmentation X R U W (L.X n) ≫ D'.ιTotal (.up ℤ) 0 n n _) =
      (hypercoverAbelianRowAugmentation X R U W (K.X n) ≫ D.ιTotal (.up ℤ) 0 n n _) ≫
        (HomologicalComplex₂.total.map g (.up ℤ)).f n
    simp only [Category.assoc, HomologicalComplex₂.ιTotal_map]
    rw [← Category.assoc]
    exact congrArg (fun z ↦ z ≫ D'.ιTotal (.up ℤ) 0 n n (by simp))
      (hypercoverAbelianRowAugmentation_naturality X R U W (f.f n))

private instance hypercoverAbelianSections_additive :
    (hypercoverAbelianSections.{t, u, v} X R U W).Additive where
  map_add := by intros; rfl

private instance sectionEvaluation_additive (p : ℕ) :
    (hypercoverAbelianSections X R U W ⋙ (CategoryTheory.evaluation _ _).obj ⦋p⦌).Additive where
  map_add {_I _J} {f g} := congr_app
    ((hypercoverAbelianSections X R U W).map_add (f := f) (g := g)) ⦋p⦌

private instance sectionEvaluation_preservesZero (p : ℕ) :
    (hypercoverAbelianSections.{t, u, v} X R U W ⋙
      (CategoryTheory.evaluation _ _).obj ⦋p⦌).PreservesZeroMorphisms where
  map_zero := by intros; rfl

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `AddCommGrpCat.{max u v (t + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

private theorem sectionsEvaluation_preservesHomology (R : Sheaf (topology X) RingCat.{u})
    (p : ℕ)
    (hweak : (topology X).IsWeaklyContractible.{max u v (t + 1)} (W _⦋p⦌).left) :
    (hypercoverAbelianSections.{t, u, v} X R U W ⋙
      (CategoryTheory.evaluation _ _).obj ⦋p⦌).PreservesHomology := by
  let q : X.ProEt ≌ AsSmall.{max u v (t + 1)} X.ProEt := AsSmall.equiv
  let J := q.inverse.inducedTopology (topology X)
  have : HasSheafify (topology X) AddCommGrpCat.{max u v (t + 1)} :=
    q.hasSheafify (topology X) J _
  have : (topology X).WEqualsLocallyBijective AddCommGrpCat.{max u v (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.transport (topology X) J q.inverse
      (Functor.IsDenseSubsite.coverPreserving _ _ _)
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{max u v (t + 1)} R) :=
    (moduleSheaves_colimits_forgetful R).2.2.1
  let ev := SheafOfModules.evaluation.{max u v (t + 1)} R (op (W _⦋p⦌).left)
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (SheafOfModules.toSheaf R).map f
    have : Epi g := inferInstance
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v (t + 1)} g).mpr
        inferInstance
    let g' := (sheafCompose (topology X)
      (CategoryTheory.forget AddCommGrpCat.{max u v (t + 1)})).map g
    have : Sheaf.IsLocallySurjective g' := inferInstance
    exact (ModuleCat.epi_iff_surjective (ev.map f)).mpr (hweak g' inferInstance)
  have : ev.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels ev
  have : PreservesFiniteLimits ev := Functor.preservesFiniteLimits_of_preservesHomology ev
  have : PreservesFiniteColimits ev := Functor.preservesFiniteColimits_of_preservesHomology ev
  let G := forget₂
    (ModuleCat.{max u v (t + 1)} (R.obj.obj (op (W _⦋p⦌).left)))
      AddCommGrpCat.{max u v (t + 1)}
  have : PreservesColimits G :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max u v (t + 1), u,
      max u v (t + 1), max u v (t + 1)} (R.obj.obj (op (W _⦋p⦌).left))
  change (ev ⋙ G).PreservesHomology
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionColumnIso
    (E : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ) (p : ℕ) :
    (HomologicalComplex₂.flip
      (((hypercoverAbelianRows X R U W).mapHomologicalComplex (.up ℤ)).obj E)).X (p : ℤ) ≅
      (((hypercoverAbelianSections X R U W ⋙
        (CategoryTheory.evaluation _ _).obj ⦋p⦌).mapHomologicalComplex
        (.up ℤ)).obj E) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q ↦
    (((AlgebraicTopology.alternatingCofaceMapComplex _).obj
      ((hypercoverAbelianSections X R U W).obj (E.X q))).extendXIso
        ComplexShape.embeddingUpNat (i := p) rfl)) ?_
  intro q r h
  symm
  change ((ComplexShape.embeddingUpNat.extendFunctor _).map
    ((AlgebraicTopology.alternatingCofaceMapComplex _).map
      ((hypercoverAbelianSections X R U W).map (E.d q r)))).f (p : ℤ) ≫ _ = _
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := p) rfl]
  simp

private theorem sectionBicomplex_zero
    (E : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ)
    (N : ℤ) [E.IsStrictlyGE N] (p q : ℤ) (h : p < 0 ∨ q < N) :
    IsZero (((HomologicalComplex₂.flip
      (((hypercoverAbelianRows X R U W).mapHomologicalComplex (.up ℤ)).obj E)).X p).X q) := by
  change IsZero (((hypercoverAbelianRows X R U W).obj (E.X q)).X p)
  rcases h with hp | hq
  · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
      intro i hi
      change (i : ℤ) = p at hi
      omega)
  · exact (HomologicalComplex.eval _ _ p).map_isZero
      ((hypercoverAbelianRows X R U W).map_isZero (E.isZero_of_isStrictlyGE N q hq))

set_option maxHeartbeats 800000 in
-- Comparing section-column maps unfolds the section and extension functor compositions.
set_option backward.isDefEq.respectTransparency false in
/-- Weakly contractible terms suffice for bounded-below quasi-isomorphism invariance;
no covering or matching-map hypotheses are needed for this comparison.
Source: Stacks Project, Tags 09A2 and 0946 (1).
(blueprint: det-pe-hypercover-complex).

Proof: choose a common lower bound N. In each nonnegative simplicial degree p,
evaluation at U_p preserves homology by weak contractibility. Thus the vertical
complex map is a quasi-isomorphism.
The extension-by-zero column isomorphisms identify these vertical maps with the
columns of the section bicomplex map. Negative columns are zero. Both bicomplexes
vanish for p<0 or q<N, so bounded-below total-column comparison applies. -/
private theorem hypercoverAbelianTotal_map_quasiIso_of_weaklyContractible
    (hweak : ∀ p : ℕ,
      (topology X).IsWeaklyContractible.{max u v (t + 1)} (W _⦋p⦌).left)
    (E F : CochainComplex.Plus (ringedSiteModules.{max u v (t + 1)} R))
    (f : E ⟶ F) (hf : QuasiIso f.hom) :
    QuasiIso ((hypercoverAbelianTotal X R U W).map f.hom) := by
  have : QuasiIso f.hom := hf
  obtain ⟨NE, hE⟩ := E.property
  obtain ⟨NF, hF⟩ := F.property
  let N := min NE NF
  have := hE
  have := hF
  have := E.obj.isStrictlyGE_of_ge N NE (min_le_left _ _)
  have := F.obj.isStrictlyGE_of_ge N NF (min_le_right _ _)
  let g := (HomologicalComplex₂.flipFunctor _ (.up ℤ) (.up ℤ)).map
    (((hypercoverAbelianRows X R U W).mapHomologicalComplex (.up ℤ)).map f.hom)
  apply HomologicalComplex₂.quasiIso_totalMap_of_boundedBelow_columns g 0 N
    (sectionBicomplex_zero X R U W E.obj N) (sectionBicomplex_zero X R U W F.obj N)
  intro p
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    let ev := hypercoverAbelianSections X R U W ⋙ (CategoryTheory.evaluation _ _).obj ⦋p⦌
    have : ev.PreservesHomology := sectionsEvaluation_preservesHomology X U W R p (hweak p)
    have : QuasiIso ((ev.mapHomologicalComplex (.up ℤ)).map f.hom) := inferInstance
    apply (quasiIso_iff_of_arrow_mk_iso (g.f (p : ℤ)) _
      (Arrow.isoMk (sectionColumnIso X R U W E.obj p)
        (sectionColumnIso X R U W F.obj p) ?_)).mpr this
    apply HomologicalComplex.hom_ext
    intro q
    dsimp only [HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_hom_f]
    symm
    change ((ComplexShape.embeddingUpNat.extendFunctor _).map
      ((AlgebraicTopology.alternatingCofaceMapComplex _).map
        ((hypercoverAbelianSections X R U W).map (f.hom.f q)))).f (p : ℤ) ≫ _ = _
    erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := p) rfl]
    simp [sectionColumnIso]
    rfl
  · have hzero (A : CochainComplex.Plus (ringedSiteModules.{max u v (t + 1)} R)) :
        IsZero ((HomologicalComplex₂.flip
          (((hypercoverAbelianRows X R U W).mapHomologicalComplex (.up ℤ)).obj A.obj)).X p) := by
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex.hom_ext
      intro q
      change (𝟙 (((hypercoverAbelianRows X R U W).obj (A.obj.X q)).X p)) = 0
      exact (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
        intro i hi
        change (i : ℤ) = p at hi
        omega)).eq_of_src _ _
    have : IsIso (g.f p) := (hzero E).isIso (hzero F) _
    infer_instance


set_option maxHeartbeats 800000 in
-- The comparison expands the evaluation, single-complex and section functors.
set_option backward.isDefEq.respectTransparency false in
/-- Exact descent for individual injective sheaves implies descent for a
bounded-below complex of injective sheaves.
Source: Stacks Project, Tags 09A2 and 01GE.
(blueprint: det-pe-hypercover-complex).
Proof: use the canonical restriction as a chain augmentation into the zeroth
simplicial column. Naturality makes it a map of complexes. Its transposed column
in coefficient degree n is precisely the single-sheaf row augmentation, hence is
quasi-isomorphic by hypothesis. The bicomplex vanishes below simplicial degree zero
and below a lower bound for J. Apply bounded-below row augmentation comparison. -/
private theorem hypercoverAbelianAugmentation_quasiIso_of_injective_rows
    (hrows : ∀ (I : ringedSiteModules.{max u v (t + 1)} R), Injective I →
      QuasiIso (hypercoverAbelianRowAugmentationComplex X R U W I))
    (J : CochainComplex.Plus (ringedSiteModules.{max u v (t + 1)} R))
    (hJ : ∀ n : ℤ, Injective (J.obj.X n)) :
    QuasiIso ((hypercoverAbelianAugmentation X R U W).app J.obj) := by
  let K := HomologicalComplex₂.flip
    (((hypercoverAbelianRows X R U W).mapHomologicalComplex (.up ℤ)).obj J.obj)
  let A : CochainComplex _ ℤ :=
    ((hypercoverAbelianEvaluation X R U).mapHomologicalComplex (.up ℤ)).obj J.obj
  let a : A ⟶ K.X 0 :=
    { f := fun n ↦ hypercoverAbelianRowAugmentation X R U W (J.obj.X n)
      comm' := fun n m _ ↦
        (hypercoverAbelianRowAugmentation_naturality X R U W (J.obj.d n m)).symm }
  have ha : ∀ p, (ComplexShape.up ℤ).Rel 0 p → a ≫ K.d 0 p = 0 := by
    intro p hp
    obtain rfl : p = 1 := by simpa using hp.symm
    apply HomologicalComplex.hom_ext
    intro n
    exact hypercoverAbelianRowAugmentation_d X R U W (J.obj.X n)
  obtain ⟨N, hN⟩ := J.property
  have := hN
  have : A.IsStrictlyGE N := by
    apply (CochainComplex.isStrictlyGE_iff A N).mpr
    intro n hn
    exact (hypercoverAbelianEvaluation X R U).map_isZero
      (J.obj.isZero_of_isStrictlyGE N n hn)
  refine HomologicalComplex₂.quasiIso_of_boundedBelow_row_augmentation K A N ?_ a ha
    ((hypercoverAbelianAugmentation X R U W).app J.obj) (fun _ ↦ rfl) ?_
  · intro p q h
    change IsZero (((hypercoverAbelianRows X R U W).obj (J.obj.X q)).X p)
    rcases h with hp | hq
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
        intro i hi
        change (i : ℤ) = p at hi
        omega)
    · exact (HomologicalComplex.eval _ _ p).map_isZero
        ((hypercoverAbelianRows X R U W).map_isZero
          (J.obj.isZero_of_isStrictlyGE N q hq))
  · intro n
    apply (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk
        ((HomologicalComplex.singleMapHomologicalComplex
          (HomologicalComplex.eval _ (.up ℤ) n) (.up ℤ) 0).app A)
        (Iso.refl _) ?_)).mpr (hrows (J.obj.X n) (hJ n))
    apply HomologicalComplex.hom_ext
    intro p
    by_cases hp : p = 0
    · subst p
      dsimp only [HomologicalComplex.comp_f, Arrow.mk_hom,
        Iso.refl_hom, HomologicalComplex.id_f, Category.comp_id]
      erw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
      dsimp only [hypercoverAbelianRowAugmentationComplex]
      rw [HomologicalComplex.mkHomFromSingle_f]
      change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom.f n ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (A.X n)).inv) ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (A.X n)).hom ≫ _ = _
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id]
      change _ = ((HomologicalComplex.mkHomFromSingle a ha).f 0).f n
      rw [HomologicalComplex.mkHomFromSingle_f]
      rfl
    · exact ((HomologicalComplex.eval _ (.up ℤ) n).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 A p hp)).eq_of_src _ _


private theorem all_lower_simplex_eq_of_faces {C : Type*} [Category* C]
    (U : SimplicialObject C) (n : ℕ) (T : C)
    (p : ∀ (Δ : SimplexCategory), Δ.len < n + 1 →
      (Δ ⟶ SimplexCategory.mk (n + 1)) → (T ⟶ U.obj (op Δ)))
    (hc : ∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n + 1)
      (h' : Δ'.len < n + 1) (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk (n + 1)),
      p Δ h θ ≫ U.map α.op = p Δ' h' (α ≫ θ))
    (t : T ⟶ U _⦋n + 1⦌)
    (ht : ∀ i : Fin (n + 2), t ≫ U.δ i = p (SimplexCategory.mk n) (by simp)
      (SimplexCategory.δ i)) :
    ∀ (Δ : SimplexCategory) (h : Δ.len < n + 1)
      (θ : Δ ⟶ SimplexCategory.mk (n + 1)), t ≫ U.map θ.op = p Δ h θ := by
  intro Δ h θ
  obtain ⟨i, θ', hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective θ (by
    intro hs
    have hh := Fintype.card_le_of_surjective θ.toOrderHom hs
    simp only [Fintype.card_fin] at hh
    have : Δ.len + 1 < n + 2 := by omega
    exact (not_le.mpr this) hh)
  rw [hθ, op_comp, U.map_comp, ← Category.assoc]
  change (t ≫ U.δ i) ≫ U.map θ'.op = _
  rw [ht]
  exact hc _ _ (by simp) h θ' (SimplexCategory.δ i)

set_option backward.isDefEq.respectTransparency false in
private theorem properFace_matching_local_lifting
    (hzero : Presieve.singleton (W _⦋0⦌).hom ∈ (precoverage X) U)
    (hmatching : ∀ r : ℕ,
      ∃ (c : Cone (SimplicialObject.properFaceDiagram W (r + 1)))
        (μ : W _⦋r + 1⦌ ⟶ c.pt),
        Nonempty (IsLimit c) ∧ Presieve.singleton μ.left ∈ (precoverage X) c.pt.left ∧
          ∀ a : SimplicialObject.ProperFaceCategory (r + 1),
            μ ≫ c.π.app (op a) = W.map a.obj.hom.op)
    (n : ℕ) (T : X.ProEt) (w : T ⟶ U)
    (p : ∀ (Δ : SimplexCategory), Δ.len < n →
      (Δ ⟶ SimplexCategory.mk n) → (T ⟶ (W ⋙ Over.forget U).obj (op Δ)))
    (hp : ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
      p Δ h θ ≫ (W.obj (op Δ)).hom = w)
    (hc : ∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
      p Δ h θ ≫ (W.map α.op).left = p Δ' h' (α ≫ θ)) :
    ∃ S : Sieve T, S ∈ topology X T ∧
      ∀ (V : X.ProEt) (f : V ⟶ T), S f →
        ∃ t : V ⟶ (W _⦋n⦌).left,
          t ≫ (W _⦋n⦌).hom = f ≫ w ∧
          ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
            t ≫ (W.map θ.op).left = f ≫ p Δ h θ := by
  cases n with
  | zero =>
    let S := (Sieve.generate (Presieve.singleton (W _⦋0⦌).hom)).pullback w
    refine ⟨S, (topology X).pullback_stable w
      (Precoverage.generate_mem_toGrothendieck hzero), ?_⟩
    intro V f hf
    obtain ⟨Z, t, g, hg, ht⟩ := hf
    cases hg
    exact ⟨t, ht, fun Δ h θ ↦ by omega⟩
  | succ n =>
    obtain ⟨c, μ, ⟨hlim⟩, hμcover, hμ⟩ := hmatching n
    let cone : Cone (SimplicialObject.properFaceDiagram W (n + 1)) :=
      { pt := Over.mk w
        π :=
          { app := fun a ↦ Over.homMk
              (p a.unop.obj.left a.unop.property.1 a.unop.obj.hom)
              (hp _ _ _)
            naturality := by
              intro a b f
              apply Over.OverMorphism.ext
              symm
              change p _ _ _ ≫ (W.map f.unop.hom.left.op).left = _
              rw [hc _ _ a.unop.property.1 b.unop.property.1]
              congr 1
              exact f.unop.hom.w } }
    let g := hlim.lift cone
    let S := (Sieve.generate (Presieve.singleton μ.left)).pullback g.left
    refine ⟨S, (topology X).pullback_stable g.left
      (Precoverage.generate_mem_toGrothendieck hμcover), ?_⟩
    intro V f hf
    obtain ⟨Z, t, k, hk, ht⟩ := hf
    cases hk
    refine ⟨t, ?_, ?_⟩
    · rw [← μ.w, ← Category.assoc, ht, Category.assoc, g.w]
      rfl
    · apply all_lower_simplex_eq_of_faces (W ⋙ Over.forget U) n V
        (fun Δ h θ ↦ f ≫ p Δ h θ)
      · intro Δ Δ' h h' α θ
        change (f ≫ p Δ h θ) ≫ (W.map α.op).left = _
        rw [Category.assoc, hc]
      · intro i
        have hfac := hlim.fac cone (op (SimplicialObject.properFace n i))
        have hmu := hμ (SimplicialObject.properFace n i)
        change μ ≫ c.π.app (op (SimplicialObject.properFace n i)) = W.δ i at hmu
        change t ≫ (W.δ i).left = _
        rw [← hmu]
        change t ≫ (μ.left ≫ _) = _
        rw [← Category.assoc, ht, Category.assoc]
        exact congrArg (fun z ↦ f ≫ z.left) hfac

private theorem singleAbelianAugmentation_quasiIso
    (K : CochainComplex AddCommGrpCat.{v} ℕ) (M : AddCommGrpCat.{v})
    (f : (CochainComplex.single₀ _).obj M ⟶ K)
    (hinj : Function.Injective (f.f 0))
    (hzero : Function.Exact (f.f 0) (K.d 0 1))
    (hpos : ∀ n : ℕ, K.ExactAt (n + 1)) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    apply (ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_).mpr
      ⟨(ShortComplex.ab_exact_iff_function_exact _).mpr hzero,
        (AddCommGrpCat.mono_iff_injective _).mpr hinj⟩
    · exact HomologicalComplex.single_obj_d (.up ℕ) 0 M 0 1
    · exact HomologicalComplex.single_obj_d (.up ℕ) 0 M 0 0
    · exact K.shape 0 0 (by simp)
  | succ n =>
    exact (quasiIsoAt_iff_exactAt f (n + 1)
      (HomologicalComplex.ExactAt.of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ (n + 1) (by omega)))).mpr (hpos n)

set_option maxHeartbeats 800000 in
-- Transporting the site unfolds pushforward, restriction of scalars and extension functors.
set_option backward.isDefEq.respectTransparency false in
private theorem hypercoverAbelianRowAugmentationComplex_quasiIso_of_injective
    (hzero : Presieve.singleton (W _⦋0⦌).hom ∈ (precoverage X) U)
    (hmatching : ∀ r : ℕ,
      ∃ (c : Cone (SimplicialObject.properFaceDiagram W (r + 1)))
        (μ : W _⦋r + 1⦌ ⟶ c.pt),
        Nonempty (IsLimit c) ∧ Presieve.singleton μ.left ∈ (precoverage X) c.pt.left ∧
          ∀ a : SimplicialObject.ProperFaceCategory (r + 1),
            μ ≫ c.π.app (op a) = W.map a.obj.hom.op)
    (I : ringedSiteModules.{max u v (t + 1)} R) [Injective I] :
    QuasiIso (hypercoverAbelianRowAugmentationComplex X R U W I) := by
  let C' := ULiftHom.{t + 1} X.ProEt
  let up : X.ProEt ⥤ C' := ULiftHom.up
  let down : C' ⥤ X.ProEt := ULiftHom.down
  let top' := down.inducedTopology (topology X)
  have : down.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').inverse.IsEquivalence)
  have : up.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').functor.IsEquivalence)
  have : down.IsContinuous top' (topology X) := by dsimp [top', down]; infer_instance
  have : up.IsContinuous (topology X) top' := by
    exact inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').functor.IsContinuous
      (topology X) ((ULiftHom.equiv : X.ProEt ≌ C').inverse.inducedTopology (topology X)))
  have : (ULiftHom.equiv.symm : C' ≌ X.ProEt).functor.IsContinuous top'
      (topology X) := by change down.IsContinuous top' (topology X); infer_instance
  have : (ULiftHom.equiv.symm : C' ≌ X.ProEt).inverse.IsContinuous
      (topology X) top' := by change up.IsContinuous (topology X) top'; infer_instance
  have : HasPullbacks C' := Adjunction.hasLimitsOfShape_of_equivalence down
  let pc := top'.toPrecoverage
  have hpc : pc.toGrothendieck = top' := by
    refine le_antisymm top'.toGrothendieck_toPrecoverage_le ?_
    intro T S hS
    have h := pc.generate_mem_toGrothendieck
      ((top'.arrows_mem_toPrecoverage_iff S).mpr hS)
    simpa only [Sieve.generate_sieve] using h
  have : (topology X).Subcanonical := (proetale_site_properties X).2.1
  have : top'.Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful down top' (topology X)
  let R' := (down.sheafPushforwardContinuous RingCat.{u} top' (topology X)).obj R
  let E : SheafOfModules.{max u v (t + 1)} R ≌
      SheafOfModules.{max u v (t + 1)} R' :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (ULiftHom.equiv.symm : C' ≌ X.ProEt) (𝟙 R') (𝟙 R)
      (by ext V x; change (R.obj.map (𝟙 _)).hom x = x; simp)
      (by ext V x; change (R.obj.map (𝟙 _)).hom x = x; simp)
  let I' : SheafOfModules.{max u v (t + 1)} R' := E.functor.obj I
  have : Injective I' := (E.map_injective_iff I).mpr inferInstance
  have : pc.toGrothendieck.Subcanonical := by rw [hpc]; infer_instance
  have hseq' := ringedHypercover_injective_augmentation_exact_ring.{t + 1, v, u} pc
  rw [hpc] at hseq'
  let e : W ⋙ Over.forget U ⟶ (Functor.const _).obj U :=
    { app := fun Δ ↦ (W.obj Δ).hom
      naturality := by
        intro Δ Δ' f
        simp only [Functor.comp_map, Over.forget_map, Functor.const_obj_map]
        exact (W.map f).w }
  have hseq := hseq' R' I' (up.obj U) (W ⋙ Over.forget U ⋙ up)
    (Functor.whiskerRight e up) (by
      intro n T w p hp hcomp
      obtain ⟨S, hS, hlift⟩ := properFace_matching_local_lifting X U W hzero hmatching
        n (down.obj T) (down.map w)
        (fun Δ h θ ↦ down.map (p Δ h θ))
        (fun Δ h θ ↦ congrArg down.map (hp Δ h θ))
        (fun Δ Δ' h h' α θ ↦ congrArg down.map (hcomp Δ Δ' h h' α θ))
      refine ⟨S.functorPullback down, ?_, ?_⟩
      · change _ ∈ down.inducedTopology (topology X) T
        rw [← Functor.restrictedTopology_eq_inducedTopology]
        exact Functor.IsCocontinuous.cover_lift hS
      · intro V f hf
        obtain ⟨t, ht, htp⟩ := hlift (down.obj V) (down.map f) hf
        exact ⟨ULift.up t, congrArg ULift.up ht,
          fun Δ h θ ↦ congrArg ULift.up (htp Δ h θ)⟩)
  let row := (AlgebraicTopology.alternatingCofaceMapComplex _).obj
    ((hypercoverAbelianSections X R U W).obj I)
  let a : (CochainComplex.single₀ _).obj
      ((hypercoverAbelianEvaluation X R U).obj I) ⟶ row :=
    (CochainComplex.fromSingle₀Equiv row _).symm
      ⟨hypercoverAbelianRestrictionZero X R U W I,
        hypercoverAbelianRestrictionZero_d X R U W I⟩
  have hd (n : ℕ) (s : row.X n) :
      (row.d n (n + 1)) s =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.val.map (W.δ j).left.op s := by
    change ((AlgebraicTopology.AlternatingCofaceMapComplex.obj
      ((hypercoverAbelianSections X R U W).obj I)).d n (n + 1)) s = _
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj,
      CochainComplex.of_d, AlgebraicTopology.AlternatingCofaceMapComplex.objD]
    change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      (((hypercoverAbelianSections X R U W).obj I).δ j)).hom s = _
    change (AddCommGrpCat.homAddEquiv
      (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        (((hypercoverAbelianSections X R U W).obj I).δ j))) s = _
    rw [map_sum]
    simp only [map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply]
    rfl
  have ha : QuasiIso a := by
    apply singleAbelianAugmentation_quasiIso row _ a
    · have h := hseq.1
      change Function.Injective (I.val.map (W _⦋0⦌).hom.op) at h
      change Function.Injective (hypercoverAbelianRestrictionZero X R U W I)
      intro x y hxy
      apply h
      exact hxy
    · have h := hseq.2.1
      change Function.Exact (I.val.map (W _⦋0⦌).hom.op)
        (fun s ↦ ∑ j : Fin 2, (-1 : ℤ) ^ j.val • I.val.map (W.δ j).left.op s) at h
      change Function.Exact (fun x ↦ hypercoverAbelianRestrictionZero X R U W I x)
        (fun x ↦ (row.d 0 1) x)
      simp only [hypercoverAbelianRestrictionZero_apply, hd]
      exact h
    · intro n
      rw [HomologicalComplex.exactAt_iff' row n (n + 1) (n + 2) (by simp) (by simp)]
      apply (ShortComplex.ab_exact_iff_function_exact _).mpr
      have h := hseq.2.2 n
      change Function.Exact
        (fun s ↦ ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.val.map (W.δ j).left.op s)
        (fun s ↦ ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • I.val.map (W.δ j).left.op s) at h
      change Function.Exact (fun x ↦ (row.d n (n + 1)) x)
        (fun x ↦ (row.d (n + 1) (n + 2)) x)
      simp only [hd]
      exact h
  have he : QuasiIso (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat) :=
    inferInstance
  apply (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      ((hypercoverAbelianEvaluation X R U).obj I) 0 0 rfl) (Iso.refl _) ?_)).mp he
  apply (cancel_epi (HomologicalComplex.extendSingleIso
    ComplexShape.embeddingUpNat ((hypercoverAbelianEvaluation X R U).obj I)
      0 0 rfl).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f]
  erw [HomologicalComplex.extendMap_f a ComplexShape.embeddingUpNat (i := 0) rfl]
  simp [hypercoverAbelianRowAugmentationComplex, hypercoverAbelianRowAugmentation, a]
  rfl

private noncomputable def hypercoverAbelianDerivedUnit
    [HasDerivedCategory.{wA} (ringedSiteModules.{max u v (t + 1)} R)]
    [HasDerivedCategory.{wB} AddCommGrpCat.{max u v (t + 1)}] :
    (hypercoverAbelianEvaluation.{t, u, v} X R U).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙
        (hypercoverAbelianEvaluation.{t, u, v} X R U).rightDerivedFunctorOfQuasiIsoResolutions
          (moduleQuasiIsoKInjectiveResolutions X R) where
  app K :=
    (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
      ((hypercoverAbelianEvaluation.{t, u, v} X R U).rightDerivedFunctorOfQuasiIsoResolutionsUnit
        (moduleQuasiIsoKInjectiveResolutions X R)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
      ((hypercoverAbelianEvaluation.{t, u, v} X R U).rightDerivedFunctorOfQuasiIsoResolutions
        (moduleQuasiIsoKInjectiveResolutions X R)).map
          ((DerivedCategory.quotientCompQhIso _).hom.app K)
  naturality K L f := by
    have h :=
      ((hypercoverAbelianEvaluation.{t, u, v} X R U).rightDerivedFunctorOfQuasiIsoResolutionsUnit
        (moduleQuasiIsoKInjectiveResolutions X R)).naturality
          ((HomotopyCategory.quotient _ (.up ℤ)).map f)
    simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at h
    simp only [Functor.comp_map,
      DerivedCategory.quotientCompQhIso_inv_naturality_assoc, Category.assoc]
    rw [reassoc_of% h, ← Functor.map_comp, ← Functor.map_comp,
      DerivedCategory.quotientCompQhIso_hom_naturality]

set_option maxHeartbeats 800000 in
-- The unit comparisons expand the resolution and localization functor compositions.
set_option backward.isDefEq.respectTransparency false in
private theorem hypercoverAbelianNaturalIso_of_injective_rows
    [HasDerivedCategory.{wA} (ringedSiteModules.{max u v (t + 1)} R)]
    [HasDerivedCategory.{wB} AddCommGrpCat.{max u v (t + 1)}]
    (hweak : ∀ p : ℕ,
      (topology X).IsWeaklyContractible.{max u v (t + 1)} (W _⦋p⦌).left)
    (hrows : ∀ (I : ringedSiteModules.{max u v (t + 1)} R), Injective I →
      QuasiIso (hypercoverAbelianRowAugmentationComplex X R U W I)) :
    Nonempty
      (CochainComplex.Plus.ι (ringedSiteModules.{max u v (t + 1)} R) ⋙ DerivedCategory.Q ⋙
          (hypercoverAbelianEvaluation.{t, u, v} X R U).rightDerivedFunctorOfQuasiIsoResolutions
            (moduleQuasiIsoKInjectiveResolutions X R) ≅
        CochainComplex.Plus.ι (ringedSiteModules.{max u v (t + 1)} R) ⋙
          hypercoverAbelianTotal X R U W ⋙ DerivedCategory.Q) := by
  classical
  let A := ringedSiteModules.{max u v (t + 1)} R
  let F := hypercoverAbelianEvaluation.{t, u, v} X R U
  let H := hypercoverAbelianTotal.{t, u, v} X R U W
  let RF := F.rightDerivedFunctorOfQuasiIsoResolutions
    (moduleQuasiIsoKInjectiveResolutions X R)
  let α := hypercoverAbelianAugmentation.{t, u, v} X R U W
  let ν := hypercoverAbelianDerivedUnit.{t, u, v, wA, wB} X R U
  have : IsGrothendieckAbelian.{max u v (t + 1)} A :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{t + 1, t, u, v} (topology X) R
  have res (K : CochainComplex.Plus A) : ∃ (J : CochainComplex A ℤ) (j : K.obj ⟶ J),
      ∃ (_ : QuasiIso j) (_ : ∀ n : ℤ, Injective (J.X n)),
        ∃ a : ℤ, J.IsStrictlyGE a := by
    obtain ⟨a, ha⟩ := K.property
    have := ha
    obtain ⟨J, j, hj, hJ, hJa⟩ :=
      CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K.obj a
    exact ⟨J, j, hj, hJ, a, hJa⟩
  choose J j hj hJ a hJa using res
  have (K : CochainComplex.Plus A) : QuasiIso (j K) := hj K
  have (K : CochainComplex.Plus A) : (J K).IsStrictlyGE (a K) := hJa K
  have (K : CochainComplex.Plus A) (n : ℤ) : Injective ((J K).X n) := hJ K n
  have (K : CochainComplex.Plus A) : (J K).IsKInjective :=
    CochainComplex.isKInjective_of_injective (J K) (a K)
  let resJ (K : CochainComplex.Plus A) : K.obj.KInjectiveResolution :=
    { I := J K, ι := j K }
  let Jplus (K : CochainComplex.Plus A) : CochainComplex.Plus A := ⟨J K, a K, hJa K⟩
  have hν (K : CochainComplex.Plus A) : IsIso (ν.app (J K)) := by
    have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso
      (moduleQuasiIsoKInjectiveResolutions X R) (J K)
    dsimp [ν, hypercoverAbelianDerivedUnit]
    infer_instance
  have hαJ (K : CochainComplex.Plus A) : QuasiIso (α.app (J K)) :=
    hypercoverAbelianAugmentation_quasiIso_of_injective_rows X R U W hrows (Jplus K) (hJ K)
  have hH (K L : CochainComplex.Plus A) (f : K ⟶ L) (hf : QuasiIso f.hom) :
      QuasiIso (H.map f.hom) :=
    hypercoverAbelianTotal_map_quasiIso_of_weaklyContractible X R U W hweak K L f hf
  have hHj (K : CochainComplex.Plus A) : QuasiIso (H.map (j K)) :=
    hH K (Jplus K) ⟨j K⟩ (hj K)
  let e (K : CochainComplex.Plus A) : RF.obj (DerivedCategory.Q.obj K.obj) ≅
      DerivedCategory.Q.obj (H.obj K.obj) :=
    asIso (RF.map (DerivedCategory.Q.map (j K))) ≪≫
      (asIso (ν.app (J K))).symm ≪≫ asIso (DerivedCategory.Q.map (α.app (J K))) ≪≫
        (asIso (DerivedCategory.Q.map (H.map (j K)))).symm
  have he (K : CochainComplex.Plus A) :
      (e K).hom ≫ DerivedCategory.Q.map (H.map (j K)) =
        RF.map (DerivedCategory.Q.map (j K)) ≫
          CategoryTheory.inv (ν.app (J K)) ≫ DerivedCategory.Q.map (α.app (J K)) := by
    simp [e]
  refine ⟨NatIso.ofComponents e ?_⟩
  intro K L f
  let g := (resJ K).map (resJ L) f.hom
  have hhom : Homotopy (j K ≫ g) (f.hom ≫ j L) :=
    (resJ K).mapHomotopy (resJ L) f.hom
  have hR : RF.map (DerivedCategory.Q.map (j K)) ≫
      RF.map (DerivedCategory.Q.map g) =
      RF.map (DerivedCategory.Q.map f.hom) ≫ RF.map (DerivedCategory.Q.map (j L)) := by
    simpa only [Functor.comp_map, Functor.map_comp] using
      map_eq_of_boundedBelow_homotopy (DerivedCategory.Q ⋙ RF)
        (fun E G φ hφ ↦ by
          have := hφ
          change IsIso (RF.map (DerivedCategory.Q.map φ.hom))
          infer_instance)
        K (Jplus L) _ _ hhom
  have hT : DerivedCategory.Q.map (H.map (j K)) ≫ DerivedCategory.Q.map (H.map g) =
      DerivedCategory.Q.map (H.map f.hom) ≫ DerivedCategory.Q.map (H.map (j L)) := by
    simpa only [Functor.comp_map, Functor.map_comp] using
      map_eq_of_boundedBelow_homotopy (H ⋙ DerivedCategory.Q)
        (fun E G φ hφ ↦ by
          have := hH E G φ hφ
          change IsIso (DerivedCategory.Q.map (H.map φ.hom))
          infer_instance)
        K (Jplus L) _ _ hhom
  have hνg : RF.map (DerivedCategory.Q.map g) ≫ CategoryTheory.inv (ν.app (J L)) =
      CategoryTheory.inv (ν.app (J K)) ≫ DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map g) := by
    apply (cancel_mono (ν.app (J L))).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hn := ν.naturality g
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g) ≫
      ν.app (J L) = ν.app (J K) ≫ RF.map (DerivedCategory.Q.map g) at hn
    rw [hn]
    simp
  have hαg : DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g) ≫
      DerivedCategory.Q.map (α.app (J L)) =
      DerivedCategory.Q.map (α.app (J K)) ≫ DerivedCategory.Q.map (H.map g) := by
    rw [← Functor.map_comp, ← Functor.map_comp, α.naturality]
  apply (cancel_mono (DerivedCategory.Q.map (H.map (j L)))).mp
  change (RF.map (DerivedCategory.Q.map f.hom) ≫ (e L).hom) ≫ _ =
    ((e K).hom ≫ DerivedCategory.Q.map (H.map f.hom)) ≫ _
  simp only [Category.assoc]
  rw [he]
  rw [← Category.assoc, ← hR]
  simp only [Category.assoc]
  rw [reassoc_of% hνg, hαg]
  rw [← reassoc_of% (he K), hT]


/-- Derived sections are naturally the alternating total sections of any weakly
contractible hypercover. `Plus` means that some integer a is a strict lower bound
on the terms, so it includes every complex and every bound in the node. The
natural isomorphism is on the full category of such complexes, hence includes maps
between complexes with different bounds. RΓ is exactly the recorded right derived
functor of abelian evaluation, using the existing K-injective resolution interface.
No affineness, quasi-compactness or quasi-separatedness assumption is imposed.

Source: blueprint main-20261015, det-pe-hypercover-complex.md; Stacks Project,
Tag 09A2 (blueprint: det-pe-hypercover-complex).

Proof (the seven steps of the node):
1. Simplicial identities pair the terms in delta squared with opposite signs.
   Naturality of d_K makes it commute with every restriction. The mixed terms
   `(-1)^(r+1) d_K delta` and `(-1)^r delta d_K` cancel. The construction above
   realizes this signed total functor. If b≥a and r+b=q, then 0≤r≤q-a, including
   the empty diagonal for q<a.
2. By def-weil-sheaf-of-modules-category, kernels are sectionwise. The forgetful
   functor to abelian sheaves preserves kernels and cokernels by
   lem-weil-pbc-module-sheaves-colimits-forgetful. The abelian- and set-sheaf
   locally-surjective-epi criteria and sk-def-pe-weak-contractible make evaluation
   at every W_r exact. The cycle-boundary short exact sequences then show that
   it preserves cohomology and every quasi-isomorphism.
3. On the common-universe small model of def-weil-pbc-proetale-site, choose a
   bounded-below termwise-injective K-injective resolution s:K→I by
   lem-sc-bounded-below-injective-resolution. If c bounds I, use N=min(a,c).
   The ring-sheaf Grothendieck theorem and lem-sfb-grothendieck-k-injective supply
   resolutions of all complexes, the hypothesis of def-sfb-right-derived-functor.
   Its resolution comparison identifies RΓ(U,K) with I(U).
4. det-pe-topos-functoriality-site gives the site axioms and subcanonicity.
   Pull the matching covers back along compatible lower-simplex tuples.
   Apply lem-sc-ringed-hypercover-injective-augmentation-ring to obtain each
   exact augmented row 0→I^b(U)→I^b(W_0)→I^b(W_1)→... . Injectivity here is
   injectivity as module sheaves, without forgetting the scalar action.
5. Restriction into column zero defines alpha_E:E(U)→T(E), naturally in E.
   The two faces agree after augmentation, so its outgoing horizontal component
   is zero. The vertical sign in column zero is one. The exact rows and common
   lower bound N let lem-weil-pbc-bounded-below-row-augmentation prove alpha_I
   a quasi-isomorphism.
6. Step 2 makes s a columnwise quasi-isomorphism. Apply
   lem-weil-pbc-bounded-below-total-column-comparison with P=0,Q=N to T(s).
   Compose the resolution comparison, alpha_I and the inverse of T(s) in D(Ab).
   The same argument with a common bound proves that T inverts every
   quasi-isomorphism between bounded-below complexes.
7. lem-weil-pbc-kinjective-hom-derived lifts derived comparison maps into
   K-injective resolutions to chain maps, uniquely up to homotopy, and makes
   the resolution squares commute up to homotopy. A coefficient homotopy h
   induces total homotopy `(-1)^r h(W_r)`; its horizontal terms cancel and its
   vertical terms give dh+hd. Restriction augmentation is strictly natural.
   These identities give the natural isomorphism below, independent of every
   resolution choice. Since T inverts quasi-isomorphisms, naturality also holds
   after passing to derived morphisms. -/
theorem hypercover_complex_natural_iso (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U))
    [HasDerivedCategory.{wA} (ringedSiteModules.{max u v (t + 1)} R)]
    [HasDerivedCategory.{wB} AddCommGrpCat.{max u v (t + 1)}]
    (hweak : ∀ r : ℕ,
      (topology X).IsWeaklyContractible.{max u v (t + 1)} (W _⦋r⦌).left)
    (hzero : Presieve.singleton (W _⦋0⦌).hom ∈ (precoverage X) U)
    (hmatching : ∀ r : ℕ,
      ∃ (c : Cone (SimplicialObject.properFaceDiagram W (r + 1)))
        (μ : W _⦋r + 1⦌ ⟶ c.pt),
        Nonempty (IsLimit c) ∧ Presieve.singleton μ.left ∈ (precoverage X) c.pt.left ∧
          ∀ a : SimplicialObject.ProperFaceCategory (r + 1),
            μ ≫ c.π.app (op a) = W.map a.obj.hom.op) :
    Nonempty
      (CochainComplex.Plus.ι (ringedSiteModules.{max u v (t + 1)} R) ⋙ DerivedCategory.Q ⋙
          (hypercoverAbelianEvaluation.{t, u, v} X R U).rightDerivedFunctorOfQuasiIsoResolutions
            (moduleQuasiIsoKInjectiveResolutions X R) ≅
        CochainComplex.Plus.ι (ringedSiteModules.{max u v (t + 1)} R) ⋙
          hypercoverAbelianTotal X R U W ⋙ DerivedCategory.Q) := by
  apply hypercoverAbelianNaturalIso_of_injective_rows X R U W hweak
  intro I hI
  exact hypercoverAbelianRowAugmentationComplex_quasiIso_of_injective X R U W
    hzero hmatching I

end AlgebraicGeometry.Scheme.ProEt
