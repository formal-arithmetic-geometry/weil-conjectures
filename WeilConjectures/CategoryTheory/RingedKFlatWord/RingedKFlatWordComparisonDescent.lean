/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.ScalarTensorSection
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Simultaneous K-flat word models and normalized comparison descent

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 0G7E, 06YY and 0D6D;
sites-modules.tex, Tags 03EK and 0GMW. Finite-word argument in the DAG proof
(blueprint: lem-trf-ringed-kflat-word-comparison-descent).

Words retain their parenthesizations. Their cochain counits are the actual composites
of the chosen universal edge counits. All constructions occur on the whole ringed site,
including the coefficient sequence site, before evaluation or inverse limit.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.checkUnivs false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u v r d z e
open CategoryTheory CategoryTheory.Limits CategoryTheory.CochainPullback

namespace CategoryTheory.RingedKFlatWord

-- Direct limit preservation and transport to a small site suffice for these functors.
attribute [local instance 0] hasSheafCompose_of_preservesMulticospan
attribute [local instance 20000] hasSheafCompose_of_preservesLimitsOfSize

set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency.types true

/-- A ringed site in fixed size bounds, with the existing module derived category.
Source: Stacks 06YS and 06YY; size convention def-weil-size-convention
(blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
structure Site where
  C : Type u
  [category : Category.{v} C]
  [small : EssentiallySmall.{r} C]
  J : GrothendieckTopology C
  R : Sheaf J CommRingCat.{r}
  [derivedCategory : HasDerivedCategory.{d} (CochainPullback.Modules.{r, u, v} (J := J) R)]

attribute [instance] Site.category Site.small Site.derivedCategory

private theorem siteHasSheafCompose (X : Site.{u, v, r, d}) :
    X.J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := inferInstance

private theorem siteHasSheafify (X : Site.{u, v, r, d}) :
    HasSheafify X.J AddCommGrpCat.{r} := inferInstance

private theorem siteWEquals (X : Site.{u, v, r, d}) :
    X.J.WEqualsLocallyBijective AddCommGrpCat.{r} := inferInstance

@[instance_reducible]
private noncomputable def siteAbelian (X : Site.{u, v, r, d}) :
    Abelian (CochainPullback.Modules.{r, u, v} X.R) := inferInstance

/-- An edge is an actual ringed pullback with its chosen universal cochain counit.
Exact derived functors are included through their canonical universal counit.
Source: Stacks 06YY and 0D6D
(blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
structure Edge (X Y : Site.{u, v, r, d}) where
  pullback : CategoryTheory.CochainPullback.RingedPullback.{r, u, v, u, v} (J := X.J) (K := Y.J)
      X.R Y.R
  derived : DerivedCategory (CochainPullback.Modules.{r, u, v} (J := X.J) X.R) ⥤
    DerivedCategory (CochainPullback.Modules.{r, u, v} (J := Y.J) Y.R)
  counit : DerivedCategory.Q ⋙ derived ⟶
    CochainPullback.pull.{r, u, v, u, v} pullback ⋙ DerivedCategory.Q
  universal : derived.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (CochainPullback.Modules.{r, u, v} (J := X.J) X.R) (.up ℤ))

variable {I : Type z} (S : I → Site.{u, v, r, d}) (E : I → I → Type e)
  (A : ∀ {i j : I}, E i j → Edge (S i) (S j))

/-- Finite composable words, including empty words and all parenthesizations.
Source: finite-word argument following Stacks 0D6D
(blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
inductive Word : I → I → Type (max z e)
  | nil (i : I) : Word i i
  | edge {i j : I} (a : E i j) : Word i j
  | comp {i j k : I} (w : Word i j) (v : Word j k) : Word i k

/-- The ordinary composite together with its inherited additivity proof.
Source: degreewise additive pullback, Stacks 06YY
(blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
def Word.ordinaryData {i j : I} : Word E i j →
    {F : CochainPullback.Modules.{r, u, v} (J := (S i).J) (S i).R ⥤
      CochainPullback.Modules.{r, u, v} (J := (S j).J) (S j).R // F.Additive}
  | .nil _ => ⟨𝟭 _, inferInstance⟩
  | .edge a => ⟨(A a).pullback.L, inferInstance⟩
  | .comp w v =>
      @id {F : CochainPullback.Modules.{r, u, v} (S _).R ⥤
        CochainPullback.Modules.{r, u, v} (S _).R // F.Additive}
        (let fw := ordinaryData w
         let fv := ordinaryData v
         letI := fw.property
         letI := fv.property
         ⟨fw.val ⋙ fv.val, inferInstance⟩)

/-- The ordinary word functor, without any change of module category.
Source: Stacks 0D6D (blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
abbrev Word.ordinary {i j : I} (w : Word E i j) := (w.ordinaryData S E A).val

/-- Additivity inherited from the ordinary pullback factors.
Source: Stacks 06YY (blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
instance Word.additive {i j : I} (w : Word E i j) : (w.ordinary S E A).Additive :=
  (w.ordinaryData S E A).property

/-- Degreewise application of the ordinary composite to entire unbounded complexes.
Source: Stacks 06YY (blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
abbrev Word.complex {i j : I} (w : Word E i j) :=
  (w.ordinary S E A).mapHomologicalComplex (.up ℤ)

/-- The composite of the specified derived edge functors.
Source: Stacks 0D6D (blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
noncomputable def Word.derived {i j : I} : Word E i j →
    (DerivedCategory (CochainPullback.Modules.{r, u, v} (J := (S i).J) (S i).R) ⥤
      DerivedCategory (CochainPullback.Modules.{r, u, v} (J := (S j).J) (S j).R))
  | .nil _ => 𝟭 _
  | .edge a => (A a).derived
  | .comp w v => derived w ⋙ derived v

/-- The displayed composite counit, including canonical degreewise compositors.
Source: Stacks 0D6D and DAG proof step 2
(blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
noncomputable def Word.counit : {i j : I} → (w : Word E i j) →
    (P : CochainComplex (CochainPullback.Modules.{r, u, v} (J := (S i).J) (S i).R) ℤ) →
    ((w.derived S E A).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((w.complex S E A).obj P))
  | _, _, .nil i, P => DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexIdIso
        (CochainPullback.Modules.{r, u, v} (J := (S i).J) (S i).R) (.up ℤ)).inv.app P)
  | _, _, .edge a, P => (A a).counit.app P
  | _, _, .comp w v, P => (v.derived S E A).map (counit w P) ≫
      counit v ((w.complex S E A).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (w.ordinary S E A ⋙ v.ordinary S E A)) (.up ℤ)).hom.app P)

/-- Flat-term K-flat is a conjunction of the two recorded predicates.
Source: Stacks 06YS (blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
abbrev Resolving (X : Site.{u, v, r, d})
    (P : CochainComplex (CochainPullback.Modules.{r, u, v} (J := X.J) X.R) ℤ) : Prop :=
  P.IsKFlatIndependentCoefficients ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := X.J) (R := X.R) (P.X n)

set_option backward.isDefEq.respectTransparency.types true

section

attribute [local instance 40000] siteHasSheafCompose siteHasSheafify siteWEquals siteAbelian

private theorem resolving_resolution (X : Site.{u, v, r, d})
    (K : CochainComplex (CochainPullback.Modules.{r, u, v} X.R) ℤ) :
    ∃ (P : CochainComplex (CochainPullback.Modules.{r, u, v} X.R) ℤ) (p : P ⟶ K),
      QuasiIso p ∧ Resolving X P := by
  obtain ⟨P, p, hk, hf, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  exact ⟨P, p, hp, hk, fun n ↦ (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso X.R (P.X n)).symm (hf n)⟩

end

set_option backward.isDefEq.respectTransparency.types true

/-- Normalization of a descended ordinary cell through the actual word counits.
Source: DAG proof steps 3--4 following Stacks 06YY and 0D6D
(blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
def Normalized {i j : I} {w v : Word E i j}
    (t : w.ordinary S E A ⟶ v.ordinary S E A)
    (tL : w.derived S E A ⟶ v.derived S E A) : Prop :=
  ∀ (P : CochainComplex (CochainPullback.Modules.{r, u, v} (J := (S i).J) (S i).R) ℤ), Resolving
      (S i) P →
    tL.app (DerivedCategory.Q.obj P) ≫ v.counit S E A P =
      w.counit S E A P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app P)

set_option backward.isDefEq.respectTransparency.types true

section

attribute [local instance 40000] siteHasSheafCompose siteHasSheafify siteWEquals siteAbelian

private noncomputable def counitNat : {i j : I} → (w : Word E i j) →
    (DerivedCategory.Q ⋙ w.derived S E A ⟶ w.complex S E A ⋙ DerivedCategory.Q)
  | _, _, .nil i => Functor.whiskerRight
      (Functor.mapHomologicalComplexIdIso
        (CochainPullback.Modules.{r, u, v} (J := (S i).J) (S i).R) (.up ℤ)).inv
      DerivedCategory.Q
  | _, _, .edge a => (A a).counit
  | _, _, .comp w v => Functor.whiskerRight (counitNat w) (v.derived S E A) ≫
      Functor.whiskerLeft (w.complex S E A) (counitNat v) ≫
        Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
          (Iso.refl (w.ordinary S E A ⋙ v.ordinary S E A)) (.up ℤ)).hom DerivedCategory.Q

private theorem counitNat_app {i j : I} (w : Word E i j)
    (P : CochainComplex (CochainPullback.Modules.{r, u, v} (J := (S i).J) (S i).R) ℤ) :
    (counitNat S E A w).app P = w.counit S E A P := by
  induction w with
  | nil i => rfl
  | edge a => rfl
  | comp w v hw hv =>
      dsimp only [counitNat, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Word.counit]
      rw [hw P, hv ((w.complex S E A).obj P)]

private theorem counit_naturality {i j : I} (w : Word E i j)
    {P Q : CochainComplex (CochainPullback.Modules.{r, u, v} (J := (S i).J) (S i).R) ℤ}
    (p : P ⟶ Q) :
    (w.derived S E A).map (DerivedCategory.Q.map p) ≫ w.counit S E A Q =
      w.counit S E A P ≫ DerivedCategory.Q.map ((w.complex S E A).map p) := by
  simpa only [counitNat_app, Functor.comp_map] using (counitNat S E A w).naturality p

end

-- Inline these canonical instances to avoid repeated dependent instance reduction.
set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency.types true

/-- Finite pastings of ordinary cells, with the actual functor associators and unitors.
Whiskering by words includes whiskering by each specified edge.
Source: DAG proof steps 6--8 following Stacks 0D6D
(blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
inductive Expression : {i j : I} → Word E i j → Word E i j →
    Type (max z e u v (r + 1) d)
  | cell {i j : I} {w v : Word E i j}
      (t : w.ordinary S E A ⟶ v.ordinary S E A) : Expression w v
  | id {i j : I} (w : Word E i j) : Expression w w
  | comp {i j : I} {w v q : Word E i j}
      (f : Expression w v) (g : Expression v q) : Expression w q
  | input {h i j : I} (x : Word E h i) {w v : Word E i j}
      (f : Expression w v) : Expression (.comp x w) (.comp x v)
  | output {i j k : I} {w v : Word E i j} (f : Expression w v)
      (x : Word E j k) : Expression (.comp w x) (.comp v x)
  | assoc {i j k l : I} (w : Word E i j) (v : Word E j k) (q : Word E k l) :
      Expression (.comp (.comp w v) q) (.comp w (.comp v q))
  | assocInv {i j k l : I} (w : Word E i j) (v : Word E j k) (q : Word E k l) :
      Expression (.comp w (.comp v q)) (.comp (.comp w v) q)
  | leftUnit {i j : I} (w : Word E i j) : Expression (.comp (.nil i) w) w
  | leftUnitInv {i j : I} (w : Word E i j) : Expression w (.comp (.nil i) w)
  | rightUnit {i j : I} (w : Word E i j) : Expression (.comp w (.nil j)) w
  | rightUnitInv {i j : I} (w : Word E i j) : Expression w (.comp w (.nil j))

/-- Ordinary evaluation uses the literal composition and whiskering operations.
Source: DAG proof steps 6--8, Stacks 0D6D
(blueprint: lem-trf-ringed-kflat-word-comparison-descent). -/
def Expression.ordinary {i j : I} {w v : Word E i j} :
    Expression S E A w v → (w.ordinary S E A ⟶ v.ordinary S E A)
  | .cell t => t
  | .id _ => 𝟙 _
  | .comp f g => ordinary f ≫ ordinary g
  | .input x f => Functor.whiskerLeft (x.ordinary S E A) (ordinary f)
  | .output f x => Functor.whiskerRight (ordinary f) (x.ordinary S E A)
  | .assoc w v q =>
      (Functor.associator (w.ordinary S E A) (v.ordinary S E A) (q.ordinary S E A)).hom
  | .assocInv w v q =>
      (Functor.associator (w.ordinary S E A) (v.ordinary S E A) (q.ordinary S E A)).inv
  | .leftUnit w => (Functor.leftUnitor (w.ordinary S E A)).hom
  | .leftUnitInv w => (Functor.leftUnitor (w.ordinary S E A)).inv
  | .rightUnit w => (Functor.rightUnitor (w.ordinary S E A)).hom
  | .rightUnitInv w => (Functor.rightUnitor (w.ordinary S E A)).inv

set_option backward.isDefEq.respectTransparency.types true

section

attribute [local instance 40000] siteHasSheafCompose siteHasSheafify siteWEquals siteAbelian

private theorem identity_normalization
    {B D : Type*} [Category B] [Category D] (Q : B ⥤ D)
    {P : B} {X : D} (f g : X ⟶ Q.obj P) (h : f = g) :
    𝟙 X ≫ f = g ≫ Q.map (𝟙 P) :=
  (Category.id_comp f).trans (h.trans
    ((congrArg (fun a ↦ g ≫ a) (Q.map_id P)).trans (Category.comp_id g)).symm)

end

-- Inline these canonical instances to avoid repeated dependent instance reduction.
set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency.types false

section ScalarFormulas

universe wR wS wT
open SheafOfModules CategoryTheory.PrincipalQuotientCompletion
open scoped ChangeOfRings

attribute [local irreducible] scalarTensorSection

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S T : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wR} (CochainPullback.Modules.{r, u, v} (J := J) R)]
  [HasDerivedCategory.{wS} (CochainPullback.Modules.{r, u, v} (J := J) S)]
  [HasDerivedCategory.{wT} (CochainPullback.Modules.{r, u, v} (J := J) T)]

private theorem scalar_section_smul {a : R ⟶ S}
    (F : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a)
    (M : CochainPullback.Modules.{r, u, v} R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    scalarTensorSection F M U s x = s • scalarTensorSection F M U 1 x := by
  unfold scalarTensorSection
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
      (changeOfRingsPresheaf a M)
  let g := (eqToHom (F.obj_eq M).symm).val.app U
  change g (η.app U (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)) =
    s • g (η.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x))
  rw [← g.hom.map_smul, ← (η.app U).hom.map_smul]
  congr 2
  symm
  exact (ModuleCat.ExtendScalars.smul_tmul (f := (a.hom.app U).hom) s 1 x).trans
    (by rw [mul_one])

attribute [local semireducible] scalarTensorSection in
private theorem scalar_adjunction {a : R ⟶ S}
    (F : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a) :
    ∃ adj : F.E ⊣ restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a),
      ∀ M U (x : M.val.obj U),
        (adj.unit.app M).val.app U x = scalarTensorSection F M U 1 x := by
  obtain ⟨_, _, hadj⟩ := sheafRingCoefficientOrdinaryAdjunction a
  obtain ⟨adj, hn⟩ := hadj F.E F.obj_eq F.map_eq
  refine ⟨adj, ?_⟩
  intro M U x
  have h := hn M (F.E.obj M) (eqToHom (F.obj_eq M).symm) U x
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at h
  exact h

private theorem scalar_transpose_tmul {a : R ⟶ S}
    (F : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a)
    (adj : F.E ⊣ restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a))
    (hn : ∀ M U (x : M.val.obj U),
      (adj.unit.app M).val.app U x = scalarTensorSection F M U 1 x)
    (M : CochainPullback.Modules.{r, u, v} R)
    (N : CochainPullback.Modules.{r, u, v} S) (f : F.E.obj M ⟶ N)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    f.val.app U (scalarTensorSection F M U s x) =
      s • (show N.val.obj U from (adj.homEquiv M N f).val.app U x) := by
  rw [scalar_section_smul, ← hn, Adjunction.homEquiv_unit]
  exact (f.val.app U).hom.map_smul s _

private noncomputable def scalar_restriction_unit :
    restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map (𝟙 R)) ≅
      𝟭 (CochainPullback.Modules.{r, u, v} R) :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      ModuleCat.restrictScalarsId'App ((show R ⟶ R from 𝟙 R).hom.app U).hom rfl (M.val.obj U))
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)

end ScalarFormulas

end CategoryTheory.RingedKFlatWord
