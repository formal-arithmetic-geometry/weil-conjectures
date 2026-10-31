/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import WeilConjectures.CategoryTheory.RingedCoefficientCounit.RingedCoefficientCounitPresentations
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedModuleExactIndependent
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeExtensionLeftExact
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import all WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.ConstantModuleScalar.ConstantScalarNormalizedBasis
import WeilConjectures.CategoryTheory.ConstantModuleScalar.ConstantScalarInverseImageCenter
import WeilConjectures.CategoryTheory.ConstantModuleScalar.AlgebraicOpenScalarRestriction

/-!
# Finite-free constant scalars and the constituents of compact support

Source: blueprint main-20261015, sk-thm-purity-transport.proof.md, Steps 1 and 3;
Stacks, Tags 03DI, 03DJ, 03CZ, 07A6, 0D6D and 0D6E
(blueprint: lem-pur-topos-finite-free-compact-constituents).

Presentations retain the geometric Hom bijections, the constant-section normalization,
and the actual sheafified tensor functor. Every comparison below is an adjunction mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v r w i
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedCoefficientCounit
open scoped ChangeOfRings

namespace CategoryTheory.ToposFiniteFreeCompact

set_option linter.checkUnivs false

/-- A fixed small-site presentation. The coefficient universe contains the site;
object and morphism universes are independent.
Source: Stacks 00XA, 00VI (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
structure Site where
  C : Type u
  [category : Category.{v} C]
  J : GrothendieckTopology C
  [small : EssentiallySmall.{r} C]
  [setSheafify : HasSheafify J (Type r)]
  [ringSheafify : HasWeakSheafify J CommRingCat.{r}]
  [groupSheafify : HasSheafify J AddCommGrpCat.{r}]
  [groupLocal : J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  ringCompose : J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := inferInstance
  ringSetCompose : J.HasSheafCompose (forget CommRingCat.{r}) := inferInstance
  groupCompose : J.HasSheafCompose (forget AddCommGrpCat.{r}) := inferInstance

attribute [instance] Site.category Site.small Site.setSheafify Site.ringSheafify
  Site.groupSheafify Site.groupLocal Site.ringCompose Site.ringSetCompose Site.groupCompose

-- Prefer the recorded composition witnesses to reconstructing them on a small model.
attribute [local instance 1000000] Site.ringCompose Site.ringSetCompose Site.groupCompose

variable (A B : CommRingCat.{r}) [Algebra A B]

/-- The actual constant ring homomorphism.
Source: Stacks 03CZ (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def coefficientMap (T : Site.{u, v, r}) : constantRing T.J A ⟶ constantRing T.J B :=
  (constantSheaf T.J CommRingCat.{r}).map (CommRingCat.ofHom (algebraMap A B))

/-- Constant-coefficient module sheaves in the recorded ringed-site category.
Source: Stacks 03D7 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
abbrev Mod (T : Site.{u, v, r}) (R : CommRingCat.{r}) := modules.{u, v, r} (constantRing T.J R)

/-- Ordinary coefficient restriction, retaining its actual section modules.
Source: Stacks 03CZ (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
abbrev res (T : Site.{u, v, r}) : Mod T B ⥤ Mod T A :=
  restriction.{u, v, r} (coefficientMap A B T)

private theorem exact_derived_counit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (E : C ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hε : F.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso C (.up ℤ))) :
    IsIso ε := by
  let := hε
  apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (W := HomologicalComplex.quasiIso C (.up ℤ)) F ε
  intro K L f hf
  have : QuasiIso f := hf
  have : QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f) := inferInstance
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance

/-- Finite-free extension is exact and its universal derived counit is invertible
on every unbounded complex.
Source: blueprint transport Steps 1 and 3; Stacks 06YY
(blueprint: lem-pur-topos-finite-free-compact-constituents).
Proof: use a finite basis and its coordinate maps to identify restricted extension
with a finite direct sum. The two inverse formulas hold locally on pure tensors,
then sheafify. Restriction is exact and detects zero sheaves. Thus extension is exact,
and its universal left-derived counit is the exact-functor localization isomorphism.
The empty basis gives the zero functor; no boundedness is used. -/
theorem scalar_exact (T : Site.{u, v, r})
    [HasDerivedCategory.{w} (Mod T A)] [HasDerivedCategory.{w} (Mod T B)]
    [Module.Finite A B] [Module.Free A B]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w} (coefficientMap A B T)) :
    PreservesFiniteLimits D.E ∧ PreservesFiniteColimits D.E ∧ IsIso D.ε := by
  have hlim : PreservesFiniteLimits D.E :=
    constantFiniteFree_extensionLeftExact T.J A B D.E D.obj_eq D.map_eq
  obtain ⟨_, _, ha⟩ :=
    SheafOfModules.sheafRingCoefficientOrdinaryAdjunction (coefficientMap A B T)
  obtain ⟨a, _⟩ := ha D.E D.obj_eq D.map_eq
  have hcolim : PreservesFiniteColimits D.E := by
    let : PreservesColimitsOfSize.{0, 0} D.E := a.leftAdjoint_preservesColimits
    infer_instance
  let := hlim
  let := hcolim
  exact ⟨hlim, hcolim, exact_derived_counit_isIso D.E D.T D.ε D.universal⟩

/-- A normalized presentation of the scalar adjunction on a fixed site. Its extension
is the recorded sheafified tensor construction, and the Hom formula fixes the ordinary
adjunction on pure tensors. The two derived categories are ordinary unbounded localizations.
Source: Stacks 03CZ, 06YY, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
structure ScalarSite extends Site.{u, v, r} where
  [derivedA : HasDerivedCategory.{w} (Mod toSite A)]
  [derivedB : HasDerivedCategory.{w} (Mod toSite B)]
  [injectivesA : Abelian.HasKInjectiveResolutions (Mod toSite A)]
  [injectivesB : Abelian.HasKInjectiveResolutions (Mod toSite B)]
  model : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
    (coefficientMap A B toSite)
  resLimits : PreservesFiniteLimits (res A B toSite)
  resColimits : PreservesFiniteColimits (res A B toSite)
  adj : model.E ⊣ res A B toSite
  adjFormula : ∀ (M : Mod toSite A) (N : Mod toSite B)
    (f : SheafOfModules.changeOfRings.{v, u, r} (coefficientMap A B toSite) M ⟶ N)
    (V : Cᵒᵖ) (x : M.val.obj V),
    (adj.homEquiv M N (eqToHom (model.obj_eq M) ≫ f)).val.app V x =
      f.val.app V
        ((toSheafify J
          (SheafOfModules.changeOfRingsPresheaf.{v, u, r}
            (coefficientMap A B toSite) M).presheaf).app V
            ((1 : (constantRing J B).obj.obj V) ⊗ₜ[(constantRing J A).obj.obj V,
              ((coefficientMap A B toSite).hom.app V).hom] x))

attribute [instance] ScalarSite.derivedA ScalarSite.derivedB
  ScalarSite.injectivesA ScalarSite.injectivesB ScalarSite.resLimits ScalarSite.resColimits

variable {A B}

/-- Exactness of the specified tensor extension.
Source: finite-free coordinates (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
instance scalarLimits [Module.Finite A B] [Module.Free A B]
    (T : ScalarSite.{u, v, r, w} A B) : PreservesFiniteLimits T.model.E :=
  (scalar_exact A B T.toSite T.model).1

/-- Exactness of the specified tensor extension.
Source: finite-free coordinates (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
instance scalarColimits [Module.Finite A B] [Module.Free A B]
    (T : ScalarSite.{u, v, r, w} A B) : PreservesFiniteColimits T.model.E :=
  (scalar_exact A B T.toSite T.model).2.1

/-- Exact restriction on the ordinary unbounded derived categories.
Source: Stacks 03CZ, 07A6 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def U (T : ScalarSite.{u, v, r, w} A B) := (res A B T.toSite).mapDerivedCategory

/-- Derived extension, in its exact termwise model.
Source: Stacks 06YY (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def S [Module.Finite A B] [Module.Free A B] (T : ScalarSite.{u, v, r, w} A B) :=
  T.model.E.mapDerivedCategory

/-- The original scalar adjunction localized termwise, retaining its unit normalization.
Source: Stacks 07A6 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def scalarAdj [Module.Finite A B] [Module.Free A B] (T : ScalarSite.{u, v, r, w} A B) :
    S T ⊣ U T := CategoryTheory.Adjunction.onDerivedCategory T.adj

/-- One geometric morphism and its two constant-coefficient module lifts. Constants
are normalized on every scalar summand, and the ordinary Hom equations retain the
original geometric adjunction. The restriction square is the identity on underlying
inverse images. These are presentations of the specified functors, not arbitrary maps.
Source: Stacks 00YV, 03D7, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
structure Geometric (T W : ScalarSite.{u, v, r, w} A B) where
  inverse : Sheaf W.J (Type r) ⥤ Sheaf T.J (Type r)
  direct : Sheaf T.J (Type r) ⥤ Sheaf W.J (Type r)
  geom : inverse ⊣ direct
  leftExact : PreservesFiniteLimits inverse
  liftA : SheafOfModules.AlgebraicInverseImage.{r, u, v, u, v} inverse
    (constantRing W.J A) (constantRing T.J A)
  liftB : SheafOfModules.AlgebraicInverseImage.{r, u, v, u, v} inverse
    (constantRing W.J B) (constantRing T.J B)
  point : inverse.obj ((constantSheaf W.J (Type r)).obj PUnit.{r+1}) ≅
    (constantSheaf T.J (Type r)).obj PUnit.{r+1}
  constantsA : ∀ a : A,
    inverse.map ((constantSheaf W.J (Type r)).map
      (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ a)) ≫
        (constantCommuteCompose W.J (forget CommRingCat.{r})).inv.app A) ≫
        liftA.ringUnderlying.hom =
      point.hom ≫ (constantSheaf T.J (Type r)).map
        (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ a)) ≫
        (constantCommuteCompose T.J (forget CommRingCat.{r})).inv.app A
  constantsB : ∀ b : B,
    inverse.map ((constantSheaf W.J (Type r)).map
      (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ b)) ≫
        (constantCommuteCompose W.J (forget CommRingCat.{r})).inv.app B) ≫
        liftB.ringUnderlying.hom =
      point.hom ≫ (constantSheaf T.J (Type r)).map
        (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ b)) ≫
        (constantCommuteCompose T.J (forget CommRingCat.{r})).inv.app B
  [addA : liftA.modules.Additive]
  [addB : liftB.modules.Additive]
  [limA : PreservesFiniteLimits liftA.modules]
  [colimA : PreservesFiniteColimits liftA.modules]
  [limB : PreservesFiniteLimits liftB.modules]
  [colimB : PreservesFiniteColimits liftB.modules]
  pushA : Mod T.toSite A ⥤ Mod W.toSite A
  pushB : Mod T.toSite B ⥤ Mod W.toSite B
  [pushAddA : pushA.Additive]
  [pushAddB : pushB.Additive]
  pushUnderlyingA : pushA ⋙ underlying.{u, v, r} (constantRing W.J A) ≅
    underlying.{u, v, r} (constantRing T.J A) ⋙ direct
  pushUnderlyingB : pushB ⋙ underlying.{u, v, r} (constantRing W.J B) ≅
    underlying.{u, v, r} (constantRing T.J B) ⋙ direct
  adjA : liftA.modules ⊣ pushA
  adjB : liftB.modules ⊣ pushB
  homA : ∀ M N (f : liftA.modules.obj M ⟶ N),
    (underlying.{u, v, r} (constantRing W.J A)).map (adjA.homEquiv M N f) ≫
        pushUnderlyingA.hom.app N =
      geom.homEquiv _ _ (liftA.moduleUnderlying.inv.app M ≫
        (underlying.{u, v, r} (constantRing T.J A)).map f)
  homB : ∀ M N (f : liftB.modules.obj M ⟶ N),
    (underlying.{u, v, r} (constantRing W.J B)).map (adjB.homEquiv M N f) ≫
        pushUnderlyingB.hom.app N =
      geom.homEquiv _ _ (liftB.moduleUnderlying.inv.app M ≫
        (underlying.{u, v, r} (constantRing T.J B)).map f)
  restriction : res A B W.toSite ⋙ liftA.modules ≅ liftB.modules ⋙ res A B T.toSite
  restrictionFormula : ∀ M,
    (underlying.{u, v, r} (constantRing T.J A)).map (restriction.hom.app M) =
      liftA.moduleUnderlying.hom.app ((res A B W.toSite).obj M) ≫
        liftB.moduleUnderlying.inv.app M

attribute [instance] Geometric.addA Geometric.addB Geometric.limA Geometric.colimA
  Geometric.limB Geometric.colimB Geometric.pushAddA Geometric.pushAddB

/-- Actual derived inverse image with A coefficients.
Source: Stacks 07A6 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def LA {T W : ScalarSite.{u, v, r, w} A B} (f : Geometric T W) :=
  f.liftA.modules.mapDerivedCategory

/-- Actual derived inverse image with B coefficients.
Source: Stacks 07A6 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def LB {T W : ScalarSite.{u, v, r, w} A B} (f : Geometric T W) :=
  f.liftB.modules.mapDerivedCategory

/-- Actual unbounded derived direct image with A coefficients.
Source: Stacks 07A6 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def RA {T W : ScalarSite.{u, v, r, w} A B} (f : Geometric T W) :=
  f.pushA.rightDerivedFunctor

/-- Actual unbounded derived direct image with B coefficients.
Source: Stacks 07A6 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def RB {T W : ScalarSite.{u, v, r, w} A B} (f : Geometric T W) :=
  f.pushB.rightDerivedFunctor

/-- The exact inverse-image/derived-direct-image adjunction.
Source: Stacks 07A6 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def adjA {T W : ScalarSite.{u, v, r, w} A B} (f : Geometric T W) : LA f ⊣ RA f :=
  f.adjA.mapDerivedCategoryRightDerivedAdjunction

/-- The exact inverse-image/derived-direct-image adjunction.
Source: Stacks 07A6 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def adjB {T W : ScalarSite.{u, v, r, w} A B} (f : Geometric T W) : LB f ⊣ RB f :=
  f.adjB.mapDerivedCategoryRightDerivedAdjunction

/-- Exact localization of the identity on underlying pulled-back module sheaves.
Source: Stacks 03D7 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def tau {T W : ScalarSite.{u, v, r, w} A B} (f : Geometric T W) :
    U W ⋙ LA f ≅ LB f ⋙ U T :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso f.restriction ≪≫ Functor.mapDerivedCategoryCompIso _ _

variable [Module.Finite A B] [Module.Free A B]

/-- The tensor comparison in the reverse direction, defined by its scalar adjunct.
Source: Stacks 03CZ, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def tensorPullbackInv {T W : ScalarSite.{u, v, r, w} A B} (f : Geometric T W) :
    LA f ⋙ S T ⟶ S W ⋙ LB f :=
  ((mateEquiv (scalarAdj W) (scalarAdj T)).symm
    (TwoSquare.mk _ _ _ _ (tau f).hom)).natTrans

private theorem constant_map_unit (T : Site.{u, v, r}) {P Q : Type r}
    (f : P ⟶ Q) (V : T.Cᵒᵖ) (x : P) :
    ((constantSheaf T.J (Type r)).map f).hom.app V
      ((toSheafify T.J ((Functor.const T.Cᵒᵖ).obj P)).app V x) =
    (toSheafify T.J ((Functor.const T.Cᵒᵖ).obj Q)).app V (f x) :=
  (congrArg (fun t ↦ t.app V x)
    (toSheafify_naturality T.J ((Functor.const T.Cᵒᵖ).map f))).symm

section
omit [Module.Finite A B] [Module.Free A B]

private theorem inverse_constant_hom_ext {T W : ScalarSite.{u, v, r, w} A B}
    (f : Geometric T W) {P : Type r} {H : Sheaf T.J (Type r)}
    {α β : f.inverse.obj ((constantSheaf W.J (Type r)).obj P) ⟶ H}
    (h : ∀ a : P,
      f.inverse.map ((constantSheaf W.J (Type r)).map
        (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ a))) ≫ α =
      f.inverse.map ((constantSheaf W.J (Type r)).map
        (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ a))) ≫ β) : α = β := by
  apply (f.geom.homEquiv _ _).injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (f.direct.obj H).property
  ext V a
  have ha := congrArg (f.geom.homEquiv _ _) (h a)
  rw [f.geom.homEquiv_naturality_left, f.geom.homEquiv_naturality_left] at ha
  have hx := congrArg (fun t ↦ t.hom.app V
    ((toSheafify W.J ((Functor.const W.Cᵒᵖ).obj PUnit.{r+1})).app V PUnit.unit)) ha
  change ((f.geom.homEquiv _ _) α).hom.app V
      ((toSheafify W.J ((Functor.const W.Cᵒᵖ).obj P)).app V a) =
    ((f.geom.homEquiv _ _) β).hom.app V
      ((toSheafify W.J ((Functor.const W.Cᵒᵖ).obj P)).app V a)
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, constant_map_unit W.toSite, TypeCat.ofHom_apply] using hx

set_option maxHeartbeats 1600000 in
-- Comparing the dependent module and sheaf presentations needs extra elaboration time.
private theorem inverse_coefficient_square {T W : ScalarSite.{u, v, r, w} A B}
    (f : Geometric T W) :
    f.inverse.map ((sheafCompose W.J (forget CommRingCat.{r})).map
      (coefficientMap A B W.toSite)) ≫ f.liftB.ringUnderlying.hom =
    f.liftA.ringUnderlying.hom ≫
      (sheafCompose T.J (forget CommRingCat.{r})).map
        (coefficientMap A B T.toSite) := by
  let a : A ⟶ B := CommRingCat.ofHom (algebraMap A B)
  have hκ (V : Site.{u, v, r}) :=
    (constantCommuteCompose V.J (forget CommRingCat.{r})).inv.naturality a
  apply (cancel_epi (f.inverse.map
    ((constantCommuteCompose W.J (forget CommRingCat.{r})).inv.app A))).1
  apply inverse_constant_hom_ext f
  intro x
  have hx : (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ x)) ≫
      (forget CommRingCat.{r}).map a =
      TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ algebraMap A B x) := rfl
  have hc (V : Site.{u, v, r}) :
      (constantSheaf V.J (Type r)).map
          (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ x)) ≫
        (constantCommuteCompose V.J (forget CommRingCat.{r})).inv.app A ≫
          (sheafCompose V.J (forget CommRingCat.{r})).map (coefficientMap A B V) =
      (constantSheaf V.J (Type r)).map
          (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ algebraMap A B x)) ≫
        (constantCommuteCompose V.J (forget CommRingCat.{r})).inv.app B := by
    change _ ≫ _ ≫ ((constantSheaf V.J CommRingCat) ⋙
      sheafCompose V.J (forget CommRingCat.{r})).map a = _
    erw [← hκ V, ← Category.assoc]
    dsimp only [Functor.comp_map]
    rw [← Functor.map_comp, hx]
  calc
    _ = f.inverse.map ((constantSheaf W.J (Type r)).map
          (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ x)) ≫
        (constantCommuteCompose W.J (forget CommRingCat.{r})).inv.app A ≫
          (sheafCompose W.J (forget CommRingCat.{r})).map
            (coefficientMap A B W.toSite)) ≫ f.liftB.ringUnderlying.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = f.inverse.map ((constantSheaf W.J (Type r)).map
          (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ algebraMap A B x)) ≫
        (constantCommuteCompose W.J (forget CommRingCat.{r})).inv.app B) ≫
          f.liftB.ringUnderlying.hom := by rw [hc W.toSite]
    _ = f.point.hom ≫ (constantSheaf T.J (Type r)).map
          (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ algebraMap A B x)) ≫
        (constantCommuteCompose T.J (forget CommRingCat.{r})).inv.app B :=
      f.constantsB _
    _ = f.point.hom ≫ (constantSheaf T.J (Type r)).map
          (TypeCat.ofHom (fun _ : PUnit.{r+1} ↦ x)) ≫
        (constantCommuteCompose T.J (forget CommRingCat.{r})).inv.app A ≫
          (sheafCompose T.J (forget CommRingCat.{r})).map
            (coefficientMap A B T.toSite) := by rw [hc T.toSite]
    _ = _ := by
      rw [← reassoc_of% f.constantsA x]
      simp only [Functor.map_comp, Category.assoc]

private theorem ordinary_tensor_mate_isIso {T W : ScalarSite.{u, v, r, w} A B}
    (f : Geometric T W) :
    IsIso (((mateEquiv W.adj T.adj).symm
      (TwoSquare.mk _ _ _ _ f.restriction.hom)).natTrans) := by
  let := f.leftExact
  obtain ⟨e, he⟩ := SheafOfModules.ScalarIndependent.exists_scalarInverseImageIndependent
    f.inverse f.direct f.geom f.liftA f.liftB
    (coefficientMap A B W.toSite) (coefficientMap A B T.toSite)
    (inverse_coefficient_square f) W.model.E T.model.E W.adj T.adj
  have hu (M : Mod W.toSite A) :
      f.liftA.modules.map (W.adj.unit.app M) ≫ f.restriction.hom.app (W.model.E.obj M) =
        T.adj.unit.app (f.liftA.modules.obj M) ≫ (res A B T.toSite).map (e.inv.app M) := by
    apply (underlying (constantRing T.J A)).map_injective
    apply (cancel_mono ((underlying (constantRing T.J B)).map (e.hom.app M))).1
    simp only [Functor.map_comp, Category.assoc, f.restrictionFormula]
    change (underlying (constantRing T.J A)).map
        (f.liftA.modules.map (W.adj.unit.app M)) ≫
          f.liftA.moduleUnderlying.hom.app ((res A B W.toSite).obj (W.model.E.obj M)) ≫
            f.liftB.moduleUnderlying.inv.app (W.model.E.obj M) ≫
              (underlying (constantRing T.J B)).map (e.hom.app M) =
      (underlying (constantRing T.J A)).map (T.adj.unit.app (f.liftA.modules.obj M)) ≫
        (underlying (constantRing T.J B)).map (e.inv.app M) ≫
          (underlying (constantRing T.J B)).map (e.hom.app M)
    rw [← Functor.map_comp, e.inv_hom_id_app]
    erw [Functor.map_id, Category.comp_id]
    have hn := f.liftA.moduleUnderlying.hom.naturality (W.adj.unit.app M)
    dsimp only [Functor.comp_map] at hn
    erw [reassoc_of% hn, he M, Iso.hom_inv_id_app_assoc]
  have hm : (((mateEquiv W.adj T.adj).symm
      (TwoSquare.mk _ _ _ _ f.restriction.hom)).natTrans) = e.inv := by
    apply NatTrans.ext
    funext M
    apply (T.adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm W.adj T.adj
      (TwoSquare.mk _ _ _ _ f.restriction.hom) M).symm.trans (hu M)
  rw [hm]
  infer_instance

end

/-- Tensor and geometric inverse image commute, with the canonical scalar adjunct.
Source: Stacks 03EL, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents).
Proof: the ordinary tensor balancing map and its inverse send each local pure tensor
of a pulled-back section to the same tensor. Sheafification gives inverse natural
maps. Their scalar adjunct is the identity on underlying inverse images, hence is
tau. Exact localization and its Hom bijection give precisely tensorPullbackInv. -/
theorem tensorPullbackInv_isIso {T W : ScalarSite.{u, v, r, w} A B}
    (f : Geometric T W) : IsIso (tensorPullbackInv f) := by
  let := ordinary_tensor_mate_isIso f
  exact (exact_localization_inverse_mate W.adj T.adj f.restriction).1

attribute [instance] tensorPullbackInv_isIso

/-- The specified tensor/inverse-image isomorphism, fixed by the scalar unit.
Source: Stacks 03EL, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def lambda {T W : ScalarSite.{u, v, r, w} A B} (f : Geometric T W) :
    S W ⋙ LB f ≅ LA f ⋙ S T :=
  letI := tensorPullbackInv_isIso f
  (asIso (tensorPullbackInv f)).symm

/-- The direct-image comparison, as the geometric mate of lambda.
Source: Stacks 07A6 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def chi {T W : ScalarSite.{u, v, r, w} A B} (f : Geometric T W) :
    RA f ⋙ S W ⟶ S T ⋙ RB f :=
  (mateEquiv (adjA f) (adjB f) (TwoSquare.mk _ _ _ _ (lambda f).hom)).natTrans

/-- The canonical restriction/direct-image comparison, obtained from the underlying
inverse-image identity by the geometric Hom bijections.
Source: Stacks 03D7, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def restrictionPushforward {T W : ScalarSite.{u, v, r, w} A B}
    (f : Geometric T W) : RB f ⋙ U W ⟶ U T ⋙ RA f :=
  (mateEquiv (adjB f) (adjA f) (TwoSquare.mk _ _ _ _ (tau f).hom)).natTrans

/-- Restriction commutes with the derived direct image by its canonical mate.
Source: Stacks 03D7, 07A6, 0D6E
(blueprint: lem-pur-topos-finite-free-compact-constituents).
Proof: on underlying section modules restriction and direct image are identical.
Their ordinary adjunction transposes give the displayed mate. Resolve by K-injectives
and use the two universal right-derived factorizations. The resulting comparison is
invertible and its counit square identifies it with restrictionPushforward. -/
theorem restrictionPushforward_isIso {T W : ScalarSite.{u, v, r, w} A B}
    (f : Geometric T W) : IsIso (restrictionPushforward f) := by
  let := tensorPullbackInv_isIso f
  have h : IsIso (conjugateEquiv ((scalarAdj W).comp (adjB f))
      ((adjA f).comp (scalarAdj T)) (tensorPullbackInv f)) := inferInstance
  rw [← iterated_mateEquiv_conjugateEquiv (scalarAdj W) (scalarAdj T)
    (adjA f) (adjB f)] at h
  simpa only [restrictionPushforward, tensorPullbackInv, Equiv.apply_symm_apply] using h

/-- An open subtopos is the slice at a subterminal sheaf. Its extension is the exact
fully faithful left adjoint to its actual module inverse image; this determines the
extension together with its unit up to the unique adjunction-preserving isomorphism.
Source: Stacks 03DI, 03DJ (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
structure Open (V T : ScalarSite.{u, v, r, w} A B) where
  geometric : Geometric V T
  subterminal : Sheaf T.J (Type r)
  isSubterminal : IsSubterminal subterminal
  slice : Sheaf V.J (Type r) ≌ Over subterminal
  inverseIso : geometric.inverse ⋙ slice.functor ≅ Over.star subterminal
  extensionA : Mod V.toSite A ⥤ Mod T.toSite A
  extensionB : Mod V.toSite B ⥤ Mod T.toSite B
  [addA : extensionA.Additive]
  [addB : extensionB.Additive]
  [limA : PreservesFiniteLimits extensionA]
  [limB : PreservesFiniteLimits extensionB]
  [colimA : PreservesFiniteColimits extensionA]
  [colimB : PreservesFiniteColimits extensionB]
  adjA : extensionA ⊣ geometric.liftA.modules
  adjB : extensionB ⊣ geometric.liftB.modules
  [unitA : IsIso adjA.unit]
  [unitB : IsIso adjB.unit]

attribute [instance] Open.addA Open.addB Open.limA Open.limB Open.colimA Open.colimB
  Open.unitA Open.unitB

/-- Actual exact extension by zero, localized termwise with A coefficients.
Source: Stacks 03DI, 03DJ (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def IA {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :=
  j.extensionA.mapDerivedCategory

/-- Actual exact extension by zero, localized termwise with B coefficients.
Source: Stacks 03DI, 03DJ (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def IB {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :=
  j.extensionB.mapDerivedCategory

/-- Localize the original open adjunction, retaining its unit.
Source: Stacks 03DI, 07A6 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def openAdjA {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :
    IA j ⊣ LA j.geometric :=
  CategoryTheory.Adjunction.onDerivedCategory j.adjA

/-- Localize the original open adjunction, retaining its unit.
Source: Stacks 03DI, 07A6 (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def openAdjB {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :
    IB j ⊣ LB j.geometric :=
  CategoryTheory.Adjunction.onDerivedCategory j.adjB

/-- The inverse balancing map, specified by the open Hom bijection.
Source: Stacks 03DI, 0E8I (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def betaInv {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :
    S V ⋙ IB j ⟶ IA j ⋙ S T :=
  ((mateEquiv (openAdjA j) (openAdjB j)).symm
    (TwoSquare.mk _ _ _ _ (lambda j.geometric).inv)).natTrans

/-- The balancing mate is invertible, on unbounded inputs.
Source: Stacks 03DI, 03DJ, 0E8I
(blueprint: lem-pur-topos-finite-free-compact-constituents).
Proof: on the localized-site sum presheaf both maps send a summand tensor to the same
summand tensor; on the complement the module is zero. Tensor balancing and sheafification
prove the inverse identities. All ordinary functors are exact, so termwise localization
preserves them. The open Hom formula identifies the inverse with betaInv. -/
theorem betaInv_isIso {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :
    IsIso (betaInv j) := by
  have h := iterated_mateEquiv_conjugateEquiv_symm (openAdjA j) (openAdjB j)
    (scalarAdj V) (scalarAdj T) (TwoSquare.mk _ _ _ _ (tau j.geometric).hom)
  have hi : IsIso ((conjugateEquiv ((openAdjA j).comp (scalarAdj T))
      ((scalarAdj V).comp (openAdjB j))).symm (tau j.geometric).hom) := inferInstance
  dsimp only [betaInv, lambda, Iso.symm_inv, asIso_hom, tensorPullbackInv]
  rw [h]
  exact hi

/-- The canonical balancing isomorphism for extension by zero.
Source: Stacks 03DI, 0E8I (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def beta {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :
    IA j ⋙ S T ≅ S V ⋙ IB j :=
  letI := betaInv_isIso j
  (asIso (betaInv j)).symm

/-- Restriction/open extension comparison, fixed by the open adjunction and tau.
Source: Stacks 03DI, 03CZ
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def restrictionOpen {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :
    U V ⋙ IA j ⟶ IB j ⋙ U T :=
  ((mateEquiv (openAdjB j) (openAdjA j)).symm
    (TwoSquare.mk _ _ _ _ (tau j.geometric).inv)).natTrans

/-- The constant scalar section, obtained by the associated-sheaf unit.
Source: Stacks 03CZ (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def constantSection (T : Site.{u, v, r}) (R : CommRingCat.{r})
    (V : T.Cᵒᵖ) (a : R) : (constantRing T.J R).obj.obj V :=
  (toSheafify T.J ((Functor.const T.Cᵒᵖ).obj R)).app V a

/-- The actual sheafified pure tensor in the specified tensor-extension model.
Source: Stacks 03CY, 03CZ
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def tensorSection (T : ScalarSite.{u, v, r, w} A B) (M : Mod T.toSite A)
    (V : T.Cᵒᵖ) (b : B) (x : M.val.obj V) : (T.model.E.obj M).val.obj V :=
  (eqToHom (T.model.obj_eq M).symm).val.app V
    ((toSheafify T.J
      (SheafOfModules.changeOfRingsPresheaf.{v, u, r}
        (coefficientMap A B T.toSite) M).presheaf).app V
          (constantSection T.toSite B V b ⊗ₜ[(constantRing T.J A).obj.obj V,
            ((coefficientMap A B T.toSite).hom.app V).hom] x))

/-- A coordinate inclusion family in the actual derived scalar extension.
Source: blueprint transport finite-basis calculation
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
abbrev Inclusions (T : ScalarSite.{u, v, r, w} A B) (I : Type i) :=
  ∀ M : DerivedCategory (Mod T.toSite A), I → (M ⟶ (U T).obj ((S T).obj M))

/-- Finite-basis coordinates, with all inclusions fixed on every unbounded complex
by the actual pure-tensor formula. The two finite-matrix identities assert precisely
that these are the inclusions of a biproduct; no nonempty-index condition is imposed.
Source: blueprint transport Steps 1 and 3; Stacks 03CY, 03CZ
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def BasisCoordinates (T : ScalarSite.{u, v, r, w} A B)
    {I : Type i} [Fintype I] (b : Module.Basis I A B) (ι : Inclusions T I) : Prop :=
  (∀ (M N : DerivedCategory (Mod T.toSite A)) (f : M ⟶ N) (a : I),
    f ≫ ι N a = ι M a ≫ (U T).map ((S T).map f)) ∧
  (∀ M : DerivedCategory (Mod T.toSite A),
    ∃ q : I → ((U T).obj ((S T).obj M) ⟶ M),
      (∀ a c : I, ι M a ≫ q c = @ite _ (a = c) (Classical.propDecidable _) (𝟙 M) 0) ∧
      ∑ a : I, q a ≫ ι M a = 𝟙 _) ∧
  ∀ (K : CochainComplex (Mod T.toSite A) ℤ) (a : I),
    ∃ k : K ⟶ ((res A B T.toSite).mapHomologicalComplex (.up ℤ)).obj
      ((T.model.E.mapHomologicalComplex (.up ℤ)).obj K),
      (∀ (n : ℤ) (V : T.Cᵒᵖ) (x : (K.X n).val.obj V),
        (k.f n).val.app V x = tensorSection T (K.X n) V (b a) x) ∧
      ι (DerivedCategory.Q.obj K) a ≫
          (U T).map (T.model.E.mapDerivedCategoryFactors.hom.app K) ≫
          (res A B T.toSite).mapDerivedCategoryFactors.hom.app
            ((T.model.E.mapHomologicalComplex (.up ℤ)).obj K) = DerivedCategory.Q.map k

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem matrix_isIso
    {C : Type*} [Category C] [Preadditive C] {I : Type*} [Fintype I] [DecidableEq I]
    {M X Y : C} (ι : I → (M ⟶ X)) (q : I → (X ⟶ M))
    (κ : I → (M ⟶ Y)) (r : I → (Y ⟶ M))
    (hX : ∑ a, q a ≫ ι a = 𝟙 X)
    (hκ : ∀ a c, κ a ≫ r c = if a = c then 𝟙 M else 0)
    (hY : ∑ a, r a ≫ κ a = 𝟙 Y)
    (f : X ⟶ Y) (hf : ∀ a, ι a ≫ f = κ a) : IsIso f := by
  classical
  let g : Y ⟶ X := ∑ a, r a ≫ ι a
  have hcol (a : I) : κ a ≫ g = ι a := by
    simp only [g, Preadditive.comp_sum, ← Category.assoc, hκ]
    calc
      ∑ c, (if a = c then 𝟙 M else 0) ≫ ι c =
          ∑ c, if a = c then ι c else 0 := by
        apply Finset.sum_congr rfl
        intro c _
        split_ifs <;> simp
      _ = ι a := by simp
  have hfg : f ≫ g = 𝟙 X := by
    calc
      f ≫ g = (∑ a, q a ≫ ι a) ≫ f ≫ g := by rw [hX]; simp
      _ = ∑ a, q a ≫ ι a := by
        simp only [Preadditive.sum_comp, Category.assoc]
        apply Finset.sum_congr rfl
        intro a _
        rw [← Category.assoc (ι a), hf, hcol]
      _ = 𝟙 X := hX
  have hgf : g ≫ f = 𝟙 Y := by
    simpa only [g, Preadditive.sum_comp, Category.assoc, hf] using hY
  exact ⟨⟨g, hfg, hgf⟩⟩

private theorem matrix_map_isIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {I : Type*} [Fintype I] [DecidableEq I] (F : C ⥤ D) [F.Additive] {M N : C} {P : D}
    (ι : I → (M ⟶ N)) (q : I → (N ⟶ M))
    (κ : I → (F.obj M ⟶ P)) (r : I → (P ⟶ F.obj M))
    (hι : ∀ a c, ι a ≫ q c = if a = c then 𝟙 M else 0)
    (hN : ∑ a, q a ≫ ι a = 𝟙 N)
    (hP : ∑ a, r a ≫ κ a = 𝟙 P)
    (f : P ⟶ F.obj N) (hf : ∀ a, κ a ≫ f = F.map (ι a)) : IsIso f := by
  classical
  apply matrix_isIso κ r (fun a ↦ F.map (ι a)) (fun a ↦ F.map (q a)) hP
    ?_ ?_ f hf
  · intro a c
    rw [← F.map_comp, hι]
    split_ifs <;> simp
  · simpa only [F.map_sum, F.map_comp, F.map_id] using congrArg F.map hN

set_option linter.unusedSectionVars false in
/-- The restriction/open comparison is the identity on defining section sums.
Source: Stacks 03DI, 03DJ, 03CZ
(blueprint: lem-pur-topos-finite-free-compact-constituents).
Proof: the ordinary sum-presheaf identity is invertible on the open and zero on its
complement. Its adjoint is the restriction/inverse-image identity tau. Exact
localization retains this adjoint equation and both inverse identities. -/
theorem restrictionOpen_isIso {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :
    IsIso (restrictionOpen j) := by
  let : IsIso ((mateEquiv j.adjB j.adjA).symm
      (TwoSquare.mk _ _ _ _ j.geometric.restriction.symm.hom)).natTrans := by
    dsimp only [Mod, res, coefficientMap, Iso.symm]
    exact ConstantModuleScalar.open_restriction_mate_isIso T.J V.J A B
      j.geometric.inverse j.geometric.liftA j.geometric.liftB
      j.subterminal j.isSubterminal j.slice j.inverseIso
      j.extensionA j.extensionB j.adjA j.adjB
      j.geometric.restriction j.geometric.restrictionFormula
  have h := (exact_localization_inverse_mate j.adjB j.adjA
    j.geometric.restriction.symm).1
  have hs : (Functor.mapDerivedCategorySquareIso j.geometric.restriction.symm).hom =
      (tau j.geometric).inv := by
    exact Functor.square_symm_hom j.geometric.restriction
  rw [hs] at h
  convert h using 1 <;> rfl

attribute [instance] restrictionOpen_isIso

/-- The specified compact-support functor with A coefficients.
Source: blueprint transport Step 1
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def FA {X T Y : ScalarSite.{u, v, r, w} A B}
    (j : Open X T) (p : Geometric T Y) :
    DerivedCategory (Mod X.toSite A) ⥤ DerivedCategory (Mod Y.toSite A) := IA j ⋙ RA p

/-- The specified compact-support functor with B coefficients.
Source: blueprint transport Step 1
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def FB {X T Y : ScalarSite.{u, v, r, w} A B}
    (j : Open X T) (p : Geometric T Y) :
    DerivedCategory (Mod X.toSite B) ⥤ DerivedCategory (Mod Y.toSite B) := IB j ⋙ RB p

/-- The prescribed direct-image mate followed by open balancing.
Source: blueprint transport Steps 1 and 3
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def compactComparison {X T Y : ScalarSite.{u, v, r, w} A B}
    (j : Open X T) (p : Geometric T Y) : FA j p ⋙ S Y ⟶ S X ⋙ FB j p :=
  (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (IA j) (chi p) ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (beta j).hom (RB p) ≫
      (Functor.associator _ _ _).hom

/-- The canonical sectionwise restriction comparison, with its prescribed order.
Source: Stacks 03DI, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def rho {X T Y : ScalarSite.{u, v, r, w} A B}
    (j : Open X T) (p : Geometric T Y) : U X ⋙ FA j p ≅ FB j p ⋙ U Y :=
  letI := restrictionOpen_isIso j
  letI := restrictionPushforward_isIso p
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (restrictionOpen j)) (RA p) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (IB j) (asIso (restrictionPushforward p)).symm ≪≫
    (Functor.associator _ _ _).symm

private theorem exact_reflects_derived
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F.ReflectsIsomorphisms] :
    F.mapDerivedCategory.ReflectsIsomorphisms := by
  constructor
  intro X Y f hf
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (F.map ((DerivedCategory.homologyFunctor C n).map f)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ F

private theorem scalar_mate_transpose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {S₁ : C ⥤ E} {U₁ : E ⥤ C} {S₂ : D ⥤ F} {U₂ : F ⥤ D}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (s : S₁ ⊣ U₁) (t : S₂ ⊣ U₂)
    (τ : U₁ ⋙ L₁ ≅ L₂ ⋙ U₂) (l : S₁ ⋙ L₂ ≅ L₁ ⋙ S₂)
    (c : R₁ ⋙ S₁ ⟶ S₂ ⋙ R₂) (d : R₂ ⋙ U₁ ⟶ U₂ ⋙ R₁)
    (M : D)
    (hu : L₁.map (s.unit.app (R₁.obj M)) ≫ τ.hom.app (S₁.obj (R₁.obj M)) =
      t.unit.app (L₁.obj (R₁.obj M)) ≫ U₂.map (l.inv.app (R₁.obj M)))
    (hc : L₂.map (c.app M) ≫ b.counit.app (S₂.obj M) =
      l.hom.app (R₁.obj M) ≫ S₂.map (a.counit.app M))
    (hd : L₁.map (d.app (S₂.obj M)) ≫ a.counit.app (U₂.obj (S₂.obj M)) =
      τ.hom.app (R₂.obj (S₂.obj M)) ≫ U₂.map (b.counit.app (S₂.obj M))) :
    s.unit.app (R₁.obj M) ≫ U₁.map (c.app M) ≫ d.app (S₂.obj M) =
      R₁.map (t.unit.app M) := by
  apply (a.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hd]
  have hn := τ.hom.naturality (c.app M)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← U₂.map_comp, hc, U₂.map_comp]
  rw [← Category.assoc, ← Category.assoc, hu]
  simp only [Category.assoc, ← U₂.map_comp_assoc, Iso.inv_hom_id_app]
  have ha := a.counit.naturality (t.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at ha
  apply Eq.trans ?_ ha.symm
  have ht := (t.unit.naturality (a.counit.app M)).symm
  simpa only [Functor.map_id, Category.id_comp, Functor.comp_obj, Functor.comp_map,
    Functor.id_obj, Functor.id_map] using ht

private theorem restrictScalars_reflects
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{r}} (α : R ⟶ R') :
    (SheafOfModules.restrictScalars.{r} α).ReflectsIsomorphisms := by
  have : (SheafOfModules.restrictScalars.{r} α ⋙
      SheafOfModules.toSheaf R).ReflectsIsomorphisms := by
    change (SheafOfModules.toSheaf R').ReflectsIsomorphisms
    infer_instance
  exact reflectsIsomorphisms_of_comp _ (SheafOfModules.toSheaf R)

set_option linter.unusedSectionVars false in
private theorem restriction_reflects (T : ScalarSite.{u, v, r, w} A B) :
    (U T).ReflectsIsomorphisms := by
  have : (res A B T.toSite).ReflectsIsomorphisms := by
    dsimp only [res, restriction]
    exact restrictScalars_reflects _
  exact exact_reflects_derived (res A B T.toSite)

private theorem chi_transpose {T Y : ScalarSite.{u, v, r, w} A B}
    (p : Geometric T Y) (M : DerivedCategory (Mod T.toSite A)) :
    (scalarAdj Y).unit.app ((RA p).obj M) ≫ (U Y).map ((chi p).app M) ≫
      (restrictionPushforward p).app ((S T).obj M) =
        (RA p).map ((scalarAdj T).unit.app M) := by
  have hunit := unit_mateEquiv_symm (scalarAdj Y) (scalarAdj T)
    (TwoSquare.mk _ _ _ _ (tau p).hom) ((RA p).obj M)
  change (LA p).map ((scalarAdj Y).unit.app ((RA p).obj M)) ≫
      (tau p).hom.app ((S Y).obj ((RA p).obj M)) =
    (scalarAdj T).unit.app ((LA p).obj ((RA p).obj M)) ≫
      (U T).map ((lambda p).inv.app ((RA p).obj M)) at hunit
  have hχ := mateEquiv_counit (adjA p) (adjB p)
    (TwoSquare.mk _ _ _ _ (lambda p).hom) M
  have hd := mateEquiv_counit (adjB p) (adjA p)
    (TwoSquare.mk _ _ _ _ (tau p).hom) ((S T).obj M)
  change (LB p).map ((chi p).app M) ≫ (adjB p).counit.app ((S T).obj M) =
    (lambda p).hom.app ((RA p).obj M) ≫ (S T).map ((adjA p).counit.app M) at hχ
  change (LA p).map ((restrictionPushforward p).app ((S T).obj M)) ≫
      (adjA p).counit.app ((U T).obj ((S T).obj M)) =
    (tau p).hom.app ((RB p).obj ((S T).obj M)) ≫
      (U T).map ((adjB p).counit.app ((S T).obj M)) at hd
  exact scalar_mate_transpose (adjA p) (adjB p) (scalarAdj Y) (scalarAdj T)
    (tau p) (lambda p) (chi p) (restrictionPushforward p) M hunit hχ hd

private theorem beta_transpose {V T : ScalarSite.{u, v, r, w} A B}
    (j : Open V T) (M : DerivedCategory (Mod V.toSite A)) :
    (scalarAdj T).unit.app ((IA j).obj M) ≫ (U T).map ((beta j).hom.app M) =
      (IA j).map ((scalarAdj V).unit.app M) ≫
        (restrictionOpen j).app ((S V).obj M) := by
  have he : (beta j).hom =
      ((mateEquiv (scalarAdj V) (scalarAdj T)).symm
        (TwoSquare.mk _ _ _ _ (restrictionOpen j))).natTrans := by
    have h := iterated_mateEquiv_conjugateEquiv_symm
      (scalarAdj V) (scalarAdj T) (openAdjA j) (openAdjB j)
      (TwoSquare.mk _ _ _ _ (tau j.geometric).inv)
    have h' := iterated_mateEquiv_conjugateEquiv_symm
      (openAdjA j) (openAdjB j) (scalarAdj V) (scalarAdj T)
      (TwoSquare.mk _ _ _ _ (tau j.geometric).hom)
    change (betaInv j) =
      (conjugateEquiv ((openAdjA j).comp (scalarAdj T))
        ((scalarAdj V).comp (openAdjB j))).symm (tau j.geometric).hom at h'
    change ((mateEquiv (scalarAdj V) (scalarAdj T)).symm
        (TwoSquare.mk _ _ _ _ (restrictionOpen j))).natTrans =
      (conjugateEquiv ((scalarAdj V).comp (openAdjB j))
        ((openAdjA j).comp (scalarAdj T))).symm (tau j.geometric).inv at h
    have := betaInv_isIso j
    apply (cancel_mono (betaInv j)).1
    have hid : (beta j).hom ≫ betaInv j = 𝟙 _ := by simp [beta]
    rw [hid, h, h', conjugateEquiv_symm_comp]
    simp
  rw [he]
  exact (unit_mateEquiv_symm (scalarAdj V) (scalarAdj T)
    (TwoSquare.mk _ _ _ _ (restrictionOpen j)) M).symm

section Centers
variable {C D : Type*} [Category C] [Category D]

private theorem center_right_adj (L : C ⥤ D) (R : D ⥤ C) (a : L ⊣ R)
    (zC : CatCenter C) (zD : CatCenter D)
    (h : ∀ M, L.map (zC.app M) = zD.app (L.obj M)) (N : D) :
    R.map (zD.app N) = zC.app (R.obj N) := by
  apply (a.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [h]
  exact (a.counit.naturality (zD.app N)).trans (zD.naturality (a.counit.app N))

private theorem center_left_adj (L : C ⥤ D) (R : D ⥤ C) (a : L ⊣ R)
    (zC : CatCenter C) (zD : CatCenter D)
    (h : ∀ N, R.map (zD.app N) = zC.app (R.obj N)) (M : C) :
    L.map (zC.app M) = zD.app (L.obj M) := by
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [h]
  exact (a.unit.naturality (zC.app M)).symm.trans (zC.naturality (a.unit.app M)).symm

end Centers

private def basisInclusion (T : ScalarSite.{u, v, r, w} A B)
    {I : Type i} (b : Module.Basis I A B) : Inclusions T I :=
  fun M c ↦ (scalarAdj T).unit.app M ≫
    (U T).map ((ConstantModuleScalar.derived T.J B (b c)).app ((S T).obj M))

private theorem basisInclusion_coordinates (T : ScalarSite.{u, v, r, w} A B)
    {I : Type i} [Fintype I] (b : Module.Basis I A B) :
    BasisCoordinates T b (basisInclusion T b) := by
  refine ⟨?_, ?_⟩
  · intro M N f c
    have hu := (scalarAdj T).unit.naturality f
    have hz := (ConstantModuleScalar.derived T.J B (b c)).naturality ((S T).map f)
    dsimp only [Functor.id_map, Functor.comp_map] at hu hz
    dsimp only [basisInclusion]
    rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp, hz,
      Functor.map_comp, ← Category.assoc]
  · let : PreservesFiniteLimits (restriction ((constantSheaf T.J CommRingCat).map
        (CommRingCat.ofHom (algebraMap A B)))) := by
      simpa only [res, coefficientMap] using T.resLimits
    let : PreservesFiniteColimits (restriction ((constantSheaf T.J CommRingCat).map
        (CommRingCat.ofHom (algebraMap A B)))) := by
      simpa only [res, coefficientMap] using T.resColimits
    exact ConstantModuleScalar.normalized_basis T.J A B T.model T.adj T.adjFormula b

omit [Module.Finite A B] [Module.Free A B] in
private theorem inverseImage_center {T W : ScalarSite.{u, v, r, w} A B}
    (f : Geometric T W) (b : B) (M : DerivedCategory (Mod W.toSite B)) :
    (LB f).map ((ConstantModuleScalar.derived W.J B b).app M) =
      (ConstantModuleScalar.derived T.J B b).app ((LB f).obj M) := by
  let := f.leftExact
  exact ConstantModuleScalar.inverseImage_center W.J T.J B f.inverse f.liftB
    f.point f.constantsB b M

omit [Module.Finite A B] [Module.Free A B] in
private theorem directImage_center {T W : ScalarSite.{u, v, r, w} A B}
    (f : Geometric T W) (b : B) (M : DerivedCategory (Mod T.toSite B)) :
    (RB f).map ((ConstantModuleScalar.derived T.J B b).app M) =
      (ConstantModuleScalar.derived W.J B b).app ((RB f).obj M) :=
  center_right_adj (LB f) (RB f) (adjB f)
    (ConstantModuleScalar.derived W.J B b) (ConstantModuleScalar.derived T.J B b)
    (inverseImage_center f b) M

omit [Module.Finite A B] [Module.Free A B] in
private theorem open_center {V T : ScalarSite.{u, v, r, w} A B}
    (j : Open V T) (b : B) (M : DerivedCategory (Mod V.toSite B)) :
    (IB j).map ((ConstantModuleScalar.derived V.J B b).app M) =
      (ConstantModuleScalar.derived T.J B b).app ((IB j).obj M) :=
  center_left_adj (IB j) (LB j.geometric) (openAdjB j)
    (ConstantModuleScalar.derived V.J B b) (ConstantModuleScalar.derived T.J B b)
    (inverseImage_center j.geometric b) M

private theorem basisInclusion_chi {T Y : ScalarSite.{u, v, r, w} A B}
    (p : Geometric T Y) {I : Type i} (b : Module.Basis I A B)
    (M : DerivedCategory (Mod T.toSite A)) (c : I) :
    basisInclusion Y b ((RA p).obj M) c ≫ (U Y).map ((chi p).app M) ≫
        (restrictionPushforward p).app ((S T).obj M) =
      (RA p).map (basisInclusion T b M c) := by
  have hz := (ConstantModuleScalar.derived Y.J B (b c)).naturality ((chi p).app M)
  have hn := (restrictionPushforward p).naturality
    ((ConstantModuleScalar.derived T.J B (b c)).app ((S T).obj M))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn hz
  rw [directImage_center] at hn
  dsimp only [basisInclusion]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← hz, Functor.map_comp_assoc, hn]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ (RA p).map ((U T).map
      ((ConstantModuleScalar.derived T.J B (b c)).app ((S T).obj M))))
    (chi_transpose p M)

private theorem basisInclusion_beta {V T : ScalarSite.{u, v, r, w} A B}
    (j : Open V T) {I : Type i} (b : Module.Basis I A B)
    (M : DerivedCategory (Mod V.toSite A)) (c : I) :
    basisInclusion T b ((IA j).obj M) c ≫ (U T).map ((beta j).hom.app M) =
      (IA j).map (basisInclusion V b M c) ≫
        (restrictionOpen j).app ((S V).obj M) := by
  have hz := (ConstantModuleScalar.derived T.J B (b c)).naturality ((beta j).hom.app M)
  have hn := (restrictionOpen j).naturality
    ((ConstantModuleScalar.derived V.J B (b c)).app ((S V).obj M))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn hz
  rw [open_center] at hn
  dsimp only [basisInclusion]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp, ← hz, Functor.map_comp, ← Category.assoc,
    beta_transpose, Category.assoc, ← hn]


/-- The restricted maps are exactly the finite-biproduct comparisons, with every
basis column specified, on all unbounded inputs.
Source: blueprint transport Steps 1 and 3; Stacks 03CZ, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents).
Proof: sheafify the mutually inverse formulas b tensor x maps to (q_a(b)x)_a and
(x_a)_a maps to sum b_a tensor x_a. Their identities follow from basis expansion;
they commute with restrictions, differentials and module maps, so localize on every
complex. The scalar transpose of chi gives the column for 1. B-linearity and
naturality of restrictionPushforward for multiplication by b_a give each displayed
column. For beta the same formula holds on every extension-presheaf summand and
vanishes off the open. These are the defining columns of the finite-biproduct
comparison. The finite-matrix identities also cover rank zero. -/
theorem finiteFreeCompactCoordinates {X T Y : ScalarSite.{u, v, r, w} A B}
    (j : Open X T) (p : Geometric T Y) {I : Type i} [Fintype I]
    (b : Module.Basis I A B) :
    ∃ (ιX : Inclusions X I) (ιT : Inclusions T I) (ιY : Inclusions Y I),
      BasisCoordinates X b ιX ∧ BasisCoordinates T b ιT ∧ BasisCoordinates Y b ιY ∧
      (∀ (M : DerivedCategory (Mod T.toSite A)) (a : I),
        ιY ((RA p).obj M) a ≫ (U Y).map ((chi p).app M) ≫
            (restrictionPushforward p).app ((S T).obj M) = (RA p).map (ιT M a)) ∧
      ∀ (M : DerivedCategory (Mod X.toSite A)) (a : I),
        ιT ((IA j).obj M) a ≫ (U T).map ((beta j).hom.app M) =
          (IA j).map (ιX M a) ≫ (restrictionOpen j).app ((S X).obj M) := by
  refine ⟨basisInclusion X b, basisInclusion T b, basisInclusion Y b,
    basisInclusion_coordinates X b, basisInclusion_coordinates T b,
    basisInclusion_coordinates Y b, ?_, ?_⟩
  · exact basisInclusion_chi p b
  · exact basisInclusion_beta j b



private theorem chi_isIso {X T Y : ScalarSite.{u, v, r, w} A B}
    (j : Open X T) (p : Geometric T Y) : IsIso (chi p) := by
  classical
  let b := Module.Free.chooseBasis A B
  obtain ⟨ιX, ιT, ιY, hcoord⟩ := finiteFreeCompactCoordinates j p b
  have hT := hcoord.2.1
  have hY := hcoord.2.2.1
  have hχ := hcoord.2.2.2.1
  have := restriction_reflects Y
  have := restrictionPushforward_isIso p
  have : (RA p).Additive := by
    dsimp only [RA]
    exact Functor.additive_rightDerivedFunctor p.pushA
  have h (M : DerivedCategory (Mod T.toSite A)) : IsIso ((chi p).app M) := by
    obtain ⟨qT, hiT, hqT⟩ := hT.2.1 M
    obtain ⟨qY, _, hqY⟩ := hY.2.1 ((RA p).obj M)
    have : IsIso ((U Y).map ((chi p).app M) ≫
        (restrictionPushforward p).app ((S T).obj M)) :=
      matrix_map_isIso (RA p) (ιT M) qT (ιY ((RA p).obj M)) qY
        hiT hqT hqY _ (hχ M)
    have : IsIso ((U Y).map ((chi p).app M)) := IsIso.of_isIso_comp_right _
      ((restrictionPushforward p).app ((S T).obj M))
    exact isIso_of_reflects_iso _ (U Y)
  have := h
  exact NatIso.isIso_of_isIso_app _

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Finite-free direct-image and compact-support comparisons are B-linear natural
isomorphisms, and the compact-support map has the prescribed scalar transpose.
Source: blueprint transport Steps 1 and 3; Stacks 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents).
Proof: (1) a finite basis identifies restricted exact scalar extension with finite
sums. (2) the restriction/counit identity and scalar-unit normalization of lambda
identify the scalar transpose of chi with the direct image of the scalar unit.
(3) multiplying this identity by each basis scalar gives every biproduct column.
Additivity proves invertibility; exact restriction reflects isomorphisms by cones.
(4) sum-presheaf balancing gives the analogous transpose and columns for beta.
(5) naturality of restrictionPushforward moves beta through that comparison;
substitute the two scalar transpose identities. The result is precisely rho after
FA of the scalar unit. The two already invertible constituents make their composite
invertible. All Hom bijections and equalities take place in the B-module derived
category; faithfulness of derived restriction is neither assumed nor used. -/
theorem finiteFreeCompactConstituents {X T Y : ScalarSite.{u, v, r, w} A B}
    (j : Open X T) (p : Geometric T Y) :
    IsIso (chi p) ∧ IsIso (compactComparison j p) ∧
    ∀ M : DerivedCategory (Mod X.toSite A),
      (scalarAdj Y).homEquiv _ _ ((compactComparison j p).app M) =
        (FA j p).map ((scalarAdj X).unit.app M) ≫ (rho j p).hom.app ((S X).obj M) := by
  have hc := chi_isIso j p
  constructor
  · exact hc
  constructor
  · have h (M : DerivedCategory (Mod X.toSite A)) :
        IsIso ((compactComparison j p).app M) := by
      have : IsIso ((chi p).app ((IA j).obj M)) := inferInstance
      simpa only [compactComparison, FA, FB, Functor.comp_obj, NatTrans.comp_app,
        Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Category.id_comp, Category.comp_id] using
        (inferInstance : IsIso ((chi p).app ((IA j).obj M) ≫
          (RB p).map ((beta j).hom.app M)))
    exact NatIso.isIso_of_isIso_app _
  · intro M
    have := restrictionPushforward_isIso p
    apply (cancel_mono ((restrictionPushforward p).app
      ((IB j).obj ((S X).obj M)))).1
    rw [Adjunction.homEquiv_unit]
    simp only [compactComparison, rho, FA, FB,
      Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Iso.symm_hom, asIso_hom, asIso_inv, Functor.comp_map, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj, Functor.map_comp,
      Category.id_comp, Category.comp_id, Category.assoc]
    have hn := (restrictionPushforward p).naturality ((beta j).hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [hn]
    rw [reassoc_of% chi_transpose p ((IA j).obj M)]
    rw [← Functor.map_comp, beta_transpose j M, Functor.map_comp]
    simp only [NatIso.isIso_inv_app, IsIso.inv_hom_id,
      Category.comp_id]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem localized_unit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) [IsIso a.unit] : IsIso a.onDerivedCategory.unit := by
  have h (M : DerivedCategory C) : IsIso (a.onDerivedCategory.unit.app M) := by
    rw [← NatTrans.isIso_app_iff_of_iso a.onDerivedCategory.unit
      (DerivedCategory.Q.objObjPreimageIso M)]
    dsimp only [Adjunction.onDerivedCategory]
    rw [Adjunction.localization_unit_app]
    have hu : IsIso ((a.mapHomologicalComplex (.up ℤ)).unit.app
        (DerivedCategory.Q.objPreimage M)) := by
      have hn (n : ℤ) : IsIso (((a.mapHomologicalComplex (.up ℤ)).unit.app
          (DerivedCategory.Q.objPreimage M)).f n) := by
        change IsIso (a.unit.app _)
        infer_instance
      let := hn
      exact HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  let := h
  exact NatIso.isIso_of_isIso_app _


set_option linter.unusedSectionVars false in
/-- The localized open units retain the ordinary full-faithfulness normalization.
Source: Stacks 03DI, 03DJ, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents).
Proof: exact localization sends the inverse ordinary unit to an inverse derived
unit, by the localization factorization of the original adjunction. -/
theorem open_units_isIso {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :
    IsIso (openAdjA j).unit ∧ IsIso (openAdjB j).unit := by
  exact ⟨localized_unit_isIso j.adjA, localized_unit_isIso j.adjB⟩

/-- Invertibility of the A-coefficient open unit after exact localization.
Source: Stacks 03DI (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
instance openUnitA {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :
    IsIso (openAdjA j).unit := (open_units_isIso j).1

/-- Invertibility of the B-coefficient open unit after exact localization.
Source: Stacks 03DI (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
instance openUnitB {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T) :
    IsIso (openAdjB j).unit := (open_units_isIso j).2

/-- The unit-normalization identity for the specified B-linear balancing map.
Source: Stacks 03DI, 03CZ, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents).
Proof: under the open Hom bijection the inverse balancing map is lambda inverse
following scalar extension of the open unit: both send each local summand tensor
to that same tensor. Exact localization preserves this equation. Invert the two
open units and rearrange; this yields exactly the displayed identity. -/
theorem beta_unit {V T : ScalarSite.{u, v, r, w} A B} (j : Open V T)
    (M : DerivedCategory (Mod V.toSite A)) :
    (lambda j.geometric).hom.app ((IA j).obj M) ≫
        (S V).map (inv ((openAdjA j).unit.app M)) =
      (LB j.geometric).map ((beta j).hom.app M) ≫
        inv ((openAdjB j).unit.app ((S V).obj M)) := by
  have h := unit_mateEquiv_symm (openAdjA j) (openAdjB j)
    (TwoSquare.mk _ _ _ _ (lambda j.geometric).inv) M
  change (S V).map ((openAdjA j).unit.app M) ≫
      (lambda j.geometric).inv.app ((IA j).obj M) =
    (openAdjB j).unit.app ((S V).obj M) ≫ (LB j.geometric).map ((betaInv j).app M) at h
  let := betaInv_isIso j
  have hb : (beta j).hom.app M = inv ((betaInv j).app M) := by simp [beta]
  rw [hb]
  apply eq_of_inv_eq_inv
  simpa only [IsIso.inv_comp, Functor.map_inv, IsIso.inv_inv,
    NatIso.inv_hom_app] using h

/-- A presentation of a composite geometric morphism. The inverse-image compositor
is specified on sheaves of sets; the module compositors are its unique lifts on the
actual underlying inverse images, rather than arbitrary derived identifications.
Source: Stacks 0D6D, 0D6E
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
structure Composite {T W Z : ScalarSite.{u, v, r, w} A B}
    (f : Geometric T W) (g : Geometric W Z) (h : Geometric T Z) where
  inverse : h.inverse ≅ g.inverse ⋙ f.inverse
  moduleA : h.liftA.modules ≅ g.liftA.modules ⋙ f.liftA.modules
  moduleB : h.liftB.modules ≅ g.liftB.modules ⋙ f.liftB.modules
  underlyingA : ∀ M : Mod Z.toSite A,
    (underlying.{u, v, r} (constantRing T.J A)).map (moduleA.hom.app M) =
      h.liftA.moduleUnderlying.hom.app M ≫
        inverse.hom.app ((underlying.{u, v, r} (constantRing Z.J A)).obj M) ≫
        f.inverse.map (g.liftA.moduleUnderlying.inv.app M) ≫
        f.liftA.moduleUnderlying.inv.app (g.liftA.modules.obj M)
  underlyingB : ∀ M : Mod Z.toSite B,
    (underlying.{u, v, r} (constantRing T.J B)).map (moduleB.hom.app M) =
      h.liftB.moduleUnderlying.hom.app M ≫
        inverse.hom.app ((underlying.{u, v, r} (constantRing Z.J B)).obj M) ≫
        f.inverse.map (g.liftB.moduleUnderlying.inv.app M) ≫
        f.liftB.moduleUnderlying.inv.app (g.liftB.modules.obj M)

/-- The exact localization of the canonical A-coefficient inverse-image compositor.
Source: Stacks 0D6D (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def compLA {T W Z : ScalarSite.{u, v, r, w} A B}
    {f : Geometric T W} {g : Geometric W Z} {h : Geometric T Z}
    (c : Composite f g h) : LA h ≅ LA g ⋙ LA f :=
  Functor.mapDerivedCategoryNatIso c.moduleA ≪≫ Functor.mapDerivedCategoryCompIso _ _

/-- The exact localization of the canonical B-coefficient inverse-image compositor.
Source: Stacks 0D6D (blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def compLB {T W Z : ScalarSite.{u, v, r, w} A B}
    {f : Geometric T W} {g : Geometric W Z} {h : Geometric T Z}
    (c : Composite f g h) : LB h ≅ LB g ⋙ LB f :=
  Functor.mapDerivedCategoryNatIso c.moduleB ≪≫ Functor.mapDerivedCategoryCompIso _ _

/-- The direct-image compositor with its canonical derived-adjunction normalization.
Source: Stacks 0D6E; derived-composition adjunction normalization
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def compRA {T W Z : ScalarSite.{u, v, r, w} A B}
    {f : Geometric T W} {g : Geometric W Z} {h : Geometric T Z}
    (c : Composite f g h) : RA f ⋙ RA g ≅ RA h :=
  conjugateIsoEquiv ((adjA g).comp (adjA f)) (adjA h) (compLA c)

/-- The B-linear direct-image compositor with the same normalization.
Source: Stacks 0D6E; derived-composition adjunction normalization
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def compRB {T W Z : ScalarSite.{u, v, r, w} A B}
    {f : Geometric T W} {g : Geometric W Z} {h : Geometric T Z}
    (c : Composite f g h) : RB f ⋙ RB g ≅ RB h :=
  conjugateIsoEquiv ((adjB g).comp (adjB f)) (adjB h) (compLB c)

section
omit [Module.Finite A B] [Module.Free A B]

set_option maxHeartbeats 1600000 in
-- Comparing the dependent module and sheaf presentations needs extra elaboration time.
private theorem restriction_comp {T W Z : ScalarSite.{u, v, r, w} A B}
    {f : Geometric T W} {g : Geometric W Z} {h : Geometric T Z}
    (c : Composite f g h) (M : Mod Z.toSite B) :
    c.moduleA.hom.app ((res A B Z.toSite).obj M) ≫
        f.liftA.modules.map (g.restriction.hom.app M) ≫
          f.restriction.hom.app (g.liftB.modules.obj M) =
      h.restriction.hom.app M ≫ (res A B T.toSite).map (c.moduleB.hom.app M) := by
  apply (underlying (constantRing T.J A)).map_injective
  simp only [Functor.map_comp, Category.assoc, f.restrictionFormula,
    h.restrictionFormula, c.underlyingA]
  change _ = h.liftA.moduleUnderlying.hom.app ((res A B Z.toSite).obj M) ≫
    h.liftB.moduleUnderlying.inv.app M ≫
      (underlying (constantRing T.J B)).map (c.moduleB.hom.app M)
  erw [c.underlyingB, Iso.inv_hom_id_app_assoc]
  have hn := f.liftA.moduleUnderlying.inv.naturality (g.restriction.hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  erw [g.restrictionFormula]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  rfl

set_option maxHeartbeats 1600000 in
-- Comparing the dependent module and sheaf presentations needs extra elaboration time.
private theorem tau_comp {T W Z : ScalarSite.{u, v, r, w} A B}
    {f : Geometric T W} {g : Geometric W Z} {h : Geometric T Z}
    (c : Composite f g h) (M : DerivedCategory (Mod Z.toSite B)) :
    (compLA c).hom.app ((U Z).obj M) ≫
        (LA f).map ((tau g).hom.app M) ≫
          (tau f).hom.app ((LB g).obj M) =
      (tau h).hom.app M ≫ (U T).map ((compLB c).hom.app M) := by
  exact (Functor.exactSquare_comp_inverse
    g.liftB.modules f.liftB.modules h.liftB.modules
    g.liftA.modules f.liftA.modules h.liftA.modules
    (res A B Z.toSite) (res A B W.toSite) (res A B T.toSite)
    g.restriction f.restriction h.restriction c.moduleB c.moduleA
    (fun M ↦ (restriction_comp c M).symm) M).symm

end

set_option maxHeartbeats 1600000 in
-- Comparing the dependent module and sheaf presentations needs extra elaboration time.
private theorem tensor_comp {T W Z : ScalarSite.{u, v, r, w} A B}
    {f : Geometric T W} {g : Geometric W Z} {h : Geometric T Z}
    (c : Composite f g h) (M : DerivedCategory (Mod Z.toSite A)) :
    (S T).map ((compLA c).hom.app M) ≫
        (tensorPullbackInv f).app ((LA g).obj M) ≫
          (LB f).map ((tensorPullbackInv g).app M) =
      (tensorPullbackInv h).app M ≫ (compLB c).hom.app ((S Z).obj M) := by
  let αg := (mateEquiv (scalarAdj Z) (scalarAdj W)).symm
    (TwoSquare.mk _ _ _ _ (tau g).hom)
  let αf := (mateEquiv (scalarAdj W) (scalarAdj T)).symm
    (TwoSquare.mk _ _ _ _ (tau f).hom)
  let αh := (mateEquiv (scalarAdj Z) (scalarAdj T)).symm
    (TwoSquare.mk _ _ _ _ (tau h).hom)
  have he : (((TwoSquare.hComp αg αf).whiskerTop (compLA c).hom).whiskerBottom (𝟙 _)) =
      ((αh.whiskerTop (𝟙 _)).whiskerBottom (compLB c).hom) := by
    apply (mateEquiv (scalarAdj Z) (scalarAdj T)).injective
    rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_whiskerTop_whiskerBottom,
      mateEquiv_vcomp (scalarAdj Z) (scalarAdj W) (scalarAdj T)]
    simp only [αg, αf, αh, Equiv.apply_symm_apply]
    ext N
    simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      TwoSquare.vComp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.id_app, Functor.map_id, Category.assoc]
    erw [Category.comp_id, Category.id_comp]
    exact tau_comp c N
  have heM := congrArg (fun α ↦ α.natTrans.app M) he
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.hComp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.id_app, Functor.map_id] at heM
  erw [Category.comp_id, Category.id_comp] at heM
  exact heM

set_option maxHeartbeats 1600000 in
-- Comparing the dependent module and sheaf presentations needs extra elaboration time.
private theorem lambda_comp {T W Z : ScalarSite.{u, v, r, w} A B}
    {f : Geometric T W} {g : Geometric W Z} {h : Geometric T Z}
    (c : Composite f g h) (M : DerivedCategory (Mod Z.toSite A)) :
    (compLB c).hom.app ((S Z).obj M) ≫
        (LB f).map ((lambda g).hom.app M) ≫
          (lambda f).hom.app ((LA g).obj M) =
      (lambda h).hom.app M ≫ (S T).map ((compLA c).hom.app M) := by
  have hc := tensor_comp c M
  change (S T).map ((compLA c).hom.app M) ≫
      (lambda f).inv.app ((LA g).obj M) ≫
        (LB f).map ((lambda g).inv.app M) =
    (lambda h).inv.app M ≫ (compLB c).hom.app ((S Z).obj M) at hc
  apply (cancel_mono ((lambda f).inv.app ((LA g).obj M) ≫
    (LB f).map ((lambda g).inv.app M))).1
  simp only [Category.assoc]
  calc
    _ = (compLB c).hom.app ((S Z).obj M) := by
      erw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
        Functor.map_id, Category.comp_id]
    _ = (lambda h).hom.app M ≫
        ((lambda h).inv.app M ≫ (compLB c).hom.app ((S Z).obj M)) := by
      erw [Iso.hom_inv_id_app_assoc]
    _ = _ := by rw [← hc]

set_option maxHeartbeats 1600000 in
-- Comparing the dependent module and sheaf presentations needs extra elaboration time.
/-- The specified counit mates commute with composition of geometric morphisms.
Source: Stacks 0D6D, 0D6E; blueprint transport Step 1
(blueprint: lem-pur-topos-finite-free-compact-constituents).
Proof: pure-tensor balancing gives inverse-image coherence of lambda. The canonical
derived direct-image compositor is the conjugate of the inverse-image compositor,
so its counit is the composite counit. Pasting the two lambda squares and applying
the mate bijection yields the right-hand word. Its transpose is the defining
transpose of chi for the composite. The Hom bijection proves equality in D_B. -/
theorem chi_comp {T W Z : ScalarSite.{u, v, r, w} A B}
    {f : Geometric T W} {g : Geometric W Z} {h : Geometric T Z}
    (c : Composite f g h) (M : DerivedCategory (Mod T.toSite A)) :
    (S Z).map ((compRA c).hom.app M) ≫ (chi h).app M ≫
        (compRB c).inv.app ((S T).obj M) =
      (chi g).app ((RA f).obj M) ≫ (RB g).map ((chi f).app M) := by
  let αg := TwoSquare.mk _ _ _ _ (lambda g).hom
  let αf := TwoSquare.mk _ _ _ _ (lambda f).hom
  let αh := TwoSquare.mk _ _ _ _ (lambda h).hom
  have he : αh.whiskerLeft (compLA c).hom =
      (TwoSquare.vComp αg αf).whiskerRight (compLB c).hom := by
    ext N
    simpa only [αg, αf, αh, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      TwoSquare.vComp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using (lambda_comp c N).symm
  have hm := congrArg (mateEquiv ((adjA g).comp (adjA f)) (adjB h)) he
  rw [conjugateEquiv_mateEquiv_vcomp ((adjA g).comp (adjA f)) (adjA h) (adjB h),
    mateEquiv_conjugateEquiv_vcomp ((adjA g).comp (adjA f))
      ((adjB g).comp (adjB f)) (adjB h),
    mateEquiv_hcomp (adjA g) (adjB g) (adjA f) (adjB f)] at hm
  have hmM := congrArg (fun α ↦ α.natTrans.app M) hm
  have heM : (S Z).map ((compRA c).hom.app M) ≫ (chi h).app M =
      ((chi g).app ((RA f).obj M) ≫ (RB g).map ((chi f).app M)) ≫
        (compRB c).hom.app ((S T).obj M) := by
    simpa only [αg, αf, αh, chi, compRA, compRB, conjugateIsoEquiv_apply_hom,
      TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp_app,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      using hmM
  rw [← Category.assoc, heM]
  simp


/-- The open-extension compositor, uniquely preserving the original open adjunctions.
Source: Stacks 03DI, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def compIA {V T Z : ScalarSite.{u, v, r, w} A B}
    {j₁ : Open V T} {j₂ : Open T Z} {j : Open V Z}
    (c : Composite j₁.geometric j₂.geometric j.geometric) : IA j₁ ⋙ IA j₂ ≅ IA j :=
  (conjugateIsoEquiv (openAdjA j) ((openAdjA j₁).comp (openAdjA j₂))).symm (compLA c)

/-- The B-linear open-extension compositor preserving the same units.
Source: Stacks 03DI, 07A6
(blueprint: lem-pur-topos-finite-free-compact-constituents). -/
def compIB {V T Z : ScalarSite.{u, v, r, w} A B}
    {j₁ : Open V T} {j₂ : Open T Z} {j : Open V Z}
    (c : Composite j₁.geometric j₂.geometric j.geometric) : IB j₁ ⋙ IB j₂ ≅ IB j :=
  (conjugateIsoEquiv (openAdjB j) ((openAdjB j₁).comp (openAdjB j₂))).symm (compLB c)

set_option maxHeartbeats 1600000 in
-- Comparing the dependent module and sheaf presentations needs extra elaboration time.
/-- The balancing maps commute with composition of open embeddings.
Source: Stacks 03DI, 03DJ, 07A6; blueprint transport Step 1
(blueprint: lem-pur-topos-finite-free-compact-constituents).
Proof: transpose the inverse of the composite balancing word under the composite
open adjunction. Twice applying beta_unit gives lambda inverse followed by scalar
extension of the composite open unit. Coherence of lambda identifies this with the
transpose of beta inverse for the composite. Injectivity of the open Hom bijection
proves equality of inverses and hence the displayed equality. The conjugate open
compositor is the section-presheaf compositor because both preserve its generators. -/
theorem beta_comp {V T Z : ScalarSite.{u, v, r, w} A B}
    {j₁ : Open V T} {j₂ : Open T Z} {j : Open V Z}
    (c : Composite j₁.geometric j₂.geometric j.geometric)
    (M : DerivedCategory (Mod V.toSite A)) :
    (S Z).map ((compIA c).inv.app M) ≫ (beta j₂).hom.app ((IA j₁).obj M) ≫
        (IB j₂).map ((beta j₁).hom.app M) ≫ (compIB c).hom.app ((S V).obj M) =
      (beta j).hom.app M := by
  let α₁ := (mateEquiv (openAdjA j₁) (openAdjB j₁)).symm
    (TwoSquare.mk _ _ _ _ (lambda j₁.geometric).inv)
  let α₂ := (mateEquiv (openAdjA j₂) (openAdjB j₂)).symm
    (TwoSquare.mk _ _ _ _ (lambda j₂.geometric).inv)
  let α := (mateEquiv (openAdjA j) (openAdjB j)).symm
    (TwoSquare.mk _ _ _ _ (lambda j.geometric).inv)
  have he : (TwoSquare.vComp α₁ α₂).whiskerLeft (compIA c).hom =
      α.whiskerRight (compIB c).hom := by
    apply (mateEquiv (openAdjA j) ((openAdjB j₁).comp (openAdjB j₂))).injective
    rw [conjugateEquiv_mateEquiv_vcomp (openAdjA j)
        ((openAdjA j₁).comp (openAdjA j₂)) ((openAdjB j₁).comp (openAdjB j₂)),
      mateEquiv_conjugateEquiv_vcomp (openAdjA j) (openAdjB j)
        ((openAdjB j₁).comp (openAdjB j₂)),
      mateEquiv_hcomp (openAdjA j₁) (openAdjB j₁) (openAdjA j₂) (openAdjB j₂)]
    simp only [α₁, α₂, α, Equiv.apply_symm_apply, compIA, compIB,
      conjugateIsoEquiv_symm_apply_hom, Equiv.apply_symm_apply]
    ext N
    simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.hComp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, lambda, Iso.symm_inv, asIso_hom] using tensor_comp c N
  have heM := congrArg (fun α ↦ α.natTrans.app M) he
  have hi : (IB j₂).map ((betaInv j₁).app M) ≫
      (betaInv j₂).app ((IA j₁).obj M) ≫
        (S Z).map ((compIA c).hom.app M) =
      (compIB c).hom.app ((S V).obj M) ≫ (betaInv j).app M := by
    simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      TwoSquare.vComp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc, α₁, α₂, α, betaInv] using heM
  change (IB j₂).map ((beta j₁).inv.app M) ≫
      (beta j₂).inv.app ((IA j₁).obj M) ≫
        (S Z).map ((compIA c).hom.app M) =
      (compIB c).hom.app ((S V).obj M) ≫ (beta j).inv.app M at hi
  apply (cancel_mono ((beta j).inv.app M)).1
  simp only [Category.assoc]
  rw [← hi]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [Functor.map_id]
  simp only [Category.id_comp, Iso.hom_inv_id_app_assoc]
  erw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  rfl

end CategoryTheory.ToposFiniteFreeCompact
