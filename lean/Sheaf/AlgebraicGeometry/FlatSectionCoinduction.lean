module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
public import WeilConjectures.AlgebraicGeometry.ClosedModulePushforwardHomology
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapAlgebra
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.SheafCoinductionAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Coinduction for a closed section

Source: Stacks Project, duality.tex, Tags 0A76, 0A77, 0A9X and 0E2T.
(blueprint: lem-sfb-flat-section-coinduction).
The multiplication and unit below use the ordinary direct-image algebra, its degree-zero
complex, and the canonical localization tensor map. The supplied adjunction is on D_QCoh.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wZ wW
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- The ordinary direct-image algebra as a module. Source: Stacks 0A77, 0E2T
(blueprint: lem-sfb-flat-section-coinduction). -/
abbrev flatSectionAlgebraModule {Z W : Scheme.{u}} (i : Z ⟶ W) :
    SheafOfModules.{u} (moduleRings W.toRingedSpace) :=
  (SheafOfModules.pushforward i.toRingCatSheafHom).obj
    (SheafOfModules.unit (moduleRings Z.toRingedSpace))

/-- The structure sheaf in degree zero. Source: Stacks 0A77
(blueprint: lem-sfb-flat-section-coinduction). -/
abbrev flatSectionStructureObject (Z : Scheme.{u})
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] :
    schemeDerivedCategory Z :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (moduleRings Z.toRingedSpace))

/-- The ordinary direct-image algebra in degree zero. Source: Stacks 0A77, 0E2T
(blueprint: lem-sfb-flat-section-coinduction). -/
abbrev flatSectionAlgebraObject {Z W : Scheme.{u}} (i : Z ⟶ W)
    [HasDerivedCategory.{wW} (SheafOfModules.{u} (moduleRings W.toRingedSpace))] :
    schemeDerivedCategory W :=
  (DerivedCategory.singleFunctor _ 0).obj (flatSectionAlgebraModule i)

/-- The canonical algebra unit in degree zero. Source: Stacks 0A77, 0E2T
(blueprint: lem-sfb-flat-section-coinduction). -/
def flatSectionAlgebraUnit {Z W : Scheme.{u}} (i : Z ⟶ W)
    [HasDerivedCategory.{wW} (SheafOfModules.{u} (moduleRings W.toRingedSpace))] :
    flatSectionStructureObject W ⟶ flatSectionAlgebraObject i :=
  (DerivedCategory.singleFunctor _ 0).map
    (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)

/-- Sectionwise multiplication, uniquely determined by its values on pure section tensors.
The first witness of moduleBaseChangeMap_algebra for the identity square has precisely
this property; sheafification and the tensor universal property determine it uniquely.
Source: Stacks 0E2T; module base-change algebra compatibility, 08HY
(blueprint: lem-sfb-flat-section-coinduction). -/
def flatSectionOrdinaryMultiplication {Z W : Scheme.{u}} (i : Z ⟶ W) :
    (SheafOfModules.monoidalCategory W.sheaf).tensorObj
      (flatSectionAlgebraModule i) (flatSectionAlgebraModule i) ⟶
        flatSectionAlgebraModule i :=
  Classical.choose (Scheme.Modules.moduleBaseChangeMap_algebra i i (𝟙 W) (𝟙 Z)
    ((Category.id_comp i).trans (Category.comp_id i).symm))

/-- The canonical tensor comparison for two degree-zero complexes.
Source: Stacks 0E2T and 06YH (blueprint: lem-sfb-flat-section-coinduction). -/
def flatSectionTensorSingleIso {Z W : Scheme.{u}} (i : Z ⟶ W) :
    pullbackTensorTotal W
      ((CochainComplex.singleFunctor _ 0).obj (flatSectionAlgebraModule i))
      ((CochainComplex.singleFunctor _ 0).obj (flatSectionAlgebraModule i)) ≅
      (CochainComplex.singleFunctor _ 0).obj
        ((SheafOfModules.monoidalCategory W.sheaf).tensorObj
          (flatSectionAlgebraModule i) (flatSectionAlgebraModule i)) := by
  letI := SheafOfModules.monoidalCategory W.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor W.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj W.sheaf
  exact CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _)
      (flatSectionAlgebraModule i) ((CochainComplex.singleFunctor _ 0).obj
        (flatSectionAlgebraModule i)) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex
      (tensorLeft (flatSectionAlgebraModule i)) (.up ℤ) 0).app _

/-- The canonical derived multiplication induced by ordinary algebra multiplication.
Source: Stacks 0E2T and 06YH (blueprint: lem-sfb-flat-section-coinduction). -/
def flatSectionDerivedMultiplication {Z W : Scheme.{u}} (i : Z ⟶ W)
    [HasDerivedCategory.{wW} (SheafOfModules.{u} (moduleRings W.toRingedSpace))] :
    flatSectionAlgebraObject i ⊗ flatSectionAlgebraObject i ⟶
      flatSectionAlgebraObject i :=
  (((DerivedCategory.singleFunctorIsoCompQ _ 0).app (flatSectionAlgebraModule i)).hom ⊗ₘ
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (flatSectionAlgebraModule i)).hom) ≫
    pullbackTensorModelMap W
      ((CochainComplex.singleFunctor _ 0).obj (flatSectionAlgebraModule i))
      ((CochainComplex.singleFunctor _ 0).obj (flatSectionAlgebraModule i)) ≫
    DerivedCategory.Q.map ((flatSectionTensorSingleIso i).hom ≫
      (CochainComplex.singleFunctor _ 0).map (flatSectionOrdinaryMultiplication i)) ≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (flatSectionAlgebraModule i)).inv

/-- The structure sheaf in degree zero is the derived tensor unit.
Source: Stacks 06YH (blueprint: lem-sfb-flat-section-coinduction). -/
def flatSectionStructureUnitIso (W : Scheme.{u})
    [HasDerivedCategory.{wW} (SheafOfModules.{u} (moduleRings W.toRingedSpace))] :
    flatSectionStructureObject W ≅ 𝟙_ (schemeDerivedCategory W) := by
  letI := pullbackDescentModuleTensor W
  letI := moduleSymmetric W
  letI := modulePreadditive W
  letI := moduleClosed W
  letI := moduleGrothendieck W
  letI := moduleResolutions W
  exact DerivedCategory.singleFunctorObjUnitIso
    (SheafOfModules.{u} (moduleRings W.toRingedSpace))

/-- Exact closed pushforward identifies Ri_* O_Z with the ordinary algebra in degree zero.
Source: Stacks 0A77 (blueprint: lem-sfb-flat-section-coinduction). -/
def flatSectionPushforwardStructureIso {Z W : Scheme.{u}} (i : Z ⟶ W)
    [IsClosedImmersion i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wW} (SheafOfModules.{u} (moduleRings W.toRingedSpace))] :
    (schemeDerivedDirectImage i).obj (flatSectionStructureObject Z) ≅
      flatSectionAlgebraObject i := by
  let F := RingedSpace.moduleDirectImage i.toLRSHom.toShHom
  have : F.PreservesHomology := closed_modulePushforward_preservesHomology i
  have : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
  have : PreservesFiniteColimits F := Functor.preservesFiniteColimits_of_preservesHomology F
  have : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  exact (F.singleFunctorCompRightDerivedFunctorIso).app
    (SheafOfModules.unit (moduleRings Z.toRingedSpace))

/-- Restriction of the canonical derived pushforward to the full quasi-coherent categories.
Source: Stacks 08D5 and 0A9X (blueprint: lem-sfb-flat-section-coinduction). -/
def flatSectionQCohPushforward {Z W : Scheme.{u}} (i : Z ⟶ W)
    [IsClosedImmersion i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wW} (SheafOfModules.{u} (moduleRings W.toRingedSpace))] :
    schemeDerivedQCohCategory Z ⥤ schemeDerivedQCohCategory W :=
  (schemeDerivedQCohProperty W).lift
    ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i)
    (fun E ↦ schemeDerivedDirectImage_preserves_QCoh i E.obj E.property)

/-- Internal Hom from the ordinary closed-section algebra, with its canonical action on maps.
Source: Stacks 0A77 (blueprint: lem-sfb-flat-section-coinduction). -/
abbrev flatSectionRHomFunctor {Z W : Scheme.{u}} (i : Z ⟶ W)
    [HasDerivedCategory.{wW} (SheafOfModules.{u} (moduleRings W.toRingedSpace))] :
    schemeDerivedCategory W ⥤ schemeDerivedCategory W :=
  ((Functor.const (schemeDerivedCategory W)).obj (op (flatSectionAlgebraObject i))).prod'
    (𝟭 (schemeDerivedCategory W)) ⋙
      derivedInternalHom (Opens.grothendieckTopology W) W.sheaf

/-- Coinduction for a closed section, natural on bounded-below quasi-coherent inputs,
with counit evaluation and the specified multiplication transpose.
Source: Stacks Project, duality.tex, Tags 0A76, 0A77, 0A9X and 0E2T;
more-morphisms.tex, Tags 0695 and 0683.
(blueprint: lem-sfb-flat-section-coinduction).

Proof:
1. The structure sheaf is pseudo-coherent over the identity of Z. Apply
   lem-sfb-flat-ambient-relative-pseudocoherence to Z → W → Z, using p i = id,
   flatness and local finite presentation of p. Exact closed pushforward identifies
   its image with the ordinary algebra B in degree zero.
2. Modules on Z are exactly B-modules on W: the unit-quotient formula and full
   faithfulness of closed pushforward give the equivalence. Maps are B-linear
   because the structure-algebra quotient is locally surjective; the equivalence is exact.
3. By lem-sc-sheaf-coinduction-adjunction, scalar restriction has right adjoint
   Hom(B,-), with action (b φ)(b') = φ(bb') and counit evaluation at one.
   Transfer through the equivalence in step 2. The right adjoint of this exact
   pushforward preserves K-injectives (lem-weil-pbc-right-adjoint-preserves-kinjective).
4. Take a K-injective representative I of M. Chain adjunction preserves homotopies,
   so lem-weil-pbc-kinjective-hom-derived gives an adjunction on unbounded derived
   categories. Exact pushforward identifies the pushed right adjoint with Hom(B,I),
   hence with the recorded derived internal Hom.
5. Pseudo-coherence of B and bounded-below M imply quasi-coherence of RHom(B,M)
   by lem-sc-rhom-supported-qcoherent. Exactness of pushforward and the equivalence
   for modules annihilated by the closed ideal give quasi-coherence on Z.
6. The supplied c(M) and this constructed object represent the same functor on
   D_QCoh(Z). Adjunction gives inverse comparison maps carrying one counit to the
   other. This proves naturality and the displayed evaluation equation.
7. Represent h by a map into the K-injective coinduction complex. Its pushed map g
   is B-linear. Thus g(b)(b') = (b' g(b))(1) = g(b'b)(1) = ξ(bb').
8. Resolve the source B by a K-flat P → B. The fixed canonical tensor-Hom bijection
   uncarries g to P tensor B → M, x tensor b ↦ ξ(q(x)b), precisely the canonical
   derived multiplication followed by ξ. The normalization uses the actual exact
   degree-zero comparison and localization tensor map, not unspecified isomorphisms.
-/
theorem exists_flatSectionCoinduction
    {Z W : Scheme.{u}}
    [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace W] [QuasiSeparatedSpace W]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wW} (SheafOfModules.{u} (moduleRings W.toRingedSpace))]
    (p : W ⟶ Z) [Flat p] [LocallyOfFinitePresentation p]
    (i : Z ⟶ W) [IsClosedImmersion i] (hi : i ≫ p = 𝟙 Z)
    (c : schemeDerivedQCohCategory W ⥤ schemeDerivedQCohCategory Z)
    (adj : flatSectionQCohPushforward i ⊣ c) :
    ∃ Φ : ∀ (M : schemeDerivedQCohCategory W) (_hM : ∃ n : ℤ, M.obj.IsGE n),
        (schemeDerivedDirectImage i).obj (c.obj M).obj ≅
          (flatSectionRHomFunctor i).obj M.obj,
      (∀ (M N : schemeDerivedQCohCategory W)
        (hM : ∃ n : ℤ, M.obj.IsGE n) (hN : ∃ n : ℤ, N.obj.IsGE n) (f : M ⟶ N),
        (schemeDerivedDirectImage i).map (c.map f).hom ≫ (Φ N hN).hom =
          (Φ M hM).hom ≫ (flatSectionRHomFunctor i).map f.hom) ∧
      (∀ (M : schemeDerivedQCohCategory W) (hM : ∃ n : ℤ, M.obj.IsGE n),
        (𝟙 ((schemeDerivedDirectImage i).obj (c.obj M).obj) ⊗ₘ flatSectionAlgebraUnit i) ≫
            schemeDerivedTensorHomEquiv W _ _ M.obj (Φ M hM).hom =
          (𝟙 ((schemeDerivedDirectImage i).obj (c.obj M).obj) ⊗ₘ
              (flatSectionStructureUnitIso W).hom) ≫
            (ρ_ ((schemeDerivedDirectImage i).obj (c.obj M).obj)).hom ≫
              (adj.counit.app M).hom) ∧
      (∀ (M : schemeDerivedQCohCategory W) (hM : ∃ n : ℤ, M.obj.IsGE n)
        (h : flatSectionStructureObject Z ⟶ (c.obj M).obj),
        schemeDerivedTensorHomEquiv W (flatSectionAlgebraObject i)
            (flatSectionAlgebraObject i) M.obj
            ((flatSectionPushforwardStructureIso i).inv ≫
              (schemeDerivedDirectImage i).map h ≫ (Φ M hM).hom) =
          flatSectionDerivedMultiplication i ≫ (flatSectionPushforwardStructureIso i).inv ≫
            (schemeDerivedDirectImage i).map h ≫ (adj.counit.app M).hom) := by
  sorry

end AlgebraicGeometry
