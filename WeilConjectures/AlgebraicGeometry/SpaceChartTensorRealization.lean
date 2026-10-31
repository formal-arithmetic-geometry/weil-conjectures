/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.SpaceChartLimitEnlargedSections
public import WeilConjectures.AlgebraicGeometry.AtlasEtaleRestriction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIsoSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Chart adjunctions and the normalized ringed tensor construction

Source: Stacks Project, Modules on Sites, Tags 03D7 and 03D8; Properties of Spaces,
Tags 03G8, 03LV and 03LW (blueprint: lem-trf-space-chart-adjunction-tensor-realization).

The tensor presentation below retains the universal properties of algebraic inverse
image. Scalar extension is the existing sectionwise tensor followed by sheafification.
The conclusion supplies presentations and comparisons, rather than assuming them.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u c v

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped ChangeOfRings

namespace AlgebraicGeometry.AlgebraicSpace

/-- Forgetting commutativity preserves the sheaf condition without enlarging coefficients.
Source: Stacks, Tag 03D7 (blueprint: lem-trf-space-chart-adjunction-tensor-realization).
Proof: the original sheaf cone supplies a limit. Its underlying set of sections is
small in the coefficient universe, so the explicit commutative-ring and ring limit
cones exist even when the site is larger. Forgetting commutativity preserves these
cones, and therefore preserves the sheaf condition. -/
theorem chartTensor_forgetSheaves {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := by
  constructor
  intro P hP
  rw [Presheaf.isSheaf_iff_isLimit] at hP ⊢
  intro U R hR
  obtain ⟨h⟩ := hP R hR
  let F := R.arrows.diagram.op ⋙ P
  let : HasLimit F := ⟨_, h⟩
  let : HasLimit (F ⋙ CategoryTheory.forget CommRingCat) := inferInstance
  let : Small.{u} (F ⋙ CategoryTheory.forget CommRingCat).sections :=
    (Types.hasLimit_iff_small_sections _).1 inferInstance
  let : Small.{u}
      ((F ⋙ forget₂ CommRingCat RingCat) ⋙ CategoryTheory.forget RingCat).sections := by
    change Small.{u} (F ⋙ CategoryTheory.forget CommRingCat).sections
    infer_instance
  let : PreservesLimit F (forget₂ CommRingCat RingCat) :=
    preservesLimit_of_preserves_limit_cone (CommRingCat.limitConeIsLimit F)
      (RingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat RingCat))
  exact ⟨isLimitOfPreserves (forget₂ CommRingCat RingCat) h⟩

attribute [instance] chartTensor_forgetSheaves

/-- Forget a commutative ring sheaf to its ring sheaf.
Source: Stacks, Tag 03D7 (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
abbrev tensorRing {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- Sectionwise scalar extension with the existing restriction and morphism maps.
Source: Stacks, Tag 03CZ (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def chartScalarExtensionPresheaf {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {R B : Sheaf J CommRingCat.{u}} (a : R ⟶ B) :
    SheafOfModules.{u} (tensorRing R) ⥤ PresheafOfModules.{u} (tensorRing B).obj where
  obj M := SheafOfModules.changeOfRingsPresheafOfUniverses.{v, c, u, u} a M
  map {M N} h :=
    { app := fun U ↦ (ModuleCat.extendScalars (a.hom.app U).hom).map (h.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses a M h }
  map_id M := by
    ext U : 1
    exact (ModuleCat.extendScalars (a.hom.app U).hom).map_id _
  map_comp h j := by
    ext U : 1
    exact (ModuleCat.extendScalars (a.hom.app U).hom).map_comp _ _

/-- Scalar extension is sectionwise tensor followed by the existing sheafification.
Source: Stacks, Tag 03CZ (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def chartScalarExtension {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {R B : Sheaf J CommRingCat.{u}} (a : R ⟶ B) :
    SheafOfModules.{u} (tensorRing R) ⥤ SheafOfModules.{u} (tensorRing B) :=
  chartScalarExtensionPresheaf a ⋙ PresheafOfModules.sheafification (𝟙 (tensorRing B).obj)

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- A presentation of the enlarged ringed tensor construction. The commutative rings
are identified with the specified structure rings. Ring inverse image is adjoint to
actual precomposition. Its unit makes module inverse image a pullback over the inverse
image ring. Thus the two inverse images are fixed by universal properties, not arbitrary
functors. The small module universe is retained even on the larger enlarged site.
Source: Stacks, Tags 03D2, 03D7 and 03G8
(blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
structure SpaceRingedTensorData (f : X ⟶ Y) where
  sourceRing : Sheaf X.enlargedEtaleTopology CommRingCat.{u}
  sourceIso : tensorRing sourceRing ≅ X.enlargedStructureSheaf
  targetRing : Sheaf Y.enlargedEtaleTopology CommRingCat.{u}
  targetIso : tensorRing targetRing ≅ Y.enlargedStructureSheaf
  inverseRings : Sheaf Y.enlargedEtaleTopology CommRingCat.{u} ⥤
    Sheaf X.enlargedEtaleTopology CommRingCat.{u}
  ringAdjunction : inverseRings ⊣ enlargedDirectImage f CommRingCat.{u}
  inverseModules : SheafOfModules.{u} (tensorRing targetRing) ⥤
    SheafOfModules.{u} (tensorRing (inverseRings.obj targetRing))
  moduleAdjunction : inverseModules ⊣ SheafOfModules.pushforward
    ((sheafCompose Y.enlargedEtaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).map
      (ringAdjunction.unit.app targetRing))
  sheafification : HasWeakSheafify X.enlargedEtaleTopology AddCommGrpCat.{u}
  localEquivalences : X.enlargedEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}

namespace SpaceRingedTensorData

variable {f : X ⟶ Y} (D : SpaceRingedTensorData f)

/-- The direct-image form of the structural map, using exactly the enlarged model's map.
Source: Stacks, Tag 03G8 (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def structuralDirect : D.targetRing ⟶ (enlargedDirectImage f CommRingCat.{u}).obj
    D.sourceRing :=
  (sheafCompose Y.enlargedEtaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).preimage
    (D.targetIso.hom ≫ enlargedStructuralMap f ≫
      (enlargedDirectImage f RingCat.{u}).map D.sourceIso.inv)

/-- The structural map on the inverse-image ring is the transpose of the specified map.
Source: Stacks, Tag 03D7 (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def structural : D.inverseRings.obj D.targetRing ⟶ D.sourceRing :=
  (D.ringAdjunction.homEquiv D.targetRing D.sourceRing).symm D.structuralDirect

/-- Extend a small-site module and express it over the identified commutative ring.
Source: Stacks, Tags 03H7 and 03G8
(blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def input : Y.Modules ⥤ SheafOfModules.{u} (tensorRing D.targetRing) :=
  (smallEnlargedModuleEquivalence.{u, u} Y).inverse ⋙
    SheafOfModules.restrictScalars D.targetIso.hom

/-- Actual inverse image, scalar extension, then transport back to the small site.
Source: Stacks, Tag 03D7 (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def pullback : Y.Modules ⥤ X.Modules :=
  letI := D.sheafification
  letI := D.localEquivalences
  D.input ⋙ D.inverseModules ⋙ chartScalarExtension D.structural ⋙
    SheafOfModules.restrictScalars D.sourceIso.inv ⋙ smallEnlargedModuleRestriction.{u, u} X

/-- Extend a section using the specified extension counit; no arbitrary extension is used.
Source: Stacks, Tag 03H7 (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def inputSection (M : Y.Modules) (V : Y.EtaleSite) (m : M.val.obj (op V)) :
    (D.input.obj M).val.obj (op ((enlargedSchemeInclusion Y).obj V)) :=
  (((smallEnlargedModuleEquivalence.{u, u} Y).counitIso.inv.app M).val.app (op V)) m

/-- The inverse-image section induced by the actual chart triangle.
Source: Stacks, Tags 03D2 and 03G8
(blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def inverseSection (M : Y.Modules) (V : Y.EtaleSite) (q : ModuleChart f V)
    (m : M.val.obj (op V)) :
    (D.inverseModules.obj (D.input.obj M)).val.obj
      (op ((enlargedSchemeInclusion X).obj q.left)) :=
  (D.inverseModules.obj (D.input.obj M)).val.map (enlargedModuleChartLift f V q).op
    (((D.moduleAdjunction.unit.app (D.input.obj M)).val.app
      (op ((enlargedSchemeInclusion Y).obj V))) (D.inputSection M V m))

/-- A regular function on a scheme chart, expressed in the identified enlarged ring.
Source: Stacks, Tag 03G7 (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def scalar (T : X.EtaleSite) (b : X.structureSheaf.obj.obj (op T)) :
    D.sourceRing.obj.obj (op ((enlargedSchemeInclusion X).obj T)) :=
  D.sourceIso.inv.hom.app (op ((enlargedSchemeInclusion X).obj T))
    ((enlargedStructureRestriction X).inv.hom.app (op T) b)

/-- A pure tensor in the existing tensor SHEAF: the sectionwise tensor is sent through
its sheafification unit. This makes no claim that all sheaf sections are pure tensors.
Source: Stacks, Tags 03CZ and 03D7
(blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def tensorSection (M : Y.Modules) (V : Y.EtaleSite) (q : ModuleChart f V)
    (b : X.structureSheaf.obj.obj (op q.left)) (m : M.val.obj (op V)) :
    (D.pullback.obj M).val.obj (op q.left) :=
  letI := D.sheafification
  letI := D.localEquivalences
  SheafOfModules.scalarExtensionRingIsoTmul.{u + 1, u + 1, u, u} D.structural
    (D.inverseModules.obj (D.input.obj M))
    (op ((enlargedSchemeInclusion X).obj q.left)) (D.inverseSection M V q m)
    (D.scalar q.left b)

end SpaceRingedTensorData

/-- The projection-preserving direct-image comparison, fixed by the all-chart limit.
Source: Stacks, Tags 03G8 and 03H7
(blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def chartTensorDirectImageIso (f : X ⟶ Y) :
    moduleDirectImage f ≅ enlargedSmallModuleDirectImage f :=
  (space_chart_limit_enlarged_sections f).2.2.2.2.choose

/-- A tensor realization with its specified tensor unit and the uniquely unit-compatible
comparison from the chosen chart adjunction. Naturality in modules and restrictions is
included by the natural-isomorphism type; the displayed formulas record it on generators.
Source: Stacks, Tags 03D7 and 03G8
(blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
structure SpaceChartTensorComparison (f : X ⟶ Y) where
  data : SpaceRingedTensorData f
  adjunction : data.pullback ⊣ enlargedSmallModuleDirectImage f
  tensorUnit (M : Y.Modules) (V : Y.EtaleSite) (q : ModuleChart f V)
      (m : M.val.obj (op V)) :
    enlargedModuleChartRestriction f (data.pullback.obj M) V q
        (((adjunction.unit.app M).val.app (op V)) m) =
      data.tensorSection M V q 1 m
  comparison : moduleTensorPullback f ≅ data.pullback
  unitEquation (M : Y.Modules) :
    (moduleTensorAdjunction f).unit.app M ≫
        (chartTensorDirectImageIso f).hom.app ((moduleTensorPullback f).obj M) ≫
        (enlargedSmallModuleDirectImage f).map (comparison.hom.app M) =
      adjunction.unit.app M
  unique (e : moduleTensorPullback f ≅ data.pullback)
      (he : ∀ M : Y.Modules,
        (moduleTensorAdjunction f).unit.app M ≫
            (chartTensorDirectImageIso f).hom.app ((moduleTensorPullback f).obj M) ≫
            (enlargedSmallModuleDirectImage f).map (e.hom.app M) =
          adjunction.unit.app M) : e = comparison
  chartTensor (M : Y.Modules) (V : Y.EtaleSite) (q : ModuleChart f V)
      (b : X.structureSheaf.obj.obj (op q.left)) (m : M.val.obj (op V)) :
    (comparison.hom.app M).val.app (op q.left) (moduleTensorSection f M V q b m) =
      data.tensorSection M V q b m
  restriction (M : Y.Modules) (V : Y.EtaleSite) (q r : ModuleChart f V)
      (a : r ⟶ q) (b : X.structureSheaf.obj.obj (op q.left))
      (m : M.val.obj (op V)) :
    (data.pullback.obj M).val.map a.left.op (data.tensorSection M V q b m) =
      data.tensorSection M V r (X.structureSheaf.obj.map a.left.op b) m
  moduleMap (M N : Y.Modules) (h : M ⟶ N) (V : Y.EtaleSite) (q : ModuleChart f V)
      (b : X.structureSheaf.obj.obj (op q.left)) (m : M.val.obj (op V)) :
    (data.pullback.map h).val.app (op q.left) (data.tensorSection M V q b m) =
      data.tensorSection N V q b (h.val.app (op V) m)

/-- The comparison on chosen left adjoints induced by the three tensor identifications.
Source: Stacks, Tag 03D8 (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def chartTensorInducedComposition (f : X ⟶ Y) (k : Z ⟶ X)
    (F : SpaceChartTensorComparison f) (K : SpaceChartTensorComparison k)
    (C : SpaceChartTensorComparison (k ≫ f))
    (μ : F.data.pullback ⋙ K.data.pullback ≅ C.data.pullback) :
    moduleTensorPullback f ⋙ moduleTensorPullback k ≅ moduleTensorPullback (k ≫ f) :=
  isoWhiskerRight F.comparison (moduleTensorPullback k) ≪≫
    isoWhiskerLeft F.data.pullback K.comparison ≪≫ μ ≪≫ C.comparison.symm

/-- Multiplication of nested local tensor coefficients and insertion of the inner unit.
The composite chart is any chart with the same underlying scheme and the displayed
composite triangle. This uses the existing chart category, without a second chart type.
Source: Stacks, Tag 03D8 (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def ChartTensorCompositionFormula (f : X ⟶ Y) (k : Z ⟶ X)
    (F : SpaceChartTensorComparison f) (K : SpaceChartTensorComparison k)
    (C : SpaceChartTensorComparison (k ≫ f))
    (μ : F.data.pullback ⋙ K.data.pullback ≅ C.data.pullback) : Prop :=
  ∀ (M : Y.Modules) (V : Y.EtaleSite) (q : ModuleChart f V) (r : ModuleChart k q.left)
    (t : (moduleChartTarget (k ≫ f)).obj r.left ⟶ V.obj),
    t.left = r.hom.left ≫ q.hom.left →
    (∀ (a : Z.structureSheaf.obj.obj (op r.left))
        (b : X.structureSheaf.obj.obj (op q.left)) (m : M.val.obj (op V)),
      (μ.hom.app M).val.app (op r.left)
          (K.data.tensorSection (F.data.pullback.obj M) q.left r a
            (F.data.tensorSection M V q b m)) =
        C.data.tensorSection M V (CostructuredArrow.mk (Y := r.left) t)
          (a * moduleChartScalar k q.left r b) m) ∧
    (∀ (e : Z.structureSheaf.obj.obj (op r.left)) (m : M.val.obj (op V)),
      (μ.inv.app M).val.app (op r.left)
          (C.data.tensorSection M V (CostructuredArrow.mk (Y := r.left) t) e m) =
        K.data.tensorSection (F.data.pullback.obj M) q.left r e
          (F.data.tensorSection M V q 1 m))

/-- Restriction on the small étale sites for a chartwise étale map. It is literal
precomposition, with the identity ring map on the unchanged underlying scheme.
Source: Stacks, Tags 03LV and 03LW
(blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def chartTensorEtaleRestriction (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    Y.Modules ⥤ X.Modules :=
  letI := chartwiseEtaleMap_continuous f hf
  SheafOfModules.pushforward (F := chartwiseEtaleMap f hf) ⟨𝟙 _⟩

/-- The chart triangle becomes the actual restriction arrow for an étale map.
Source: Stacks, Tag 03LW (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def chartTensorEtaleArrow (f : X ⟶ Y) (hf : IsChartwiseEtale f)
    (V : Y.EtaleSite) (q : ModuleChart f V) :
    (chartwiseEtaleMap f hf).obj q.left ⟶ V :=
  ObjectProperty.homMk q.hom

/-- The identity triangle on the image of an étale chart.
Source: Stacks, Tag 03LW (blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def chartTensorEtaleSelfChart (f : X ⟶ Y) (hf : IsChartwiseEtale f) (U : X.EtaleSite) :
    ModuleChart f ((chartwiseEtaleMap f hf).obj U) :=
  CostructuredArrow.mk (Y := U) (𝟙 _)

/-- The ring and tensor normalization for étale restriction. The ring isomorphism is
exactly the structural map, so it identifies the inverse-image ring with the restricted
structure ring, including all ring operations and restrictions. The two section formulas
are multiplication and insertion of one, and the last equation is balancing in the
sectionwise tensor BEFORE sheafification, for every inverse-image module section.
Source: Stacks, Tags 03LV and 03LW
(blueprint: lem-trf-space-chart-adjunction-tensor-realization). -/
def ChartTensorEtaleFormula (f : X ⟶ Y) (hf : IsChartwiseEtale f)
    (F : SpaceChartTensorComparison f) : Prop :=
  ∃ ρ : F.data.inverseRings.obj F.data.targetRing ≅ F.data.sourceRing,
    ρ.hom = F.data.structural ∧
    ∃ σ : F.data.pullback ≅ chartTensorEtaleRestriction f hf,
      (∀ (M : Y.Modules) (V : Y.EtaleSite) (q : ModuleChart f V)
          (a : X.structureSheaf.obj.obj (op q.left)) (m : M.val.obj (op V)),
        (σ.hom.app M).val.app (op q.left) (F.data.tensorSection M V q a m) =
          a • M.val.map (chartTensorEtaleArrow f hf V q).op m) ∧
      (∀ (M : Y.Modules) (U : X.EtaleSite)
          (m : M.val.obj (op ((chartwiseEtaleMap f hf).obj U))),
        (σ.inv.app M).val.app (op U) m =
          F.data.tensorSection M ((chartwiseEtaleMap f hf).obj U)
            (chartTensorEtaleSelfChart f hf U) 1 m) ∧
      (∀ (M : Y.Modules) (U : X.EnlargedEtaleSite)
          (a : (F.data.inverseRings.obj F.data.targetRing).obj.obj (op U))
          (m : (F.data.inverseModules.obj (F.data.input.obj M)).val.obj (op U)),
        (1 : F.data.sourceRing.obj.obj (op U)) ⊗ₜ[
            (F.data.inverseRings.obj F.data.targetRing).obj.obj (op U),
            (F.data.structural.hom.app (op U)).hom] (a • m) =
          (F.data.structural.hom.app (op U) a) ⊗ₜ[
            (F.data.inverseRings.obj F.data.targetRing).obj.obj (op U),
            (F.data.structural.hom.app (op U)).hom] m)

/-- The chosen chart adjunction realizes the normalized ringed tensor construction,
including its composition and étale multiplication formulas.
Source: Stacks, Tags 03D7, 03D8, 03G8, 03LV and 03LW
(blueprint: lem-trf-space-chart-adjunction-tensor-realization).
Proof, following the eight steps in the DAG:
1. Extend to the enlarged sites and transport their ringed module adjunction back
   through the normalized module equivalences. The chart-limit theorem identifies
   the direct images by every chart projection, including the coefficient action.
2. The scalar-extension Hom bijection transposes h to x ↦ h(1 tensor x). Together
   with geometric-module transport this gives the tensor unit on every chart as
   the inverse-image section followed by insertion of one and sheafification.
3. Apply unit-compatible uniqueness of left adjoints with the normalized direct-image
   comparison. Naturality of that comparison rewrites the equation as unitEquation.
4. Project this equation to a chart and multiply by its coefficient. Module linearity
   gives chartTensor; functorial restriction and naturality give restriction and moduleMap.
5. The enlarged ringed composition and inverse-image tensor comparisons identify the
   two iterated tensors with C tensor_B (B tensor_R N) and C tensor_R N. The inverse
   image composition comparison preserves their nested local representatives.
6. Send a tensor (b tensor m) to a k-sharp(b) tensor m; the inverse inserts one.
   Balancing proves well-definedness and both inverse identities, first on presheaf
   tensors and then by the universal property of each successive sheafification.
7. Conjugate this natural isomorphism by the three comparisons, exactly as in
   chartTensorInducedComposition. Successive tensor units insert two ones, and the
   composition removes the inner one, fixing the adjunction normalization also for
   identity morphisms. Local tensor formulas determine the comparison uniquely.
8. For an étale map, inverse image is restriction with identical regular functions.
   Tensoring over this same ring identifies with restriction by multiplication, with
   inverse insertion of one. The two composites are identities by the displayed
   balancing relation, which already holds before sheafification. The chart formula
   then identifies the original specified chart-unit tensor with the same product. -/
theorem space_chart_adjunction_tensor_realization (f : X ⟶ Y) (k : Z ⟶ X) :
    (∃ (F : SpaceChartTensorComparison f) (K : SpaceChartTensorComparison k)
        (C : SpaceChartTensorComparison (k ≫ f)),
      ∃! μ : F.data.pullback ⋙ K.data.pullback ≅ C.data.pullback,
        ChartTensorCompositionFormula f k F K C μ) ∧
    (∀ (X' Y' : AlgebraicSpace S) (l : X' ⟶ Y') (hl : IsChartwiseEtale l),
      ∃ L : SpaceChartTensorComparison l, ChartTensorEtaleFormula l hl L) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
