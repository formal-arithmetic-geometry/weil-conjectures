/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.EtaleGradedModuleAlgebra
public import WeilConjectures.TraceFormula.EtaleModuleEvaluationTensorPowers
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
public import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import WeilConjectures.CategoryTheory.Monoidal.TensorInverse
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorPairingIsIso
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.AlgebraicGeometry.RingedTopoiScalarTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Graded evaluation and its ordinary-scheme normalization

Source: Stacks Project, spaces-descent.tex, Tag 0D3C; descent.tex, Tags 03DX and 03LC;
sites-modules.tex, Tags 03D7 and 03EL
(blueprint: lem-trf-graded-evaluation-zariski-etale-comparison).

The comparison functors are restriction to the actual scheme charts and open subschemes.
Their tensor left adjoints retain their units. Evaluation is the specified counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- The inclusion of ordinary small étale schemes into representable-space charts.
It keeps the underlying scheme and all regular functions unchanged.
Source: Stacks, Tags 03DX and 03LC
(blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationSchemeEtale (T : Over S) : T.left.Etale ⥤ (schemeSpace T).EtaleSite where
  obj V := ⟨CostructuredArrow.mk
    (yoneda.map (Over.homMk V.hom : Over.mk (V.hom ≫ T.hom) ⟶ T)),
    (representable_etale_scheme_tests.2.2.2.2.2.2.2.1 _ _ _).2 V.prop⟩
  map a := ObjectProperty.homMk (CostructuredArrow.homMk
    (Over.homMk a.left (by
      change a.left ≫ (_ ≫ _) = _ ≫ _
      rw [← Category.assoc, MorphismProperty.Over.w a])) (by
        change yoneda.map _ ≫ yoneda.map _ = yoneda.map _
        rw [← yoneda.map_comp]
        congr 1
        apply Over.OverMorphism.ext
        exact MorphismProperty.Over.w a))
  map_id V := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply Over.OverMorphism.ext
    rfl
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply Over.OverMorphism.ext
    rfl


/-- Continuity of the actual representable-chart inclusion.
Source: Stacks, Tag 03DX (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison).
Proof: a covering family on either site is a jointly surjective étale family of the same
underlying schemes. Pullback squares and covering equalizers are therefore unchanged. -/
@[instance] theorem evaluationSchemeEtale_continuous (T : Over S) :
    (evaluationSchemeEtale T).IsContinuous T.left.smallEtaleTopology
      (schemeSpace T).etaleTopology := by
  sorry

/-- Restriction to ordinary small étale schemes uses the identity of regular functions.
Source: Stacks, Tag 03DX (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationEtaleRestriction (T : Over S) :
    (schemeSpace T).Modules ⥤ Scheme.Modules.SmallEtaleModules T.left :=
  SheafOfModules.pushforward (F := evaluationSchemeEtale T) ⟨𝟙 _⟩

/-- Restriction between these two presentations of the same ringed site is an equivalence.
Source: Stacks, Tag 03DX (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison).
Proof: Yoneda identifies a chart h_V to h_T with its unique scheme map V to T.
The representable étale scheme test identifies the object predicates. These inverse
site identifications keep all regular functions and covering families, so restriction
is an equivalence for module sheaves. -/
@[instance] theorem evaluationEtaleRestriction_isEquivalence (T : Over S) :
    (evaluationEtaleRestriction T).IsEquivalence := by
  sorry

/-- Proof data for the existing canonical Zariski/small-étale module functors.
Proof: take the context supplied by scheme_zariski_etale_quasiCoherent_equivalence;
its fields assert continuity and existence of the specified adjoint, both propositions.
Source: Stacks, Tags 03FH and 03DX
(blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
theorem evaluationContext (T : Over S) : Scheme.Modules.ZariskiEtaleModuleContext T.left := by
  sorry

/-- Restriction to Zariski opens of the representable algebraic space.
Source: Stacks, Tag 03DX (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationZariskiRestriction (T : Over S) : (schemeSpace T).Modules ⥤ T.left.Modules :=
  evaluationEtaleRestriction T ⋙ (evaluationContext T).restriction

/-- Tensor extension from Zariski modules to representable-space étale modules.
Source: Stacks, Tags 03FH and 03DX
(blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationZariskiExtension (T : Over S) : T.left.Modules ⥤ (schemeSpace T).Modules :=
  (evaluationContext T).extension ⋙ (evaluationEtaleRestriction T).asEquivalence.inverse

/-- The fixed extension/restriction adjunction, retaining its unit and counit.
Source: Stacks, Tag 03FH (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationZariskiAdjunction (T : Over S) :
    evaluationZariskiExtension T ⊣ evaluationZariskiRestriction T :=
  (evaluationContext T).adjunction.comp
    (evaluationEtaleRestriction T).asEquivalence.symm.toAdjunction

/-- The morphism of representable algebraic spaces induced by a scheme morphism over S.
Source: Stacks, Tag 03LC (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationSchemeMap {U T : Over S} (a : U ⟶ T) : schemeSpace U ⟶ schemeSpace T :=
  ObjectProperty.homMk ⟨yoneda.map a⟩

/-- The left comparison is the adjoint mate of the specified right comparison.
Source: Stacks, Tags 03FH and 03LC
(blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationPullbackComparison {U T : Over S} (a : U ⟶ T)
    (r : moduleDirectImage (evaluationSchemeMap a) ⋙ evaluationZariskiRestriction T ≅
      evaluationZariskiRestriction U ⋙ Scheme.Modules.pushforward a.left) :
    evaluationZariskiExtension T ⋙ moduleTensorPullback (evaluationSchemeMap a) ≅
      Scheme.Modules.tensorPullback a.left ⋙ evaluationZariskiExtension U :=
  (((evaluationZariskiAdjunction T).comp
    (moduleTensorAdjunction (evaluationSchemeMap a))).ofNatIsoRight r).leftAdjointUniq
      ((Scheme.Modules.tensorPullbackSectionAdjunction a.left).comp
        (evaluationZariskiAdjunction U))

/-- Homogeneous Zariski direct image is restriction of the specified chart direct image.
Source: Stacks, Tag 0D3C (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationDegree {X : AlgebraicSpace S} (T : Over S) (f : X ⟶ schemeSpace T)
    (B : ℕ → X.Modules) (d : ℕ) : T.left.Modules :=
  (evaluationZariskiRestriction T).obj ((moduleDirectImage f).obj (B d))

/-- A section of an extended Zariski module on an affine chart over its open domain.
Source: Stacks, Tags 03FH and 03DX
(blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationSmallSection (U : Over S) (M : U.left.Modules) (W : U.left.Opens)
    (V : (schemeSpace U).SmallEtaleModel)
    (p : (schemeSpace U).smallEtaleInclusion.obj V ⟶
      (evaluationSchemeEtale U).obj ((gabberOpenEtale U.left).obj W)) (s : Γ(M, W)) :
    ((schemeSpace U).smallModuleRestriction.obj
      ((evaluationZariskiExtension U).obj M)).val.obj (op V) :=
  ((evaluationZariskiExtension U).obj M).val.map p.op
    (((evaluationZariskiAdjunction U).unit.app M).app W s)

/-- Ordinary tensor pullback of a cofan, retaining its specified injections.
Source: Stacks, Tag 0096 (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationOrdinaryPullbackCofan {U T : Over S} (a : U ⟶ T)
    (C : ℕ → T.left.Modules) (c : Cofan C) :
    Cofan (fun n ↦ (Scheme.Modules.tensorPullback a.left).obj (C n)) :=
  Cofan.mk ((Scheme.Modules.tensorPullback a.left).obj c.pt)
    (fun n ↦ (Scheme.Modules.tensorPullback a.left).map (c.inj n))

/-- The ordinary total Zariski evaluation, descended from the actual normalized counits.
Source: Stacks, Tags 0096 and 0D3C
(blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationOrdinaryTotal {U T : Over S} (a : U ⟶ T) (H : ℕ → U.left.Modules)
    (c : Cofan (fun n ↦ (Scheme.Modules.pushforward a.left).obj (H n))) (b : Cofan H)
    (h : IsColimit (evaluationOrdinaryPullbackCofan a _ c)) :
    (Scheme.Modules.tensorPullback a.left).obj c.pt ⟶ b.pt :=
  Cofan.IsColimit.desc h (fun n ↦
    (Scheme.Modules.tensorPullbackSectionAdjunction a.left).counit.app (H n) ≫ b.inj n)

/-- Evaluate directly from the extended Zariski direct-image degree.
Source: Stacks, Tags 03LC and 03D7
(blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationFromZariski {X : AlgebraicSpace S} (T : Over S)
    (f : X ⟶ schemeSpace T) (B : X.Modules) :
    (moduleTensorPullback f).obj ((evaluationZariskiExtension T).obj
      ((evaluationZariskiRestriction T).obj ((moduleDirectImage f).obj B))) ⟶ B :=
  (moduleTensorPullback f).map
      ((evaluationZariskiAdjunction T).counit.app ((moduleDirectImage f).obj B)) ≫
    evaluationCounit f B

/-- The homogeneous products and unit of the Zariski degrees A_d are those of compatible
chart sections: the products and unit CG of the direct images project, on every chart, to
the products of B and to its unit after the chart scalar map, and on the open charts they
are the products and unit AG of A. These are the clauses of graded_evaluation_zariski_etale.
Source: Stacks, Tag 0D3C, the graded section algebra
(blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def IsEvaluationSectionAlgebra {X : AlgebraicSpace S} (T : Over S) (f : X ⟶ schemeSpace T)
    (B : ℕ → X.Modules) (BG : EtaleGradedModuleAlgebra B)
    (CG : EtaleGradedModuleAlgebra (fun d ↦ (moduleDirectImage f).obj (B d)))
    (AG : GradedSheafAlgebra (evaluationDegree T f B)) : Prop :=
  (∀ (m n : ℕ) (V : (schemeSpace T).EtaleSite) (q : ModuleChart f V)
    (s : ((moduleDirectImage f).obj (B m)).val.obj (op V))
    (t : ((moduleDirectImage f).obj (B n)).val.obj (op V)),
    ((moduleDirectImageModel f).projection (B (m + n)) V).app (op q)
        (CG.mul m n V s t) =
      BG.mul m n q.left
        (((moduleDirectImageModel f).projection (B m) V).app (op q) s)
        (((moduleDirectImageModel f).projection (B n) V).app (op q) t)) ∧
  (∀ (V : (schemeSpace T).EtaleSite) (q : ModuleChart f V)
    (r : (schemeSpace T).structureSheaf.obj.obj (op V)),
    ((moduleDirectImageModel f).projection (B 0) V).app (op q)
        (CG.unit.val.app (op V) r) =
      BG.unit.val.app (op q.left) (moduleChartScalar f V q r)) ∧
  (∀ (m n : ℕ) (W : T.left.Opens)
    (s : Γ(evaluationDegree T f B m, W)) (t : Γ(evaluationDegree T f B n, W)),
    @id (((moduleDirectImage f).obj (B (m + n))).val.obj
      (op ((evaluationSchemeEtale T).obj ((gabberOpenEtale T.left).obj W))))
      (AG.mul m n W s t) =
    CG.mul m n ((evaluationSchemeEtale T).obj ((gabberOpenEtale T.left).obj W)) s t) ∧
  (∀ (W : T.left.Opens) (r : Γ(T.left, W)),
    @id (((moduleDirectImage f).obj (B 0)).val.obj
      (op ((evaluationSchemeEtale T).obj ((gabberOpenEtale T.left).obj W))))
      (AG.unit.val.app (op W) r) =
    CG.unit.val.app
      (op ((evaluationSchemeEtale T).obj ((gabberOpenEtale T.left).obj W)))
      (T.left.restrictFunctorΓ.inv.app (op W) r))

/-- Degreewise counit evaluation is a homomorphism of ordinary commutative graded algebras,
and its coproduct descent is the total evaluation.

Source: Stacks, spaces-descent.tex, Tag 0D3C, psi_d and psi; sites-modules.tex,
Tags 03D7 and 03EL (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison).

Proof:
1. Apply lem-trf-graded-qc-section-algebra-construction to the given qc separated map
and quasi-coherent homogeneous sheaves. Restriction to opens gives the degrees A_d;
the products are the products of compatible chart sections and the unit is the
pullback of regular functions followed by the given unit. The Zariski/étale counit
identifies their extensions with the specified direct images, identically on opens.
2. Project the triangle identity of moduleTensorAdjunction to any chart q.
Naturality of the specified chart projections gives the evaluation on the unit
insertion; linearity gives a times the projection of s. The unit-normalized chart
tensor realization identifies this with the usual sheafified tensor construction.
3. A left adjoint preserves coproducts by the Hom universal property. Thus the pulled
cofan is colimiting, and descent of the homogeneous counits is the total evaluation.
Tensor/Hom adjunction implies that products on a pair of coproducts are determined
by all pairs of homogeneous summands; no assertion about arbitrary open sections
commuting with infinite coproducts is used.
4. The canonical ringed tensor comparison sends the pair of local tensors to the
product of their scalar coefficients tensor the homogeneous product. Its inverse
inserts 1; balancing gives both inverse identities. The unit comparison is scalar
multiplication and its inverse inserts 1.
5. Applying step 2 to the product rule of step 4 gives ab times the product of the
two chart projections, which is also the product of their separate evaluations.
The same formula sends the degree-zero unit to the unit. Bilinearity, sheafification
and the tensor universal property extend these identities from local tensors to
module maps, and step 3 extends them to the total coproduct evaluation. -/
theorem graded_evaluation_zariski_etale
    (T : Over S) (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)
    (_hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (_hsep : IsSeparatedPresheafMap f.hom.hom)
    (B : ℕ → X.Modules) (_hB : ∀ d, (B d).IsQuasicoherent)
    (BG : EtaleGradedModuleAlgebra B) :
    ∃ (AG : GradedSheafAlgebra (evaluationDegree T f B))
      (CG : EtaleGradedModuleAlgebra (fun d ↦ (moduleDirectImage f).obj (B d)))
      (PG : EtaleGradedModuleAlgebra
        (fun d ↦ (moduleTensorPullback f).obj ((moduleDirectImage f).obj (B d))))
      (ev : PG.Hom BG),
      (∀ d, (evaluationDegree T f B d).IsQuasicoherent ∧
        IsIso ((evaluationZariskiAdjunction T).counit.app
          ((moduleDirectImage f).obj (B d)))) ∧
      IsEvaluationSectionAlgebra T f B BG CG AG ∧
      (∀ d, ev.degree d = evaluationCounit f (B d)) ∧
      (∀ (d : ℕ) (V : (schemeSpace T).EtaleSite) (q : ModuleChart f V)
        (a : X.structureSheaf.obj.obj (op q.left))
        (s : ((moduleDirectImage f).obj (B d)).val.obj (op V)),
        (ev.degree d).val.app (op q.left)
            (moduleTensorSection f ((moduleDirectImage f).obj (B d)) V q a s) =
          a • @id ((B d).val.obj (op q.left))
            (((moduleDirectImageModel f).projection (B d) V).app (op q) s)) ∧
      (∀ (m n : ℕ) (V : (schemeSpace T).EtaleSite) (q : ModuleChart f V)
        (a b : X.structureSheaf.obj.obj (op q.left))
        (s : ((moduleDirectImage f).obj (B m)).val.obj (op V))
        (t : ((moduleDirectImage f).obj (B n)).val.obj (op V)),
        PG.mul m n q.left
            (moduleTensorSection f ((moduleDirectImage f).obj (B m)) V q a s)
            (moduleTensorSection f ((moduleDirectImage f).obj (B n)) V q b t) =
          moduleTensorSection f ((moduleDirectImage f).obj (B (m + n))) V q
            (a * b) (CG.mul m n V s t)) ∧
      (∀ (V : (schemeSpace T).EtaleSite) (q : ModuleChart f V),
        PG.unit.val.app (op q.left) (1 : X.structureSheaf.obj.obj (op q.left)) =
          moduleTensorSection f ((moduleDirectImage f).obj (B 0)) V q 1
            (CG.unit.val.app (op V) (1 : (schemeSpace T).structureSheaf.obj.obj (op V)))) ∧
      ∃ (c : Cofan (fun d ↦ (moduleDirectImage f).obj (B d))) (b : Cofan B)
        (p : Cofan (fun d ↦ (moduleTensorPullback f).obj ((moduleDirectImage f).obj (B d))))
        (_hc : IsColimit c) (_hb : IsColimit b) (_hp : IsColimit p)
        (hpc : IsColimit (evaluationPullbackCofan f _ c))
        (e : (moduleTensorPullback f).obj c.pt ≅ p.pt),
        (∀ d, (moduleTensorPullback f).map (c.inj d) ≫ e.hom = p.inj d) ∧
        (∀ d, (moduleTensorPullback f).map (c.inj d) ≫ evaluationTotal f B c b hpc =
          ev.degree d ≫ b.inj d) ∧
        ∃ (z : Cofan (fun d ↦ (evaluationZariskiExtension T).obj
              (evaluationDegree T f B d))) (_hz : IsColimit z)
          (q : z.pt ≅ c.pt),
          (∀ d, z.inj d ≫ q.hom =
            ((evaluationZariskiAdjunction T).counit.app
              ((moduleDirectImage f).obj (B d))) ≫ c.inj d) ∧
          ∀ d, (moduleTensorPullback f).map (z.inj d) ≫
              (moduleTensorPullback f).map q.hom ≫ evaluationTotal f B c b hpc =
            evaluationFromZariski T f (B d) ≫ b.inj d := by
  sorry

/-- The actual chart of the inverse image of a Zariski open under a scheme morphism.
Source: Stacks, Tag 03LC (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationOpenChart {U T : Over S} (a : U ⟶ T) (W : T.left.Opens) :
    ModuleChart (evaluationSchemeMap a)
      ((evaluationSchemeEtale T).obj ((gabberOpenEtale T.left).obj W)) :=
  CostructuredArrow.mk
    (Y := (evaluationSchemeEtale U).obj ((gabberOpenEtale U.left).obj (a.left ⁻¹ᵁ W)))
    (CostructuredArrow.homMk
      (Over.homMk (a.left ∣_ W) (by
        change (a.left ∣_ W) ≫ (W.ι ≫ T.hom) = (a.left ⁻¹ᵁ W).ι ≫ U.hom
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc, a.w])) (by
      change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ yoneda.map _
      rw [← yoneda.map_comp, ← yoneda.map_comp]
      congr 1
      apply Over.OverMorphism.ext
      exact morphismRestrict_ι a.left W))

/-- Ordinary-scheme normalization of all degrees, their products and units, and evaluation.
The comparison with B is any specified identification with the extended H; its products
and unit are transported using the actual extension/restriction unit on open sections.

Source: Stacks, descent.tex, Tag 03LC (1),(3); spaces-morphisms.tex, discussion before
lemma-pushforward (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison).

Proof:
6. On an open W both right-adjoint paths have the compatible sections on a^{-1}W.
The projection to this scheme chart is the identity on these sections. The normalized
right comparison is consequently natural for every module. The adjunction mate is
precisely evaluationPullbackComparison, for all modules. For quasi-coherent H the
unit of the Zariski/étale equivalence is invertible, and composing this unit comparison
with the right comparison gives A_d isomorphic to the ordinary pushforward a_*H_d.
The products and unit AG of A_d are those of compatible chart sections of B, as in
IsEvaluationSectionAlgebra. The product of two compatible sections projects to their
product, and the same holds for the unit. Through e and the transport hypotheses these
are the products and unit of H; this proves the two displayed identities for d.
7. Transpose the étale counit through the specified adjunctions and the right comparison.
Its transpose is the identity, so injectivity of the ordinary adjunction Hom bijection
identifies it with the ordinary Zariski counit, transported by the pullback comparison.
Coproduct maps are determined by their summand composites, so the same equality holds
for total evaluation. This includes empty schemes and opens and degree zero. -/
theorem graded_evaluation_ordinary_scheme
    {U T : Over S} (a : U ⟶ T) (_hqc : QuasiCompact a.left) (_hsep : IsSeparated a.left)
    (H : ℕ → U.left.Modules) (_hH : ∀ d, (H d).IsQuasicoherent)
    (HG : GradedSheafAlgebra H) (B : ℕ → (schemeSpace U).Modules)
    (BG : EtaleGradedModuleAlgebra B)
    (e : ∀ d, (evaluationZariskiExtension U).obj (H d) ≅ B d)
    (_hmul : ∀ (m n : ℕ) (W : U.left.Opens) (s : Γ(H m, W)) (t : Γ(H n, W)),
      ((evaluationZariskiAdjunction U).unit.app (H (m + n)) ≫
          (evaluationZariskiRestriction U).map (e (m + n)).hom).app W
          (HG.mul m n W s t) =
        BG.mul m n ((evaluationSchemeEtale U).obj ((gabberOpenEtale U.left).obj W))
          ((((evaluationZariskiAdjunction U).unit.app (H m) ≫
            (evaluationZariskiRestriction U).map (e m).hom).app W s))
          ((((evaluationZariskiAdjunction U).unit.app (H n) ≫
            (evaluationZariskiRestriction U).map (e n).hom).app W t)))
    (_hunit : ∀ (W : U.left.Opens) (r : Γ(U.left, W)),
      ((evaluationZariskiAdjunction U).unit.app (H 0) ≫
          (evaluationZariskiRestriction U).map (e 0).hom).app W
          (HG.unit.val.app (op W) r) =
        BG.unit.val.app
          (op ((evaluationSchemeEtale U).obj ((gabberOpenEtale U.left).obj W)))
          (U.left.restrictFunctorΓ.inv.app (op W) r)) :
    ∃ r : moduleDirectImage (evaluationSchemeMap a) ⋙ evaluationZariskiRestriction T ≅
        evaluationZariskiRestriction U ⋙ Scheme.Modules.pushforward a.left,
      (∀ (M : (schemeSpace U).Modules) (W : T.left.Opens)
        (s : ((evaluationZariskiRestriction T).obj
          ((moduleDirectImage (evaluationSchemeMap a)).obj M)).val.obj (op W)),
        ((r.hom.app M).app W) s =
          ((moduleDirectImageModel (evaluationSchemeMap a)).projection M
            ((evaluationSchemeEtale T).obj ((gabberOpenEtale T.left).obj W))).app
              (op (evaluationOpenChart a W)) s) ∧
      ∃ (j : ∀ d, H d ≅ (evaluationZariskiRestriction U).obj
            ((evaluationZariskiExtension U).obj (H d)))
        (d : ∀ n, evaluationDegree T (evaluationSchemeMap a) B n ≅
          (Scheme.Modules.pushforward a.left).obj (H n))
        (AG : GradedSheafAlgebra (evaluationDegree T (evaluationSchemeMap a) B)),
        (∃ CG : EtaleGradedModuleAlgebra
            (fun k ↦ (moduleDirectImage (evaluationSchemeMap a)).obj (B k)),
          IsEvaluationSectionAlgebra T (evaluationSchemeMap a) B BG CG AG) ∧
        (∀ n, (j n).hom = (evaluationZariskiAdjunction U).unit.app (H n)) ∧
        (∀ n, (d n).hom =
          (evaluationZariskiRestriction T).map
              ((moduleDirectImage (evaluationSchemeMap a)).map (e n).inv) ≫
            r.hom.app ((evaluationZariskiExtension U).obj (H n)) ≫
            (Scheme.Modules.pushforward a.left).map (j n).inv) ∧
        (∀ (m n : ℕ) (W : T.left.Opens)
          (s : Γ(evaluationDegree T (evaluationSchemeMap a) B m, W))
          (t : Γ(evaluationDegree T (evaluationSchemeMap a) B n, W)),
          (d (m + n)).hom.app W (AG.mul m n W s t) =
            HG.mul m n (a.left ⁻¹ᵁ W) ((d m).hom.app W s) ((d n).hom.app W t)) ∧
        (∀ (W : T.left.Opens) (z : Γ(T.left, W)),
          (d 0).hom.app W (AG.unit.val.app (op W) z) =
            HG.unit.val.app (op (a.left ⁻¹ᵁ W)) (a.left.app W z)) ∧
        (∀ n, evaluationFromZariski T (evaluationSchemeMap a) (B n) =
          (evaluationPullbackComparison a r).hom.app
              (evaluationDegree T (evaluationSchemeMap a) B n) ≫
            (evaluationZariskiExtension U).map
              ((Scheme.Modules.tensorPullback a.left).map (d n).hom ≫
                (Scheme.Modules.tensorPullbackSectionAdjunction a.left).counit.app (H n)) ≫
            (e n).hom) ∧
        ∀ (ca : Cofan (evaluationDegree T (evaluationSchemeMap a) B))
          (cz : Cofan (fun n ↦ (Scheme.Modules.pushforward a.left).obj (H n)))
          (ch : Cofan H) (cb : Cofan B)
          (cc : Cofan (fun n ↦ (moduleDirectImage (evaluationSchemeMap a)).obj (B n)))
          (_ha : IsColimit ca) (_hz : IsColimit cz) (_hh : IsColimit ch)
          (_hb : IsColimit cb) (_hc : IsColimit cc)
          (hp : IsColimit (evaluationPullbackCofan (evaluationSchemeMap a) _ cc))
          (hzp : IsColimit (evaluationOrdinaryPullbackCofan a _ cz))
          (q : (evaluationZariskiExtension T).obj ca.pt ≅ cc.pt)
          (x : ca.pt ≅ cz.pt) (y : (evaluationZariskiExtension U).obj ch.pt ≅ cb.pt)
          (_hq : ∀ n, (evaluationZariskiExtension T).map (ca.inj n) ≫ q.hom =
            ((evaluationZariskiAdjunction T).counit.app
              ((moduleDirectImage (evaluationSchemeMap a)).obj (B n))) ≫ cc.inj n)
          (_hx : ∀ n, ca.inj n ≫ x.hom = (d n).hom ≫ cz.inj n)
          (_hy : ∀ n, (evaluationZariskiExtension U).map (ch.inj n) ≫ y.hom =
            (e n).hom ≫ cb.inj n),
          (moduleTensorPullback (evaluationSchemeMap a)).map q.hom ≫
              evaluationTotal (evaluationSchemeMap a) B cc cb hp =
            (moduleTensorPullback (evaluationSchemeMap a)).map
                ((evaluationZariskiExtension T).map x.hom) ≫
              (evaluationPullbackComparison a r).hom.app cz.pt ≫
              (evaluationZariskiExtension U).map (evaluationOrdinaryTotal a H cz ch hzp) ≫
              y.hom := by
  sorry

/-- View a power identification on the actual small affine charts, using the counit of
restriction and extension between presentations of the étale site.
Source: Stacks, Tags 039Z and 03EL
(blueprint: lem-trf-graded-evaluation-zariski-etale-comparison). -/
def evaluationPowerComparison (U : Over S) (H : U.left.Modules)
    (L : (schemeSpace U).Modules) (n : ℕ)
    (e : (evaluationZariskiExtension U).obj (H.tensorPow n) ≅
      evaluationLinePower (schemeSpace U) L n) :
    (schemeSpace U).smallModuleRestriction.obj
      ((evaluationZariskiExtension U).obj (H.tensorPow n)) ≅
        evaluationSmallPower (schemeSpace U) L n :=
  (schemeSpace U).smallModuleRestriction.mapIso e ≪≫
    (schemeSpace U).smallModuleEquivalence.counitIso.app
      (evaluationSmallPower (schemeSpace U) L n)

/-- A scheme line module corresponds to the tensor powers of the ordinary invertible
module, including degree zero, with the canonical concatenation products.

Source: Stacks, descent.tex, Tags 03DX (2), 05VG (rank one), and sites-modules.tex,
Tag 03EL (blueprint: lem-trf-graded-evaluation-zariski-etale-comparison).

Proof:
8. The line-module clause of the Zariski/étale quasi-coherent equivalence supplies the
ordinary invertible H and its extension identification with L. The normalized ringed
tensor comparison identifies extension of the structure module with the structure
module, by multiplication, in degree zero. Inductively its binary comparison identifies
extension of H tensor H^n with L tensor L^n; the inverse inserts the unit coefficient.
On the small affine étale model this is the same sheaf tensor and the restriction
equivalence retains all chart regular functions. Both paths for a product in degrees
m,n concatenate the same m+n factors with the same scalar coefficient. The tensor
universal property and sheafification identify these paths on all sections. In degree
zero the map is the actual regular-functions pullback, so both unit products agree.
Transporting through the small-module equivalence gives the claimed isomorphisms on
the original étale site. Applying restriction identifies the corresponding H_d with
H tensor powers; the normalized equivalence gives their inverse identification.
Empty schemes and degree zero are included; there are no graded cochain signs. -/
theorem graded_evaluation_line_powers (U : Over S) (L : (schemeSpace U).Modules)
    (_hL : (schemeSpace U).IsLineModule L) :
    ∃ (H : U.left.Modules) (_hH : H.IsInvertible)
      (i : (evaluationZariskiExtension U).obj H ≅ L)
      (e : ∀ n, (evaluationZariskiExtension U).obj (H.tensorPow n) ≅
        evaluationLinePower (schemeSpace U) L n),
      ((evaluationPowerComparison U H L 1 (e 1)).hom ≫
          (MonoidalCategory.rightUnitor ((schemeSpace U).smallModuleRestriction.obj L)).hom =
        (schemeSpace U).smallModuleRestriction.map
          ((evaluationZariskiExtension U).map (MonoidalCategory.rightUnitor H).hom ≫ i.hom)) ∧
      (∀ (m n : ℕ) (W : U.left.Opens) (V : (schemeSpace U).SmallEtaleModel)
        (p : (schemeSpace U).smallEtaleInclusion.obj V ⟶
          (evaluationSchemeEtale U).obj ((gabberOpenEtale U.left).obj W))
        (s : Γ(H.tensorPow m, W)) (t : Γ(H.tensorPow n, W)),
        (evaluationPowerComparison U H L (m + n) (e (m + n))).hom.val.app (op V)
            (evaluationSmallSection U (H.tensorPow (m + n)) W V p
              ((H.tensorPowAddIso m n).inv.app W (Scheme.Modules.tmulSection s t))) =
          (evaluationPowerAddIso ((schemeSpace U).smallModuleRestriction.obj L) m n).inv.val.app
            (op V)
            (evaluationSmallTmul (schemeSpace U)
              (evaluationSmallPower (schemeSpace U) L m)
              (evaluationSmallPower (schemeSpace U) L n) V
              ((evaluationPowerComparison U H L m (e m)).hom.val.app (op V)
                (evaluationSmallSection U (H.tensorPow m) W V p s))
              ((evaluationPowerComparison U H L n (e n)).hom.val.app (op V)
                (evaluationSmallSection U (H.tensorPow n) W V p t)))) ∧
      (∀ (W : U.left.Opens) (V : (schemeSpace U).SmallEtaleModel)
        (p : (schemeSpace U).smallEtaleInclusion.obj V ⟶
          (evaluationSchemeEtale U).obj ((gabberOpenEtale U.left).obj W))
        (r : Γ(U.left, W)),
        (evaluationPowerComparison U H L 0 (e 0)).hom.val.app (op V)
            (evaluationSmallSection U (H.tensorPow 0) W V p
              (Scheme.Modules.unitSectionsEquiv W r)) =
          @id ((evaluationSmallPower (schemeSpace U) L 0).val.obj (op V))
            ((schemeSpace U).structureSheaf.obj.map p.op
              (U.left.restrictFunctorΓ.inv.app (op W) r))) ∧
      ∀ n, Nonempty
        ((evaluationZariskiRestriction U).obj (evaluationLinePower (schemeSpace U) L n) ≅
          H.tensorPow n) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
