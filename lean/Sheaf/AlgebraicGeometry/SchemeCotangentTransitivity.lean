/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.LciCotangentPresentation
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Homology.SingleHomology
import Sheaf.Topology.StandardSheafCotangentFlatModel
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Topology.SheafCotangentComparison
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.Sites.InverseImageDifferentials
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact

/-!
# Scheme cotangent transitivity

Source: Stacks Project, Cotangent Complex, Tags 08T2, 08T4, 08UV and 08QL
(blueprint: lem-sfb-scheme-cotangent-transitivity).

All cotangent objects and chain arrows use the recorded intrinsic standard-resolution
system. The first derived arrow uses its retained derived-pullback counit. No geometric
finiteness or regularity hypothesis enters the transitivity statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false

universe u w

open CategoryTheory CategoryTheory.Limits Pretriangulated Opposite TopologicalSpace
open Algebra.CotangentResolution

namespace AlgebraicGeometry.CotangentPresentation

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The canonical source-functoriality arrow on the intrinsic cotangent complex.
Source: Stacks, Tags 08QL, 08T2 and 08T4
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def sourceArrow {C : Coherence.{u}} (D : System C)
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (derivedPullback a).obj (cotangent (D.model b)) ⟶ cotangent (D.model (a ≫ b)) :=
  derivedChange D (D.square b (a ≫ b) a (𝟙 Z) (Category.comp_id _).symm)

/-- The section-normalized identity comparison on complexes, as an isomorphism.
Source: Stacks, Tags 0095 and 08QL
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def identityComplexIso {X : Scheme.{u}}
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    pullbackComplex (𝟙 X) K ≅ K :=
  letI := (Scheme.Modules.tensorPullbackSectionAdjunction (𝟙 X)).left_adjoint_additive
  (NatIso.mapHomologicalComplex (Scheme.Modules.tensorPullbackSectionId X) (.up ℤ)).app K

/-- The standard base-functoriality arrow, with identity source pullback removed.
Source: Stacks, Tags 08QL and 08T4
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def relativeArrow {C : Coherence.{u}} (D : System C)
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    cotangent (D.model (a ≫ b)) ⟶ cotangent (D.model a) :=
  DerivedCategory.Q.{w}.map
    ((identityComplexIso (sheafComplex (D.model (a ≫ b)))).inv ≫
      D.change (D.square (a ≫ b) a (𝟙 X) b (Category.id_comp _)))

/-- The identity-source identification computed on the same standard complex.
Source: Stacks, Tags 0095 and 08QL
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def sourceIdentity {C : Coherence.{u}} (D : System C)
    {X Z : Scheme.{u}} (b : X ⟶ Z) :
    (derivedPullback (𝟙 X)).obj (cotangent (D.model b)) ⟶ cotangent (D.model b) :=
  (recordedDerivedPullbackCounit (𝟙 X)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (sheafComplex (D.model b))) ≫
    DerivedCategory.Q.{w}.map (identityComplex (sheafComplex (D.model b)))

/-- The degree-zero complex of a module and its canonical H0 identification.
Source: Stacks, Tag 08UV (blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def singleH0Iso {X : Scheme.{u}}
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (DerivedCategory.homologyFunctor.{w} _ 0).obj
      (DerivedCategory.Q.{w}.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≅ M :=
  (DerivedCategory.homologyFunctorFactors _ 0).app _ ≪≫
    (HomologicalComplex.homologyFunctorSingleIso _ (.up ℤ) 0).app M

/-- The augmentation-induced map H0(L) → Ω, with no chosen H0 isomorphism.
Source: Stacks, Tags 08UR and 08UV
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def augmentationH0 {C : Coherence.{u}} (D : System C)
    {X Z : Scheme.{u}} (b : X ⟶ Z) :
    (DerivedCategory.homologyFunctor.{w} _ 0).obj (cotangent (D.model b)) ⟶
      b.relativeDifferentials :=
  (DerivedCategory.homologyFunctor.{w} _ 0).map
      (DerivedCategory.Q.{w}.map (D.augmentation b)) ≫
    (singleH0Iso b.relativeDifferentials).hom

/-- Pullback commutes with forming a degree-zero complex by the standard component map.
Source: Stacks, Tags 0095 and 08UV
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def pullbackSingleIso {X Y : Scheme.{u}} (a : X ⟶ Y)
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :
    pullbackComplex a ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≅
      (HomologicalComplex.single _ (.up ℤ) 0).obj ((Scheme.Modules.tensorPullback a).obj M) :=
  letI := (Scheme.Modules.tensorPullbackSectionAdjunction a).left_adjoint_additive
  (HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.tensorPullback a) (.up ℤ) 0).app M

/-- The canonical derived-to-ordinary pullback map on degree-zero modules.
Source: Stacks, Tags 06YJ and 08UV
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def pullbackSingleComparison {X Y : Scheme.{u}} (a : X ⟶ Y)
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :
    (derivedPullback a).obj
      (DerivedCategory.Q.{w}.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ⟶
    DerivedCategory.Q.{w}.obj
      ((HomologicalComplex.single _ (.up ℤ) 0).obj ((Scheme.Modules.tensorPullback a).obj M)) :=
  (recordedDerivedPullbackCounit a).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≫
    DerivedCategory.Q.{w}.map (pullbackSingleIso a M).hom

/-- The canonical H0 comparison from derived pullback of a cotangent complex.
For a flat source map it is the usual identification with pullback of Ω.
Source: Stacks, Tags 08UV and 06YJ
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def pullbackAugmentationH0 {C : Coherence.{u}} (D : System C)
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (DerivedCategory.homologyFunctor.{w} _ 0).obj
      ((derivedPullback a).obj (cotangent (D.model b))) ⟶
        (Scheme.Modules.tensorPullback a).obj b.relativeDifferentials :=
  (DerivedCategory.homologyFunctor.{w} _ 0).map
      ((derivedPullback a).map (DerivedCategory.Q.{w}.map (D.augmentation b)) ≫
        pullbackSingleComparison a b.relativeDifferentials) ≫
    (singleH0Iso ((Scheme.Modules.tensorPullback a).obj b.relativeDifferentials)).hom

/-- The comparison on the first term of a source-restriction square. It uses
only the recorded pullback associators and the intrinsic cotangent comparison.
Source: Stacks, Tags 08QL and 08SV
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def sourceRestriction {C : Coherence.{u}} (D : System C)
    {X Y Z X' Y' Z' : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (a' : X' ⟶ Y') (b' : Y' ⟶ Z')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (z : Z' ⟶ Z)
    (s : x ≫ a = a' ≫ y) (q : BaseSquare b b' y z) :
    (derivedPullback x).obj ((derivedPullback a).obj (cotangent (D.model b))) ⟶
      (derivedPullback a').obj (cotangent (D.model b')) :=
  (recordedDerivedPullbackComposition x a).hom.app (cotangent (D.model b)) ≫
    (eqToIso (congrArg (fun k : X' ⟶ Y ↦ derivedPullback.{u, w} k) s)).hom.app
      (cotangent (D.model b)) ≫
    (recordedDerivedPullbackComposition a' y).inv.app (cotangent (D.model b)) ≫
    (derivedPullback a').map (derivedChange D q)

/-- Shift compatibility is normalized by the retained tensor-pullback counit.
It therefore refers to the canonical derived shift comparison, rather than an
unrelated isomorphism between shifted objects.
Source: Stacks, Tags 06YJ and 08T4
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def PullbackShiftCompatibility {X Y : Scheme.{u}} (a : X ⟶ Y)
    (σ : (derivedPullback.{u, w} a).CommShift ℤ) : Prop :=
  letI := σ
  letI := (Scheme.Modules.tensorPullbackSectionAdjunction a).left_adjoint_additive
  NatTrans.CommShift (recordedDerivedPullbackCounit a) ℤ

/-- The shifted-object comparison of a specified derived shift structure.
Source: Stacks, Tags 06YJ and 08T4
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
def pullbackShiftHom {X Y : Scheme.{u}} (a : X ⟶ Y)
    (σ : (derivedPullback.{u, w} a).CommShift ℤ) (K : schemeDerivedCategory.{u, w} Y) :
    (derivedPullback a).obj (K⟦(1 : ℤ)⟧) ⟶
      ((derivedPullback a).obj K)⟦(1 : ℤ)⟧ :=
  letI := σ
  ((derivedPullback a).commShiftIso (1 : ℤ)).hom.app K

/-- The complete transitivity and augmentation assertions on the recorded intrinsic
complexes. All maps except the connecting boundary are explicit constructions above.
The restriction fields use arbitrary open-immersion diagrams, so in particular they
include restrictions to smaller opens in any of the three schemes.
Source: Stacks, Tags 08T4, 08UV, 08QL and 08SV
(blueprint: lem-sfb-scheme-cotangent-transitivity). -/
structure TransitivityProperties {C : Coherence.{u}} (D : System C)
    (σ : ∀ {X Y : Scheme.{u}} (a : X ⟶ Y), (derivedPullback.{u, w} a).CommShift ℤ)
    (δ : ∀ {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z),
      cotangent (D.model a) ⟶
        ((derivedPullback a).obj (cotangent (D.model b)))⟦(1 : ℤ)⟧) : Prop where
  shift_compatibility : ∀ {X Y : Scheme.{u}} (a : X ⟶ Y),
    PullbackShiftCompatibility a (σ a)
  distinguished : ∀ {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z),
    Triangle.mk (sourceArrow D a b) (relativeArrow D a b) (δ a b) ∈
      distTriang (schemeDerivedCategory.{u, w} X)
  source_restriction : ∀ {X Y Z X' Y' Z' : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (a' : X' ⟶ Y') (b' : Y' ⟶ Z')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (z : Z' ⟶ Z),
    IsOpenImmersion x → IsOpenImmersion y → IsOpenImmersion z →
    ∀ (s : x ≫ a = a' ≫ y) (qb : BaseSquare b b' y z)
      (qab : BaseSquare (a ≫ b) (a' ≫ b') x z),
    (derivedPullback x).map (sourceArrow D a b) ≫ derivedChange D qab =
      sourceRestriction D a b a' b' x y z s qb ≫ sourceArrow D a' b'
  relative_restriction : ∀ {X Y Z X' Y' Z' : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (a' : X' ⟶ Y') (b' : Y' ⟶ Z')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (z : Z' ⟶ Z),
    IsOpenImmersion x → IsOpenImmersion y → IsOpenImmersion z →
    ∀ (qa : BaseSquare a a' x y) (qab : BaseSquare (a ≫ b) (a' ≫ b') x z),
    (derivedPullback x).map (relativeArrow D a b) ≫ derivedChange D qa =
      derivedChange D qab ≫ relativeArrow D a' b'
  boundary_restriction : ∀ {X Y Z X' Y' Z' : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (a' : X' ⟶ Y') (b' : Y' ⟶ Z')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (z : Z' ⟶ Z),
    IsOpenImmersion x → IsOpenImmersion y → IsOpenImmersion z →
    ∀ (s : x ≫ a = a' ≫ y) (qb : BaseSquare b b' y z) (qa : BaseSquare a a' x y),
    (derivedPullback x).map (δ a b) ≫
        pullbackShiftHom x (σ x) ((derivedPullback a).obj (cotangent (D.model b))) ≫
          (sourceRestriction D a b a' b' x y z s qb)⟦(1 : ℤ)⟧' =
      derivedChange D qa ≫ δ a' b'
  composition : ∀ {W X Y Z : Scheme.{u}}
    (c : W ⟶ X) (a : X ⟶ Y) (b : Y ⟶ Z),
    sourceArrow D (c ≫ a) b ≫
        eqToHom (congrArg (fun k : W ⟶ Z ↦ cotangent (D.model k))
          (Category.assoc c a b)) =
      (recordedDerivedPullbackComposition c a).inv.app (cotangent (D.model b)) ≫
        (derivedPullback c).map (sourceArrow D a b) ≫ sourceArrow D c (a ≫ b)
  identity : ∀ {X Z : Scheme.{u}} (b : X ⟶ Z),
    sourceArrow D (𝟙 X) b ≫
      eqToHom (congrArg (fun k : X ⟶ Z ↦ cotangent (D.model k)) (Category.id_comp b)) =
        sourceIdentity D b
  identity_isIso : ∀ {X Z : Scheme.{u}} (b : X ⟶ Z), IsIso (sourceIdentity D b)
  augmentation : ∀ {X Z : Scheme.{u}} (b : X ⟶ Z), IsIso (augmentationH0 D b)
  augmentation_square : ∀ {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z),
    sourceArrow D a b ≫ DerivedCategory.Q.{w}.map (D.augmentation (a ≫ b)) =
      (derivedPullback a).map (DerivedCategory.Q.{w}.map (D.augmentation b)) ≫
        pullbackSingleComparison a b.relativeDifferentials ≫
          DerivedCategory.Q.{w}.map
            ((HomologicalComplex.single _ (.up ℤ) 0).map
              (b.relativeDifferentialsPullbackMap a))
  flat_identification : ∀ {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z),
    Flat a → IsIso (pullbackAugmentationH0 D a b)
  flat_H0 : ∀ {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z), Flat a →
    (DerivedCategory.homologyFunctor.{w} _ 0).map (sourceArrow D a b) ≫
        augmentationH0 D (a ≫ b) =
      pullbackAugmentationH0 D a b ≫ b.relativeDifferentialsPullbackMap a
  differential_formula : ∀ {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z), Flat a →
    ∀ (V : Y.Opens) (r : Γ(X, a ⁻¹ᵁ V)) (s : Γ(Y, V)),
      (b.relativeDifferentialsPullbackMap a).val.app (op (a ⁻¹ᵁ V))
        (r • b.relativeDifferentialsPullbackGenerator a V s) =
      r • (a ≫ b).relativeDifferentialsDerivation.d (X := op (a ⁻¹ᵁ V)) (a.app V s)

/-- Arbitrary scheme morphisms have the canonical cotangent transitivity triangle,
source-composition and restriction laws, and augmentation to relative differentials.
The existential intrinsic system is the same one as in the recorded lci theorem;
its objects and maps remain fixed by the sectionwise standard-resolution formulas.

Source: Stacks Project, Cotangent Complex, Tags 08T2, 08T4, 08UV and 08QL
(blueprint: lem-sfb-scheme-cotangent-transitivity).

Proof:
1. Use the flat K-flat models of
   lem-sfb-standard-sheaf-cotangent-flat-functorial-model. For an injective map of
   ring sheaves B → C, lem-sfb-injective-sheaf-cotangent-sequence-roof identifies
   the quotient of the standard differential sequence with L(C/B), including
   its arrow. Apply lem-weil-pbc-complex-ses-triangle and
   lem-pur-derived-change-of-rings to obtain the triangle and its boundary.
2. For arbitrary B → C factor through the injective graph B → B × C, and derive
   tensor with C. Projection B × C → C is localization at (0,1). The localization
   clause of lem-trf-affine-cotangent-comparison, exact module sheafification and
   lem-pc-sites-module-sheafification-tensor identify the terms and both arrows
   with the standard ones. The flat functorial models make this compatible with
   restriction. The tensor comparison sends (v tensor d) tensor c to v tensor pr(d)c.
3. On X set A = (ba)⁻¹ O_Z, B = a⁻¹ O_Y and C = O_X. Use
   lem-trf-lci-cotangent-presentation and the normalized/alternating homotopy
   equivalence to identify the intrinsic complexes. Inverse-image compatibility
   in lem-trf-affine-cotangent-comparison and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback identify the first term with
   La* L(Y/Z), with its retained counit. Standard-resolution maps and tensor
   associativity send s tensor dp to s d((ac)-sharp p) along both source-composition
   paths. Identity source maps give the tensor unitor. The same strict maps give
   all open-restriction squares, including the boundary. The universal derived
   shift structure is normalized by commutation with the retained counit.
4. Apply lem-sfb-standard-sheaf-cotangent-augmentation to the structure-ring maps.
   lem-trf-topos-inverse-image-differentials identifies the differential sheaves.
   This proves that augmentation induces H0(L) = Ω and the canonical derived
   augmentation square. If a is flat,
   lem-weil-pbc-flat-module-pullback-exact-pushforward-injective makes ordinary
   pullback exact. Hence pullbackAugmentationH0 is invertible and the H0 square
   identifies H0(u) with r tensor ds mapping to r d(a-sharp s).
   No separation, finiteness, Noetherianity or smoothness enters any step. -/
theorem exists_schemeCotangentTransitivity (C : Coherence.{u}) (κ : Naive.Comparison C) :
    ∃ (D : System C) (F : AffineIdentifications D) (E : LciIdentifications D F κ)
      (σ : ∀ {X Y : Scheme.{u}} (a : X ⟶ Y), (derivedPullback.{u, w} a).CommShift ℤ)
      (δ : ∀ {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z),
        cotangent (D.model a) ⟶
          ((derivedPullback a).obj (cotangent (D.model b)))⟦(1 : ℤ)⟧),
      Properties D F κ E ∧ TransitivityProperties D σ δ := by
  sorry

end AlgebraicGeometry.CotangentPresentation
