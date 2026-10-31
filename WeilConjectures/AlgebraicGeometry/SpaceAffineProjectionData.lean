/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarDualEvaluationDescent
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
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
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.SiteConstantModuleHomSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Normalized affine scalar adjunction and its projection arrow

Source: Stacks Project, Tags 08IN, 03EK, 06YT and 0B56
(blueprint: def-sfb-affine-scalar-projection-data).

The scalar sheaf, exact derived functor, right derived sections and counit mate
use existing canonical constructions. The records retain their ordinary generator,
structural-action, chain-transpose and K-flat representative normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.AlgebraicSpace

/-- The structural A-action on the regular functions of an actual affine étale chart.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineScalarChart (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    (U : X.SmallEtaleModelᵒᵖ) : A ⟶ X.smallStructureSheaf.obj.obj U :=
  (Scheme.ΓSpecIso A).inv ≫
    Scheme.Γ.map ((X.smallEtaleInclusion.obj U.unop).obj.left.hom).op

/-- Structural scalars commute with chart restriction.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data).
Proof: the triangle of schemes over Spec A commutes. Apply the contravariant regular
functions functor and compose with the canonical Gamma-Spec isomorphism. -/
theorem affineScalarChart_naturality (A : CommRingCat.{u})
    (X : AlgebraicSpace (Spec A)) {U V : X.SmallEtaleModelᵒᵖ} (g : U ⟶ V) :
    affineScalarChart A X U ≫ X.smallStructureSheaf.obj.map g =
      affineScalarChart A X V := by
  sorry

/-- The structural map from the constant A-presheaf to regular functions.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineScalarPresheafMap (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A)) :
    (Functor.const X.SmallEtaleModelᵒᵖ).obj A ⟶ X.smallStructureSheaf.obj where
  app := affineScalarChart A X
  naturality _ _ g := (affineScalarChart_naturality A X g).symm

/-- Sheafification of the structural coefficient map, with its canonical universal lift.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineScalarRingMap (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A)) :
    (constantSheaf X.smallEtaleModelTopology CommRingCat.{u}).obj A ⟶
      X.smallStructureSheaf :=
  ⟨sheafifyLift X.smallEtaleModelTopology (affineScalarPresheafMap A X)
    X.smallStructureSheaf.property⟩

/-- F_N is the existing sheafified scalar tensor of the existing constant module sheaf.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
abbrev affineScalarSheaf (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    (N : ModuleCat.{u} A) : X.SmallModules :=
  SheafOfModules.scalarConstantRealization X.smallEtaleModelTopology A
    X.smallStructureSheaf (affineScalarRingMap A X) N

/-- The actual map F_N to F_N' induced by a module homomorphism.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineScalarSheafMap (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    {N N' : ModuleCat.{u} A} (g : N ⟶ N') :
    affineScalarSheaf A X N ⟶ affineScalarSheaf A X N' :=
  SheafOfModules.scalarConstantRealizationMap X.smallEtaleModelTopology A
    X.smallStructureSheaf (affineScalarRingMap A X) g

/-- The generator b tensor n of F_N on a small affine chart.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineScalarGenerator (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    (N : ModuleCat.{u} A) (U : X.SmallEtaleModelᵒᵖ)
    (b : X.smallStructureSheaf.obj.obj U) (n : N) :
    (affineScalarSheaf A X N).val.obj U :=
  SheafOfModules.scalarConstantGenerator X.smallEtaleModelTopology A
    X.smallStructureSheaf (affineScalarRingMap A X) N U b n

/-- An additive functor applied termwise, with its instance argument explicit.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineProjectionComplex {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) (hF : F.Additive) :
    CochainComplex C ℤ ⥤ CochainComplex D ℤ :=
  letI := hF
  F.mapHomologicalComplex (.up ℤ)

/-- Localization of an exact scalar functor, with no chosen replacement data.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineProjectionDerived (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} X.SmallModules]
    (H : ModuleCat.{u} A ⥤ X.SmallModules) (ha : H.Additive)
    (hl : PreservesFiniteLimits H) (hc : PreservesFiniteColimits H) :
    DerivedCategory (ModuleCat.{u} A) ⥤ X.DerivedModules :=
  letI := ha
  letI := hl
  letI := hc
  H.mapDerivedCategory

/-- The exact scalar functor's specified localization comparison.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineProjectionDerivedComparison (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} X.SmallModules]
    (H : ModuleCat.{u} A ⥤ X.SmallModules) (ha : H.Additive)
    (hl : PreservesFiniteLimits H) (hc : PreservesFiniteColimits H) :
    DerivedCategory.Q ⋙ affineProjectionDerived A X H ha hl hc ≅
      affineProjectionComplex H ha ⋙ DerivedCategory.Q :=
  letI := ha
  letI := hl
  letI := hc
  H.mapDerivedCategoryFactors

/-- The canonical K-injective right derived functor of the specified global sections.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineProjectionRGamma (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} X.SmallModules]
    (G : X.SmallModules ⥤ ModuleCat.{u} A) (ha : G.Additive) :
    X.DerivedModules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  letI := ha
  G.rightDerivedFunctor

/-- The right-derived comparison on actual complexes, retaining the fixed localization units.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineProjectionRGammaComparison (A : CommRingCat.{u})
    (X : AlgebraicSpace (Spec A))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} X.SmallModules]
    (G : X.SmallModules ⥤ ModuleCat.{u} A) (ha : G.Additive)
    (I : CochainComplex X.SmallModules ℤ) :
    DerivedCategory.Q.obj ((affineProjectionComplex G ha).obj I) ⟶
      (affineProjectionRGamma A X G ha).obj (DerivedCategory.Q.obj I) :=
  letI := ha
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I) ≫
      G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app I)

/-- The canonical degree-zero specialization of exact scalar pullback.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineProjectionSingleComparison (A : CommRingCat.{u})
    (X : AlgebraicSpace (Spec A))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} X.SmallModules]
    (H : ModuleCat.{u} A ⥤ X.SmallModules) (ha : H.Additive)
    (hl : PreservesFiniteLimits H) (hc : PreservesFiniteColimits H)
    (ho : ∀ N, H.obj N = affineScalarSheaf A X N) (N : ModuleCat.{u} A) :
    (affineProjectionDerived A X H ha hl hc).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ≅
      (DerivedCategory.singleFunctor X.SmallModules 0).obj (affineScalarSheaf A X N) :=
  letI := ha
  letI := hl
  letI := hc
  (H.mapDerivedCategorySingleFunctor 0).app N ≪≫
    (DerivedCategory.singleFunctor X.SmallModules 0).mapIso (eqToIso (ho N))

/-- The existing K-flat derived tensor, on the equivalent small ringed site.
Source: Stacks 08IN and 06YT
(blueprint: def-sfb-affine-scalar-projection-data). -/
def affineProjectionTensor (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    [HasDerivedCategory.{w} X.SmallModules] :
    X.DerivedModules × X.DerivedModules ⥤ X.DerivedModules :=
  @tensor (X.DerivedModules) _
    (CategoryTheory.RingedDerivedNative.monoidal.{u, u, u, w}
      X.smallEtaleModelTopology X.smallStructureSheaf)

/-- The canonical lax localization tensor map used to normalize derived comparisons.
Source: Stacks 06YT (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineProjectionTensorLocalization (A : CommRingCat.{u})
    (X : AlgebraicSpace (Spec A)) [HasDerivedCategory.{w} X.SmallModules]
    (P Q : CochainComplex X.SmallModules ℤ) :
    (affineProjectionTensor A X).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj
        ((coefficientTotalTensor.{u, u, u} X.smallEtaleModelTopology
          X.smallStructureSheaf).obj (P, Q)) :=
  letI := CategoryTheory.RingedDerivedNative.monoidal.{u, u, u, w}
    X.smallEtaleModelTopology X.smallStructureSheaf
  letI := CategoryTheory.RingedDerivedNative.lax.{u, u, u, w}
    X.smallEtaleModelTopology X.smallStructureSheaf
  Functor.LaxMonoidal.μ DerivedCategory.Q P Q

/-- The specified ordinary adjunction applied to actual complexes.
Source: Stacks 08IN (blueprint: def-sfb-affine-scalar-projection-data). -/
def affineProjectionChainTranspose (A : CommRingCat.{u})
    (X : AlgebraicSpace (Spec A))
    (H : ModuleCat.{u} A ⥤ X.SmallModules) (ha : H.Additive)
    (G : X.SmallModules ⥤ ModuleCat.{u} A) (ga : G.Additive) (ad : H ⊣ G)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (I : CochainComplex X.SmallModules ℤ)
    (f : (affineProjectionComplex H ha).obj P ⟶ I) :
    P ⟶ (affineProjectionComplex G ga).obj I :=
  letI := ha
  letI := ga
  (ad.mapHomologicalComplex (.up ℤ)).homEquiv P I f

/-- The pure tensor in the existing localization tensor of module sheaves.
Source: Stacks 03EK and 08IN
(blueprint: def-sfb-affine-scalar-projection-data). -/
def affineProjectionSheafTmul (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    (M N : X.SmallModules) (U : X.SmallEtaleModelᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) : (M ⊗ N).val.obj U :=
  ((SheafOfModules.tensorObjIsoSheafification (R := X.smallStructureSheaf) M N).inv.val.app U)
    ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.smallStructureRings.obj)).unit.app
      (M.val ⊗ N.val)).app U) (m ⊗ₜ[X.smallStructureSheaf.obj.obj U] n))

/-- The ordinary tensor comparison on total complexes is the existing monoidal
termwise comparison, not a separately chosen chain map.
Source: Stacks 08IN and 06YN
(blueprint: def-sfb-affine-scalar-projection-data). -/
def affineProjectionTotalComparison (A : CommRingCat.{u})
    (X : AlgebraicSpace (Spec A)) (H : ModuleCat.{u} A ⥤ X.SmallModules)
    (ha : H.Additive) (mh : H.Monoidal)
    (G : X.SmallModules ⥤ ModuleCat.{u} A) (ad : H ⊣ G)
    (P Q : CochainComplex (ModuleCat.{u} A) ℤ) :
    (affineProjectionComplex H ha).obj (P ⊗ Q) ⟶
      (coefficientTotalTensor.{u, u, u} X.smallEtaleModelTopology X.smallStructureSheaf).obj
        ((affineProjectionComplex H ha).obj P, (affineProjectionComplex H ha).obj Q) :=
  letI := ha
  letI := mh
  letI := ad.isLeftAdjoint
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) H).app P).app Q

set_option genSizeOf false in
set_option genInjectivity false in
/-- Normalized presentations of the scalar adjunction and its derived tensor comparison.
Every functor is pinned to actual scalar tensors or actual compatible chart sections;
the derived adjunction is pinned to the ordinary chain transpose, and the tensor
comparison is pinned on K-flat representatives. No projection-formula assertion is
included in this record.
Source: Stacks 08IN, 07A4 and 0B56
(blueprint: def-sfb-affine-scalar-projection-data). -/
structure AffineScalarData (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} X.SmallModules] where
  /-- Ordinary scalar extension. -/
  H : ModuleCat.{u} A ⥤ X.SmallModules
  /-- The specified scalar tensor objects. -/
  objects : ∀ N, H.obj N = affineScalarSheaf A X N
  /-- The specified scalar tensor maps. -/
  maps : ∀ {N N' : ModuleCat.{u} A} (g : N ⟶ N'),
    H.map g = eqToHom (objects N) ≫ affineScalarSheafMap A X g ≫
      eqToHom (objects N').symm
  /-- Exactness includes additivity. -/
  additive : H.Additive
  /-- Left exactness of the scalar functor. -/
  limits : PreservesFiniteLimits H
  /-- Right exactness of the scalar functor. -/
  colimits : PreservesFiniteColimits H
  /-- The ordinary scalar functor's monoidal structure. -/
  monoidal : H.Monoidal
  /-- The ordinary tensorator has the balanced pure-tensor formula. -/
  tensor_formula : ∀ (M N : ModuleCat.{u} A) (U : X.SmallEtaleModelᵒᵖ)
      (b c : X.smallStructureSheaf.obj.obj U) (m : M) (n : N),
    ((@Functor.LaxMonoidal.μ _ _ _ _ _ _ H monoidal.toLaxMonoidal M N).val.app U)
      (affineProjectionSheafTmul A X (H.obj M) (H.obj N) U
        ((eqToHom (objects M).symm).val.app U (affineScalarGenerator A X M U b m))
        ((eqToHom (objects N).symm).val.app U (affineScalarGenerator A X N U c n))) =
      (eqToHom (objects (M ⊗ N)).symm).val.app U
        (affineScalarGenerator A X (M ⊗ N) U (b * c) (m ⊗ₜ[A] n))
  /-- Global sections, with values in A-modules. -/
  G : X.SmallModules ⥤ ModuleCat.{u} A
  /-- Global sections are additive. -/
  sections_additive : G.Additive
  /-- Sections are actual compatible chart families. -/
  sections : ∀ M : X.SmallModules, G.obj M ≃ M.sections
  /-- Evaluation respects addition. -/
  sections_add : ∀ (M : X.SmallModules) (x y : G.obj M) (U : X.SmallEtaleModelᵒᵖ),
    (sections M (x + y)).val U = (sections M x).val U + (sections M y).val U
  /-- The A-action is precisely the structural action on every chart. -/
  sections_smul : ∀ (M : X.SmallModules) (a : A) (x : G.obj M)
      (U : X.SmallEtaleModelᵒᵖ),
    (sections M (a • x)).val U =
      affineScalarChart A X U a • @id (M.val.obj U) ((sections M x).val U)
  /-- Maps on global sections are the actual section maps. -/
  sections_map : ∀ {M M' : X.SmallModules} (g : M ⟶ M') (x : G.obj M),
    sections M' (G.map g x) = SheafOfModules.sectionsMap g (sections M x)
  /-- The ordinary scalar/global-sections adjunction. -/
  adjunction : H ⊣ G
  /-- Its transpose sends a scalar generator to b times the corresponding section. -/
  transpose : ∀ (N : ModuleCat.{u} A) (M : X.SmallModules) (g : H.obj N ⟶ M)
      (U : X.SmallEtaleModelᵒᵖ) (b : X.smallStructureSheaf.obj.obj U) (n : N),
    g.val.app U ((eqToHom (objects N).symm).val.app U
      (affineScalarGenerator A X N U b n)) =
        b • @id (M.val.obj U) ((sections M ((adjunction.homEquiv N M g) n)).val U)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The derived extension of the normalized scalar adjunction. All comparisons retain
ordinary transposes and K-flat representative formulas.
Source: Stacks 08IN and 0B56
(blueprint: def-sfb-affine-scalar-projection-data). -/
structure AffineProjectionData (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} X.SmallModules]
    extends AffineScalarData A X where
  /-- The derived adjunction uses the fixed exact and K-injective derived functors. -/
  derivedAdjunction : affineProjectionDerived A X H additive limits colimits ⊣
    affineProjectionRGamma A X G sections_additive
  /-- The derived transpose agrees with localization of the ordinary chain transpose. -/
  derivedTranspose : ∀ (P : CochainComplex (ModuleCat.{u} A) ℤ)
      (I : CochainComplex X.SmallModules ℤ)
      (g : (affineProjectionComplex H additive).obj P ⟶ I),
    derivedAdjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
      ((affineProjectionDerivedComparison A X H additive limits colimits).hom.app P ≫
        DerivedCategory.Q.map g) =
      DerivedCategory.Q.map
        (affineProjectionChainTranspose A X H additive G sections_additive adjunction P I g) ≫
          affineProjectionRGammaComparison A X G sections_additive I
  /-- The canonical pullback tensor comparison is natural in both derived inputs. -/
  tensorComparison : tensor (DerivedCategory (ModuleCat.{u} A)) ⋙
      affineProjectionDerived A X H additive limits colimits ≅
    ((affineProjectionDerived A X H additive limits colimits).prod
      (affineProjectionDerived A X H additive limits colimits)) ⋙ affineProjectionTensor A X
  /-- Its representative characterization uses the native localization tensor maps.
  Both representatives are K-flat for the existing quasi-isomorphism tensor structure. -/
  tensorRepresentative : ∀ (P Q : CochainComplex (ModuleCat.{u} A) ℤ),
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) →
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) →
    (affineProjectionDerived A X H additive limits colimits).map
        (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      (affineProjectionDerivedComparison A X H additive limits colimits).hom.app
        (P ⊗ Q) ≫
      DerivedCategory.Q.map
        (affineProjectionTotalComparison A X H additive monoidal G adjunction P Q) =
    tensorComparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (affineProjectionTensor A X).map
        (Prod.mkHom
          ((affineProjectionDerivedComparison A X H additive limits colimits).hom.app P)
          ((affineProjectionDerivedComparison A X H additive limits colimits).hom.app Q)) ≫
      affineProjectionTensorLocalization A X
        ((affineProjectionComplex H additive).obj P)
        ((affineProjectionComplex H additive).obj Q)

/-- The counit-defined scalar projection map, transported by the canonical degree-zero
pullback comparison. The composite scalar adjunction is p_X = p_SpecA composed with f;
the Stacks projection-composition identity identifies this map with the f-projection map
under the affine derived-sections equivalence.
Source: Stacks 08IN and 0B56
(blueprint: def-sfb-affine-scalar-projection-data). -/
def affineDerivedProjectionMap (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} X.SmallModules]
    (d : AffineProjectionData A X) (E : X.DerivedModules) (N : ModuleCat.{u} A) :
    (affineProjectionRGamma A X d.G d.sections_additive).obj E ⊗
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N ⟶
      (affineProjectionRGamma A X d.G d.sections_additive).obj
        ((affineProjectionTensor A X).obj
          (E, (DerivedCategory.singleFunctor X.SmallModules 0).obj (affineScalarSheaf A X N))) :=
  d.derivedAdjunction.unit.app _ ≫
    (affineProjectionRGamma A X d.G d.sections_additive).map
      (d.tensorComparison.hom.app
        ((affineProjectionRGamma A X d.G d.sections_additive).obj E,
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ≫
        (affineProjectionTensor A X).map
          (Prod.mkHom (d.derivedAdjunction.counit.app E)
            (affineProjectionSingleComparison A X d.H d.additive d.limits d.colimits
              d.objects N).hom))

end AlgebraicGeometry.AlgebraicSpace
