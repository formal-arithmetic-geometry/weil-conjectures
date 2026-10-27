/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.Paper.KFlatScalarComparisonNormalization
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.RingedDerivedTensorAugmentationNaturality
import Sheaf.Algebra.Homology.RingedTensorComparisonExtension
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import Sheaf.CategoryTheory.GeometricModuleConstruction
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Cartesian scalar extension and the canonical tensor pullback square

Source: Stacks Project, sites-modules.tex, Tag 03EL, lemma-tensor-product-pullback;
sites-cohomology.tex, Tags 06YS, 06YT, 06YU, 0G7E and 0FPH.
(blueprint: lem-sfb-cartesian-scalar-tensor-square).

The helpers below name the ordinary balanced maps and their localization coordinates.
All coefficients are arbitrary ring sheaves on the original small pro-etale sites:
objects have universe u+1, morphisms universe u, and modules universe u+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.CartesianScalarTensor

variable {Z : Scheme.{u}} {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}}

/-- Exact scalar restriction preserves finite limits in the existing module category.
Source: Stacks 05RT (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
instance restrictionLimits (a : R ⟶ S) :
    PreservesFiniteLimits (proEtaleRingRestrictScalars a) :=
  proEtaleRingRestrictScalars_preservesFiniteLimits a

/-- Exact scalar restriction preserves finite colimits in the existing module category.
Source: Stacks 05RT (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
instance restrictionColimits (a : R ⟶ S) :
    PreservesFiniteColimits (proEtaleRingRestrictScalars a) :=
  proEtaleRingRestrictScalars_preservesFiniteColimits a

/-- The target coefficient ring with its restricted source action.
Source: Stacks 03EK (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
abbrev coefficient (a : R ⟶ S) : proEtaleRingModules Z R :=
  (proEtaleRingRestrictScalars a).obj
    (SheafOfModules.unit ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))

/-- The restricted coefficient in degree zero, with no resolution of its data.
Source: Stacks 06YU (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
abbrev coefficientComplex (a : R ⟶ S) :=
  (CochainComplex.singleFunctor (proEtaleRingModules Z R) (0 : ℤ)).obj (coefficient a)

/-- Ordinary tensor with the restricted coefficient as first factor.
Source: Stacks 03EK (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
abbrev tensorCoefficient (a : R ⟶ S) :=
  (proEtaleOrdinaryTensor Z R).obj (coefficient a)

/-- The same first-factor tensor in the specified derived tensor presentation.
Source: Stacks 06YU (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
abbrev derivedTensorCoefficient (a : R ⟶ S) (t : ProEtaleTensorModel Z R) :=
  (Functor.curryObj t.tensor).obj (DerivedCategory.Q.obj (coefficientComplex a))

/-- A pure scalar-extension section in the supplied ordinary extension presentation.
Source: Stacks 03EK (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def scalarPure {a : R ⟶ S}
    (m : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} a)
    (M : proEtaleRingModules Z R) (V : Z.ProEtᵒᵖ)
    (s : S.obj.obj V) (p : M.val.obj V) : (m.E.obj M).val.obj V :=
  (eqToHom (m.obj_eq M).symm).val.app V
    ((toSheafify (ProEt.topology Z)
      (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app V
        (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] p))

/-- The ordinary comparison is the identity on balanced generators after restriction.
Source: Stacks 03EK (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def OrdinaryNormalized {a : R ⟶ S}
    (m : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} a)
    (j : m.E ⋙ proEtaleRingRestrictScalars a ≅ tensorCoefficient a) : Prop :=
  ∀ (M : proEtaleRingModules Z R) (V : Z.ProEtᵒᵖ)
    (s : S.obj.obj V) (p : M.val.obj V),
    (j.hom.app M).val.app V (scalarPure m M V s p) =
      proEtaleTensorPair Z R (coefficient a) M V s p

/-- Apply the ordinary comparison in every degree and identify the degree-zero tensor.
Source: Stacks 06YU (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def ordinaryComplexIso {a : R ⟶ S}
    (m : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} a)
    (j : m.E ⋙ proEtaleRingRestrictScalars a ≅ tensorCoefficient a)
    (P : CochainComplex (proEtaleRingModules Z R) ℤ) :=
  (Functor.mapHomologicalComplexCompIso j (.up ℤ)).app P ≪≫
    (CochainComplex.mapBifunctorSingle₁Iso
      (proEtaleOrdinaryTensor Z R) (coefficient a) P).symm

/-- Normalization of e on a flat K-flat P, resolving the possibly nonflat coefficient too.
This equation is equivalent to the one-sided balanced representative formula; it uses
only the existing simultaneous tensor comparison and never assumes B is flat.
Source: Stacks 06YT and 06YU (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def DerivedNormalized {a : R ⟶ S}
    (m : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} a)
    (t : ProEtaleTensorModel Z R)
    (j : m.E ⋙ proEtaleRingRestrictScalars a ≅ tensorCoefficient a)
    (e : m.T ⋙ (proEtaleRingRestrictScalars a).mapDerivedCategory ≅
      derivedTensorCoefficient a t) : Prop :=
  ∀ (P V : CochainComplex (proEtaleRingModules Z R) ℤ)
    (hp : proEtaleFlatRepresentatives Z R P) (hv : proEtaleFlatRepresentatives Z R V)
    (q : V ⟶ coefficientComplex a), QuasiIso q →
    t.representative.hom.app (⟨V, hv⟩, ⟨P, hp⟩) ≫
      t.tensor.map (Prod.mkHom (DerivedCategory.Q.map q) (𝟙 (DerivedCategory.Q.obj P))) ≫
      e.inv.app (DerivedCategory.Q.obj P) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategory.map (m.ε.app P) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategoryFactors.hom.app
        ((m.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap q (𝟙 P) (proEtaleOrdinaryTensor Z R) (.up ℤ) ≫
          (ordinaryComplexIso m j P).inv)

/-- The one-sided tensor coordinates furnished by e and the universal scalar counit.
Source: Stacks 06YT and 06YU (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def representativeIso {a : R ⟶ S}
    (m : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} a)
    (t : ProEtaleTensorModel Z R)
    (j : m.E ⋙ proEtaleRingRestrictScalars a ≅ tensorCoefficient a)
    (e : m.T ⋙ (proEtaleRingRestrictScalars a).mapDerivedCategory ≅
      derivedTensorCoefficient a t)
    (P : CochainComplex (proEtaleRingModules Z R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :=
  (e.app (DerivedCategory.Q.obj P)).symm ≪≫
    (proEtaleRingRestrictScalars a).mapDerivedCategory.mapIso
      (@asIso _ _ _ _ (m.ε.app P) (m.computes P hp)) ≪≫
    (proEtaleRingRestrictScalars a).mapDerivedCategoryFactors.app
      ((m.E.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.mapIso (ordinaryComplexIso m j P)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (RY SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (RX SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (aY : RY ⟶ SY) (aX : RX ⟶ SX)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)

/-- The coefficient identification is induced by cS on inverse-image unit sections.
The compatibility of cR, cS and the scalar maps makes this map RX-linear.
Source: Stacks 03EL (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def CoefficientNormalized
    (k : (proEtaleRingModulePullback f RY RX cR).obj (coefficient aY) ≅ coefficient aX) :
    Prop :=
  ∀ (V : Y.ProEt) (s : SY.obj.obj (Opposite.op V)),
    k.hom.val.app (Opposite.op ((proEtaleBaseChange f).obj V))
      (((proEtaleRingModuleAdjunction f RY RX cR).unit.app (coefficient aY)).val.app
        (Opposite.op V) s) =
      (proEtaleRingDirectImageMap f SY SX cS).hom.app (Opposite.op V) s

/-- The degree-zero localization of the coefficient identification, using exact factors.
Source: Stacks 06YU and 03EL (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def derivedCoefficientIso
    (k : (proEtaleRingModulePullback f RY RX cR).obj (coefficient aY) ≅ coefficient aX) :=
  (proEtaleRingDerivedPullbackFactors f RY RX cR).app (coefficientComplex aY) ≪≫
    DerivedCategory.Q.mapIso
      (((proEtaleRingModulePullback f RY RX cR).mapCochainComplexSingleFunctor 0).app
        (coefficient aY) ≪≫
        (CochainComplex.singleFunctor (proEtaleRingModules X RX) (0 : ℤ)).mapIso k)

/-- The ordinary scalar comparison has precisely the transported balanced tensor formula.
Source: Stacks 03EL (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def BalancedNormalized
    (mY : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} aY)
    (mX : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} aX)
    (χ : mY.E ⋙ proEtaleRingModulePullback f SY SX cS ≅
      proEtaleRingModulePullback f RY RX cR ⋙ mX.E) : Prop :=
  ∀ (M : proEtaleRingModules Y RY) (V : Y.ProEt)
    (s : SY.obj.obj (Opposite.op V)) (p : M.val.obj (Opposite.op V)),
    (χ.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj V))
      (((proEtaleRingModuleAdjunction f SY SX cS).unit.app (mY.E.obj M)).val.app
        (Opposite.op V) (scalarPure mY M (Opposite.op V) s p)) =
      scalarPure mX ((proEtaleRingModulePullback f RY RX cR).obj M)
        (Opposite.op ((proEtaleBaseChange f).obj V))
        ((proEtaleRingDirectImageMap f SY SX cS).hom.app (Opposite.op V) s)
        (((proEtaleRingModuleAdjunction f RY RX cR).unit.app M).val.app (Opposite.op V) p)

/-- The ordinary scalar route, formed from the specified action square and balanced maps.
Source: Stacks 03EL (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def ordinaryRoute
    (comm : cR.hom ≫ aX = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ cS.hom)
    (mY : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
      u + 2, u + 2} aY)
    (mX : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
      u + 2, u + 2} aX)
    (jY : mY.E ⋙ proEtaleRingRestrictScalars aY ≅ tensorCoefficient aY)
    (jX : mX.E ⋙ proEtaleRingRestrictScalars aX ≅ tensorCoefficient aX)
    (χ : mY.E ⋙ proEtaleRingModulePullback f SY SX cS ≅
      proEtaleRingModulePullback f RY RX cR ⋙ mX.E) :
    tensorCoefficient aY ⋙ proEtaleRingModulePullback f RY RX cR ≅
      proEtaleRingModulePullback f RY RX cR ⋙ tensorCoefficient aX :=
  Functor.isoWhiskerRight jY.symm (proEtaleRingModulePullback f RY RX cR) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft mY.E
      (@asIso _ _ _ _
        (proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cR cS comm)
        (proEtaleRingRestrictionPullbackInv_isIso f RY SY RX SX aY aX cR cS comm)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight χ (proEtaleRingRestrictScalars aX) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleRingModulePullback f RY RX cR) jX

section Equations

variable
    (comm : cR.hom ≫ aX = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ cS.hom)
    (mY : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
      u + 2, u + 2} aY)
    (mX : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
      u + 2, u + 2} aX)
    (tY : ProEtaleTensorModel Y RY) (tX : ProEtaleTensorModel X RX)
    (jY : mY.E ⋙ proEtaleRingRestrictScalars aY ≅ tensorCoefficient aY)
    (jX : mX.E ⋙ proEtaleRingRestrictScalars aX ≅ tensorCoefficient aX)
    (eY : mY.T ⋙ (proEtaleRingRestrictScalars aY).mapDerivedCategory ≅
      derivedTensorCoefficient aY tY)
    (eX : mX.T ⋙ (proEtaleRingRestrictScalars aX).mapDerivedCategory ≅
      derivedTensorCoefficient aX tX)
    (k : (proEtaleRingModulePullback f RY RX cR).obj (coefficient aY) ≅ coefficient aX)
    (χ : mY.E ⋙ proEtaleRingModulePullback f SY SX cS ≅
      proEtaleRingModulePullback f RY RX cR ⋙ mX.E)
    (lambda : mY.T ⋙ proEtaleRingDerivedPullback f SY SX cS ≅
      proEtaleRingDerivedPullback f RY RX cR ⋙ mX.T)

/-- Scalar comparison agrees with its balanced ordinary cochain map.
Source: Stacks 03EL and 0FPH (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def ScalarRepresentativeNormalized : Prop :=
  ∀ (P : CochainComplex (proEtaleRingModules Y RY) ℤ),
        proEtaleFlatRepresentatives Y RY P →
        lambda.hom.app (DerivedCategory.Q.obj P) ≫
          mX.T.map ((proEtaleRingDerivedPullbackFactors f RY RX cR).hom.app P) ≫
          mX.ε.app (((proEtaleRingModulePullback f RY RX cR).mapHomologicalComplex
            (.up ℤ)).obj P) =
        (proEtaleRingDerivedPullback f SY SX cS).map (mY.ε.app P) ≫
          (proEtaleRingDerivedPullbackFactors f SY SX cS).hom.app
            ((mY.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso χ (.up ℤ)).hom.app P)

/-- The ordinary composite has the transported balanced generator formula.
Source: Stacks 03EL and 0FPH (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def RoutePureNormalized : Prop :=
  ∀ (M : proEtaleRingModules Y RY) (V : Y.ProEt)
        (s : SY.obj.obj (Opposite.op V)) (p : M.val.obj (Opposite.op V)),
        ((ordinaryRoute f RY SY RX SX aY aX cR cS comm mY mX jY jX χ).hom.app M).val.app
          (Opposite.op ((proEtaleBaseChange f).obj V))
            (((proEtaleRingModuleAdjunction f RY RX cR).unit.app
              ((tensorCoefficient aY).obj M)).val.app (Opposite.op V)
                (proEtaleTensorPair Y RY (coefficient aY) M (Opposite.op V) s p)) =
          proEtaleTensorPair X RX (coefficient aX)
            ((proEtaleRingModulePullback f RY RX cR).obj M)
            (Opposite.op ((proEtaleBaseChange f).obj V))
            ((proEtaleRingDirectImageMap f SY SX cS).hom.app (Opposite.op V) s)
            (((proEtaleRingModuleAdjunction f RY RX cR).unit.app M).val.app
              (Opposite.op V) p)

/-- The specified scalar route equals the canonical tensor pullback route.
Source: Stacks 03EL and 0FPH (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def SquareCommutes : Prop :=
  ∀ A : DerivedCategory (proEtaleRingModules Y RY),
        (proEtaleRingDerivedPullback f RY RX cR).map (eY.inv.app A) ≫
          (proEtaleRingRestrictionDerivedPullback f RY SY RX SX aY aX cR cS comm).inv.app
            (mY.T.obj A) ≫
          (proEtaleRingRestrictScalars aX).mapDerivedCategory.map (lambda.hom.app A) ≫
          eX.hom.app ((proEtaleRingDerivedPullback f RY RX cR).obj A) =
        (proEtaleCanonicalTensorComparison f RY RX cR tY tX).hom.app
          (DerivedCategory.Q.obj (coefficientComplex aY), A) ≫
          tX.tensor.map (Prod.mkHom
            (derivedCoefficientIso f RY SY RX SX aY aX cR k).hom
            (𝟙 ((proEtaleRingDerivedPullback f RY RX cR).obj A)))

/-- The canonical tensor route localizes the same ordinary cochain isomorphism.
Source: Stacks 03EL and 0FPH (blueprint: lem-sfb-cartesian-scalar-tensor-square). -/
def SquareRepresentativeNormalized : Prop :=
  ∀ (P : CochainComplex (proEtaleRingModules Y RY) ℤ)
        (hp : proEtaleFlatRepresentatives Y RY P),
        ∃ hx : proEtaleFlatRepresentatives X RX
          (((proEtaleRingModulePullback f RY RX cR).mapHomologicalComplex (.up ℤ)).obj P),
        (proEtaleRingDerivedPullback f RY RX cR).map
          ((representativeIso mY tY jY eY P hp.1).inv) ≫
          (proEtaleCanonicalTensorComparison f RY RX cR tY tX).hom.app
            (DerivedCategory.Q.obj (coefficientComplex aY), DerivedCategory.Q.obj P) ≫
          tX.tensor.map (Prod.mkHom
            (derivedCoefficientIso f RY SY RX SX aY aX cR k).hom
            ((proEtaleRingDerivedPullbackFactors f RY RX cR).hom.app P)) ≫
          (representativeIso mX tX jX eX _ hx.1).hom =
        (proEtaleRingDerivedPullbackFactors f RY RX cR).hom.app
          (CochainComplex.mapBifunctor (coefficientComplex aY) P
            (proEtaleOrdinaryTensor Y RY)) ≫
          DerivedCategory.Q.map
            (((proEtaleRingModulePullback f RY RX cR).mapHomologicalComplex (.up ℤ)).map
              (CochainComplex.mapBifunctorSingle₁Iso
                (proEtaleOrdinaryTensor Y RY) (coefficient aY) P).hom) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
              (ordinaryRoute f RY SY RX SX aY aX cR cS comm mY mX jY jX χ)
                (.up ℤ)).hom.app P) ≫
          DerivedCategory.Q.map
            (CochainComplex.mapBifunctorSingle₁Iso (proEtaleOrdinaryTensor X RX)
              (coefficient aX)
              (((proEtaleRingModulePullback f RY RX cR).mapHomologicalComplex
                (.up ℤ)).obj P)).inv

end Equations

/-- The two scalar/tensor routes agree, with their ordinary balanced and localized
representatives. All four ring sheaves and both cartesian identifications are arbitrary.
The existential adjunctions below are normalized by their actual cochain units; lambda
is their specified inverse mate, and is also characterized by its scalar counits.

Source: Stacks Project, sites-modules.tex, Tag 03EL, lemma-tensor-product-pullback;
sites-cohomology.tex, Tags 06YS, 06YT, 06YU, 0G7E and 0FPH.
(blueprint: lem-sfb-cartesian-scalar-tensor-square).

Proof plan:
1. Use flat K-flat resolutions (lem-pc-kflat-resolution), the one-sided tensor
comparison (lem-sfb-ringed-tensor-comparison-extension) and augmentation naturality
(lem-sfb-ringed-derived-tensor-augmentation-naturality). Resolve B[0] as well as P.
Naturality identifies the augmentation with the inverse one-sided comparison by
cancelling the tensor of the resolution quasi-isomorphism. B itself need not be flat.
2. The ordinary extension/tensor comparison
(lem-weil-pbc-extension-tensor-comparison) fixes j on balanced generators. Compose its
localization with the normalized scalar counit and one-sided comparison to obtain e.
The localization universal property and site-derived-tensor descent extend e uniquely;
its naturality includes arbitrary derived arrows and inverse quasi-isomorphisms.
3. Cartesian module pullback is exact (def-weil-pbc-proetale-operations) and preserves
flat K-flat representatives (lem-weil-pbc-ringed-pullback-preserves-kflat). Apply the
balanced scalar normalization (lem-sfb-kflat-scalar-comparison-normalization), transported
to these site universes, to obtain chi and lambda with the displayed counit equation.
The action comparison is the recorded lem-weil-pbc-ring-sheaf-change-adjunction map.
4. Apply the derived/ordinary pullback compatibility (Tag 0FPH) to B[0],P and cancel
its invertible one-sided comparisons. The canonical tensor pullback comparison is
therefore represented by the ordinary tensor pullback, followed by k on its first factor.
5. The ordinary scalar route and this tensor route send the inverse-image unit of
s tensor p to cS(s) tensor the inverse-image unit of p. Coefficient compatibility makes
this pairing balanced. Tensor universality and inverse-image adjunction identify the
maps on all sections; their degreewise equations commute with the differentials.
6. Localize this ordinary chain equation. Every unbounded derived object has a flat
K-flat representative. Naturality and cancellation along its localized resolution
extend the equation to every object. The same naturality for cochain maps, including
inverted quasi-isomorphisms, gives independence of representatives. No flatness of aY
or aX, boundedness, or projection-formula hypothesis enters the argument. -/
theorem cartesian_scalar_tensor_square
    (comm : cR.hom ≫ aX = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ cS.hom)
    (mY : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
      u + 2, u + 2} aY)
    (mX : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
      u + 2, u + 2} aX)
    (tY : ProEtaleTensorModel Y RY) (tX : ProEtaleTensorModel X RX) :
    ∃ (jY : mY.E ⋙ proEtaleRingRestrictScalars aY ≅ tensorCoefficient aY)
      (jX : mX.E ⋙ proEtaleRingRestrictScalars aX ≅ tensorCoefficient aX)
      (eY : mY.T ⋙ (proEtaleRingRestrictScalars aY).mapDerivedCategory ≅
        derivedTensorCoefficient aY tY)
      (eX : mX.T ⋙ (proEtaleRingRestrictScalars aX).mapDerivedCategory ≅
        derivedTensorCoefficient aX tX)
      (k : (proEtaleRingModulePullback f RY RX cR).obj (coefficient aY) ≅ coefficient aX)
      (χ : mY.E ⋙ proEtaleRingModulePullback f SY SX cS ≅
        proEtaleRingModulePullback f RY RX cR ⋙ mX.E)
      (lambda : mY.T ⋙ proEtaleRingDerivedPullback f SY SX cS ≅
        proEtaleRingDerivedPullback f RY RX cR ⋙ mX.T)
      (aAdjY : mY.E ⊣ proEtaleRingRestrictScalars aY)
      (aAdjX : mX.E ⊣ proEtaleRingRestrictScalars aX)
      (dY : mY.T ⊣ (proEtaleRingRestrictScalars aY).mapDerivedCategory)
      (dX : mX.T ⊣ (proEtaleRingRestrictScalars aX).mapDerivedCategory),
      OrdinaryNormalized mY jY ∧ OrdinaryNormalized mX jX ∧
      DerivedNormalized mY tY jY eY ∧ DerivedNormalized mX tX jX eX ∧
      CoefficientNormalized f RY SY RX SX aY aX cR cS k ∧
      BalancedNormalized f RY SY RX SX aY aX cR cS mY mX χ ∧
      (∀ (M : proEtaleRingModules Y RY) (V : Y.ProEtᵒᵖ) (p : M.val.obj V),
        (aAdjY.unit.app M).val.app V p = scalarPure mY M V 1 p) ∧
      (∀ (M : proEtaleRingModules X RX) (V : X.ProEtᵒᵖ) (p : M.val.obj V),
        (aAdjX.unit.app M).val.app V p = scalarPure mX M V 1 p) ∧
      (∀ (P : CochainComplex (proEtaleRingModules Y RY) ℤ),
        proEtaleFlatRepresentatives Y RY P →
        dY.unit.app (DerivedCategory.Q.obj P) ≫
          (proEtaleRingRestrictScalars aY).mapDerivedCategory.map (mY.ε.app P) ≫
          (proEtaleRingRestrictScalars aY).mapDerivedCategoryFactors.hom.app
            ((mY.E.mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map ((aAdjY.mapHomologicalComplex (.up ℤ)).unit.app P)) ∧
      (∀ (P : CochainComplex (proEtaleRingModules X RX) ℤ),
        proEtaleFlatRepresentatives X RX P →
        dX.unit.app (DerivedCategory.Q.obj P) ≫
          (proEtaleRingRestrictScalars aX).mapDerivedCategory.map (mX.ε.app P) ≫
          (proEtaleRingRestrictScalars aX).mapDerivedCategoryFactors.hom.app
            ((mX.E.mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map ((aAdjX.mapHomologicalComplex (.up ℤ)).unit.app P)) ∧
      (lambda.inv = SheafOfModules.ScalarPullback.mate dY dX
        (proEtaleRingRestrictionDerivedPullback f RY SY RX SX aY aX cR cS comm).inv) ∧
      ScalarRepresentativeNormalized
        f RY SY RX SX aY aX cR cS mY mX χ lambda ∧
      RoutePureNormalized
        f RY SY RX SX aY aX cR cS comm mY mX jY jX χ ∧
      SquareCommutes
        f RY SY RX SX aY aX cR cS comm mY mX tY tX eY eX k lambda ∧
      SquareRepresentativeNormalized
        f RY SY RX SX aY aX cR cS comm mY mX tY tX jY jX eY eX k χ := by
  sorry

end AlgebraicGeometry.Scheme.CartesianScalarTensor
