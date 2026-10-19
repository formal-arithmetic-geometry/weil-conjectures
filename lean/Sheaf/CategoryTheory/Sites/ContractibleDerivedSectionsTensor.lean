/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.CategoryTheory.Sites.Over

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.FlatTruncationTower
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.TelescopeColimit
import WeilConjectures.Algebra.Homology.TruncationTelescope
import Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition
import Sheaf.CategoryTheory.PartitionRefinementSheafification
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Topology.StoneanProjective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
/-!
# Derived tensor evaluation on contractible objects

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 4.1(1);
Stacks Project, Tags 0F63, 06YS and 0FPT
(blueprint: lem-zl-contractible-derived-sections-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r t

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (U : Cᵒᵖ)

/-- The actual section functor with its coefficient action.
Source: HRS Lemma 4.1(1), Stacks 03DA
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
abbrev contractibleModuleEvaluation :
    RingedTensorModules.{c, v, r} J R ⥤ ModuleCat.{max c v r} (R.obj.obj U) :=
  SheafOfModules.evaluation.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U

/-- Evaluation on complexes is additive, as both forgetful and pointwise evaluation are.
Source: Stacks 03DA (blueprint: lem-zl-contractible-derived-sections-tensor). -/
instance contractibleModuleEvaluation_additive :
    (contractibleModuleEvaluation.{c, v, r} J R U).Additive :=
  inferInstanceAs ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ U).Additive)

variable [HasDerivedCategory.{max c v r} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{max c v r} (ModuleCat.{max c v r} (R.obj.obj U))]

/-- The signed braiding on the ordinary derived category of section modules.
Source: Stacks 0FPT (blueprint: lem-zl-contractible-derived-sections-tensor). -/
abbrev contractibleSectionsBraiding :
    BraidedCategory (DerivedCategory (ModuleCat.{max c v r} (R.obj.obj U))) :=
  DerivedMonoidal.braidedCategory' DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max c v r} (R.obj.obj U)) (ComplexShape.up ℤ))

variable
  [hlim : PreservesFiniteLimits (contractibleModuleEvaluation.{c, v, r} J R U)]
  [hfin : PreservesFiniteColimits (contractibleModuleEvaluation.{c, v, r} J R U)]

/-- The type of ordinary total-complex section pairings.
Source: HRS Lemma 4.1(1), Stacks 06YN
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
abbrev ContractibleSectionsPairing :=
  ∀ P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
      ((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ⊗
        ((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Q ⟶
        ((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q))

/-- The section pairing on every pure-tensor summand, prior to localization.
Source: HRS Lemma 4.1(1), Stacks 03EK and 06YN
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
def ContractibleSectionsPairingFormula
    (pairing : ContractibleSectionsPairing.{c, v, r} J R U) : Prop :=
  ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (h : p + q = n)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      ((pairing P Q).f n)
        ((CochainComplex.ιMapBifunctor
          (((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q)
          (curriedTensor (ModuleCat.{max c v r} (R.obj.obj U))) p q n h)
            (x ⊗ₜ[R.obj.obj U] y)) =
        coefficientTensorGenerator.{r, c, v} J R P Q p q n h U x y

/-- The strong monoidal structure on termwise derived evaluation.
Source: HRS Lemma 4.1(1), Stacks 06YU
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
abbrev ContractibleSectionsMonoidal
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, max c v r} J R)) :=
  @Functor.Monoidal
    (DerivedCategory (RingedTensorModules.{c, v, r} J R)) _ S.monoidal
    (DerivedCategory (ModuleCat.{max c v r} (R.obj.obj U))) _ _
    (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategory

/-- Normalization of the derived tensorator by the ordinary section pairing and
by the canonical derived-to-ordinary module tensor comparison.
Source: HRS Lemma 4.1(1), Stacks 06YU
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
def ContractibleSectionsTensorFormula
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, max c v r} J R))
    (T : CoefficientTensorModels.{r, c, v, max c v r} J R S)
    (monoidal : ContractibleSectionsMonoidal.{c, v, r} J R U S)
    (pairing : ContractibleSectionsPairing.{c, v, r} J R U) : Prop :=
  ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
        (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
        (J := J) (R := R) Q),
      (((contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategoryFactors.hom.app P) ⊗ₘ
        ((contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategoryFactors.hom.app Q)) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)
            (((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Q) ≫ DerivedCategory.Q.map (pairing P Q) =
        monoidal.μ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
          (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategory.map
            ((T.iso J R S P Q hP hQ).inv) ≫
          (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategoryFactors.hom.app
            ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q))

/-- The braiding square for the specified derived evaluation tensorator.
Source: HRS Lemma 4.1(1), Stacks 0FPT
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
def ContractibleSectionsSymmetryFormula
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, max c v r} J R))
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal)
    (monoidal : ContractibleSectionsMonoidal.{c, v, r} J R U S) : Prop :=
  ∀ K L : DerivedCategory (RingedTensorModules.{c, v, r} J R),
    monoidal.μ K L ≫
        (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategory.map
          ((β.toBraidedCategory.braiding K L).hom) =
      ((contractibleSectionsBraiding.{c, v, r} J R U).braiding
        ((contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategory.obj K)
        ((contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategory.obj L)).hom ≫
          monoidal.μ L K

/-- The ordinary comparison of the actual degree-zero coefficient complexes.
Source: HRS Lemma 4.1(1), Stacks 0FPT
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
abbrev ContractibleSectionsUnitComplex :=
  (𝟙_ (CochainComplex (ModuleCat.{max c v r} (R.obj.obj U)) ℤ)) ≅
    ((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (ringedTensorUnitComplex.{c, v, r} J R)

/-- Scalar normalization of the ordinary unit comparison.
Source: HRS Lemma 4.1(1), Stacks 0FPT
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
def ContractibleSectionsUnitScalarFormula
    (unitComplex : ContractibleSectionsUnitComplex.{c, v, r} J R U) : Prop :=
  ∀ a : R.obj.obj U,
    (unitComplex.hom.f 0)
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (ModuleCat.of (R.obj.obj U) (R.obj.obj U))).inv a) =
      ringedTensorUnitSection.{c, v, r} J R U a

/-- The derived unit is the localization of the scalar-normalized ordinary unit.
Source: HRS Lemma 4.1(1), Stacks 06YU and 0FPT
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
def ContractibleSectionsUnitFormula
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, max c v r} J R))
    (T : CoefficientTensorModels.{r, c, v, max c v r} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal)
    (H : RingedDerivedTensorCoherence.{c, v, r, max c v r} J R S T β)
    (monoidal : ContractibleSectionsMonoidal.{c, v, r} J R U S)
    (unitComplex : ContractibleSectionsUnitComplex.{c, v, r} J R U) : Prop :=
  monoidal.ε ≫
      (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategory.map H.unitIso.hom ≫
      (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategoryFactors.hom.app
        (ringedTensorUnitComplex.{c, v, r} J R) =
    Functor.LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map unitComplex.hom

/-- The canonical termwise localization, with its fixed unit, is total right derived sections.
Source: HRS Lemma 4.1(1), Stacks 079P
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
def ContractibleSectionsRightDerived : Prop :=
  Functor.IsRightDerivedFunctor
    (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategory
      (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (RingedTensorModules.{c, v, r} J R) (ComplexShape.up ℤ))

/-- The canonical strong symmetric monoidal comparison, normalized before localization.
The pairing field is uniquely fixed by its pure-tensor summand equation; the comparison
field identifies the tensorator with that pairing, including the derived-to-ordinary
module tensor map. Thus this is not the existence of an unspecified tensor isomorphism.
The source tensor and all its constraints are the recorded K-flat model.

Source: HRS Lemma 4.1(1), Stacks 06YU and 0FPT
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
structure ContractibleDerivedSectionsTensorData
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, max c v r} J R))
    (T : CoefficientTensorModels.{r, c, v, max c v r} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal)
    (H : RingedDerivedTensorCoherence.{c, v, r, max c v r} J R S T β) where
  /-- Termwise sections, localized, are the total right derived functor. -/
  rightDerived : ContractibleSectionsRightDerived.{c, v, r} J R U
  /-- The unit and all tensor comparisons are invertible and associative and unital. -/
  monoidal : ContractibleSectionsMonoidal.{c, v, r} J R U S
  /-- Compatibility with the recorded Koszul symmetry. -/
  symmetry : ContractibleSectionsSymmetryFormula.{c, v, r} J R U S β monoidal
  /-- The ordinary section pairing of the signed total complexes. -/
  pairing : ContractibleSectionsPairing.{c, v, r} J R U
  /-- On every summand the pairing sends x tensor y to the sheafified tensor of sections. -/
  pairing_tmul : ContractibleSectionsPairingFormula.{c, v, r} J R U pairing
  /-- The derived comparison is precisely the localized section pairing. -/
  tensor_model : ContractibleSectionsTensorFormula.{c, v, r} J R U S T monoidal pairing
  /-- The coefficient ring in degree zero is evaluated identically on scalars. -/
  unitComplex : ContractibleSectionsUnitComplex.{c, v, r} J R U
  /-- The ordinary unit comparison sends a scalar to the same scalar section. -/
  unit_scalar : ContractibleSectionsUnitScalarFormula.{c, v, r} J R U unitComplex
  /-- Normalization of the derived unit by the same degree-zero identity. -/
  unit_model :
    ContractibleSectionsUnitFormula.{c, v, r} J R U S T β H monoidal unitComplex

omit hlim hfin in
/-- Exact, cocontinuous evaluation and its canonical unbounded monoidal derived functor.
The existential structures express conclusions, not assumptions on evaluation. The selected
source tensor is required to carry the full recorded representative characterization.

Source: HRS Lemma 4.1(1), Stacks 0F63 and 0FPT
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
def ContractibleDerivedSectionsTensor : Prop :=
  ∃ (hlim : PreservesFiniteLimits (contractibleModuleEvaluation.{c, v, r} J R U))
    (hfin : PreservesFiniteColimits (contractibleModuleEvaluation.{c, v, r} J R U)),
    PreservesColimitsOfSize.{max c v r, max c v r}
      (contractibleModuleEvaluation.{c, v, r} J R U) ∧
    ∃ (S : CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, max c v r} J R))
      (T : CoefficientTensorModels.{r, c, v, max c v r} J R S)
      (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
        _ S.monoidal) (H : RingedDerivedTensorCoherence.{c, v, r, max c v r} J R S T β),
      Nonempty (ContractibleDerivedSectionsTensorData.{c, v, r} J R U
        (hlim := hlim) (hfin := hfin) S T β H)

end CategoryTheory

namespace AlgebraicGeometry

/-- Evaluation on either specified contractible site is exact and preserves all small
colimits. Termwise evaluation computes total right derived sections on unbounded complexes.
The canonical tensor and unit comparisons are invertible and coherent. The coefficient
ring sheaf is arbitrary; in particular it need not come from a condensed ring.

Source: Hemo--Richarz--Scholbach, Constructible sheaves, proof of Lemma 4.1(1);
Stacks Project, Tags 098H, 0F63, 03DA, 03DB, 00HK, 077J, 06YS, 06YU and 0FPT
(blueprint: lem-zl-contractible-derived-sections-tensor).

Proof (the node's nine steps):
1. In the affine case det-pe-wcb-clopen-partition refines each cover by a finite
   clopen partition. In the profinite case det-pe-stonean-projective splits the
   surjection from the finite disjoint union, and inverse images give that partition.
2. Apply lem-zl-partition-refinement-sheafification to sectionwise colimit presheaves.
   Products of rings split modules by orthogonal idempotents, so these presheaves
   preserve finite disjoint unions and send the empty object to zero. Module
   sheafification has the set sheafification as underlying sets, by
   def-weil-presheaf-modules-sheafification and lem-pc-sites-sheafification-underlying-sets.
   Thus sheafification does not change their value at the terminal object. Kernels
   are sectionwise by lem-weil-pbc-module-sheaves-colimits-forgetful. This proves
   exactness and preservation of every small colimit, including the empty one.
3. Exact evaluation preserves cohomology and quasi-isomorphisms of all complexes.
   Its localization therefore computes RΓ: prop-pur-kinjective-resolutions-exist
   gives a resolution and def-sfb-right-derived-functor computes it there. Evaluation
   of its quasi-isomorphism is again a quasi-isomorphism, with no boundedness needed.
4. Apply the same finite-partition calculation to the tensor presheaf. Mixed
   tensors over the product ring vanish by the orthogonal idempotents. The ordinary
   section pairing and the identity on the coefficient ring are consequently invertible.
5. For a finite relation in sections of a flat sheaf, form the kernel of the
   corresponding row map from O^n to O. Flat tensor and exact sections lift the relation
   to a finite sum of pure tensors. Their coefficients trivialize it, so
   lem-weil-pbc-flat-equational-criterion proves flatness of the section module.
6. Take the compatible bounded-above flat tower of lem-pc-flat-truncation-tower.
   Its telescope is K-flat by lem-pc-kflat-closure; lem-pc-complex-hocolim-colimit and
   lem-pc-kflat-hocolim-truncations show it is a resolution of the original complex.
7. Evaluation preserves the sums and cone of this telescope. Its evaluated tower
   has bounded-above flat terms by step 5. The same K-flat closure theorem over the
   section ring makes the evaluated telescope K-flat. Exactness preserves its resolution.
8. Resolve both factors this way. Evaluation of their total tensor is the total
   tensor of their evaluations, by steps 2 and 4, including the signed differential.
   lem-weil-pbc-site-derived-tensor-descent identifies this with the canonical derived
   comparison, which is therefore invertible for all unbounded factors.
9. Resolving-class localization makes these pairings natural in all derived maps.
   The constraints of lem-sf-ringed-derived-closed-symmetric-monoidal are reassociation,
   the sign (-1)^(pq), and scalar multiplication on representatives. The section
   pairing preserves each formula. The unit is the identity on A[0]. These equations
   give the associativity, symmetry and unit compatibilities recorded in the data. -/
theorem contractible_derived_sections_tensor :
    (∀ (X : Scheme.{t}) [IsAffine X]
      [IsWContractibleRing Γ(X, ⊤)]
      (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max (t + 1) r})
      [HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{max (t + 1) r}]
      [(Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max (t + 1) r}]
      [HasDerivedCategory.{max (t + 1) r}
        (RingedTensorModules.{t + 1, t, r} (Scheme.ProEt.topology X) R)]
      [HasDerivedCategory.{max (t + 1) r}
        (ModuleCat.{max (t + 1) r} (R.obj.obj (op (Scheme.ProEt.mk (𝟙 X)))))],
      ContractibleDerivedSectionsTensor.{t + 1, t, r} (Scheme.ProEt.topology X) R
        (op (Scheme.ProEt.mk (𝟙 X)))) ∧
    (∀ (T : Profinite.{t}) [ExtremallyDisconnected T]
      (R : Sheaf ((coherentTopology Profinite.{t}).over T) CommRingCat.{max (t + 1) r})
      [HasSheafify ((coherentTopology Profinite.{t}).over T) AddCommGrpCat.{max (t + 1) r}]
      [((coherentTopology Profinite.{t}).over T).WEqualsLocallyBijective
        AddCommGrpCat.{max (t + 1) r}]
      [HasDerivedCategory.{max (t + 1) r}
        (RingedTensorModules.{t + 1, t, r} ((coherentTopology Profinite.{t}).over T) R)]
      [HasDerivedCategory.{max (t + 1) r}
        (ModuleCat.{max (t + 1) r} (R.obj.obj (op (Over.mk (𝟙 T)))))],
      ContractibleDerivedSectionsTensor.{t + 1, t, r}
        ((coherentTopology Profinite.{t}).over T) R (op (Over.mk (𝟙 T)))) := by
  sorry

end AlgebraicGeometry
