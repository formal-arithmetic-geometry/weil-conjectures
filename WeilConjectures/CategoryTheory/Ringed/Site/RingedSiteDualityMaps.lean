/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
/-! # Canonical coefficient-duality maps on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 08JD, 08JE, 0A97 and 0A98
(blueprint: lem-sfb-ringed-site-duality-maps).
The existing closed tensor-Hom representative model pins transposition to actual
sheafified pure tensors. The unit, associator and symmetry below are pinned to
ordinary complexes as well. No perfectness or invertibility is part of this model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w w' a b x y
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules WeilConjectures
namespace CategoryTheory

section Closed
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : WeilConjectures.CoefficientClosedStructure H)
  (s : @SymmetricCategory D _ S.monoidal)
  (O : D) (u : S.monoidal.tensorUnit ≅ O)

end Closed

section RestrictionAssembly
variable {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
  {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E}
  (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU)
  (s : @SymmetricCategory D _ S.monoidal)
  (sU : @SymmetricCategory E _ SU.monoidal)

variable {r : D ⥤ E} {K : Prop}

/-- The natural tensor comparison, constructed from its given components. -/
private def ringedSiteRestrictionTensorIso
    (d : RingedSliceEvaluationComparisons H HU r S SU K) :
    S.tensor ⋙ r ≅ (r.prod r) ⋙ SU.tensor :=
  NatIso.ofComponents (fun X ↦ d.rho X.1 X.2)
    (fun {X Y} f ↦ d.rho_naturality X.1 X.2 Y.1 Y.2 f.1 f.2)

/-- The natural Hom comparison, constructed from its given components. -/
private def ringedSiteRestrictionHomIso
    (d : RingedSliceEvaluationComparisons H HU r S SU K) :
    H ⋙ r ≅ (r.op.prod r) ⋙ HU :=
  NatIso.ofComponents (fun X ↦ d.eta X.1.unop X.2)
    (fun {X Y} f ↦ d.eta_naturality X.1.unop X.2 Y.1.unop Y.2 f.1.unop f.2)

end RestrictionAssembly

section Site
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The coefficient sheaf regarded as a complex in degree zero.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualityUnitComplex :=
  (HomologicalComplex.single (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
      (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))

/-- The coefficient object in the unbounded derived category.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualityUnit
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))] :=
  DerivedCategory.Q.obj (ringedSiteDualityUnitComplex.{c, v, r} J R)

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]

-- These unused generated lemmas expand the native derived coefficient category.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A presentation of the existing derived tensor and Hom, normalized on K-flats.
The symmetry uses the Koszul sign. The right unitor is scalar multiplication;
the associator reassociates pure tensors. Together with models.uncurry_model these
conditions specify the evaluation constructions of 08JD and 0A97 on representatives.
Source: Stacks 06YN, 08JD, 0A97, 0A98
(blueprint: lem-sfb-ringed-site-duality-maps). -/
structure RingedSiteDualityModel where
  /-- The existing closed tensor-Hom structure. -/
  closed : WeilConjectures.CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{c, v, r, w} J R)
  /-- The existing pure-tensor normalization of its adjunction. -/
  models : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R closed
  /-- Symmetry of this same tensor structure. -/
  symmetric : @SymmetricCategory _ _ closed.monoidal
  /-- Identification of its tensor unit with the coefficient in degree zero. -/
  unitIso : closed.monoidal.tensorUnit ≅ ringedSiteDualityUnit.{c, v, r, w} J R
  /-- The ordinary coefficient complex is K-flat. -/
  unitKFlat : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R)
    (ringedSiteDualityUnitComplex.{c, v, r} J R)
  /-- The symmetry descends the actual signed interchange of total-complex summands. -/
  symmetry_model : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P) (hQ :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q),
    ∃ σ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ⟶
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, P),
      (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (σ.f k).val.app U (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q k h U x
      y) =
          (p * q).negOnePow • WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q P q p k h'
      U y x) ∧
      (models.iso J R closed P Q hP hQ).hom ≫
          (symmetric.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
        DerivedCategory.Q.map σ ≫ (models.iso J R closed Q P hQ hP).hom
  /-- The right unit constraint is induced by the actual scalar multiplication map. -/
  unit_model : ∀ (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P),
    ∃ ρ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      ringedSiteDualityUnitComplex.{c, v, r} J R) ⟶ P,
      (∀ (p : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
        (a : ((ringedSiteDualityUnitComplex.{c, v, r} J R).X 0).val.obj U),
        (ρ.f p).val.app U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      (ringedSiteDualityUnitComplex.{c, v, r} J R)
              p 0 p (Int.add_zero p) U x a) = a • x) ∧
      (models.iso J R closed P (ringedSiteDualityUnitComplex.{c, v, r} J R)
          hP unitKFlat).hom ≫ closed.tensor.map (Prod.mkHom (𝟙 _) unitIso.inv) ≫
          (closed.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map ρ
  /-- The associator descends the actual reassociation of total-complex summands. -/
  associator_model : ∀ (P Q V : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q)
      (hV : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) V),
    ∃ α : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q), V) ⟶
        (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)),
      (∀ (p q t i j k : ℤ) (hpq : p + q = i) (hit : i + t = k)
        (hqt : q + t = j) (hpj : p + j = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (V.X t).val.obj U),
        (α.f k).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V i t k hit U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q i hpq U x y) z) =
          WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)) p j k hpj U x
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q V q t j hqt U y z)) ∧
      (models.iso J R closed ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hV).hom ≫
        closed.tensor.map (Prod.mkHom (models.iso J R closed P Q hP hQ).hom (𝟙 _)) ≫
        (closed.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj V)).hom =
      DerivedCategory.Q.map α ≫
        (models.iso J R closed P ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q,
      V)) hP
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R Q V hQ hV)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (models.iso J R closed Q V hQ hV).hom)

set_option Elab.async false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Canonical evaluation data exist without any perfectness hypothesis.
Source: Stacks 08JD, 0A97, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: descend total tensor on K-flats by site-derived-tensor descent, and derive the
ordinary componentwise tensor-Hom adjunction with a K-injective target. Its counit
has exactly the representative formula of CoefficientTensorModels. Descend the
ordinary scalar unit, reassociation, and signed interchange; their coherence
identities hold on pure tensor generators and hence after localization. The unit
is flat in degree zero. The formulas ringedSiteBidual and ringedSiteDualEvaluation
are respectively transposed signed evaluation and composition after the Hom-unit
identification. On ordinary Hom-computable representatives their components are
x ↦ (φ ↦ (-1)^{|x||φ|} φ(x)) and y tensor φ ↦ (x ↦ y φ(x)). These formulas commute
with slice restriction: restriction is exact, retains sections and the displayed
formulas, and commutes with K-flat tensor and K-injective Hom under the canonical
restriction comparisons. Naturality follows by transposing composite evaluations.
No isomorphism of either of these two maps is used or asserted. -/
theorem ringedSiteDualityMaps_exists : Nonempty (RingedSiteDualityModel.{c, v, r, w} J R) := by
  obtain ⟨S, T, β, ⟨K⟩⟩ := ringedDerived_closed_symmetric_monoidal.{c, v, r, w} J R
  have hunit : CochainComplex.IsKFlatIndependentCoefficients
      (J := J) (R := R) (ringedSiteDualityUnitComplex.{c, v, r} J R) := by
    intro F hF n
    exact (hF n).of_iso (HomologicalComplex.rightUnitor F).symm
  refine ⟨⟨S, T, β, K.unitIso, hunit, ?_, ?_, ?_⟩⟩
  · intro P Q hP hQ
    obtain ⟨s, hs, he⟩ := K.symmetry_model P Q hP hQ
    exact ⟨s.hom, hs, he⟩
  · intro P hP
    obtain ⟨ρ, hρ, he⟩ := K.rightUnitor_model P hP
    refine ⟨ρ.hom, ?_, ?_⟩
    · intro p U x a
      exact hρ p (Int.add_zero p) U a x
    · rw [K.tensorIso_both P (ringedTensorUnitComplex.{c, v, r} J R) hP hunit] at he
      exact he
  · intro P Q V hP hQ hV
    obtain ⟨α, hα, he⟩ := K.associator_model P Q V hP hQ hV
    refine ⟨α.hom, ?_, ?_⟩
    · intro p q t i j k hpq hit hqt hpj U x y z
      exact hα p q t i j k hpq hqt hit hpj U x y z
    · rw [K.tensorIso_both _ V
        (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hV,
        K.tensorIso_both P _ hP
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R Q V hQ hV)] at he
      exact he

attribute [local irreducible] homComplexFunctor homComplexπ
  derivedInternalHomOfUniverses

section OrdinaryBidualComponents

attribute [local irreducible] ringedSiteDualityUnitComplex

set_option backward.isDefEq.respectTransparency false

@[no_expose] private def ringedSiteEvalSection
    (𝒜 : Cᵒᵖ ⥤ CommRingCat.{max c v r})
    (A B : PresheafOfModules.{max c v r} (𝒜 ⋙ forget₂ _ _))
    {U : Cᵒᵖ} (x : A.obj U) :
    (PresheafOfModules.restrictOver 𝒜 U.unop).obj (PresheafOfModules.homObj (R := 𝒜) A B) ⟶
      (PresheafOfModules.restrictOver 𝒜 U.unop).obj B where
  app W := ModuleCat.ofHom
    { toFun := fun φ ↦ (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
        (A.map W.unop.hom.op x)
      map_add' := by intros; rfl
      map_smul' := by
        intro a φ
        refine (PresheafOfModules.restrictOver_smul_app_apply a φ _ _).trans ?_
        change 𝒜.map (𝟙 (op W.unop.left)) a •
          ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
            (A.map W.unop.hom.op x)) = a •
          ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
            (A.map W.unop.hom.op x))
        rw [𝒜.map_id]
        rfl }
  naturality {W W'} f := by
    ext φ
    change ((PresheafOfModules.restrictOverMap f.unop.left φ).app
        (op (Over.mk (𝟙 W'.unop.left)))).hom (A.map W'.unop.hom.op x) =
      B.map f.unop.left.op
        ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op x))
    have hx : A.map f.unop.left.op (A.map W.unop.hom.op x) =
        A.map W'.unop.hom.op x := by
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]
    exact (PresheafOfModules.restrictOver_hom_app_congr φ (Category.id_comp _) _).trans
      ((congrArg (fun z ↦ (φ.app (op (Over.mk f.unop.left))).hom z) hx.symm).trans
        (PresheafOfModules.naturality_apply φ
          (Over.homMk f.unop.left (Category.comp_id _) :
            Over.mk f.unop.left ⟶ Over.mk (𝟙 W.unop.left)).op
              (A.map W.unop.hom.op x)))

@[no_expose] private def ringedSitePresheafBidual
    (𝒜 : Cᵒᵖ ⥤ CommRingCat.{max c v r})
    (A B : PresheafOfModules.{max c v r} (𝒜 ⋙ forget₂ _ _)) :
    A ⟶ PresheafOfModules.homObj (R := 𝒜)
      (PresheafOfModules.homObj (R := 𝒜) A B) B where
      app U := ModuleCat.ofHom (R := 𝒜.obj U) (X := A.obj U)
        (Y := (PresheafOfModules.homObj (R := 𝒜)
          (PresheafOfModules.homObj (R := 𝒜) A B) B).obj U)
        { toFun := ringedSiteEvalSection.{c, v, r} 𝒜 A B
          map_add' := by
            intro x y
            apply PresheafOfModules.hom_ext
            intro W
            ext φ
            change (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op (x + y)) =
              (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op x) +
                (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op y)
            exact (congrArg (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
              ((A.map W.unop.hom.op).hom.map_add x y)).trans
              (map_add (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom _ _)
          map_smul' := by
            intro a x
            apply PresheafOfModules.hom_ext
            intro W
            ext φ
            change (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op (a • x)) =
              𝒜.map W.unop.hom.op a •
                (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op x)
            exact (congrArg (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
              (A.map_smul W.unop.hom.op a x)).trans
              ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom.map_smul _ _) }
      naturality := by
        intro U V f
        ext x : 2
        apply PresheafOfModules.hom_ext
        intro W
        ext φ
        change (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op (A.map f x)) =
          (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map (W.unop.hom ≫ f.unop).op x)
        exact congrArg (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
          (A.map_comp_apply f W.unop.hom.op x).symm

@[no_expose] private def ringedSiteSheafBidual
    (A B : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    A ⟶ SheafOfModules.homObj (R := R) (SheafOfModules.homObj (R := R) A B) B where
  val := ringedSitePresheafBidual.{c, v, r} R.obj A.val B.val

@[no_expose] private abbrev RingedSiteComplex := CochainComplex (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ

end OrdinaryBidualComponents

attribute [local irreducible] coefficientTotalTensor

section NormalizedSymmetry

end NormalizedSymmetry

/-- Slice restriction sends zero maps to zero, by its sectionwise construction.
Source: Stacks 03DJ (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: overFunctor keeps the components of a module morphism and only restricts
its index category. Each component of a zero morphism remains zero. -/
theorem ringedSiteDualityRestriction_preservesZero (U : C) :
    (SheafOfModules.overFunctor.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
        U).PreservesZeroMorphisms := by
  classical
  have hSheaf : HasSheafify J AddCommGrpCat.{max c v r} := inferInstance
  have hW : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := inferInstance
  have hDerived : HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    inferInstance
  constructor
  intro X Y
  ext V x
  rfl

/-- Forgetting commutativity commutes with slice restriction as sheaves of rings.
Source: Stacks 03DJ (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: both sides have the section ring R(V), and the same ring restriction map,
on an object V to U of the slice. Extensionality of ring sheaves gives equality;
the sheaf-condition proofs are propositionally irrelevant. -/
theorem ringedSiteDualityRestrictionCoefficient_eq (U : C) :
    (sheafCompose (J.over U)
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over U) =
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U := by
  have hSheaf : HasSheafify J AddCommGrpCat.{max c v r} := inferInstance
  have hW : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := inferInstance
  have hDerived : HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    inferInstance
  rfl

/-- The actual termwise restriction functor on complexes.
Source: Stacks 03DJ, 08FI (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualityRestrictionComplex (U : C) :=
  letI := ringedSiteDualityRestriction_preservesZero.{c, v, r} J R U
  ((SheafOfModules.overFunctor.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U) ⋙
      SheafOfModules.restrictScalars (eqToHom
        (ringedSiteDualityRestrictionCoefficient_eq.{c, v, r} J R U))).mapHomologicalComplex
          (ComplexShape.up ℤ)

attribute [local irreducible] ringedSliceDerivedRestriction

attribute [local irreducible] DerivedCategory.Q ringedSliceComplexRestriction
attribute [local irreducible] ringedSiteDualityRestrictionComplex
attribute [local irreducible] ringedSiteRestrictionTensorIso ringedSiteRestrictionHomIso

end Site
end CategoryTheory
