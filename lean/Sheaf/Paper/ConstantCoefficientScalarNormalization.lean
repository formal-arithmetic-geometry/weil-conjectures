/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.ProEtaleConstructibleSheaf
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.Paper.SfCommonStageWeilCohomology
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.SfRationalizationKaroubi
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! # Normalized scalar extension of constant coefficient objects

Source: blueprint, ordinary compact cohomology, order 1869, coefficient-object paragraph;
Bhatt--Scholze, Lemma 6.8.2 (blueprint: lem-weil-constant-coefficient-objects-constructible).
This supplements the existing constructibility module with the canonical coefficient-unit
comparison, including its strict-cone normalization, in the intrinsic rational category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : Scheme.{u})

/-- The coefficient-unit inverse is fixed by its quotient coordinates and zero shifted
component, on the regular module itself.
Source: blueprint order 1869; Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: multiplication identifies each finite scalar extension of the regular module
with the finite target coefficient module. Send s to 1 tensor pi_n(s) in each factor.
These maps commute with reductions, hence their product is killed by 1-shift. The strict
mapping cocone lift with zero shifted component gives eta. The regular module is generated
locally by one, so these formulas fix the first component in degree zero; the source is
zero in every other degree. The two cone projections then prove uniqueness. -/
theorem constantCoefficientScalarUnit_existsUnique :
    ∃! η : constantWeilIntegralComplex l L Y ⟶
        (integralScalarComplexFunctor l E L ι Y).obj (constantWeilIntegralComplex l E Y),
      (∀ (n : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (completedScalarRoosEndomorphism l E L ι Y
              (constantWeilIntegralComplex l E Y))).f 0 ≫
          (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E L ι Y).obj
            (constantWeilIntegralComplex l E Y)).obj (op m)) n).f 0).val.app (op V))
              (constantWeilUnitSection l L Y V) =
          integralScalarTensorSection l E L ι Y n
            ((constantWeilIntegralComplex l E Y).X 0) (op V) 1
            (constantWeilUnitSection l E Y V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E L ι Y
            (constantWeilIntegralComplex l E Y))).v i (i - 1) (by omega) = 0) := by
  sorry

/-- The strict scalar unit, with both cone components determined uniquely.
Source: blueprint order 1869 (blueprint: lem-weil-constant-coefficient-objects-constructible).
-/
def constantCoefficientScalarUnit :=
  (constantCoefficientScalarUnit_existsUnique l E L ι Y).exists.choose

/-- The normalized coefficient-unit map is a quasi-isomorphism.
Source: blueprint order 1869; Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: the finite scalar tower of the regular module is the target quotient tower.
Its transitions are surjective, locally by lifting coefficients, and its ordinary limit
is the completed target ring. The surjective-tower derived-limit theorem identifies the
strict cone with that limit in degree zero. Its comparison is precisely the unit above,
as the quotient and shifted coordinates agree. Thus its image under Q is invertible. -/
theorem constantCoefficientScalarUnit_isIso :
    IsIso (DerivedCategory.Q.map (constantCoefficientScalarUnit l E L ι Y)) := by
  sorry

/-- The integral beta is the inverse strict unit after the normalized representative
comparison. Its inverse sends s to the compatible pi_n(s) and zero shifted coordinate.
Source: blueprint order 1869 (blueprint: lem-weil-constant-coefficient-objects-constructible).
-/
def constantCoefficientIntegralScalarIso :
    (integralScalarExtensionOfUniverses l E L ι Y).obj
        (integralConstantCoefficientObject l E Y) ≅ integralConstantCoefficientObject l L Y :=
  (integralScalarExtensionComparisonOfUniverses l E L ι Y).app
      (constantWeilIntegralGood l E Y) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (constantCoefficientScalarUnit l E L ι Y))
      (constantCoefficientScalarUnit_isIso l E L ι Y)).symm

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- Lift the normalized beta to the full intrinsic integral category.
Source: blueprint order 1869 (blueprint: lem-weil-constant-coefficient-objects-constructible).
-/
def constantCoefficientConstructibleScalarIso :
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj
        (constantWeilIntegralObject l E D hl Y) ≅ constantWeilIntegralObject l L D hl Y :=
  ObjectProperty.isoMk _ (constantCoefficientIntegralScalarIso l E L ι Y)

private theorem iso_existsUnique_of_source_eq {C : Type*} [Category C]
    {X X' Z : C} (h : X = X') (e : X' ≅ Z) :
    ∃! e' : X ≅ Z, HEq e'.hom e.hom := by
  subst X'
  exact ⟨e, HEq.rfl, fun e' he' ↦ Iso.ext (eq_of_heq he')⟩

/-- The rational alpha is uniquely the image of the normalized integral beta.
Source: blueprint order 1869; Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: the prescribed rational scalar functor has the integral scalar object formula.
Use this equality to identify the source, and apply raw rationalization to beta.
Its inverse is the rationalization of beta inverse. The displayed hom formula determines
an isomorphism uniquely since an isomorphism is determined by its hom. -/
theorem constantCoefficientRationalScalarIso_existsUnique :
    ∃! α : (sfRationalScalarExtension l E Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          (constantWeilRationalObject l E D hl Y) ≅ constantWeilRationalObject l L D hl Y,
      HEq α.hom ((sfRationalConstructibleLocalization l L Y).map
        (constantCoefficientConstructibleScalarIso l E L ι Y D hl).hom) := by
  apply iso_existsUnique_of_source_eq
    ((sfRationalScalarExtension_existsUnique l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
        (constantWeilRationalObject l E D hl Y))
    ((sfRationalConstructibleLocalization l L Y).mapIso
      (constantCoefficientConstructibleScalarIso l E L ι Y D hl))

/-- The canonical scalar isomorphism alpha, normalized before rationalization.
Source: blueprint order 1869 (blueprint: lem-weil-constant-coefficient-objects-constructible).
-/
def constantCoefficientRationalScalarIso :=
  (constantCoefficientRationalScalarIso_existsUnique l E L ι Y D hl).exists.choose

end WeilConjectures
