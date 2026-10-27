/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Sheaf.SixFunctors.AugmentedStrictIntegralCompletion
public import Sheaf.Paper.IntegralCompletedTowerPullbackUniverses
public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.SixFunctors.OpenStrictQuotientDescent
import Sheaf.SixFunctors.OpenCoefficientOperationsExistence
import Sheaf.SixFunctors.NormalizedOpenSections
import Sheaf.SixFunctors.OpenNormalizedRoosRestriction
import Sheaf.SixFunctors.OpenExactPullbackLocalization
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Open strict quotient comparison and actual completion units

Source: Stacks Project, proetale.tex, Tag 099N (2),(5), and sites-cohomology.tex,
Tags 0G7E and 07A4 (blueprint: lem-sf-open-quotient-completion-unit-comparison).
The index n denotes exponent n+1. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenQuotientCompletion
open CompletedTowerIndependent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
  (o : IntegralOpenReduction.Operations l E e)

attribute [local irreducible] restrict HasDerivedCategory.standard

/-- The normalized exact-product comparison in the statement, on the actual signed
Roos models. Source: Stacks 0941
(blueprint: lem-sf-open-quotient-completion-unit-comparison). -/
structure RoosComparison where
  /-- The theta identifications use the actual shifted-cone functor. -/
  thetaW : DerivedCategory.Q ⋙ rlim l E W ≅ roosF ⋙ DerivedCategory.Q
  thetaV : DerivedCategory.Q ⋙ rlim l E V ≅ roosF ⋙ DerivedCategory.Q
  /-- Their K-injective normalizations fix the signs and the actual total-derived unit. -/
  thetaW_normalized : ∀ I : CochainComplex (Towers l E W) ℤ, I.IsKInjective →
    (∀ p : ℤ, Injective (I.X p)) →
    (rlimUnitCx l E W).app I ≫ thetaW.hom.app I = DerivedCategory.Q.map (ordinaryRoosMap l E W I)
  thetaV_normalized : ∀ I : CochainComplex (Towers l E V) ℤ, I.IsKInjective →
    (∀ p : ℤ, Injective (I.X p)) →
    (rlimUnitCx l E V).app I ≫ thetaV.hom.app I = DerivedCategory.Q.map (ordinaryRoosMap l E V I)
  /-- Kappa is the canonical product comparison on both signed summands. -/
  kappa : roosF (A := Modules l E W) ⋙ restrictCx l E e o ≅
    restrictTowCx l E e o ⋙ roosF (A := Modules l E V)
  kappa_first : ∀ (N : CochainComplex (Towers l E W) ℤ) (p : ℤ) (n : ℕ),
    (kappa.hom.app N).f (p+1) ≫
        signedCoordinates l E V ((restrictTowCx l E e o).obj N) p ≫ biprod.fst ≫
        (Pi.π (fun k : ℕ ↦ ((restrictTowCx l E e o).obj N).asFunctor.obj (op k)) n).f
          (p+1) =
      (restrict l E e o).map (signedCoordinates l E W N p ≫ biprod.fst ≫
        (Pi.π (fun k : ℕ ↦ N.asFunctor.obj (op k)) n).f (p+1))
  kappa_second : ∀ (N : CochainComplex (Towers l E W) ℤ) (p : ℤ) (n : ℕ),
    (kappa.hom.app N).f (p+1) ≫
        signedCoordinates l E V ((restrictTowCx l E e o).obj N) p ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ ((restrictTowCx l E e o).obj N).asFunctor.obj (op k)) n).f p =
      (restrict l E e o).map (signedCoordinates l E W N p ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ N.asFunctor.obj (op k)) n).f p)
  /-- The normalized exact-product comparison on all derived strict towers. -/
  lambda : rlim l E W ⋙ restrictD l E e o ≅ restrictTowD l E e o ⋙ rlim l E V
  /-- In Lean composition order: F(thetaW), kappa, thetaV inverse. -/
  lambda_normalized : ∀ N : CochainComplex (Towers l E W) ℤ,
    (restrictD l E e o).map (thetaW.hom.app N) ≫
        (restrict l E e o).mapDerivedCategoryFactors.hom.app (roosF.obj N) ≫
        DerivedCategory.Q.map (kappa.hom.app N) =
      lambda.hom.app (DerivedCategory.Q.obj N) ≫
        (rlim l E V).map ((restrictTow l E e o).mapDerivedCategoryFactors.hom.app N) ≫
        thetaV.hom.app ((restrictTowCx l E e o).obj N)
/-- Exact localization of the existing ordinary and strict derived ringed pullbacks.
The ordinary comparison is pinned by the adjunction's actual graph generators and
its derived version by the universal counit. Source: Stacks 03D2, 099N
(blueprint: lem-sf-open-quotient-completion-unit-comparison). -/
structure PullbackComparison where
  ordinary : pull l E e ≅ restrict l E e o
  ordinary_normalized : ∀ (M : Modules l E W)
      (Z : Over (IntegralOpenReduction.openObject e)) (x : M.val.obj (op Z.left)),
    (ordinary.hom.app M).val.app (op ((IntegralOpenReduction.sliceSite e).obj Z))
      (((pull l E e).obj M).val.map (sliceGraph e Z).op
        (((adjunction l E e).unit.app M).val.app (op Z.left) x)) =
      restrictionSection l E e o M Z x
  tower : derivedPull l E e ≅ restrictTowD l E e o
  counit_normalized : ∀ P : CochainComplex (Towers l E W) ℤ,
    tower.hom.app (DerivedCategory.Q.obj P) ≫
        (restrictTow l E e o).mapDerivedCategoryFactors.hom.app P =
      (derivedCounit l E e).app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso ordinary).hom) (.up ℤ)).app P)

/-- The strict and Roos comparisons identify the actual augmented completed pullback.
Source: Stacks 099N (2),(5)
(blueprint: lem-sf-open-quotient-completion-unit-comparison). -/
structure Comparison extends StrictComparison l E e o, RoosComparison l E e o,
    PullbackComparison l E e o where
  /-- The canonical constant-tower pullback isomorphism after exact localization. -/
  constantPull : restrictD l E e o ⋙ deltaD l E V ≅
    deltaD l E W ⋙ derivedPull l E e
  constantPull_normalized : ∀ H : DerivedCategory (Modules l E W),
    constantPull.hom.app H ≫ tower.hom.app ((deltaD l E W).obj H) =
      (constantRestriction l E e o).inv.app H
  /-- This is precisely the augmented completed-pullback construction, transported
  by the counit-normalized tower comparison. It holds on arbitrary inputs. -/
  completedComparison : ∀ H : DerivedCategory (Modules l E W),
    (constantAdjunction l E V).unit.app ((restrictD l E e o).obj H) ≫
        (rlim l E V).map (constantPull.hom.app H ≫
          (derivedPull l E e).map ((augmentation l E W).app H)) ≫
        (rlim l E V).map (tower.hom.app ((reductionPair l E W).functor.obj H)) =
      alpha l E e o H
  /-- Alpha is exactly lambda applied to the actual completion unit. -/
  alpha_eq : ∀ H : DerivedCategory (Modules l E W), alpha l E e o H =
    (restrictD l E e o).map (unit l E W H) ≫
      lambda.hom.app ((reductionPair l E W).functor.obj H)
  /-- b=Rlim(tau) carries the pulled augmentation to the target's actual unit. -/
  b_alpha : ∀ H : DerivedCategory (Modules l E W), alpha l E e o H ≫
      (rlim l E V).map (tau.hom.app H) = unit l E V ((restrictD l E e o).obj H)
  /-- rho=b lambda satisfies the requested actual-unit square, for every H. -/
  rho_unit : ∀ H : DerivedCategory (Modules l E W),
    (restrictD l E e o).map (unit l E W H) ≫
        lambda.hom.app ((reductionPair l E W).functor.obj H) ≫
        (rlim l E V).map (tau.hom.app H) = unit l E V ((restrictD l E e o).obj H)

/-- Open restriction identifies strict quotient towers and their actual completion units.
Source: Stacks 099N (2),(5), proof of (5); tensor inputs 0G7E and 07A4
(blueprint: lem-sf-open-quotient-completion-unit-comparison).
Proof:
1. Localize the small pro-etale site at the open object. Object inverse image is
restriction there. Finite constant sections and completed quotient projections give
normalized coefficient identifications, commuting with all quotient transitions.
2. Resolve by a flat-term K-flat complex. Exact ringed restriction preserves its flat
terms and K-flatness. At every degree and level, the balanced tensor restriction map
and its inverse send a pure tensor to that same restricted tensor (07A4, 0G7E).
3. The transition squares send x tensor a to x tensor r_n(a), and the augmentation
squares send x to x tensor one. Tensor universality gives strict equalities. Naturality
in cochain maps gives a natural isomorphism of complexes of strict towers.
4. Localize the good representatives. Change of rings preserves their quasi-isomorphisms;
tower cohomology is levelwise. The universal computation counits give tau with its
stated representative normalization and augmented square, independently of choices.
5. Products are exact on the pro-etale sites. Restriction has exact extension by zero
as a left adjoint, so its canonical product comparison is invertible and fixed by
projections. Apply exactProductFunctorStrictLimit. Its signed Roos normalizations give
both theta comparisons, kappa on both coordinates, and precisely the displayed lambda.
Its strict augmentation clause gives alpha_eq, with the actual constant-tower unit.
6. Apply Rlim to tau. The strict augmentation square yields b_alpha; equivalently its
signed Roos coordinates send ((e*gamma_n),0) to ((gamma'_n),0). Compose alpha_eq to get
rho_unit. Naturality of tau and lambda makes b and rho natural derived isomorphisms.
7. Exact open localization computes the total derived pullback on strict towers
termwise. Thus alpha is the augmented construction of completed pullback (099N), and
b_alpha identifies its comparison with the actual target completion unit on complete
inputs. All constructions and equations already hold for arbitrary H. No boundedness,
constructibility, completeness or quasi-compactness assumption is needed. -/
theorem openQuotientCompletionUnitComparison
    (_d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (_hd : _d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) :
    ∃ o : IntegralOpenReduction.Operations l E e, Nonempty (Comparison l E e o) := by
  obtain ⟨sections, -⟩ := IntegralOpenReduction.normalizedOpenSections l E e
  obtain ⟨o, -, -⟩ :=
    OpenSemilinearTensor.openCoefficientOperationsExistence l E e sections
  obtain ⟨s⟩ := openStrictQuotientDescent l E e o _d _hd
  obtain ⟨thetaW, thetaV, kappa, lambda, hthetaW, hthetaV, hkappa₁, hkappa₂,
    hlambda, hunit⟩ := openNormalizedRoosRestriction l E e o
  obtain ⟨ordinary, hord⟩ := openExactPullbackLocalization l E e o
  let qiso := HomologicalComplex.quasiIso (Towers l E W) (.up ℤ)
  let : (derivedPull l E e).IsLeftDerivedFunctor (derivedCounit l E e) qiso :=
    (towerPull_exists l E e).choose_spec.choose_spec.1
  let : (restrictTowD l E e o).IsLeftDerivedFunctor
      (restrictTow l E e o).mapDerivedCategoryFactors.hom qiso :=
    Functor.isLeftDerivedFunctor_of_inverts qiso _
      (restrictTow l E e o).mapDerivedCategoryFactors
  let cx : (towerPull l E e).mapHomologicalComplex (.up ℤ) ≅
      restrictTowCx l E e o :=
    NatIso.mapHomologicalComplex ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso ordinary)
      (.up ℤ)
  let tower : derivedPull l E e ≅ restrictTowD l E e o :=
    Functor.leftDerivedNatIso (derivedPull l E e) (restrictTowD l E e o)
      (derivedCounit l E e) (restrictTow l E e o).mapDerivedCategoryFactors.hom qiso
      (isoWhiskerRight cx DerivedCategory.Q)
  have htower (P : CochainComplex (Towers l E W) ℤ) :
      tower.hom.app (DerivedCategory.Q.obj P) ≫
          (restrictTow l E e o).mapDerivedCategoryFactors.hom.app P =
        (derivedCounit l E e).app P ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso ordinary).hom) (.up ℤ)).app P) := by
    exact Functor.leftDerivedNatTrans_app (derivedPull l E e) (restrictTowD l E e o)
      (derivedCounit l E e) (restrictTow l E e o).mapDerivedCategoryFactors.hom qiso
      (isoWhiskerRight cx DerivedCategory.Q).hom P
  let cp : restrictD l E e o ⋙ deltaD l E V ≅
      deltaD l E W ⋙ derivedPull l E e :=
    (constantRestriction l E e o).symm ≪≫ isoWhiskerLeft (deltaD l E W) tower.symm
  have hcp (H : DerivedCategory (Modules l E W)) :
      cp.hom.app H ≫ tower.hom.app ((deltaD l E W).obj H) =
        (constantRestriction l E e o).inv.app H := by
    dsimp only [cp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, whiskerLeft_app]
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hcompleted (H : DerivedCategory (Modules l E W)) :
      (constantAdjunction l E V).unit.app ((restrictD l E e o).obj H) ≫
          (rlim l E V).map (cp.hom.app H ≫
            (derivedPull l E e).map ((augmentation l E W).app H)) ≫
          (rlim l E V).map (tower.hom.app ((reductionPair l E W).functor.obj H)) =
        alpha l E e o H := by
    rw [← Functor.map_comp, Category.assoc, tower.hom.naturality,
      ← Category.assoc, hcp]
    rfl
  have halpha (H : DerivedCategory (Modules l E W)) :
      alpha l E e o H = (restrictD l E e o).map (unit l E W H) ≫
        lambda.hom.app ((reductionPair l E W).functor.obj H) := by
    dsimp only [alpha, unit]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc, hunit H, Category.assoc]
    exact congrArg
      (fun f ↦ (restrictD l E e o).map ((constantAdjunction l E W).unit.app H) ≫ f)
      (lambda.hom.naturality ((augmentation l E W).app H)).symm
  have hb (H : DerivedCategory (Modules l E W)) :
      alpha l E e o H ≫ (rlim l E V).map (s.tau.hom.app H) =
        unit l E V ((restrictD l E e o).obj H) := by
    dsimp only [alpha, unit]
    rw [Category.assoc, ← Functor.map_comp, Category.assoc, s.augmented]
    simp only [Iso.inv_hom_id_app_assoc]
  refine ⟨o, ⟨{ toStrictComparison := s
                toRoosComparison := {
                  thetaW := thetaW
                  thetaV := thetaV
                  thetaW_normalized := hthetaW
                  thetaV_normalized := hthetaV
                  kappa := kappa
                  kappa_first := hkappa₁
                  kappa_second := hkappa₂
                  lambda := lambda
                  lambda_normalized := hlambda }
                toPullbackComparison := {
                  ordinary := ordinary
                  ordinary_normalized := hord
                  tower := tower
                  counit_normalized := htower }
                constantPull := cp
                constantPull_normalized := hcp
                completedComparison := hcompleted
                alpha_eq := halpha
                b_alpha := hb
                rho_unit := ?_ }⟩⟩
  intro H
  rw [← Category.assoc, ← halpha H]
  exact hb H

end WeilConjectures.OpenQuotientCompletion
