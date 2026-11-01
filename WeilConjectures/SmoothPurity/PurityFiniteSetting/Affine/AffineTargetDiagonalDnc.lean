/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncInvariance
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalBaseChangeCompared
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Section.PuritySectionInvariantIntrinsic
public import WeilConjectures.AlgebraicGeometry.RelativeTangentBundle.RelativeTangentBundle
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalRegularPureCodimension
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessTheorem
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.ReesConeNormalizedExistence
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential
import WeilConjectures.AlgebraicGeometry.SmoothDiagonalRegularGenerators
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCanonicalInterfaces
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleUnit

/-! # Affine-target diagonal pairs and normalized deformation comparison

Source: main-20261015, sec-smooth-purity/sk-prop-sp-orientation,
thm-pur-diagonal-dualizing-object.proof.md, Steps 1--2.
(blueprint: lem-pur-affine-target-diagonal-dnc).

The tangent comparison is normalized on differentials of functions: da corresponds
 to the class of p2*a - p1*a. The DNC comparison uses the published family equation,
not an arbitrary isomorphism between its endpoints. No absolute separatedness is
assumed before restricting the target to an affine open.

## Main definitions and statement

* `AffineDiagonalGeometry` and `AffineDiagonalConclusion` package the chart assertions.
* `AffineDiagonalTangentNormalized` specifies the canonical tangent identification.
* `affineDiagonalRho` and `affineDiagonalAlpha` are the canonical comparison arrows.
* `AffineDiagonalDncNormalized` records the published DNC normalization equation.
* `affineTargetDiagonalDnc` states the affine-target restriction result.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The canonical normal/tangent identification, specified on degree-one generators.
The Rees comparison fixes a/t modulo t, and the other side fixes da. These generators,
with constants, determine the algebra map and hence the scheme isomorphism.
Source: blueprint Step 1; Stacks 08S2, 0630, 0632
(blueprint: lem-pur-affine-target-diagonal-dnc). -/
def AffineDiagonalTangentNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] [IsSeparated f]
    (e : (pullback.diagonal f).ker.normalCone ≅ RelativeTangentBundle.scheme f) : Prop :=
  ∃ q : (pullback.diagonal f).ker.normalCone ≅
      PurityNormalBundle.normalCone (pullback.diagonal f),
    ∃ hq : Etale.FiniteSmoothPurity.ReesConeNormalized (pullback.diagonal f) q,
    ∃ he : e.hom ≫ RelativeTangentBundle.projection f =
        Scheme.Hom.purityNormalProjection (pullback.diagonal f),
      (pullback.diagonal f).normalConeZeroSection ≫ e.hom =
        RelativeTangentBundle.zeroSection f ∧
      ∀ (U : X.Opens) (W : (pullback f f).Opens)
        (h₁ : W ≤ (pullback.fst f f) ⁻¹ᵁ U)
        (h₂ : W ≤ (pullback.snd f f) ⁻¹ᵁ U)
        (hδ : U ≤ (pullback.diagonal f) ⁻¹ᵁ W)
        (a : Γ(X, U))
        (b : (ConormalGradedAlgebra.power (pullback.diagonal f) 1).val.obj (op W)),
        (ConormalGradedAlgebra.powerInclusion (pullback.diagonal f) 1).val.app (op W) b =
          (pullback.snd f f).appLE U W h₂ a - (pullback.fst f f).appLE U W h₁ a →
        e.hom.appLE (RelativeTangentBundle.projection f ⁻¹ᵁ U)
            (Scheme.Hom.purityNormalProjection (pullback.diagonal f) ⁻¹ᵁ U)
            (by rw [← Scheme.Hom.comp_preimage, he])
            ((RelativeTangentBundle.algebraIso f).hom.right.hom.app (op U)
              ((SymmetricAlgebraSheaf.inclusion f.relativeDifferentials).val.app (op U)
                (f.relativeDifferentialsDerivation.d (X := op U) a))) =
          q.hom.appLE (PurityNormalBundle.projection (pullback.diagonal f) ⁻¹ᵁ U)
            (Scheme.Hom.purityNormalProjection (pullback.diagonal f) ⁻¹ᵁ U)
            (by rw [← Scheme.Hom.comp_preimage, hq.1])
            ((Etale.FiniteSmoothPurity.coneAlgebraIso (pullback.diagonal f)).hom.right.hom.app
              (op U)
              ((ConormalGradedAlgebra.presentation (pullback.diagonal f)).algebra.right.obj.map
                (homOfLE hδ).op
                (ConormalGradedAlgebra.homogeneousClass (pullback.diagonal f)
                  (ConormalGradedAlgebra.presentation (pullback.diagonal f)).algebra
                  (ConormalGradedAlgebra.presentation (pullback.diagonal f)).inclusion 1 W b)))

/-- Geometric assertions for one affine-target restriction, packaged only to make their
instances available to the subsequent canonical maps. All fields concern the chosen
restriction and its actual self-product.
Source: blueprint Step 1 and affine-target domain check
(blueprint: lem-pur-affine-target-diagonal-dnc). -/
structure AffineDiagonalGeometry (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) (V : Y.affineOpens) where
  [separated : IsSeparated (f ∣_ V.1)]
  [finiteType : LocallyOfFiniteType (f ∣_ V.1)]
  [quasiCompact : QuasiCompact (f ∣_ V.1)]
  [smoothDimension : SmoothOfRelativeDimension d (f ∣_ V.1)]
  [baseFiniteType : LocallyOfFiniteType (V.1.ι ≫ aY)]
  [baseQuasiCompact : QuasiCompact (V.1.ι ≫ aY)]
  [sourceSeparated : IsSeparated ((f ∣_ V.1) ≫ V.1.ι ≫ aY)]
  [sourceFiniteType : LocallyOfFiniteType ((f ∣_ V.1) ≫ V.1.ι ≫ aY)]
  [sourceQuasiCompact : QuasiCompact ((f ∣_ V.1) ≫ V.1.ι ≫ aY)]
  [productSeparated : IsSeparated
    (pullback.fst (f ∣_ V.1) (f ∣_ V.1) ≫ (f ∣_ V.1) ≫ V.1.ι ≫ aY)]
  [productFiniteType : LocallyOfFiniteType
    (pullback.fst (f ∣_ V.1) (f ∣_ V.1) ≫ (f ∣_ V.1) ≫ V.1.ι ≫ aY)]
  [productQuasiCompact : QuasiCompact
    (pullback.fst (f ∣_ V.1) (f ∣_ V.1) ≫ (f ∣_ V.1) ≫ V.1.ι ≫ aY)]

/-- The canonical open-restriction rho, in the same fixed-coefficient realization
as the DNC theorem. The compactification is obtained from the original one by base
change, and the only nonformal arrow is the specified smooth base-change mate.
Source: thm-pur-cohomological-smoothness (3); blueprint affine restriction
(blueprint: lem-pur-affine-target-diagonal-dnc). -/
def affineDiagonalRho (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.Opens) :=
  letI := Dnc.compactifiable P f aY
  let sq := (isPullback_morphismRestrict f V).flip
  letI := ((HasCompactification.compactification f).ofIsPullback sq).hasCompactification
  letI := Dnc.invertibleExponent P (f ≫ aY)
  letI := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    P.Coefficient f d sq
  letI := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).2
    (inferInstanceAs (IsIso
      ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app (𝟙_ _))))
  Dnc.pullComparison P (f ⁻¹ᵁ V).ι
      (Etale.dualizingComplex P.Coefficient f) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (f ⁻¹ᵁ V).toScheme).mapDerivedCategory.mapIso
        (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient sq))

/-- The specified alpha: inverse self-product base-change mate, pulled to the diagonal,
then the pullback-composition and identity constraints, in canonical comparison coordinates.
Source: lem-pur-diagonal-base-change, final display; blueprint Step 2
(blueprint: lem-pur-affine-target-diagonal-dnc). -/
def affineDiagonalAlpha (P : PurityFiniteSetting.{u}) {U V : Scheme.{u}}
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV] :=
  letI := Dnc.compactifiable P h aV
  letI := (P.comparedDiagonalBaseChange d h (h ≫ aV) aV rfl).2.2.2.1
  Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.diagonalComparedRestriction h
          (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
            (IsPullback.of_hasPullback h h).flip)))

/-- The published DNC normalization, including the identity base change and all
trivializations coming from the base. In etale coordinates its two fibre readings agree,
so the comparison is the identity on the standard invariant.
Source: thm-pur-dnc-invariance, uniqueness clause; blueprint Step 1
(blueprint: lem-pur-affine-target-diagonal-dnc). -/
def AffineDiagonalDncNormalized (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    (α : Dnc.sourceSection P d g aB s ≅ Dnc.normalSection P d g aB s hs) : Prop :=
  ∀ (B' : Scheme.{u}) (aB' : B' ⟶ Spec (.of P.field.k))
        [IsSeparated aB'] [LocallyOfFiniteType aB'] [QuasiCompact aB']
        (b : B' ⟶ B) (_hb : b ≫ aB = aB')
        (C₀ : _root_.DerivedCategory
          (Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
        (e : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
            (Dnc.familyEtale P d g aB s hs) ≅
          (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            (AffineSpace (ULift.{u} (Fin 1)) B' ↘ B')).leftDerivedFunctor.obj C₀),
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso α =
          (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
              (Dnc.sourceComparison P d g aB s) ≪≫
            Dnc.pullComparison P b (Dnc.sourceEtale P d g aB s) ≪≫
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory.mapIso
              (Etale.sectionRestrictionIso _ b _ (AffineSpace.oneSection_comp_map b)
                  (AffineSpace.oneSection_comp_over _ B') (Dnc.fibreOne P d g aB s hs) e ≪≫
                (Etale.sectionRestrictionIso _ b _ (AffineSpace.zeroSection_comp_map b)
                  (AffineSpace.zeroSection_comp_over _ B') (Dnc.fibreZero P d g aB s hs) e).symm) ≪≫
            ((ProEtale.upperStar
                (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
                (Dnc.normalComparison P d g aB s hs) ≪≫
              Dnc.pullComparison P b (Dnc.normalEtale P d g aB s hs)).symm

/-- All the assertions on one chart, in the recorded finite comparison coordinates.
The dictionaries are conclusions of the geometry assertion, not hypotheses on f.
Source: blueprint Steps 1--2
(blueprint: lem-pur-affine-target-diagonal-dnc). -/
def AffineDiagonalConclusion (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (V : Y.affineOpens) (H : P.AffineDiagonalGeometry f aY d V) : Prop :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  letI := Dnc.compactifiable P f aY
  letI := Dnc.compactifiable P (f ∣_ V.1) (V.1.ι ≫ aY)
  IsIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
    (isPullback_morphismRestrict f V.1).flip) ∧
  (∀ x : (f ⁻¹ᵁ V.1).toScheme,
    ∃ U : (pullback (f ∣_ V.1) (f ∣_ V.1)).affineOpens,
      pullback.diagonal (f ∣_ V.1) x ∈ U.1 ∧
      ∃ r : List Γ(pullback (f ∣_ V.1) (f ∣_ V.1), U.1),
        r.length = d ∧ RingTheory.Sequence.IsRegular Γ(pullback (f ∣_ V.1) (f ∣_ V.1), U.1) r ∧
          Ideal.ofList r = (pullback.diagonal (f ∣_ V.1)).ker.ideal U) ∧
  (f ∣_ V.1).relativeDifferentials.IsFiniteLocallyFreeOfRank d ∧
  (∃! e : (pullback.diagonal (f ∣_ V.1)).ker.normalCone ≅
      RelativeTangentBundle.scheme (f ∣_ V.1),
    AffineDiagonalTangentNormalized (f ∣_ V.1) e) ∧
  IsIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
    (IsPullback.of_hasPullback (f ∣_ V.1) (f ∣_ V.1)).flip) ∧
  Nonempty ((Scheme.sfIntrinsicDerivedEquivalence (f ⁻¹ᵁ V.1).toScheme P.Ring).functor.obj
      (Dnc.sourceSection P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
        ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))) ≅
    P.sectionInvariantFinite (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
      ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))
      (pullback.diagonal_fst (f ∣_ V.1))) ∧
  (∃! δ : Dnc.sourceSection P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
        ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1)) ≅
      Dnc.normalSection P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
        ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))
        (pullback.diagonal_fst (f ∣_ V.1)),
    AffineDiagonalDncNormalized P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
      ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))
      (pullback.diagonal_fst (f ∣_ V.1)) δ)

set_option backward.isDefEq.respectTransparency false in
private theorem tangentNormalized_exists {U V : Scheme.{u}} [IsNoetherian U]
    (h : U ⟶ V) [Smooth h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (d : ℕ) [SmoothOfRelativeDimension d h] :
    ∃ e : (pullback.diagonal h).ker.normalCone ≅ RelativeTangentBundle.scheme h,
      AffineDiagonalTangentNormalized h e := by
  have : Smooth h := SmoothOfRelativeDimension.smooth d h
  let δ := pullback.diagonal h
  obtain ⟨ω, hω⟩ := ChartNormalDifferential.differenceIdentification h
  have := ChartNormalDifferential.diagonalSymmetric d h
  obtain ⟨t, ht, hz, β, hβ, hs⟩ :=
    ChartNormalDifferential.normalTangentIdentification h δ ω
  obtain ⟨q, hq⟩ := Etale.FiniteSmoothPurity.reesConeComparison_exists δ
  let e := q ≪≫ t
  have he : e.hom ≫ RelativeTangentBundle.projection h =
      Scheme.Hom.purityNormalProjection δ := by
    change q.hom ≫ t.hom ≫ _ = _
    rw [ht, hq.1]
  refine ⟨e, q, hq, he, ?_, ?_⟩
  · change δ.normalConeZeroSection ≫ q.hom ≫ t.hom = _
    rw [← Category.assoc, hq.2.1, hz]
  · intro A W h₁ h₂ hδ a b hb
    have hd := hω A W h₁ h₂ hδ a b hb
    have hb' := hβ A (h.relativeDifferentialsDerivation.d (X := op A) a)
    rw [hd] at hb'
    have hn := ((ConormalGradedAlgebra.presentation δ).inclusion 1).val.naturality
      (homOfLE hδ).op
    have heq : β.hom.right.hom.app (op A)
        ((SymmetricAlgebraSheaf.inclusion h.relativeDifferentials).val.app (op A)
          (h.relativeDifferentialsDerivation.d (X := op A) a)) =
      (ConormalGradedAlgebra.presentation δ).algebra.right.obj.map (homOfLE hδ).op
        (ConormalGradedAlgebra.homogeneousClass δ
          (ConormalGradedAlgebra.presentation δ).algebra
          (ConormalGradedAlgebra.presentation δ).inclusion 1 W b) := by
      exact hb'.trans (ConcreteCategory.congr_hom hn
        (ConormalGradedAlgebra.representative δ 1 W b))
    have hs' := hs.2 A
      ((SymmetricAlgebraSheaf.inclusion h.relativeDifferentials).val.app (op A)
        (h.relativeDifferentialsDerivation.d (X := op A) a))
    simp only [Scheme.Hom.id_preimage] at hs'
    rw [heq] at hs'
    have hc := Scheme.Hom.appLE_comp_appLE q.hom t.hom
      (RelativeTangentBundle.projection h ⁻¹ᵁ A)
      (PurityNormalBundle.projection δ ⁻¹ᵁ A)
      (Scheme.Hom.purityNormalProjection δ ⁻¹ᵁ A)
      (by rw [← Scheme.Hom.comp_preimage, ht])
      (by rw [← Scheme.Hom.comp_preimage, hq.1])
    change ((q.hom ≫ t.hom).appLE _ _ _) _ = _
    erw [← hc]
    change q.hom.appLE _ _ _ (t.hom.appLE _ _ _ _) = _
    rw [← hs']
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tangentHom_ext {U V T : Scheme.{u}} (h : U ⟶ V) [Smooth h]
    (π : T ⟶ U) (f g : T ⟶ RelativeTangentBundle.scheme h)
    (hf : f ≫ RelativeTangentBundle.projection h = π)
    (hg : g ≫ RelativeTangentBundle.projection h = π)
    (heq : ∀ (A : U.Opens) (a : Γ(U, A)),
      f.appLE (RelativeTangentBundle.projection h ⁻¹ᵁ A) (π ⁻¹ᵁ A)
          (by rw [← Scheme.Hom.comp_preimage, hf])
          ((RelativeTangentBundle.algebraIso h).hom.right.hom.app (op A)
            ((SymmetricAlgebraSheaf.inclusion h.relativeDifferentials).val.app (op A)
              (h.relativeDifferentialsDerivation.d (X := op A) a))) =
      g.appLE (RelativeTangentBundle.projection h ⁻¹ᵁ A) (π ⁻¹ᵁ A)
          (by rw [← Scheme.Hom.comp_preimage, hg])
          ((RelativeTangentBundle.algebraIso h).hom.right.hom.app (op A)
            ((SymmetricAlgebraSheaf.inclusion h.relativeDifferentials).val.app (op A)
              (h.relativeDifferentialsDerivation.d (X := op A) a)))) : f = g := by
  let B := ChartNormalDifferential.structureAlgebra π
  let α : SymmetricAlgebraSheaf.algebra h.relativeDifferentials ⟶ B :=
    (RelativeTangentBundle.algebraIso h).hom ≫
      ChartNormalDifferential.structureAlgebraMap (RelativeTangentBundle.projection h) π f hf
  let β : SymmetricAlgebraSheaf.algebra h.relativeDifferentials ⟶ B :=
    (RelativeTangentBundle.algebraIso h).hom ≫
      ChartNormalDifferential.structureAlgebraMap (RelativeTangentBundle.projection h) π g hg
  let j := SymmetricAlgebraSheaf.inclusion h.relativeDifferentials
  let F := commAlgebraSheafModuleFunctor U.sheaf
  have hj : j ≫ F.map α = j ≫ F.map β := by
    apply (h.relativeDifferentialsHomEquiv B.toModule).injective
    ext A a
    exact heq A.unop a
  have ha : α = β := by
    apply ExistsUnique.unique (exists_quasiCoherentSymmetricAlgebra_core U
      h.relativeDifferentials B (j ≫ F.map α))
    · intro A a
      rfl
    · intro A a
      exact (congrArg (fun q ↦ q.val.app (op A) a) hj).symm
  have hh : ChartNormalDifferential.structureAlgebraMap
        (RelativeTangentBundle.projection h) π f hf =
      ChartNormalDifferential.structureAlgebraMap
        (RelativeTangentBundle.projection h) π g hg :=
    (cancel_epi (RelativeTangentBundle.algebraIso h).hom).mp ha
  have : IsAffineHom (RelativeTangentBundle.projection h) :=
    (RelativeTangentBundle.over h).property
  apply ChartNormalDifferential.schemeHom_ext_over
    (RelativeTangentBundle.projection h) π f g hf hg
  intro A
  ext a
  exact congrArg (fun q ↦ q.right.hom.app (op A) a) hh

set_option backward.isDefEq.respectTransparency false in
private theorem tangentNormalized_unique {U V : Scheme.{u}} [IsNoetherian U]
    (h : U ⟶ V) [Smooth h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (d : ℕ) [SmoothOfRelativeDimension d h] :
    ∃! e : (pullback.diagonal h).ker.normalCone ≅ RelativeTangentBundle.scheme h,
      AffineDiagonalTangentNormalized h e := by
  have : Smooth h := SmoothOfRelativeDimension.smooth d h
  obtain ⟨e, he⟩ := tangentNormalized_exists h d
  refine ⟨e, he, ?_⟩
  intro e' he'
  obtain ⟨q, hq, hp, hz, hnorm⟩ := he
  obtain ⟨q', hq', hp', hz', hnorm'⟩ := he'
  have hqq : q' = q := ExistsUnique.unique
    (Etale.FiniteSmoothPurity.reesConeComparison_existsUnique (pullback.diagonal h)) hq' hq
  subst q'
  apply Iso.ext
  apply tangentHom_ext h (Scheme.Hom.purityNormalProjection (pullback.diagonal h))
    e'.hom e.hom hp' hp
  intro A a
  obtain ⟨b, hb⟩ := ChartNormalDifferential.differenceRepresentative h A a
  have hδ : A ≤ (pullback.diagonal h) ⁻¹ᵁ
      ((pullback.fst h h) ⁻¹ᵁ A ⊓ (pullback.snd h h) ⁻¹ᵁ A) := by
    simp only [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      pullback.diagonal_fst, pullback.diagonal_snd, Scheme.Hom.id_preimage, inf_idem, le_refl]
  exact (hnorm' A _ inf_le_left inf_le_right hδ a b hb).trans
    (hnorm A _ inf_le_left inf_le_right hδ a b hb).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def intrinsicUnitComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (Scheme.sfIntrinsicDerivedEquivalence T P.Ring).functor.obj (𝟙_ _) ≅
      P.intrinsicCoefficientUnit T :=
  (Scheme.sfIntrinsicDerivedEquivalence T P.Ring).functor.mapIso
      (DerivedCategory.singleFunctorObjUnitIso
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))).symm ≪≫
    ((Scheme.sfIntrinsicModuleEquivalence T P.Ring).functor.mapDerivedCategorySingleFunctor
      0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (Scheme.proEtaleConstantModuleUnit T P.Ring)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def intrinsicSectionComparison (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) :
    (Scheme.sfIntrinsicDerivedEquivalence B P.Ring).functor.obj
      (P.sectionInvariant g aB s) ≅ P.sectionInvariantIntrinsic g s := by
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring V
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring B
  let EV := Scheme.sfIntrinsicDerivedEquivalence V P.Ring
  let EB := Scheme.sfIntrinsicDerivedEquivalence B P.Ring
  let U := ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) s
  let G := Scheme.sfIntrinsicDerivedPullback P.Ring s
  let η : G ≅ EV.inverse ⋙ U.mapDerivedCategory ⋙ EB.functor :=
    Functor.mapDerivedCategoryCompIso
        ((Scheme.sfIntrinsicModuleEquivalence V P.Ring).inverse ⋙ U)
        (Scheme.sfIntrinsicModuleEquivalence B P.Ring).functor ≪≫
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryCompIso
          (Scheme.sfIntrinsicModuleEquivalence V P.Ring).inverse U) EB.functor
  let κ : EV.functor ⋙ G ≅ U.mapDerivedCategory ⋙ EB.functor :=
    Functor.isoWhiskerLeft EV.functor η ≪≫ EV.funInvIdAssoc _
  let ε : (𝟙_ _) ≅ EB.inverse.obj (P.intrinsicCoefficientUnit B) :=
    EB.unitIso.app _ ≪≫ EB.inverse.mapIso (intrinsicUnitComparison P B)
  let ω : EV.functor.obj (P.dualizing g aB) ≅ P.intrinsicDualizing g :=
    EV.functor.mapIso
      ((ProEtale.sfFiniteExceptionalFixed P.Ring
        (HasCompactification.compactification g)).mapIso ε)
  exact EB.functor.mapIso
      ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) s).app (P.dualizing g aB)) ≪≫
    (κ.app (P.dualizing g aB)).symm ≪≫ G.mapIso ω

private theorem diagonalRegularSequences {U V : Scheme.{u}}
    (h : U ⟶ V) [IsSeparated h] (d : ℕ) [SmoothOfRelativeDimension d h] :
    ∀ x : U, ∃ W : (pullback h h).affineOpens,
      pullback.diagonal h x ∈ W.1 ∧ ∃ r : List Γ(pullback h h, W.1),
        r.length = d ∧ RingTheory.Sequence.IsRegular Γ(pullback h h, W.1) r ∧
          Ideal.ofList r = (pullback.diagonal h).ker.ideal W := by
  intro x
  obtain ⟨W, hxW, hW⟩ := exists_isRegular_smooth_diagonal_generators d h
    (pullback.diagonal h x)
  rcases hW with hempty | ⟨r, hr, hreg, hI⟩
  · have hone : (pullback.diagonal h).app W.1 1 = 0 :=
      RingHom.mem_ker.mp (hempty.symm ▸ (show (1 : Γ(pullback h h, W.1)) ∈ ⊤ from trivial))
    have : Nontrivial Γ(U, (pullback.diagonal h) ⁻¹ᵁ W.1) :=
      (U.presheaf.germ _ x hxW).hom.domain_nontrivial
    simp at hone
  · exact ⟨W, hxW, r, hr, hreg, by simpa only [Scheme.Hom.ker_apply] using hI⟩

/-- Affine-target restriction supplies the diagonal pair in the separated finite-type
DNC domain, its regular ideal and tangent normal bundle, the canonical restriction and
alpha maps, and the unique normalized DNC comparison. The finite affine cover may be empty.
Source: main-20261015, thm-pur-diagonal-dualizing-object.proof.md, Steps 1--2
(blueprint: lem-pur-affine-target-diagonal-dnc).

Proof:
1. Apply the finite-affine-cover characterization of finite type to aY
   (def-weil-finite-type-morphism). The all-affine-pairs criterion
   (lem-weil-pbc-lft-affine-pairs) gives finite generation for every affine open.
2. The open inverse image is the fibre product, by isPullback_morphismRestrict
   (def-weil-open-immersion, def-pc-fibre-product).
3. Separatedness, finite type and smooth pure relative dimension survive base change
   (lem-pod-separated-finite-type-base-change,
   lem-sbc-smooth-relative-dimension-permanence), first for f_V, then for both projections.
4. V is affine over the field, hence separated (lem-weil-pbc-affine-morphism-permanence).
   Compose separated and finite-type maps to obtain X_V and W_V in the absolute DNC
   domain (lem-weil-pbc-proper-fp-permanence, lem-sfb-finite-type-composition-base-change).
5. Cohomological smoothness clause 3 makes the specified open base-change mate
   invertible (thm-pur-cohomological-smoothness). Its inverse is the restriction rho.
6. On smooth coordinates the diagonal ideal is generated by the d coordinate
   differences (lem-pur-diagonal-regular-immersion). At d=0 use a neighbourhood of
   the clopen diagonal and the empty sequence. Its conormal is Omega by da mapping
   to p2*a-p1*a; the canonical symmetric comparison and relative Spec identify the
   actual associated-graded normal cone with RelativeTangentBundle. The Rees chart
   normalization fixes this identification uniquely, including projection and zero.
7. Pull back the inverse self-product base-change mate along the diagonal and compose
   the pullbacks using p2 Delta=id (lem-pur-diagonal-base-change). This is precisely
   affineDiagonalAlpha, with its explicit site comparison.
8. Apply thm-pur-dnc-invariance to (p1,Delta) over X_V. Steps 3--6 give its domain
   and closed-section hypotheses. Its full family equation gives the displayed
   normalization and uniqueness. The intrinsic coefficient realization identifies
   these same source objects with the recorded sectionInvariantFinite. No absolute
   separatedness of X or Y, positive d, or divisibility of the coefficient level is used. -/
theorem affineTargetDiagonalDnc (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    (∃ S : Finset Y.affineOpens,
      (⨆ V ∈ S, V.1) = ⊤ ∧ ∀ V ∈ S, (V.1.ι ≫ aY).appTop.hom.FiniteType) ∧
    ∀ V : Y.affineOpens, (V.1.ι ≫ aY).appTop.hom.FiniteType →
      ∃ H : P.AffineDiagonalGeometry f aY d V, P.AffineDiagonalConclusion f aY d V H := by
  classical
  have _ := hf
  have hft (V : Y.affineOpens) : (V.1.ι ≫ aY).appTop.hom.FiniteType := by
    exact HasRingHomProperty.appTop @LocallyOfFiniteType (V.1.ι ≫ aY) inferInstance
  constructor
  · have := QuasiCompact.compactSpace_of_compactSpace aY
    obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
      (fun V : Y.affineOpens ↦ (V.1 : Set Y)) (fun V ↦ V.1.isOpen) (by
        intro y _
        obtain ⟨_, ⟨V, hV, rfl⟩, hyV, _⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
          (show y ∈ (⊤ : Y.Opens) from trivial) isOpen_univ
        exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hyV⟩)
    refine ⟨S, ?_, fun V _ ↦ hft V⟩
    apply top_unique
    intro y _
    obtain ⟨V, hyV⟩ := Set.mem_iUnion.mp (hS (Set.mem_univ y))
    obtain ⟨hVS, hyV⟩ := Set.mem_iUnion.mp hyV
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨V,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨hVS, hyV⟩⟩
  · intro V _
    have hsep : IsSeparated (f ∣_ V.1) := inferInstance
    have hdim : SmoothOfRelativeDimension d (f ∣_ V.1) := by
      have := smoothOfRelativeDimension_isStableUnderBaseChange d
      exact MorphismProperty.of_isPullback (isPullback_morphismRestrict f V.1).flip inferInstance
    have hbase : IsSeparated (V.1.ι ≫ aY) := by
      have : IsAffine V.1.toScheme := V.2
      infer_instance
    have : Smooth (f ∣_ V.1) := SmoothOfRelativeDimension.smooth d _
    let H : P.AffineDiagonalGeometry f aY d V := {
      separated := inferInstance
      finiteType := inferInstance
      quasiCompact := inferInstance
      smoothDimension := inferInstance
      baseFiniteType := inferInstance
      baseQuasiCompact := inferInstance
      sourceSeparated := inferInstance
      sourceFiniteType := inferInstance
      sourceQuasiCompact := inferInstance
      productSeparated := inferInstance
      productFiniteType := inferInstance
      productQuasiCompact := inferInstance }
    refine ⟨H, ?_⟩
    dsimp only [AffineDiagonalConclusion]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · let := Dnc.compactifiable P f aY
      let := Dnc.invertibleExponent P (f ≫ aY)
      have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
        P.Coefficient f d (isPullback_morphismRestrict f V.1).flip
      exact (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient
        (isPullback_morphismRestrict f V.1).flip).2
        (inferInstanceAs (IsIso
          ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient
            (isPullback_morphismRestrict f V.1).flip).app (𝟙_ _))))
    · exact diagonalRegularSequences (f ∣_ V.1) d
    · exact Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials (f ∣_ V.1) d
    · have := LocallyOfFiniteType.isLocallyNoetherian ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
      have := QuasiCompact.compactSpace_of_compactSpace ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
      have : IsNoetherian (f ⁻¹ᵁ V.1).toScheme := {}
      exact tangentNormalized_unique (f ∣_ V.1) d
    · let := Dnc.compactifiable P (f ∣_ V.1) (V.1.ι ≫ aY)
      exact (P.comparedDiagonalBaseChange d (f ∣_ V.1)
        ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (V.1.ι ≫ aY) rfl).2.2.2.1
    · let := Dnc.compactifiable P (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
        ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
      exact ⟨intrinsicSectionComparison P (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
        ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))⟩
    · exact Dnc.existsUnique_dncInvariance P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
        ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))
        (pullback.diagonal_fst (f ∣_ V.1))

end WeilConjectures.PurityFiniteSetting
