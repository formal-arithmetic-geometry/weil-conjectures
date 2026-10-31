/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExtensionComposition
public import WeilConjectures.AlgebraicGeometry.FieldExtensionReductionLimits
public import WeilConjectures.AlgebraicGeometry.FieldExtensionLimitEquations
public import WeilConjectures.AlgebraicGeometry.FieldExtensionStrictLimits
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower
public import WeilConjectures.SecSmoothPurity.ReductionDirectImage
public import WeilConjectures.SecSmoothPurity.ReductionExceptional
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.AlgebraicGeometry.FieldExtensionCompletedStrictLimit
import WeilConjectures.AlgebraicGeometry.FieldExtensionReductionDescent
import WeilConjectures.AlgebraicGeometry.FieldExtensionIntegralDescent
import WeilConjectures.AlgebraicGeometry.FieldExtensionRationalDescent
import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystemComparison
import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
import WeilConjectures.Compactification.NagataCompactification
import Mathlib.Data.Nat.Prime.Infinite

/-! # FieldExtensionTowers

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md, clauses (1)--(3)
(blueprint: det-sp-field-extension-towers).

## Main definitions and statements

The declarations below package the named functors, comparisons and equations of
the indicated clauses, using the published coefficient and geometric models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers
variable (P : PurityFiniteSetting.{u})
variable (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

/-- All three clauses for the fixed smooth morphism, with comparisons simultaneously
chosen for every finite subfield and every inclusion. Every extra field is conclusion
or presentation data for the recorded functors; none is a new geometric hypothesis.
Source: clauses (1)--(3) (blueprint: det-sp-field-extension-towers). -/
structure Result where
  model : ∀ E : FieldShriekSystem.Index P, IntegralModel P D E j p d
  finite : FieldShriekSystem.Laws P D (SpTowerGamma.factorization j p)
  strictLimits : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u}),
    StrictLimitComparison P E F h T
  ordinaryClosed : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u})
    (K : Integral P E T),
    sfIntegralConstructible P.coefficients.l F.val T
      ((completedDerivedScalarExtension P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) T).obj K.obj)
  ordinaryCompleted : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u})
    (K : Integral P E T),
    IsIso ((completedScalarComparison P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T).app K.obj)
  reduction : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u})
    (RA : SpReductionTower P.coefficients.l E.val T ((D.coordinates E).abelian T))
    (RB : SpReductionTower P.coefficients.l F.val T ((D.coordinates F).abelian T)),
    Reduction P D E F h T RA RB
  reductionX : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
    Reduction P D E F h X (model E).reductionX (model F).reductionX
  reductionY : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
    Reduction P D E F h Y (model E).reductionY (model F).reductionY
  integral : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
    IntegralComparison P D j p d E F h (model E) (model F)
  reductionX_normalized : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (M : Integral P E X),
    HEq ((integral E F h).scalarReductionX.hom.app M).hom
      ((reductionX E F h).reduction.hom.app M)
  reductionY_normalized : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (K : Integral P E Y),
    HEq ((integral E F h).scalarReductionY.hom.app K).hom
      ((reductionY E F h).reduction.hom.app K)
  limits : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
    LimitEquations P D j p d E F h (model E) (model F) (integral E F h)
  composition : ∀ (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L),
    IntegralComposition P D j p d E F L h k (model E) (model F) (model L)
      (integral E F h) (integral F L k) (integral E L (h.trans k))
  rational : ∀ E : FieldShriekSystem.Index P, RationalModel P D j p d E (model E)
  rationalComparison : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
    RationalComparison P D j p d E F h (model E) (model F) (integral E F h)
      (rational E) (rational F)
  rationalComposition : ∀ (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L),
    RationalComposition P D j p d E F L h k (model E) (model F) (model L)
      (integral E F h) (integral F L k) (integral E L (h.trans k))
      (rational E) (rational F) (rational L) (rationalComparison E F h)
      (rationalComparison F L k) (rationalComparison E L (h.trans k))

end AlgebraicGeometry.ProEtale.FieldExtensionTowers

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers

private theorem ordinary_scalar_properties (P : PurityFiniteSetting.{u})
    (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u})
    (K : Integral P E T) :
    IsIso ((completedScalarComparison P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T).app K.obj) ∧
    sfIntegralConstructible P.coefficients.l F.val T
      ((completedDerivedScalarExtension P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) T).obj K.obj) := by
  obtain ⟨p₀, hp₀, hprime⟩ := Nat.exists_infinite_primes (P.coefficients.l + 1)
  let : Fact p₀.Prime := ⟨hprime⟩
  let D₀ : FiniteFieldDatum.{0} :=
    { p := p₀
      a := 1
      q := p₀
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p₀
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p₀) }
  have hl₀ : P.coefficients.l ≠ D₀.p := by change P.coefficients.l ≠ p₀; omega
  have hcomplete : IsDerivedCompleteUnrestricted P.coefficients.l E.val T K.obj :=
    ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy P.coefficients.l E.val T D₀ hl₀ K.obj).mp
      K.property.1⟩
  have hi := ((finiteFreeCompletedScalarComparison P.coefficients.l E.val F.val
    (IntermediateField.inclusion h) T).2.1 K.obj hcomplete).1
  have hclosed := sfIntegralScalarExtension_constructible P.field.p P.coefficients.l
    P.coefficients.different E.val F.val (IntermediateField.inclusion h) T K.obj K.property
  let := hi
  exact ⟨hi, ObjectProperty.prop_of_iso _
    (asIso ((completedScalarComparison P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) T).app K.obj)).symm hclosed⟩

/-- Finite coefficient-field extension has the integral tower comparisons and their
raw rational localizations stated in all three clauses of the source.
Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md (blueprint: det-sp-field-extension-towers).

Proof:
Choose the finite-free completed coefficient comparisons for all inclusions. Finite
freeness preserves constructibility, common bounds and completeness. Ordinary scalar
extension commutes with strict inverse limits by its finite-basis description; deriving
this projection-normalized map gives the unbounded strict-limit comparison. The
multiplication and insertion-of-one maps on K-flat complexes give the reduction
isomorphism as an arrow of entire derived systems, including quotient transitions.
Use the actual proper/open system comparison b and its adjunction mate c. Their
finite evaluations are the recorded finite comparisons, and their unit and counit
squares follow from mate calculus. The orientation, projection and tensor-transpose
identities give the purity square. Apply the total limit to these system arrows;
normalized reconstruction identifies them with the stated integral comparisons and
with their units, counits and gamma. Multiplication of three tensor factors gives
coefficient composition under the canonical balanced associators. Finally the
integral functors and adjunction are coefficient-linear. Extend their Hom actions to
the raw scalar-localized categories; every component is tensored with one. This
preserves all the displayed equations, including purity and coefficient composition.
Localized purity identifies the right adjoint with pullback followed by (d)[2d]. -/
theorem field_extension_towers (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))] (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated f] :
    letI := compactSpace P X
    letI := quasiSeparatedSpace P Y
    Nonempty (Compactification f) ∧ ∀ c : Compactification f,
      letI : (c.i ≫ c.g).IsOver (Spec (.of P.field.k)) :=
        c.comm ▸ (inferInstance : f.IsOver (Spec (.of P.field.k)))
      ∃ D : FieldShriekSystem.Models P, Nonempty (Result P D c.i c.g d) := by
  classical
  let := compactSpace P X
  let := quasiSeparatedSpace P Y
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  constructor
  · exact (inferInstance : HasCompactification f).nonempty_compactification
  · intro c
    let : (c.i ≫ c.g).IsOver (Spec (.of P.field.k)) :=
      c.comm ▸ (inferInstance : f.IsOver (Spec (.of P.field.k)))
    have : SmoothOfRelativeDimension d (c.i ≫ c.g) := by rw [← c.comm]; infer_instance
    have : IsSeparated (c.i ≫ c.g) := by rw [← c.comm]; infer_instance
    obtain ⟨D, b, a, A, ⟨laws⟩⟩ :=
      FieldExceptionalSystem.field_exceptional_system_comparison P X Y (c.i ≫ c.g) d
        (SpTowerGamma.factorization c.i c.g)
    let red (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u})
        (RA : SpReductionTower P.coefficients.l E.val T ((D.coordinates E).abelian T))
        (RB : SpReductionTower P.coefficients.l F.val T ((D.coordinates F).abelian T)) :
        Reduction P D E F h T RA RB :=
      Classical.choice (field_extension_reduction_descent P D E F h T RA RB)
    obtain ⟨m, i, hX, hY, hlim, hcomp⟩ :=
      field_extension_integral_descent P D c.i c.g d b a A laws red
    obtain ⟨r, q, hq⟩ := field_extension_rational_descent P D c.i c.g d m i hcomp
    refine ⟨D, ⟨{
      model := m
      finite := b
      strictLimits := fun E F h T ↦
        Classical.choice (field_extension_completed_strict_limit P E F h T)
      ordinaryClosed := fun E F h T K ↦ (ordinary_scalar_properties P E F h T K).2
      ordinaryCompleted := fun E F h T K ↦ (ordinary_scalar_properties P E F h T K).1
      reduction := red
      reductionX := fun E F h ↦ red E F h X (m E).reductionX (m F).reductionX
      reductionY := fun E F h ↦ red E F h Y (m E).reductionY (m F).reductionY
      integral := i
      reductionX_normalized := hX
      reductionY_normalized := hY
      limits := hlim
      composition := hcomp
      rational := r
      rationalComparison := q
      rationalComposition := hq }⟩⟩

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
