/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.ExceptionalFiniteRealization
public import Sheaf.Paper.PurTwistSheafLocallyFree
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
/-! # Finite coordinates and projections on the actual pro-etale systems
Source: blueprint def-weil-exceptional-inverse-image. The scalar-unit equations and
exact localization squares fix all comparisons, including their maps.
(blueprint: def-pur-adic-proetale-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The quotient ring is finite at every positive exponent.
Source: blueprint finite coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalFiniteQuotient (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Finite realization on the pro-etale site, using only scalar restriction and the
explicit quotient equivalence. It retains each underlying section.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalProRealization (W : Scheme.{u}) (n : ℕ) :
    coefficientLevelModules (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n ⥤
    Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  letI := Scheme.purTwistForgetPreservesSheafification W
  SheafOfModules.restrictScalars
      ((constantCommuteCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (integralExceptionalQuotientRing l E n))).inv ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology W)
      (integralExceptionalQuotientRing l E n) ⋙
      sheafCompose (Scheme.ProEt.topology W)
        (ModuleCat.restrictScalars (integralExceptionalQuotient l E n).symm.toRingHom)

/-- Pro-etale finite realization is an exact additive equivalence.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: its factors are restriction along the constant-ring presentation isomorphism,
the equivalence extending constant scalar actions to locally constant sections, and
restriction along a ring equivalence. Their inverses undo those operations. They
leave underlying maps unchanged and preserve kernels and cokernels. -/
theorem integralExceptionalProRealization_properties (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalProRealization l E W n).IsEquivalence ∧
      (integralExceptionalProRealization l E W n).Additive ∧
      PreservesFiniteLimits (integralExceptionalProRealization l E W n) ∧
      PreservesFiniteColimits (integralExceptionalProRealization l E W n) := by
  sorry
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_equivalence (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalProRealization l E W n).IsEquivalence :=
  (integralExceptionalProRealization_properties l E W n).1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_additive (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalProRealization l E W n).Additive :=
  (integralExceptionalProRealization_properties l E W n).2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_limits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (integralExceptionalProRealization l E W n) :=
  (integralExceptionalProRealization_properties l E W n).2.2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_colimits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (integralExceptionalProRealization l E W n) :=
  (integralExceptionalProRealization_properties l E W n).2.2.2

variable (W : Scheme.{u})

/-- Cache existing sheafification at the precise site size.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance (priority := 4000) integralExceptionalProRingRightAdjoint :
    (sheafToPresheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).IsRightAdjoint :=
  inferInstance
/-- Restriction along the explicit ring map preserves addition.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalLevel_additive (n : ℕ) :
    (integralExceptionalLevel l E W n).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{u + 1}
    (integralExceptionalRingMap l E W n)).Additive
/-- Cache componentwise addition at the actual system sizes.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance (priority := 4000) integralExceptionalEvaluation_additive :
    ∀ n, (coefficientEvaluation.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
      (ell := integralExceptionalUniformizer l E) n).Additive :=
  fun n ↦ coefficientEvaluation_additive.{u + 1, u, u + 1} n
/-- Componentwise kernels are preserved by evaluation.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalEvaluation_limits (n : ℕ) :
    PreservesFiniteLimits (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n) :=
  (coefficientEvaluation_exact.{u + 1, u, u + 1}
    (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
    (ell := integralExceptionalUniformizer l E) n).1
/-- Componentwise cokernels are preserved by evaluation.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalEvaluation_colimits (n : ℕ) :
    PreservesFiniteColimits (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n) :=
  (coefficientEvaluation_exact.{u + 1, u, u + 1}
    (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
    (ell := integralExceptionalUniformizer l E) n).2

/-- The original finite-to-generic coordinate change is itself an equivalence.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: the ring map is induced by the explicit quotient ring equivalence. Restriction
along its inverse is a two-sided inverse on module sheaves. -/
theorem integralExceptionalLevel_equivalence (n : ℕ) :
    (integralExceptionalLevel l E W n).IsEquivalence := by
  sorry
attribute [instance] integralExceptionalLevel_equivalence

/-- The coordinate realization of a fixed module is the same module. Its map is
specified on every scalar-unit section of the actual intrinsic realization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: restriction leaves the underlying abelian sheaf unchanged. The scalar-unit
map becomes an isomorphism after extending and then restricting locally constant
coefficients. Its inverse satisfies the displayed section formula. Such sections
locally generate, so the natural isomorphism is unique. -/
theorem integralExceptionalFixedUnit_existsUnique (n : ℕ) :
    ∃! e : (Scheme.sfIntrinsicModuleEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
      integralExceptionalLevel l E W n ⋙ integralExceptionalProRealization l E W n ≅ 𝟭 _,
      ∀ (M : Sheaf (Scheme.ProEt.topology W)
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
        (U : W.ProEtᵒᵖ) (m : M.obj.obj U),
        (e.hom.app M).hom.app U
          (Scheme.sfIntrinsicRealizationUnit W
            (Padic.coefficientExtensionRing l E (n + 1)) M U m) = m := by
  sorry

/-- The actual scalar-unit-normalized finite coordinate realization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalFixedUnit (n : ℕ) :=
  (integralExceptionalFixedUnit_existsUnique l E W n).exists.choose

/-- Identification with the recorded inverse realization, normalized by its unit.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: compose the preceding scalar-unit comparison with the unit and counit of the
recorded realization equivalence. Its triangle identities give the displayed equation.Essential
 surjectivity of the realization and its unit determine every component. -/
theorem integralExceptionalLevelFixed_existsUnique (n : ℕ) :
    ∃! e : integralExceptionalLevel l E W n ⋙ integralExceptionalProRealization l E W n ≅
      (Scheme.sfIntrinsicModuleEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).inverse,
      ∀ M, e.hom.app ((Scheme.sfIntrinsicModuleEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).functor.obj M) ≫
        (Scheme.sfIntrinsicModuleEquivalence W
          (Padic.coefficientExtensionRing l E (n + 1))).unitIso.inv.app M =
          (integralExceptionalFixedUnit l E W n).hom.app M := by
  sorry

/-- The finite coordinate comparison, fixed by the recorded equivalence unit.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalLevelFixed (n : ℕ) :=
  (integralExceptionalLevelFixed_existsUnique l E W n).exists.choose

/-- The exact derived coordinate comparison, induced by the specified ordinary map.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalDerivedLevelFixed (n : ℕ) :
    (integralExceptionalLevel l E W n).mapDerivedCategory ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
    (Scheme.sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).inverse :=
  letI := (Scheme.sfIntrinsicModuleEquivalence W
    (Padic.coefficientExtensionRing l E (n + 1))).inverse_additive
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (integralExceptionalLevelFixed l E W n)

/-- Coordinates preserve finite evaluation as an equality of actual ordinary functors.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: both functors take a strict system to its nth module with the quotient action
changed along the same ring equivalence. Their maps are the same nth component map;
functor extensionality gives equality. -/
theorem integralExceptionalCoordinatesEvaluation (n : ℕ) :
    integralExceptionalCoordinates l E W ⋙
      coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
        (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n =
    coefficientSequenceEvaluation l E W n ⋙ integralExceptionalLevel l E W n := by
  sorry

/-- Every normalized evaluation package has its unique exact-localization comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: both functors factor termwise evaluation through quasi-isomorphism localization. The
two displayed factorization maps give existence. Uniqueness of factorization on
complexes and roofs proves uniqueness of the natural isomorphism. -/
theorem integralExceptionalProEvaluationModel_existsUnique
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (n : ℕ) :
    ∃! e : P.evaluation n ≅
      (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
        (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)
          n).mapDerivedCategory
          ,
      ∀ J, e.hom.app (DerivedCategory.Q.obj J) ≫
        (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
          (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)
            n).mapDerivedCategoryFactors.hom.app
             J = (P.evaluationFactors n).hom.app J := by
  sorry

/-- The evaluation model, fixed on every strict complex.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
@[no_expose] def integralExceptionalProEvaluationModel
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (n : ℕ) :=
  (integralExceptionalProEvaluationModel_existsUnique l E W P n).exists.choose

/-- The direct coordinate/evaluation identification, obtained from the exact ordinary
coordinate equality and the scalar-unit-normalized finite realization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
@[no_expose] def integralExceptionalCoordinatesFixed
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (N : coefficientSequenceDerived l E W) (n : ℕ) :
    (integralExceptionalProRealization l E W n).mapDerivedCategory.obj
      ((P.evaluation n).obj ((integralExceptionalDerivedCoordinates l E W).obj N)) ≅
    (Scheme.sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
        ((coefficientSequenceDerivedEvaluation l E W n).obj N) :=
  (integralExceptionalProRealization l E W n).mapDerivedCategory.mapIso
    ((integralExceptionalProEvaluationModel l E W P n).app _ ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm.app N ≪≫
      (Functor.mapDerivedCategoryNatIso
        (eqToIso (integralExceptionalCoordinatesEvaluation l E W n))).app N ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).app N) ≪≫
    (integralExceptionalDerivedLevelFixed l E W n).app _

/-- The inverse coordinate/evaluation identification uses the actual counit of the
coordinate equivalence, rather than any choice of levelwise lift.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
@[no_expose] def integralExceptionalCoordinatesInvFixed
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (N : DerivedCategory (CoefficientSystem (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E))) (n : ℕ) :
    (Scheme.sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
      ((coefficientSequenceDerivedEvaluation l E W n).obj
        ((integralExceptionalDerivedCoordinatesInv l E W).obj N)) ≅
    (integralExceptionalProRealization l E W n).mapDerivedCategory.obj ((P.evaluation n).obj N) :=
  letI : (integralExceptionalCoordinates l E W).asEquivalence.functor.Additive :=
    integralExceptionalCoordinates_additive l E W
  (integralExceptionalCoordinatesFixed l E W P
    ((integralExceptionalDerivedCoordinatesInv l E W).obj N) n).symm ≪≫
    (integralExceptionalProRealization l E W n).mapDerivedCategory.mapIso
      ((P.evaluation n).mapIso
        (((integralExceptionalCoordinates l E W).asEquivalence.mapDerivedCategory).counitIso.app
           N))
end WeilConjectures
