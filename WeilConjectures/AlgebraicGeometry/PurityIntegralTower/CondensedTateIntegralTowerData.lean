/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.ReconstructionUniformTower
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.ProperBaseChange.ScalarPerfectCohomologyAndPidModels
import WeilConjectures.NumberTheory.Padics.ULiftDiscreteValuationRing
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Reconstruction of the normalized finite smooth-purity tower

Source: current blueprint, sk-thm-purity-transport, proof Steps 1--2; normalized
Tate-unit case of adic reconstruction
(blueprint: def-pur-condensed-tate-integral-tower-data).

Positive level n+1 is indexed by n. The coefficient ring is the inverse limit
of finite coefficient sheaves, not the discrete constant p-adic ring sheaf.
The auxiliary scalar comparisons are fixed by their restriction-adjunction mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped TensorProduct
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  SheafOfModules.monoidalCategory completedAdicDerivedChange

/-- The actual p-adic ring, lifted only to the small site's coefficient universe.
Source: sk-thm-purity-transport, integral coefficients
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
abbrev Ring (ell : ℕ) [Fact ell.Prime] := ULift.{u + 1} ℤ_[ell]

private def padicQuotientIso (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    Ring.{u} ell ⧸ (Ideal.span {(ell : Ring.{u} ell)}) ^ n ≃+* ZMod (ell ^ n) :=
  (Ideal.quotientEquiv _ _ (ULift.ringEquiv : Ring.{u} ell ≃+* ℤ_[ell])
    (by rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast])).trans
    ((Ideal.quotEquivOfEq (by rw [Ideal.span_singleton_pow, PadicInt.ker_toZModPow])).trans
      (RingHom.quotientKerEquivOfSurjective
        (ZMod.ringHom_surjective (PadicInt.toZModPow n))))

private theorem padicQuotientIso_mk (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (x : Ring.{u} ell) :
    padicQuotientIso ell n (Ideal.Quotient.mk _ x) = PadicInt.toZModPow n x.down := by
  simp only [padicQuotientIso, RingEquiv.trans_apply, Ideal.quotientEquiv_mk,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

/-- The p-adic coefficient hypotheses for the specified principal ideal.
Source: sk-thm-purity-transport, reconstruction Step 1
(blueprint: def-pur-condensed-tate-integral-tower-data).
Proof: Z_ell is a DVR, hence Noetherian. Its ideal (ell) is principal. Its first
quotient is F_ell, hence additively torsion. Every positive quotient is finite,
by toZModPow, and has the two-term finite free resolution given by multiplication
by ell^n, which is injective in this domain. Lift these statements through ULift. -/
theorem coefficientProperties (ell : ℕ) [Fact ell.Prime] :
    IsNoetherianRing (Ring.{u} ell) ∧
      (Ideal.span ({(ell : Ring.{u} ell)} : Set (Ring.{u} ell))).FG ∧
      (∀ x : Ring.{u} ell ⧸ Ideal.span {(ell : Ring.{u} ell)},
        ∃ m : ℕ, 0 < m ∧ m • x = 0) ∧
      (∀ n : ℕ, 1 ≤ n →
        adicQuotientPerfect (Ring.{u} ell) (Ideal.span {(ell : Ring.{u} ell)}) n) ∧
      ∀ n : ℕ, Finite (Ring.{u} ell ⧸
        (Ideal.span {(ell : Ring.{u} ell)}) ^ (n + 1)) := by
  have hfinite (n : ℕ) : Finite (Ring.{u} ell ⧸
      (Ideal.span {(ell : Ring.{u} ell)}) ^ (n + 1)) :=
    Finite.of_equiv (ZMod (ell ^ (n + 1))) (padicQuotientIso ell (n + 1)).symm.toEquiv
  refine ⟨inferInstance, Submodule.fg_span_singleton _, ?_, ?_, hfinite⟩
  · have : Finite (Ring.{u} ell ⧸ Ideal.span {(ell : Ring.{u} ell)}) := by
      simpa only [Nat.zero_add, pow_one] using hfinite 0
    intro x
    exact (isOfFinAddOrder_of_finite x).exists_nsmul_eq_zero
  · intro n _hn
    let R := Ring.{u} ell
    let J : Ideal R := (Ideal.span {(ell : R)}) ^ n
    let M := ModuleCat.of R (R ⧸ J)
    let := HasDerivedCategory.standard (ModuleCat.{u + 1} R)
    have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    let q : (Fin 1 → R) →ₗ[R] M := J.mkQ.comp (LinearMap.proj (0 : Fin 1))
    have hq : Function.Surjective q := by
      intro x
      obtain ⟨y, rfl⟩ := J.mkQ_surjective x
      exact ⟨fun _ ↦ y, rfl⟩
    obtain ⟨_, _, _, _, _, hperfect, _⟩ :=
      (DerivedCategory.scalar_perfect_cohomology_and_pid_models R).2 M 1 q hq
    exact hperfect

/-- The concrete (ell)-adic datum; all fields other than the ideal are proof fields.
Source: sk-thm-purity-transport, reconstruction Step 1
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def datum (ell : ℕ) [Fact ell.Prime] : AdicCoefficientDatum (Ring.{u} ell) where
  ideal := Ideal.span {(ell : Ring.{u} ell)}
  noetherian := (coefficientProperties ell).1
  finitelyGenerated := (coefficientProperties ell).2.1
  quotientTorsion := (coefficientProperties ell).2.2.1
  quotientPerfect := (coefficientProperties ell).2.2.2.1
  quotientFinite := (coefficientProperties ell).2.2.2.2

/-- The residue isomorphism is uniquely fixed by the actual p-adic residue map.
Source: sk-thm-purity-transport, A_n=Z/ell^n
(blueprint: def-pur-condensed-tate-integral-tower-data).
Proof: toZModPow is onto and its kernel is (ell^(n+1)). The quotient universal
property gives the ring equivalence and determines it on every quotient class. -/
theorem residueIso_existsUnique (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    ∃! e : PbcQuotient (datum.{u} ell) n ≃+* coefficient.{u} ell (n + 1),
      ∀ x : Ring.{u} ell,
        e (Ideal.Quotient.mk ((datum.{u} ell).ideal ^ (n + 1)) x) =
          ⟨⟨PadicInt.toZModPow (n + 1) x.down⟩⟩ := by
  let e : PbcQuotient (datum.{u} ell) n ≃+* coefficient.{u} ell (n + 1) :=
    (padicQuotientIso ell (n + 1)).trans
      ((ULift.ringEquiv : coefficient.{u} ell (n + 1) ≃+*
        FiniteReduction.Ring.{u} ell (n + 1)).trans ULift.ringEquiv).symm
  have he (x : Ring.{u} ell) :
      e (Ideal.Quotient.mk _ x) = ⟨⟨PadicInt.toZModPow (n + 1) x.down⟩⟩ := by
    change ULift.up (ULift.up (padicQuotientIso ell (n + 1) _)) = _
    exact congrArg (fun z ↦ ULift.up (ULift.up z)) (padicQuotientIso_mk ell (n + 1) x)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply RingEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (he' x).trans (he x).symm

/-- The uniquely residue-normalized identification of the two finite coefficient rings.
Source: sk-thm-purity-transport, finite coefficients
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def residueIso (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    PbcQuotient (datum.{u} ell) n ≃+* coefficient.{u} ell (n + 1) :=
  (residueIso_existsUnique ell n).exists.choose

private theorem residueIso_mk (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (x : Ring.{u} ell) :
    residueIso ell n (Ideal.Quotient.mk _ x) = ⟨⟨PadicInt.toZModPow (n + 1) x.down⟩⟩ :=
  (residueIso_existsUnique ell n).exists.choose_spec x

private theorem residueIso_quotient (ell : ℕ) [Fact ell.Prime]
    (b a : ℕ) (hab : a ≤ b) :
    (residueIso.{u} ell a).toRingHom.comp (pbcWitnessQuotientMap (datum ell) b a hab) =
      (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1)).comp
        (residueIso ell b).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  change residueIso ell a (Ideal.Quotient.mk _ x) =
    FiniteReduction.quotient ell (Nat.add_le_add_right hab 1)
      (residueIso ell b (Ideal.Quotient.mk _ x))
  rw [residueIso_mk, residueIso_mk]
  exact congrArg (fun z ↦ ULift.up (ULift.up z))
    (PadicInt.cast_toZModPow (a + 1) (b + 1) (Nat.add_le_add_right hab 1) x.down).symm

private theorem residueIso_symm_quotient (ell : ℕ) [Fact ell.Prime]
    (b a : ℕ) (hab : a ≤ b) :
    (pbcWitnessQuotientMap (datum.{u} ell) b a hab).comp
        (residueIso ell b).symm.toRingHom =
      (residueIso ell a).symm.toRingHom.comp
        (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1)) := by
  apply RingHom.ext
  intro x
  apply (residueIso ell a).injective
  have h := RingHom.congr_fun (residueIso_quotient.{u} ell b a hab)
    ((residueIso ell b).symm x)
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply] using h

/-- Constant residues acting on the continuous-function coefficient sheaf.
Source: sk-thm-purity-transport, finite coefficient presentations
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def scalars (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (coefficient.{u} ell (n + 1))) ⟶
      ((adicLisseForget T).obj ((pbcAdicRings T (datum.{u} ell)).obj (op n))).obj :=
  (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom (residueIso.{u} ell n).symm.toRingHom) ≫
    pbcFunctionScalars T (datum.{u} ell) n

/-- The finite scalar presentation is locally bijective.
Source: sk-thm-purity-transport, finite presentations
(blueprint: def-pur-condensed-tate-integral-tower-data).
Proof: the residue equivalence is bijective. The recorded pbcFunctionScalars is
locally bijective, so composing with the constant residue equivalence preserves
both local injectivity and local surjectivity. -/
theorem scalars_locallyBijective (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    Presheaf.IsLocallyInjective (ProEt.topology T) (scalars T ell n) ∧
      Presheaf.IsLocallySurjective (ProEt.topology T) (scalars T ell n) := by
  have : IsIso (RingCat.ofHom (residueIso.{u} ell n).symm.toRingHom) :=
    inferInstanceAs (IsIso (residueIso.{u} ell n).symm.toRingCatIso.hom)
  dsimp only [scalars]
  constructor <;> infer_instance

/-- Local injectivity of the actual finite presentation.
Source: sk-thm-purity-transport (blueprint: def-pur-condensed-tate-integral-tower-data). -/
instance scalars_injective (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    Presheaf.IsLocallyInjective (ProEt.topology T) (scalars T ell n) :=
  (scalars_locallyBijective T ell n).1

/-- Local surjectivity of the actual finite presentation.
Source: sk-thm-purity-transport (blueprint: def-pur-condensed-tate-integral-tower-data). -/
instance scalars_surjective (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    Presheaf.IsLocallySurjective (ProEt.topology T) (scalars T ell n) :=
  (scalars_locallyBijective T ell n).2

/-- Associated-module realization in the quotient coefficient sheaf's presentation.
Source: sk-thm-purity-transport, finite presentations
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def realization (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (coefficient ell (n + 1))) ⥤
      pbcModules T ((pbcAdicRings T (datum.{u} ell)).obj (op n)) :=
  pbcAssociatedModule T (coefficient ell (n + 1))
    ((adicLisseForget T).obj ((pbcAdicRings T (datum.{u} ell)).obj (op n))) (scalars T ell n)

/-- This change of coefficient presentation is an exact additive equivalence.
Source: sk-thm-purity-transport, finite presentations
(blueprint: def-pur-condensed-tate-integral-tower-data).
Proof: the scalar presentation is locally bijective, so the associated-module
sheafification and its inverse have invertible unit and counit. They preserve
underlying abelian sheaves and exactness; hence finite limits, colimits and sums. -/
theorem realization_exact (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    (realization T ell n).IsEquivalence ∧ (realization T ell n).Additive ∧
      PreservesFiniteLimits (realization T ell n) ∧
      PreservesFiniteColimits (realization T ell n) := by
  have : (realization T ell n).IsEquivalence :=
    coefficientRealization_isEquivalence (ProEt.topology T) (coefficient ell (n + 1))
      ((adicLisseForget T).obj ((pbcAdicRings T (datum.{u} ell)).obj (op n)))
      (scalars T ell n)
  exact ⟨this, Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- Additivity of the exact finite presentation equivalence.
Source: sk-thm-purity-transport (blueprint: def-pur-condensed-tate-integral-tower-data). -/
instance realization_additive (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    (realization T ell n).Additive := (realization_exact T ell n).2.1

/-- Finite-limit preservation of the exact finite presentation equivalence.
Source: sk-thm-purity-transport (blueprint: def-pur-condensed-tate-integral-tower-data). -/
instance realization_limits (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    PreservesFiniteLimits (realization T ell n) := (realization_exact T ell n).2.2.1

/-- Finite-colimit preservation of the exact finite presentation equivalence.
Source: sk-thm-purity-transport (blueprint: def-pur-condensed-tate-integral-tower-data). -/
instance realization_colimits (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    PreservesFiniteColimits (realization T ell n) := (realization_exact T ell n).2.2.2

/-- Exact coefficient realization on unbounded derived categories.
Source: sk-thm-purity-transport (blueprint: def-pur-condensed-tate-integral-tower-data). -/
def derivedRealization (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    proCategory (coefficient ell (n + 1)) T ⥤
      DerivedCategory (pbcModules T ((pbcAdicRings T (datum.{u} ell)).obj (op n))) :=
  (realization T ell n).mapDerivedCategory

private def quotientDiagram {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : ℕᵒᵖ ⥤ RingCat.{u + 1} where
  obj n := RingCat.of (PbcQuotient d n.unop)
  map f := RingCat.ofHom (pbcWitnessQuotientMap d _ _ (leOfHom f.unop))
  map_id n := by
    apply RingCat.hom_ext
    exact Ideal.Quotient.factor_eq
  map_comp f g := by
    apply RingCat.hom_ext
    exact (Ideal.Quotient.factor_comp
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom g.unop) 1))).symm

private theorem functionScalars_comp (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (b a : ℕ) (hab : a ≤ b) :
    pbcFunctionScalars T d b ≫
        ((adicLisseForget T).map (pbcAdicQuotient T d b a hab)).hom =
      (Functor.const T.ProEtᵒᵖ).map
        (RingCat.ofHom (pbcWitnessQuotientMap d b a hab)) ≫
          pbcFunctionScalars T d a := by
  let F := quotientDiagram d ⋙ Functor.const T.ProEtᵒᵖ
  let G := pbcAdicRings T d ⋙ adicLisseForget T ⋙
    sheafToPresheaf (ProEt.topology T) RingCat
  let η : F ⟶ G := NatTrans.ofOpSequence (pbcFunctionScalars T d)
    (fun n ↦ (pbcFunctionScalars_comp T d n).symm)
  exact (η.naturality (homOfLE hab).op).symm

/-- Residue-normalized scalar presentations commute with every quotient map.
Source: sk-thm-purity-transport, quotient cocycle
(blueprint: def-pur-condensed-tate-integral-tower-data).
Proof: evaluate on a constant coefficient represented by a p-adic integer. Both
paths take its residue at exponent a+1. The residue specifications and the
sheafification unit determine the maps on arbitrary local sections. -/
theorem scalars_comp (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (b a : ℕ) (hab : a ≤ b) :
    scalars T ell b ≫ ((adicLisseForget T).map
        (pbcAdicQuotient T (datum.{u} ell) b a hab)).hom =
      (Functor.const T.ProEtᵒᵖ).map
        (RingCat.ofHom (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))) ≫
          scalars T ell a := by
  dsimp only [scalars]
  rw [Category.assoc, functionScalars_comp]
  rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
  congr 2
  exact congrArg RingCat.ofHom (residueIso_symm_quotient ell b a hab)

/-- The restriction comparison is identity on the underlying additive sheafification.
It is the uniquely normalized comparison from the recorded realization interface.
Source: sk-thm-purity-transport, coefficient comparisons
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def restrictionComparison (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (b a : ℕ) (hab : a ≤ b) :
    Sheaf.restrictScalars (ProEt.topology T)
        (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) ⋙ realization T ell b ≅
      realization T ell a ⋙ pbcRestrict (pbcAdicQuotient T (datum.{u} ell) b a hab) :=
  (pbcAssociatedRestriction_exists T (coefficient ell (b + 1)) (coefficient ell (a + 1))
    ((adicLisseForget T).obj ((pbcAdicRings T (datum.{u} ell)).obj (op b)))
    ((adicLisseForget T).obj ((pbcAdicRings T (datum.{u} ell)).obj (op a)))
    (scalars T ell b) (scalars T ell a)
    (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
    ((adicLisseForget T).map (pbcAdicQuotient T (datum.{u} ell) b a hab))
    (scalars_comp T ell b a hab)).exists.choose

/-- Exact descent of the identity-normalized scalar restriction comparison.
Source: sk-thm-purity-transport, coefficient comparisons
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def derivedRestrictionComparison (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (b a : ℕ) (hab : a ≤ b) :
    @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (ProEt.topology T) _ _ _ _
        (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) ⋙
      derivedRealization T ell b ≅
        derivedRealization T ell a ⋙
          pbcDerivedRestrict (pbcAdicQuotient T (datum.{u} ell) b a hab) :=
  (Functor.mapDerivedCategoryCompIso
    (Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)))
    (realization T ell b)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (restrictionComparison T ell b a hab) ≪≫
      Functor.mapDerivedCategoryCompIso (realization T ell a)
        (pbcRestrict (pbcAdicQuotient T (datum.{u} ell) b a hab))

/-- The scalar-extension comparison is the mate of actual scalar restriction.
Source: sk-thm-purity-transport, coefficient comparisons
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def scalarComparisonMap (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (b a : ℕ) (hab : a ≤ b) :
    derivedRealization T ell b ⋙ pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab) ⟶
      proScalar (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) T ⋙
        derivedRealization T ell a :=
  ((mateEquiv (Adjunction.ofIsRightAdjoint
      (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (ProEt.topology T) _ _ _ _
        (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))))
    (pbcDerivedScalarAdjunction (pbcAdicQuotient T (datum.{u} ell) b a hab))).symm
    (TwoSquare.mk _ _ _ _ (derivedRestrictionComparison T ell b a hab).hom)).natTrans

/-- The specified scalar mate is invertible, including at equal indices.
Source: sk-thm-purity-transport, normalized quotients
(blueprint: def-pur-condensed-tate-integral-tower-data).
Proof: realization is an exact coefficient-presentation equivalence. Conjugate
both scalar adjunctions through its inverse. The identity-normalized restriction
isomorphism identifies their right adjoints, so its left-adjoint mate is invertible.
On K-flat representatives it is ordinary balancing, with inverse inserting one. -/
theorem scalarComparisonMap_isIso (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (b a : ℕ) (hab : a ≤ b) : IsIso (scalarComparisonMap T ell b a hab) := by
  have (m : ℕ) : (realization T ell m).IsEquivalence := (realization_exact T ell m).1
  have (m : ℕ) : (derivedRealization T ell m).IsEquivalence := by
    dsimp only [derivedRealization]
    infer_instance
  exact isIso_inverseMate_of_equivalences _ _ (derivedRestrictionComparison T ell b a hab)

/-- The canonical scalar comparison, fixed by its explicit adjunction-mate formula.
Source: sk-thm-purity-transport, normalized quotients
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def scalarComparison (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (b a : ℕ) (hab : a ≤ b) :
    derivedRealization T ell b ⋙ pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab) ≅
      proScalar (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) T ⋙
        derivedRealization T ell a :=
  @asIso _ _ _ _ (scalarComparisonMap T ell b a hab)
    (scalarComparisonMap_isIso T ell b a hab)

/-- The actual finite twist, with its ordered root tensors and shift [2d].
At d=0 it is the constant coefficient object. The finite-purity dependency
identifies its root factors with the actual pro-etale roots kernel.
Source: sk-thm-purity-transport, normalized Tate-unit tower
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def finiteTwist (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n d : ℕ) :
    proCategory (coefficient ell (n + 1)) T :=
  (comparison (coefficient ell (n + 1)) T).obj
    (line (coefficient ell (n + 1)) (ell ^ (n + 1)) (CharP.cast_eq_zero _ _) T d)

/-- Scalar extension of the constant finite unit, with its canonical normalization.
Source: sk-thm-purity-transport, quotient maps on the unit tower
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def unitReduction (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (b a : ℕ) (hab : a ≤ b) :
    (proScalar (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) T).obj
        (𝟙_ _) ≅ (𝟙_ (proCategory (coefficient ell (a + 1)) T)) :=
  (proScalar (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) T).mapIso
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
        (coefficient ell (b + 1)) T).symm ≪≫
    (ProEtale.pbcComparisonReduction T
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))).app (𝟙_ _) ≪≫
    (comparison (coefficient ell (a + 1)) T).mapIso
      (Etale.ExceptionalCoefficients.unitIso
        (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) T) ≪≫
    ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
      (coefficient ell (a + 1)) T

/-- Identify the purity source at the unit with the actual shifted root tensor.
The arrows are the fixed site comparison, pullback unit and tensor unitor.
Source: sk-thm-purity-transport, finite purity at the unit
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def unitSource (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    (finiteProSource ell (n + 1) f d).obj (𝟙_ _) ≅ finiteTwist X ell n d :=
  (finiteProSource ell (n + 1) f d).mapIso
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
        (coefficient ell (n + 1)) Y).symm ≪≫
    (sourceAtOriginIso (coefficient ell (n + 1)) f
      (line (coefficient ell (n + 1)) (ell ^ (n + 1))
        (CharP.cast_eq_zero _ _) X d) (𝟙_ _)).symm ≪≫
    (comparison (coefficient ell (n + 1)) X).mapIso
      (((Etale.derivedTensor (ModuleCat.{u + 1} (coefficient ell (n + 1))) X).mapIso
        (Etale.leftDerivedUpperStarUnitIso
          (ModuleCat.{u + 1} (coefficient ell (n + 1))) f)).app _ ≪≫
        Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} (coefficient ell (n + 1))) X _)

/-- The given finite smooth-purity map at the constant unit, in root-tensor coordinates.
The orientation in the recorded Level is fixed by diagonal deformation and Kummer.
Source: sk-thm-purity-transport, gamma at A_n
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def gammaUnit (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) (s : Level ell (n + 1) f d) :
    finiteTwist X ell n d ⟶ (exceptional (coefficient ell (n + 1)) f).obj (𝟙_ _) :=
  (unitSource ell n f d).inv ≫
    proGamma (coefficient ell (n + 1)) f
      (line (coefficient ell (n + 1)) (ell ^ (n + 1))
        (CharP.cast_eq_zero _ _) X d) s.alpha (𝟙_ _)

/-- The finite-ring comparison fixed by the p-adic residue map on constant sections.
Source: sk-thm-purity-transport, finite Tate coefficients
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def coefficientIso (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    (pbcAdicRings T (datum.{u} ell)).obj (op n) ≅ purTwistFiniteRing T ell n :=
  (pbcLevelConstantComparison T (datum.{u} ell) n).symm ≪≫
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso
      (((residueIso.{u} ell n).trans
        ((ULift.ringEquiv : coefficient.{u} ell (n + 1) ≃+*
            FiniteReduction.Ring.{u} ell (n + 1)).trans
          ((ULift.ringEquiv : FiniteReduction.Ring.{u} ell (n + 1) ≃+*
              ZMod (ell ^ (n + 1))).trans
            (ULift.ringEquiv : ULift.{u + 1} (ZMod (ell ^ (n + 1))) ≃+*
              ZMod (ell ^ (n + 1))).symm))).toCommRingCatIso)

private theorem coefficientIso_naturality (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) :
    (coefficientIso T ell (n + 1)).hom ≫ purTwistFiniteTransition T ell n =
      pbcAdicQuotient T (datum ell) (n + 1) n (Nat.le_succ n) ≫
        (coefficientIso T ell n).hom := by
  apply (cancel_epi (pbcLevelConstantComparison T (datum ell) (n + 1)).hom).1
  have h := pbcConstantSystemComparison_naturality T (datum ell)
    (homOfLE (Nat.le_succ n)).op
  change (adicLisseRingSystem T (datum ell).ideal).map (homOfLE (Nat.le_succ n)).op ≫
      (pbcLevelConstantComparison T (datum ell) n).hom =
    (pbcLevelConstantComparison T (datum ell) (n + 1)).hom ≫
      pbcAdicQuotient T (datum ell) (n + 1) n (Nat.le_succ n) at h
  dsimp only [coefficientIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ,
    purTwistFiniteTransition, purTwistFiniteTransitionOfUniverses]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  change ULift.up
      (ZMod.cast (residueIso ell (n + 1) (Ideal.Quotient.mk _ x)).down.down) =
    ULift.up (residueIso ell n (Ideal.Quotient.mk _ x)).down.down
  rw [residueIso_mk, residueIso_mk]
  exact congrArg ULift.up
    (PadicInt.cast_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _) x.down)

private def coefficientTowerIso (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] :
    pbcAdicRings T (datum ell) ≅ purTwistZlTower T ell :=
  NatIso.ofComponents (fun n ↦ coefficientIso T ell n.unop) (by
      let h : (pbcAdicRings T (datum ell)) ⟶ purTwistZlTower T ell :=
        NatTrans.ofOpSequence (fun n ↦ (coefficientIso T ell n).hom) (by
          intro n
          simpa only [purTwistZlTower, purTwistZlTowerOfUniverses, pbcAdicQuotient,
            pbcAdicRings, AdicCoefficients.ringSystem,
            Functor.ofOpSequence_map_homOfLE_succ] using
            (coefficientIso_naturality T ell n).symm)
      intro j k f
      simpa only [h, NatTrans.ofOpSequence_app] using h.naturality f)

private theorem coefficientTowerIso_hom_app (T : Scheme.{u}) (ell : ℕ)
    [Fact ell.Prime] (n : ℕᵒᵖ) :
    (coefficientTowerIso T ell).hom.app n = (coefficientIso T ell n.unop).hom := rfl

private theorem limitIso_existsUnique
    {J C : Type*} [Category J] [Category C] {F G : J ⥤ C}
    [HasLimit F] [HasLimit G] (η : F ≅ G) :
    ∃! e : limit F ≅ limit G, ∀ j : J,
      e.hom ≫ limit.π G j = limit.π F j ≫ η.hom.app j := by
  refine ⟨HasLimit.isoOfNatIso η, HasLimit.isoOfNatIso_hom_π η, ?_⟩
  intro e he
  apply Iso.ext
  exact limit.hom_ext (fun j ↦ (he j).trans (HasLimit.isoOfNatIso_hom_π η j).symm)

/-- The two completed-ring presentations are uniquely identified by every projection.
Source: sk-thm-purity-transport, completed Tate coefficients
(blueprint: def-pur-condensed-tate-integral-tower-data).
Proof: the finite residue comparisons commute with quotient maps because both
send a p-adic integer to its residue. They give an isomorphism of inverse systems.
The induced limit isomorphism has the displayed projection equations; joint
monicity of the limit projections proves uniqueness. -/
theorem completionIso_existsUnique (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] :
    ∃! e : pbcAdicCompletion T (datum.{u} ell) ≅ purTwistZlCompletion T ell,
      ∀ n : ℕ, e.hom ≫ purTwistZlProjection T ell n =
        pbcAdicProjection T (datum.{u} ell) n ≫ (coefficientIso T ell n).hom := by
  obtain ⟨e, he, hu⟩ := limitIso_existsUnique (coefficientTowerIso T ell)
  have hproj (n : ℕᵒᵖ) :
      e.hom ≫ limit.π (purTwistZlTower T ell) n =
        limit.π (pbcAdicRings T (datum ell)) n ≫ (coefficientIso T ell n.unop).hom :=
    (he n).trans (congrArg (limit.π (pbcAdicRings T (datum ell)) n ≫ ·)
      (coefficientTowerIso_hom_app T ell n))
  refine ⟨e, fun n ↦ hproj (op n), ?_⟩
  intro e' he'
  apply hu e'
  intro n
  exact (he' n.unop).trans
    (congrArg (limit.π (pbcAdicRings T (datum ell)) n ≫ ·)
      (coefficientTowerIso_hom_app T ell n).symm)

/-- The uniquely projection-normalized completed-ring comparison.
Source: sk-thm-purity-transport, completed Tate coefficients
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def completionIso (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] :
    pbcAdicCompletion T (datum.{u} ell) ≅ purTwistZlCompletion T ell :=
  (completionIso_existsUnique T ell).exists.choose

/-- The actual integral root line, with scalar action transported by the fixed comparison.
Source: sk-thm-purity-transport, inverse limit of roots
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def integralRoot (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] :
    pbcModules T (pbcAdicCompletion T (datum.{u} ell)) :=
  (pbcRestrict (completionIso T ell).hom).obj (purTwistZlModule T ell)

/-- The ordered ordinary d-fold tensor of the actual integral root line, with unit at zero.
Source: sk-thm-purity-transport, H_X=Z_X tensor-power d
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def integralLine (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] :
    ℕ → pbcModules T (pbcAdicCompletion T (datum.{u} ell))
  | 0 => SheafOfModules.unit ((adicLisseForget T).obj (pbcAdicCompletion T (datum.{u} ell)))
  | d + 1 => @MonoidalCategory.tensorObj _ _
      (@SheafOfModules.cochainModulesMonoidal.{u + 1, u, u + 1}
        T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} T.ProEt)
        (ProEt.topology T) inferInstance
          (pbcAdicCompletion T (datum.{u} ell))).toMonoidalCategoryStruct
      (integralLine T ell d) (integralRoot T ell)

/-- The strict quotient tower of the actual root tensor, constructed before localization.
The recorded ordinary tensor tower has the quotient maps as its transitions.
The actual root projections identify these transitions with root-power transitions.
Source: sk-thm-purity-transport, strict normalized Tate-unit tower
(blueprint: def-pur-condensed-tate-integral-tower-data). -/
def strictTower (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (d : ℕ) :
    pbcTowers T (pbcAdicCompletion T (datum.{u} ell)) :=
  (localReductionModuleTower T (pbcAdicCompletion T (datum.{u} ell))
    (pbcAdicRings T (datum.{u} ell))
    { app := fun n ↦ pbcAdicProjection T (datum.{u} ell) n.unop
      naturality := fun _ _ f ↦ (limit.w (pbcAdicRings T (datum.{u} ell)) f).symm }).obj
        (integralLine T ell d)

/-- The finite ordinary root tensor in the coefficient-sheaf presentation.
Source: reconstruction Step 2 (blueprint: def-pur-condensed-tate-integral-tower-data). -/
def finiteSheaf (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n d : ℕ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (coefficient ell (n + 1))) T).obj
    (finiteEtaleTateTwist T (ell ^ (n + 1)) (coefficient ell (n + 1))
      (CharP.cast_eq_zero _ _) d)

/-- Exact realization commutes with the canonical shifts.
Source: reconstruction Step 2 (blueprint: def-pur-condensed-tate-integral-tower-data). -/
instance derivedRealization_shift (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    (derivedRealization T ell n).CommShift ℤ :=
  inferInstanceAs ((realization T ell n).mapDerivedCategory.CommShift ℤ)

/-- Exact site comparison commutes with the canonical shifts.
Source: reconstruction Step 2 (blueprint: def-pur-condensed-tate-integral-tower-data). -/
instance comparison_shift (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    (comparison (coefficient ell (n + 1)) T).CommShift ℤ :=
  inferInstanceAs ((ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (coefficient ell (n + 1))) T).mapDerivedCategory.CommShift ℤ)

/-- Regroup the specified shifted finite roots using the existing tensor-counit comparison.
Source: reconstruction Step 2 (blueprint: def-pur-condensed-tate-integral-tower-data). -/
def finiteModelIso (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ) :
    (derivedRealization T ell n).obj (finiteTwist T ell n d) ≅
      (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
        ((realization T ell n).obj (finiteSheaf T ell n d)) :=
  (derivedRealization T ell n).mapIso
      ((comparison (coefficient ell (n + 1)) T).mapIso
        (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (n + 1))
          (ell ^ (n + 1)) (pow_pos (Fact.out : ell.Prime).pos _)
          (CharP.cast_eq_zero _ _) T (by simpa using hT.pow (n + 1)) d) ≪≫
        ((comparison (coefficient ell (n + 1)) T).commShiftIso (2 * (d : ℤ))).app _ ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          ((Functor.mapDerivedCategorySingleFunctor
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (coefficient ell (n + 1))) T) 0).app _)) ≪≫
    ((derivedRealization T ell n).commShiftIso (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (((realization T ell n).mapDerivedCategorySingleFunctor 0).app _) ≪≫
    ((_root_.DerivedCategory.singleFunctors _).shiftIso (2 * (d : ℤ))
      (-(2 * (d : ℤ))) 0 (by omega)).app _

attribute [local irreducible] finiteModelIso

attribute [local irreducible] integralPure

attribute [local irreducible] integralGenerator

attribute [local irreducible] ProjectionBalanced

attribute [local irreducible] ProjectionNormalized

/-- At zero, the finite twist is the unit through the existing comparison-unit map.
Source: reconstruction Step 2 (blueprint: def-pur-condensed-tate-integral-tower-data). -/
def finiteZeroIso (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    finiteTwist T ell n 0 ≅ 𝟙_ (proCategory (coefficient ell (n + 1)) T) :=
  (comparison (coefficient ell (n + 1)) T).mapIso
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} (coefficient ell (n + 1))) T) ≪≫
    ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
      (coefficient ell (n + 1)) T

attribute [local irreducible] Reconstructed

end AlgebraicGeometry.Scheme.PurityIntegralTower
