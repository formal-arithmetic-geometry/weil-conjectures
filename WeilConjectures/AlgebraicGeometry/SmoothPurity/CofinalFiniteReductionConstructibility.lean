/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CofinalCoefficientProjectionCocone
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.AlgebraicGeometry.SmoothPurityFiniteScalarReconstructionTools
public import WeilConjectures.SmoothPurity.ChangeOfRingsKFlatIndependentCoefficients

/-! # Cofinal finite reductions and constructibility

Source: blueprint main-20261015, sk-lem-sp-tower, final integral-constructibility sentence;
Stacks Tags 0D6D and 0G7E; scalar-extension proof paragraphs (2) and (4)
(blueprint: lem-sp-cofinal-finite-reduction-constructibility).

Index n means positive exponent n+1. The ordinary and derived tensors below are the
published universal presentations. Their normalization records the pure-tensor formula,
K-flat counit calculation, and naturality under commuting coefficient squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.SuccessiveDerivedQuotient

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})

section
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify

attribute [local instance] cofinalSiteSmall

end

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- The quotient exists exactly at the stated cofinal exponents.
Source: blueprint tower proof, quotient arithmetic; Stacks 0D6D
(blueprint: lem-sp-cofinal-finite-reduction-constructibility).
Proof: ell = v*pi^e implies ell^(N+1) = v^(N+1)*pi^(e*(N+1)).
When j+1 <= e*(N+1), factor out pi^(j+1). The principal-ideal power formula
then gives the required inclusion. This uses no unramifiedness assumption. -/
theorem sp_cofinal_finite_ideal_le (e : ℕ)
    (v : (Padic.coefficientExtensionIntegers l E)ˣ)
    (hfactor : (l : Padic.coefficientExtensionIntegers l E) =
      v * Padic.coefficientExtensionUniformizer l E ^ e)
    (N j : ℕ) (h : j + 1 ≤ e * (N + 1)) :
    spEllIdeal l E ^ (N + 1) ≤ Padic.coefficientExtensionIdeal l E (j + 1) := by
  change Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ (N + 1) ≤
    Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ (j + 1)
  rw [hfactor, Ideal.span_singleton_mul_left_unit v.isUnit,
    ← Ideal.span_singleton_pow, ← pow_mul]
  exact Ideal.pow_le_pow_right h

/-- The canonical quotient, sending the class of x to the class of x.
Source: blueprint tower proof, quotient arithmetic
(blueprint: lem-sp-cofinal-finite-reduction-constructibility). -/
def spCofinalFiniteQuotient (e : ℕ)
    (v : (Padic.coefficientExtensionIntegers l E)ˣ)
    (hfactor : (l : Padic.coefficientExtensionIntegers l E) =
      v * Padic.coefficientExtensionUniformizer l E ^ e)
    (N j : ℕ) (h : j + 1 ≤ e * (N + 1)) :
    (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (N + 1)) →+*
      Padic.coefficientExtensionRing l E (j + 1) :=
  Ideal.Quotient.factor (sp_cofinal_finite_ideal_le l E e v hfactor N j h)

/-- Constant sheafification of the actual cofinal quotient, retaining target coefficients.
Source: blueprint tower proof, quotient arithmetic
(blueprint: lem-sp-cofinal-finite-reduction-constructibility). -/
def spCofinalFiniteCoefficientMap (e : ℕ)
    (v : (Padic.coefficientExtensionIntegers l E)ˣ)
    (hfactor : (l : Padic.coefficientExtensionIntegers l E) =
      v * Padic.coefficientExtensionUniformizer l E ^ e)
    (N j : ℕ) (h : j + 1 ≤ e * (N + 1)) :
    (spCoefficientCommRings.{u, u} l E T).obj (op N) ⟶
      WeilConjectures.integralCoefficientCommRingSheaf.{u, u} l E T j :=
  letI : HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
    WeilConjectures.integralCoefficientRingSheafify.{u, u} T
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((spCofinalFiniteQuotient l E e v hfactor N j h).comp
        ULift.ringEquiv.toRingHom)))

/-- The standard-localization instance of the recorded universal scalar presentation.
This is only an abbreviation of the dependency's data, not a new tensor construction.
Source: Stacks 06YY (blueprint: lem-sp-cofinal-finite-reduction-constructibility). -/
abbrev spCofinalScalarPresentation
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :=
  Presentation.{u + 1, u, u + 1, u + 2} (C := T.ProEt)
    (J := Scheme.ProEt.topology T)
    (hD := fun R ↦ HasDerivedCategory.standard
      (SheafOfModules.SuccessiveDerivedQuotient.Modules.{u + 1, u, u + 1} R)) a

private def cofinalPresentationScalarIso {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B)
    (P : spCofinalScalarPresentation T (Scheme.proEtaleConstantRingMap (T := T) f)) :
    P.derived ≅ spFiniteScalarExtension f T := by
  let φ := Scheme.proEtaleConstantRingMap (T := T) f
  let F := reductionChange T φ
  let i : P.ordinary ≅ F := NatIso.ofComponents
    (fun M ↦ eqToIso ((P.obj_eq M).trans (reductionChange_obj_eq T φ M).symm)) (by
      intro M N g
      dsimp only [eqToIso.hom]
      rw [P.map_eq, reductionChange_map_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
      rfl)
  let ih : P.ordinary.mapHomotopyCategory (.up ℤ) ≅ F.mapHomotopyCategory (.up ℤ) :=
    { hom := i.hom.mapHomotopyCategory (.up ℤ)
      inv := i.inv.mapHomotopyCategory (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, i.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, i.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  have := P.universal
  exact Functor.leftDerivedNatIso P.derived (reductionDerivedChange T φ)
    P.counit (reductionDerivedCounit T φ)
    (HomotopyCategory.quasiIso (SheafOfModules.SuccessiveDerivedQuotient.Modules.{u + 1, u, u + 1}
      (Scheme.proEtaleConstantRing T A)) (.up ℤ))
    (Functor.isoWhiskerRight ih DerivedCategory.Qh)

private theorem cofinalTorIso {A : Type u} [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (i : K ≅ L) (a b : ℤ)
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  obtain ⟨P, hf, hb, ⟨e⟩⟩ := (spFiniteScalar_tor_flat_model T A K a b h.1).mp h
  exact (spFiniteScalar_tor_flat_model T A L a b h.1).mpr
    ⟨P, hf, hb, ⟨i.symm ≪≫ e⟩⟩

private theorem cofinalTorVanishing {A : Type u} [CommRing A]
    (K : Scheme.proEtaleDerivedCategory T A) (a b : ℤ)
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) (i : ℤ) (hi : i < a ∨ b < i) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
  obtain ⟨P, _, hb, ⟨e⟩⟩ := (spFiniteScalar_tor_flat_model T A K a b h.1).mp h
  exact ((P.sc i).isZero_homology_of_isZero_X₂ (hb i hi)).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P)

/-- Cofinal scalar associativity, its K-flat model, and transfer of constructibility
and the same Tor interval. The completed ell projections are specified by equality
with the uniquely normalized limit comparison; they are not arbitrary coefficient maps.
The family `n` is the published normalized presentation of scalar extension. Its fields
`ordinary_hom`, `ordinary_inv`, and `representative` specify precisely the ordinary
reassociation formula and its derived class; `coefficient_naturality` and `associative`
specify compatibility with further quotients in both indices. They apply to the displayed
canonical quotients. Using arbitrary such presentations expresses independence of models.
Source: blueprint main-20261015, tower proof final integral-constructibility sentence;
Stacks 0D6D, 0G7E; scalar-extension proof (2),(4)
(blueprint: lem-sp-cofinal-finite-reduction-constructibility).

Proof: (1) The ideal inclusion above defines the quotient. Every quotient square commutes
because all maps send the class of x to the class of x. Composing the completed ell
projection with the quotient is the uniformizer projection: check after the canonical
constant-to-completion map and use the finite-quotient normalization/uniqueness.
(2) For an acyclic B-complex L, exact scalar restriction preserves acyclicity. Ordinary
scalar-tensor cancellation identifies the restriction of L tensor_B (P tensor_R B)
with Res(L) tensor_R P. K-flatness of P kills its cohomology; restriction detects this.
Thus the extended representative is K-flat (lem-pur-sheaf-ring-derived-coefficient-adjunction,
lem-sfb-scalar-tensor-cancellation-independent, def-pc-kflat-complex).
(3) Apply lem-sfb-successive-derived-quotient-normalization and lem-pc-kflat-resolution.
Its ordinary formula is (x tensor b) tensor d mapped to x tensor (bar(b)*d), with inverse
x tensor d mapped to (x tensor 1) tensor d; its counit equation fixes the derived map
in D(D_j). Naturality and coherence give all further quotient compatibilities.
(4) Test the assumed Tor interval on the degree-zero unit B_N: cohomology vanishes
outside [a,b]. Thus each reduction is bounded constructible of finite Tor dimension.
For j choose N=j (in positive-exponent notation); e>=1 makes this cofinal. Apply clause
(2) of det-sp-scalar-extension-functor to the finite quotient map, with no flatness or
finite projective-dimension requirement. Transport constructibility and the same Tor
interval through (3); testing on D_j gives the stated cohomology vanishing. No assumption
on completeness, invertibility of ell on T, or boundedness of the original K is used. -/
theorem sp_cofinal_finite_reduction_constructibility (e : ℕ) (he : 1 ≤ e)
    (v : (Padic.coefficientExtensionIntegers l E)ˣ)
    (hfactor : (l : Padic.coefficientExtensionIntegers l E) =
      v * Padic.coefficientExtensionUniformizer l E ^ e)
    (β : ∀ N : ℕ, WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶
      (spCoefficientCommRings.{u, u} l E T).obj (op N))
    (hβ : ∀ N : ℕ,
      (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (β N) =
      (sp_completed_coefficient_limit l E T).exists.choose.hom ≫
        limit.π (spCoefficientRings l E T) (op N))
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
      (a : R ⟶ S), spCofinalScalarPresentation T a)
    (n : Normalization.{u + 1, u, u + 1, u + 2}
      (C := T.ProEt) (J := Scheme.ProEt.topology T)
      (hD := fun R ↦ HasDerivedCategory.standard
      (SheafOfModules.SuccessiveDerivedQuotient.Modules.{u + 1, u, u + 1} R)) p) :
    (∀ (N j : ℕ) (h : j + 1 ≤ e * (N + 1)),
      ∃ hcomp : β N ≫ spCofinalFiniteCoefficientMap l E T e v hfactor N j h =
          WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j,
        ∃ α : (p (β N)).derived ⋙
            (p (spCofinalFiniteCoefficientMap l E T e v hfactor N j h)).derived ≅
          (p (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j)).derived,
          α = n.derived (β N) (spCofinalFiniteCoefficientMap l E T e v hfactor N j h) ≪≫
            eqToIso (congrArg (fun f ↦ (p f).derived) hcomp)) ∧
    (∀ (N : ℕ)
      (P : CochainComplex
        (SheafOfModules.SuccessiveDerivedQuotient.Modules.{u + 1, u, u + 1}
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients P →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := Scheme.ProEt.topology T)
        (R := WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (P.X i)) →
      CochainComplex.IsKFlatIndependentCoefficients
        (((p (β N)).ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ∧
    ∀ (K : @DerivedCategory
        (SheafOfModules.SuccessiveDerivedQuotient.Modules.{u + 1, u, u + 1}
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T))
          _ _ (HasDerivedCategory.standard _)) (a b : ℤ), a ≤ b →
      (∀ N : ℕ,
        (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (N + 1))
          ((DerivedCategory.homologyFunctor _ i).obj ((p (β N)).derived.obj K))) ∧
        Scheme.HasProEtaleTorAmplitude T
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (N + 1))
          ((p (β N)).derived.obj K) a b) →
      ∀ j : ℕ,
        (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T
          (Padic.coefficientExtensionRing l E (j + 1))
          ((DerivedCategory.homologyFunctor _ i).obj
            ((p (WeilConjectures.completedIntegralCommRingProjectionUnrestricted
              l E T j)).derived.obj
              K))) ∧
        Scheme.HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (j + 1))
          ((p (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j)).derived.obj
            K) a b ∧
        ∀ i : ℤ, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((p (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j)).derived.obj
            K)) := by
  obtain ⟨H, hH, _⟩ := sp_cofinal_coefficient_projection_cocone l E T e he v hfactor
  have hc (N j : ℕ) (h : j + 1 ≤ e * (N + 1)) :
      β N ≫ spCofinalFiniteCoefficientMap l E T e v hfactor N j h =
        WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j := by
    apply (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
    rw [Functor.map_comp, hβ N]
    have hchoose : (sp_completed_coefficient_limit l E T).exists.choose =
        (sp_completed_coefficient_limit l E T).choose :=
      (sp_completed_coefficient_limit l E T).unique
        (sp_completed_coefficient_limit l E T).exists.choose_spec
        (sp_completed_coefficient_limit l E T).choose_spec.1
    rw [hchoose]
    convert (hH N j h).2.2.2.1 using 1
    · rfl
    · ext U x
      rfl
  refine ⟨?_, ?_, ?_⟩
  · intro N j h
    refine ⟨hc N j h, ?_⟩
    refine ⟨n.derived (β N)
      (spCofinalFiniteCoefficientMap l E T e v hfactor N j h) ≪≫
        eqToIso (congrArg (fun f ↦ (p f).derived) (hc N j h)), rfl⟩
  · intro N P hP hf
    exact (SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      (J := Scheme.ProEt.topology T)
      (β N) P (p (β N)).ordinary (p (β N)).obj_eq (p (β N)).map_eq hP
        (fun i ↦ (SheafOfModules.flat_to_cat.{u + 1, u, u + 1} _ (P.X i) (hf i)).2)).1
  · intro K a b hab hK j
    have hj : j + 1 ≤ e * (j + 1) := Nat.le_mul_of_pos_left (j + 1) he
    let q := spCofinalFiniteQuotient l E e v hfactor j j hj
    let δ := WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j
    let α : (p (β j)).derived ⋙
        (p (spCofinalFiniteCoefficientMap l E T e v hfactor j j hj)).derived ≅
          (p δ).derived :=
      n.derived (β j) (spCofinalFiniteCoefficientMap l E T e v hfactor j j hj) ≪≫
      eqToIso (congrArg (fun f ↦ (p f).derived) (hc j j hj))
    let i : (spFiniteScalarExtension q T).obj ((p (β j)).derived.obj K) ≅
        (p δ).derived.obj K :=
      (cofinalPresentationScalarIso T q
        (p (spCofinalFiniteCoefficientMap l E T e v hfactor j j hj))).symm.app _ ≪≫
        α.app K
    have hkill : (l ^ (j + 1) :
        Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (j + 1)) = 0 :=
      (hH j j hj).2.2.2.2.2.2.1
    have hkill' : (l ^ (j + 1) : Padic.coefficientExtensionRing l E (j + 1)) = 0 :=
      (hH j j hj).2.2.2.2.2.2.2
    have hA : ∃ n : ℕ, ∀ x :
        Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (j + 1),
        (l ^ n) • x = 0 := by
      refine ⟨j + 1, fun x ↦ ?_⟩
      rw [nsmul_eq_mul, Nat.cast_pow, hkill, zero_mul]
    have hB : ∃ n : ℕ, ∀ x : Padic.coefficientExtensionRing l E (j + 1),
        (l ^ n) • x = 0 := by
      refine ⟨j + 1, fun x ↦ ?_⟩
      rw [nsmul_eq_mul, Nat.cast_pow, hkill', zero_mul]
    obtain ⟨_, hconstructible, htor⟩ := spFiniteScalar_preserves_constructible_tor
      l hA hB q T ((p (β j)).derived.obj K)
      (spFiniteScalar_bounded_of_tor T _ _ a b (hK j).2) (hK j).1 a b (hK j).2
    have ht := cofinalTorIso T i a b htor
    refine ⟨?_, ht, cofinalTorVanishing T _ a b ht⟩
    intro k
    exact constructibleProEtale_of_iso T _
      ((DerivedCategory.homologyFunctor _ k).mapIso i) (hconstructible k)

end AlgebraicGeometry.ProEtale
