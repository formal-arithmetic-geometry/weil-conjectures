/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
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
public import Mathlib.CategoryTheory.Sites.Equivalence
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.SixFunctors.Finite.FiniteConstructibleHom
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Residue-controlled uniform bounds for finite internal Homs

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-tower,
cor-coef-integral-internal-hom.proof.md, sentences 2–3 and the final sentence
(blueprint: lem-coef-residue-controlled-finite-homs).

The index `n : ℕ` denotes exponent `n+1`; index zero is the residue reduction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem support_of_torAmplitude (X : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory X A) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A K a b) :
    proEtaleCohomologicalSupport K ⊆ Set.Icc a b := by
  classical
  let R := proEtaleConstantRing X A
  let C := proEtaleRingModules X R
  let := SheafOfModules.monoidalCategory R
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  have := SheafOfModules.tensorPreadditive R
  have : (DerivedCategory.Q (C := C)).EssSurj :=
    Localization.essSurj _ (HomologicalComplex.quasiIso C (.up ℤ))
  let L := (DerivedCategory.Q (C := C)).objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K :=
    (DerivedCategory.Q (C := C)).objObjPreimageIso K
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral (R := R) L
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
  let et : derivedTensor X A L
      ((HomologicalComplex.single C (.up ℤ) 0).obj (MonoidalCategory.tensorUnit C))
      P f hf hP ≅ K :=
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫
      asIso (DerivedCategory.Q.map f) ≪≫ e
  intro i hi
  by_contra hout
  have hoff : i < a ∨ b < i := by
    change ¬ (a ≤ i ∧ i ≤ b) at hout
    omega
  have hz := h.2 L P ⟨e⟩ f hf hP (MonoidalCategory.tensorUnit C) i hoff
  exact hi (hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso et.symm))

/-- The finite internal Hom of the two canonical reductions, at exponent `n+1`.
It uses modules over the constant finite coefficient sheaf on the original small site.
Source: main-20261015, cor-coef-integral-internal-hom.proof.md, sentence 3
(blueprint: lem-coef-residue-controlled-finite-homs). -/
noncomputable def integralFiniteInternalHom
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K L : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)) :=
  (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
    (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))).obj
      (op ((scalarReductionDerivedExtension.{u, u} l E X n).obj K),
        (scalarReductionDerivedExtension.{u, u} l E X n).obj L)

/-- Residue cohomological bounds give one uniform interval for bounded constructibility,
Tor amplitude and cohomological support of all finite internal Homs.
Source: main-20261015, cor-coef-integral-internal-hom.proof.md, sentences 2–3
and the final sentence (blueprint: lem-coef-residue-controlled-finite-homs).

Proof:
1. Integral constructibility gives bounded constructibility of every reduction.
Since l differs from the characteristic of the base field, l is invertible on X.
Apply lem-coef-integral-residue-tor to K and L with the supplied residue intervals,
obtaining Tor intervals [a,b] and [c,e] at every positive level. Together with
constructibility these are the conditions of def-weil-finite-tor-amplitude.
2. Apply the pro-etale clause of cor-weil-finite-constructible-hom at exponent n+1.
It gives bounded constructibility and Tor interval [c-b-2d,e-a+2d]. The endpoints
involve only the residue bounds and d, so they are independent of n.
3. Test Tor amplitude against the coefficient sheaf in degree zero. On a K-flat
representative P, the maps P tensor B_n → P, x tensor r ↦ r x, and
P → P tensor B_n, x ↦ x tensor 1, are inverse chain maps by tensor balancing
and linearity of the differential. Hence the tensor test is the same derived
object, giving the stated cohomological support inclusion. -/
theorem residue_controlled_finite_homs
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (K L : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hK : sfIntegralConstructible l E X K) (_hL : sfIntegralConstructible l E X L)
    (a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)
    (_hK₁ : proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K) ⊆ Set.Icc a b)
    (_hL₁ : proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L) ⊆ Set.Icc c e) :
    ∀ n : ℕ,
      intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X (integralFiniteInternalHom l E X K L n) ∧
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        (integralFiniteInternalHom l E X K L n)
        (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) ∧
      proEtaleCohomologicalSupport (integralFiniteInternalHom l E X K L n) ⊆
        Set.Icc (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) := by
  classical
  have hunit : IsUnit (l : D.k) := by
    let := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    have : CharP D.k D.p :=
      charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  let residueMap (x : X) : D.k →+* X.residueField x :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      (X ↘ Spec (.of D.k)).appTop ≫ X.Γevaluation x).hom
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (map_natCast (residueMap x) l) ▸ (hunit.map (residueMap x)).invertible
  have hKt := (integral_residue_tor D l _hl E X).1 K _hK a b _hab
    (fun i hi ↦ _hK₁ hi)
  have hLt := (integral_residue_tor D l _hl E X).1 L _hL c e _hce
    (fun i hi ↦ _hL₁ hi)
  obtain ⟨_, r, s, hrs, hKs⟩ := _hK
  obtain ⟨_, t, v, htv, hLs⟩ := _hL
  intro n
  have hKn : finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) :=
    ⟨(hKs n).1, a, b, hKt n⟩
  have hLn : finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj L) :=
    ⟨(hLs n).1, c, e, hLt n⟩
  have hhom := finite_constructible_derivedHom_proEtale D l _hl E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) X d _hd a b c e _hab _hce
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj L) hKn hLn (hKt n) (hLt n)
  exact ⟨hhom.1.1, hhom.2,
    support_of_torAmplitude X _ _ _ _ hhom.2⟩

end WeilConjectures
