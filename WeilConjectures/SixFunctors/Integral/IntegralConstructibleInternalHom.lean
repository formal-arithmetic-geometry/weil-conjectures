/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralHomReductionComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Integral.IntegralHomReduction
import WeilConjectures.SixFunctors.Integral.IntegralHomComparisonNormalization
import WeilConjectures.SixFunctors.Supporting.ResidueControlledFiniteHoms
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import Mathlib.Algebra.Homology.Monoidal
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

/-! # Constructible integral internal Hom

Source: Weil conjectures blueprint, `sec-six-functors/sk-prop-sf-biduality-general`,
`cor-coef-integral-internal-hom`, order 2147
(blueprint: cor-coef-integral-internal-hom).
The index `n : ℕ` denotes the positive exponent `n + 1` throughout.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures

attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
private theorem support_of_torAmplitude (X : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory X A) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A K a b) :
    proEtaleCohomologicalSupport K ⊆ Set.Icc a b := by
  classical
  let R : Sheaf (ProEt.topology X) CommRingCat.{u + 1} := proEtaleConstantRing X A
  let C := SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
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

private theorem torAmplitude_of_iso (X : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory X A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A L a b) :
    HasProEtaleTorAmplitude X A K a b := by
  refine ⟨h.1, ?_⟩
  intro Q P hQ f hf hP M i hi
  obtain ⟨eQ⟩ := hQ
  exact h.2 Q P ⟨eQ ≪≫ e⟩ f hf hP M i hi

attribute [-instance] IntegralHom.derivedCategory in
private theorem support_of_iso (X : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory X A} (e : K ≅ L) (a b : ℤ)
    (h : proEtaleCohomologicalSupport L ⊆ Set.Icc a b) :
    proEtaleCohomologicalSupport K ⊆ Set.Icc a b := by
  intro i hi
  apply h
  intro hz
  exact hi (hz.of_iso ((DerivedCategory.homologyFunctor
    (proEtaleRingModules X (proEtaleConstantRing X A)) i).mapIso e))

private theorem integral_to_sf
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (K : completedIntegralDerivedCategory l E X D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E X K) :
    sfIntegralConstructible l E X K := by
  obtain ⟨hc, a, b, hab, h⟩ := hK
  refine ⟨(sfDerivedComplete_iff_legacy l E X D hl K).mpr hc, a, b, hab, ?_⟩
  intro n
  exact ⟨(h n).1, fun i hi ↦ (h n).2 i hi⟩

/-- The ambient completed-coefficient Hom is constructible and derived complete;
its canonical evaluation-defined reductions are isomorphisms, with the stated uniform
Tor interval over the finite quotient coefficient sheaf.

Source: blueprint order 2147 (blueprint: cor-coef-integral-internal-hom).
Proof:
1. The defining integral predicate makes K and L complete and their residue reductions
bounded constructible. Choose intervals bounding residue cohomology (any interval works
for zero). Apply lem-coef-integral-residue-tor separately to obtain uniform finite-level
Tor intervals. The coefficient ring is the specified DVR, and l is invertible on X
because X is over the algebraic closure of a field of characteristic p different from l.
2. Apply lem-coef-integral-hom-reduction to the ambient internal Hom H. Completeness of
L implies completeness of H. The reduction comparison, defined as the transpose of
reduced evaluation, is an A_n-linear isomorphism, without site-perfectness of K.
3. By lem-kun-dimension-finite-type choose one nonnegative bound d₀ for dim X, independent
of n. The empty scheme has dimension bottom and admits d₀ = 0.
4. Apply cor-weil-finite-constructible-hom on the pro-etale site at each positive level.
The reductions are bounded constructible and finite-Tor. It gives constructibility of
their internal Hom and Tor interval [c-b-2d,e-a+2d] for any supplied input intervals
and dimension bound. Transport through the canonical isomorphism from step 2.
5. Test the output Tor condition against the coefficient sheaf in degree zero.
The maps P tensor A_n → P, x tensor r ↦ rx, and x ↦ x tensor 1 give the unit isomorphism
on a K-flat representative. Hence output cohomology lies in the same uniform interval.
Together with steps 2 and 4 this is exactly def-weil-derived-complete-integral-detailed.
-/
theorem integral_constructible_internalHom
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (K L : completedIntegralDerivedCategory l E X D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E X K)
    (hL : boundedConstructibleDerivedCompleteIntegral D l hl E X L) :
    boundedConstructibleDerivedCompleteIntegral D l hl E X
        ((homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L)) ∧
      (∀ n : ℕ, IsIso (integralHomReductionComparison D l hl E X n K L)) ∧
      ∀ a b c e : ℤ, a ≤ b → c ≤ e →
        ∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
          (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
            ((integralDerivedReduction l E X D hl n).obj K) a b) →
          (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
            ((integralDerivedReduction l E X D hl n).obj L) c e) →
          ∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
            ((integralDerivedReduction l E X D hl n).obj
              ((homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L)))
            (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) := by
  classical
  obtain ⟨model, hcomplete, hmodels⟩ := integralHomReduction l E X D hl
  have hcomparison (n : ℕ) : IsIso (integralHomReductionComparison D l hl E X n K L) := by
    obtain ⟨m, hm⟩ := hmodels n
    rw [integralHomComparison_normalization D l hl E X n model m K L]
    exact (hm K L).1
  let H := (homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L)
  let eH (n : ℕ) : (integralDerivedReduction l E X D hl n).obj H ≅
      integralFiniteInternalHom l E X K L n := by
    have := hcomparison n
    exact asIso (integralHomReductionComparison D l hl E X n K L)
  have hKs := integral_to_sf D l hl E X K hK
  have hLs := integral_to_sf D l hl E X L hL
  refine ⟨?_, hcomparison, ?_⟩
  · refine ⟨hcomplete K L hL.1, ?_⟩
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
    obtain ⟨_, a, b, hab, hKb⟩ := hK
    obtain ⟨_, c, e, hce, hLb⟩ := hL
    have hfinite := residue_controlled_finite_homs D l hl E X d hd K L hKs hLs
      a b c e hab hce (fun i hi ↦ (hKb 0).2 i hi) (fun i hi ↦ (hLb 0).2 i hi)
    refine ⟨c - b - 2 * (d : ℤ), e - a + 2 * (d : ℤ), by omega, ?_⟩
    intro n
    have hn := hfinite n
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    have hcon := (proEtale_bounded_constructible_isTriangulated X
      (Padic.coefficientExtensionRing l E (n + 1))).1
    let W : ObjectProperty (proEtaleDerivedCategory X
        (Padic.coefficientExtensionRing l E (n + 1))) :=
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
    have : W.IsClosedUnderIsomorphisms := hcon
    exact ⟨W.prop_of_iso (eH n).symm hn.1,
      fun i hi ↦ support_of_iso X _ (eH n) _ _ hn.2.2 hi⟩
  · intro a b c e hab hce d hd hKt hLt n
    have hfinite := residue_controlled_finite_homs D l hl E X d hd K L hKs hLs
      a b c e hab hce
      (support_of_torAmplitude X _ _ _ _ (hKt 0))
      (support_of_torAmplitude X _ _ _ _ (hLt 0)) n
    exact torAmplitude_of_iso X _ (eH n) _ _ hfinite.2.1

end WeilConjectures
