/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SecSmoothPurity.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientInputModels
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompactificationExact
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-! # Finite-Tor domains for compact support and coefficient extension

Source: Stacks Project, Tag 0GL6, remark-Rf-lower-shriek-change-of-rings;
blueprint Charts and Locality in det-sp-reduction-exceptional
(blueprint: lem-sp-finite-compact-support-domains).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

private abbrev EtaleCtf (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :=
  Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) T

private abbrev Domain (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule R T) : Prop :=
  _root_.DerivedCategory.TStructure.t.bounded K ∧
  (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
    ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
  (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn R T a b K) ∧
  (∃ a : ℤ, K.IsGE a) ∧
  _root_.DerivedCategory.TStructure.t.bounded
    ((comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj K) ∧
  (∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf T R
    ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj K))) ∧
  DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} R) T
    ((comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj K) ∧
  (∃ a : ℤ,
    ((comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj K).IsGE a)

private theorem ctf_of_intrinsic (R : Type (u + 1)) [CommRing R] [Finite R]
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule R T)
    (hb : _root_.DerivedCategory.TStructure.t.bounded K)
    (hc : ∀ q : ℤ, IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K))
    (ht : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn R T a b K) :
    EtaleCtf R T K := by
  obtain ⟨a, b, _, ht⟩ := ht
  exact ⟨⟨hb, fun q ↦
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc q)⟩,
    a, b, Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht⟩

private theorem domain_scalar (ℓ : ℕ) [Fact ℓ.Prime]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (T : Scheme.{u}) [IsNoetherian T] (K : Etale.DerivedCategoryModule A T)
    (hK : EtaleCtf A T K) :
    Domain A T K ∧
    EtaleCtf B T ((pbcFixedScalarExtension T.smallEtaleTopology φ).obj K) ∧
    (∃ a : ℤ, ((finiteInputProScalar φ T).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K)).IsGE a) := by
  obtain ⟨hbc, a, b, ht⟩ := hK
  have hc : ∀ q : ℤ, IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K) :=
    fun q ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hbc.2 q)
  have ht' : Etale.DerivedCategory.hasTorAmplitudeIn A T (min a b) b K :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (_root_.DerivedCategory.torAmplitudeIn.mono (min_le_left a b) le_rfl ht)
  have hbc' : Etale.DerivedCategory.isBoundedConstructible A T K := by
    obtain ⟨⟨c, hc'⟩, ⟨d, hd'⟩⟩ := hbc.1
    let := hc'
    let := hd'
    refine ⟨hc, min c d, d, min_le_right _ _, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact _root_.DerivedCategory.isZero_of_isGE K c q (lt_of_lt_of_le hq (min_le_left _ _))
    · exact _root_.DerivedCategory.isZero_of_isLE K d q hq
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbcB, htB,
    hcN, hbN, htN, _, hbNB, _⟩ :=
    finiteCoefficientInputModels T ℓ Fact.out A B hA hB φ (min a b) b
      (min_le_right _ _) K hbc' ht'
  refine ⟨⟨hbc.1, hc, ⟨min a b, b, min_le_right _ _, ht'⟩,
    hbc.1.1, hbN, hcN, ⟨min a b, b, htN⟩, hbN.1⟩, ?_, hbNB.1⟩
  obtain ⟨c, d, _, hz⟩ := hbcB.2
  have hbB : _root_.DerivedCategory.TStructure.t.bounded
      ((pbcFixedScalarExtension T.smallEtaleTopology φ).obj K) :=
    ⟨⟨c, (_root_.DerivedCategory.isGE_iff _ c).mpr
      (fun q hq ↦ hz q (Or.inl hq))⟩,
      ⟨d, (_root_.DerivedCategory.isLE_iff _ d).mpr
      (fun q hq ↦ hz q (Or.inr hq))⟩⟩
  exact ctf_of_intrinsic B T _ hbB hbcB.1 ⟨min a b, b, min_le_right _ _, htB⟩

private theorem compact_support_lower_bound (R : Type (u + 1)) [CommRing R]
    {U V : Scheme.{u}} {h : U ⟶ V} (c : Compactification h)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)))
    (hK : ∃ a : ℤ, K.IsGE a) :
    ∃ a : ℤ,
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj K).IsGE a := by
  obtain ⟨a, ha⟩ := hK
  let := ha
  have := (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).isGE_mapDerivedCategory_obj K a
  exact ⟨a, Functor.isGE_rightDerivedFunctor_obj _ _ a⟩

/-- Compact support, the two actual scalar extensions, and their site pullbacks have
bounded constructible cohomology and finite Tor amplitude. The dependent pairs in the
second clause list exactly L_B on U, (F_A L)_B on V, and F_B(L_B) on V.
Source: Stacks Project, Tag 0GL6; blueprint Charts and Locality in
 det-sp-reduction-exceptional (blueprint: lem-sp-finite-compact-support-domains).

Proof:
1. Finite rings are Noetherian. Finite type over a field gives quasi-compactness;
   separatedness gives quasi-separatedness. These properties also hold for the proper
   factor and the quasi-compact open factor of the given compactification.
2. Exact open extension preserves lower bounds. Apply the canonical proper counit mate
   to j_!E and compose with the degreewise canonical open comparison. Both arrows are
   invertible for every bounded-below E, as recorded in the second theorem below.
3. Noetherian finite-Tor comparison sends a bounded constructible finite-Tor E to the
   intrinsic pro-etale domain. The single-compactification preservation theorem applies
   there. The finite-discrete ordinary-module equivalence identifies its output with
   the actual Rr_*j_! for this same compactification.
4. Exactness of comparison identifies cohomology before and after pullback. Its fully
   faithful heart functor detects zero objects and lifts the constructible cohomology
   isomorphisms and their inverses. Thus F_R E is bounded constructible. Apply the
   Noetherian Tor comparison only after this reflection to obtain its finite Tor bound.
5. Compute actual change of rings on K-flat models with flat terms. Tensor-pullback
   comparison, with constant second factor B, identifies N(K_B) with (NK)_B as
   B-complexes; the B action is multiplication on that factor. Scalar preservation
   gives bounded intrinsic constructibility and the same Tor interval on the latter.
6. Reflect boundedness and constructibility through the exact unbounded comparison,
   without first assuming K_B bounded below. Apply Tor comparison after this reflection.
7. Apply steps 3--4 to L over A, steps 5--6 to L and F_A L, and steps 3--4 to L_B over B.
   All resulting complexes are bounded, hence bounded below. The named compact-support
   comparison supplies the same lower bounds for the actual pro-etale outputs.
   No finite projective dimension or flatness of B over A is used. -/
theorem finiteCompactSupportDomains
    (ℓ p : ℕ) [Fact ℓ.Prime] (hp : 0 < p) (hℓ : ℓ ≠ p)
    (k : Type u) [Field k] [CharP k p]
    {U V : Scheme.{u}} [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))] (c : Compactification h)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (L : Etale.DerivedCategoryModule A U)
    (hb : _root_.DerivedCategory.TStructure.t.bounded L)
    (hc : ∀ q : ℤ, IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj L))
    (ht : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A U a b L) :
    (∀ (K : Etale.DerivedCategoryModule A V),
      K ∈ [(Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).obj L] →
      _root_.DerivedCategory.TStructure.t.bounded K ∧
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A V a b K) ∧
      (∃ a : ℤ, K.IsGE a) ∧
      _root_.DerivedCategory.TStructure.t.bounded
        ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K) ∧
      (∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf V A
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K))) ∧
      AlgebraicGeometry.ProEtale.DerivedCategory.finiteTorAmplitude.{u + 2, u}
        (ModuleCat.{u + 1} A) V
        ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K) ∧
      (∃ a : ℤ,
        ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K).IsGE a)) ∧
    (∀ P : Σ T : Scheme.{u}, Etale.DerivedCategoryModule B T,
      P ∈ [⟨U, (pbcFixedScalarExtension.{u} U.smallEtaleTopology φ).obj L⟩,
        ⟨V, (pbcFixedScalarExtension.{u} V.smallEtaleTopology φ).obj
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L)⟩,
        ⟨V, (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
          ((pbcFixedScalarExtension.{u} U.smallEtaleTopology φ).obj L)⟩] →
      _root_.DerivedCategory.TStructure.t.bounded P.2 ∧
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj P.2)) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn B P.1 a b P.2) ∧
      (∃ a : ℤ, P.2.IsGE a) ∧
      _root_.DerivedCategory.TStructure.t.bounded
        ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2) ∧
      (∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf P.1 B
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2))) ∧
      AlgebraicGeometry.ProEtale.DerivedCategory.finiteTorAmplitude.{u + 2, u}
        (ModuleCat.{u + 1} B) P.1
        ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2) ∧
      (∃ a : ℤ,
        ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2).IsGE a)) ∧
    (∃ a : ℤ,
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L)).IsGE a) ∧
    (∃ a : ℤ,
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} B) U).mapDerivedCategory.obj
          ((pbcFixedScalarExtension.{u} U.smallEtaleTopology φ).obj L))).IsGE a) ∧
    (∀ P : Σ T : Scheme.{u}, Etale.DerivedCategoryModule A T,
      P ∈ [⟨U, L⟩,
        ⟨V, (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L⟩] →
      ∃ a : ℤ, ((@pbcFixedScalarExtension.{u} P.1.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology P.1)
        A B inferInstance inferInstance φ).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) P.1).mapDerivedCategory.obj P.2)).IsGE a) := by
  have _ := hp
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (V ↘ Spec (.of k))
  have : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
  have : IsLocallyNoetherian V :=
    LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of k))
  have : IsNoetherian U := {}
  have : IsNoetherian V := {}
  have : QuasiCompact (h ≫ (V ↘ Spec (.of k))) := by
    rw [comp_over h (Spec (.of k))]
    infer_instance
  have : QuasiCompact h := QuasiCompact.of_comp h (V ↘ Spec (.of k))
  have compact (R : Type (u + 1)) [CommRing R] [Finite R]
      (hR : ∃ n : ℕ, ∀ x : R, (ℓ ^ n) • x = 0)
      (K : Etale.DerivedCategoryModule R U) (hK : EtaleCtf R U K) :
      EtaleCtf R V
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj K) := by
    obtain ⟨n, hn⟩ := hR
    have hℓk : (ℓ : k) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hℓ.symm
    have : HasInvertibleExponent R (Spec (.of k)) :=
      ⟨ℓ ^ n, pow_pos (Fact.out : ℓ.Prime).pos _, by simpa using hn 1,
        by
          simpa using (isUnit_iff_ne_zero.mpr (pow_ne_zero n hℓk)).map
            (Scheme.ΓSpecIso (.of k)).inv.hom⟩
    have : HasInvertibleExponent R V := .of_hom (V ↘ Spec (.of k))
    exact (Etale.rightDerivedLowerShriekOfCompactification_isTriangulated_and_ctf R c).2.2
      (V ↘ Spec (.of k)) hK
  have hL := ctf_of_intrinsic A U L hb hc ht
  have hFA := compact A hA L hL
  obtain ⟨hDU, hLB, hscalarU⟩ := domain_scalar ℓ A B hA hB φ U L hL
  obtain ⟨hDFA, hFAB, hscalarV⟩ := domain_scalar ℓ A B hA hB φ V _ hFA
  have hFB := compact B hB _ hLB
  have hDLB := (domain_scalar ℓ B B hB hB (RingHom.id B) U _ hLB).1
  have hDFAB := (domain_scalar ℓ B B hB hB (RingHom.id B) V _ hFAB).1
  have hDFB := (domain_scalar ℓ B B hB hB (RingHom.id B) V _ hFB).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K hK
    obtain rfl := List.mem_singleton.mp hK
    exact hDFA
  · intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl
    · exact hDLB
    · exact hDFAB
    · exact hDFB
  · exact compact_support_lower_bound A c _ hDU.2.2.2.2.2.2.2
  · exact compact_support_lower_bound B c _ hDLB.2.2.2.2.2.2.2
  · intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · exact hscalarU
    · exact hscalarV

/-- The specified compact-support comparison is invertible for every bounded-below
etale input. Its first arrow is the recorded proper counit mate; its second arrow
is the proper derived image of the termwise canonical open comparison.
Source: Stacks Project, Tag 0GL6; blueprint Charts and Locality in
 det-sp-reduction-exceptional (blueprint: lem-sp-finite-compact-support-domains).

Proof: step 1 of the node gives qcqs for the proper map of the compactification and
Noetherianity of the finite coefficient ring. Exact open extension sends E into D+.
Apply isIso_fixedComparisonDirectImageMatePlus to c.g and j_!E. The second factor
is the derived image of the natural open comparison isomorphism. Both factors are
therefore isomorphisms. The proper factor is exactly the counit-normalized mate,
and the open factor is exactly the section-normalized open comparison. The standard
Plus compatibility isomorphisms identify their source and target with the restrictions
of the unbounded F_et and F_pro used in finiteCompactSupportDomains. -/
theorem finiteCompactSupportDomains_comparison_isIso
    (ℓ p : ℕ) [Fact ℓ.Prime] (hp : 0 < p) (hℓ : ℓ ≠ p)
    (k : Type u) [Field k] [CharP k p]
    {U V : Scheme.{u}} [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))] (c : Compactification h)
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (hR : ∃ n : ℕ, ∀ x : R, (ℓ ^ n) • x = 0)
    (E : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    IsIso
      ((fixedComparisonDirectImageMatePlus R c.g).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} R) c.i).mapDerivedCategoryPlus.obj E) ≫
        (lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctorPlus.map
          (((Functor.mapDerivedCategoryPlusCompIso
              (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)
              (comparisonUpperStar (ModuleCat.{u + 1} R) c.Z)).symm ≪≫
            Functor.mapDerivedCategoryPlusNatIso
              (openImmersionLowerShriekComparisonUpperStarIso
                (ModuleCat.{u + 1} R) c.i) ≪≫
            Functor.mapDerivedCategoryPlusCompIso
              (comparisonUpperStar (ModuleCat.{u + 1} R) U)
              (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)).hom.app E)) := by
  have _ := hp
  have _ := hℓ
  have _ := hR
  let := isIso_fixedComparisonDirectImageMatePlus R c.g
  infer_instance

end AlgebraicGeometry.ProEtale
