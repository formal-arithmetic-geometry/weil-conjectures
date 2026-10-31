/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence

import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePointPullbackSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.FiniteStrataCompletion.FiniteStrataCompletionDetection
import WeilConjectures.AlgebraicGeometry.FiniteScalarCompletion.FiniteScalarLocalModelComplete
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientConstructible
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# Completeness and classical reductions of qcqs integral finite-model inputs

Source: Bhatt--Scholze, The pro-etale topology for schemes, Sections 6.5--6.6;
blueprint main-20261015, localizing-closure-ctf-equals-bc, finite scalar models
(blueprint: lem-sfb-qcqs-integral-finite-model-completeness).

The scheme is arbitrary qcqs. The integral ring carries its spectral norm topology.
The completion predicate uses the specified strict-tower augmentation. Finite reductions
are formed by the recorded derived extension along the actual quotient homomorphism.
The ordinary coordinate condition retains the comparison equivalence and etale-origin pair.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Limits

attribute [local irreducible] IsDerivedComplete

private theorem complete_triangulated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (V : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsDerivedComplete l E V) ∧
      ObjectProperty.IsTriangulated (IsDerivedComplete l E V) := by
  obtain ⟨data, hdata, a, F, c, κ, sF, hF, ha, hc, hψ, hcomplete, hshift, htriangle⟩ :=
    CompletionTriangle.completion_triangle_comparison l E V
  let := hF
  have hi : ObjectProperty.IsClosedUnderIsomorphisms (IsDerivedComplete l E V) := by
    refine ⟨fun e h ↦ (hcomplete _).2 ?_⟩
    exact (NatTrans.isIso_app_iff_of_iso c e).mp ((hcomplete _).1 h)
  let := hi
  have : ObjectProperty.IsStableUnderShift (IsDerivedComplete l E V) ℤ := ⟨fun r ↦ ⟨by
    intro K hK
    have : IsIso (c.app K) := (hcomplete _).1 hK
    apply (hcomplete _).2
    have : IsIso (c.app (K⟦r⟧) ≫
        (Functor.commShiftIso (self := sF) F r).hom.app K) := by
      rw [hshift]
      infer_instance
    exact IsIso.of_isIso_comp_right (c.app (K⟦r⟧))
      ((Functor.commShiftIso (self := sF) F r).hom.app K)⟩⟩
  have : ObjectProperty.IsTriangulatedClosed₂ (IsDerivedComplete l E V) :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (by
      intro T hT h₁ h₃
      obtain ⟨hFT, γ, hγ₁, hγ₂, hγ₃⟩ := htriangle T hT
      apply (hcomplete _).2
      rw [← hγ₂]
      apply isIso₂_of_isIso₁₃ γ hT hFT
      · rw [hγ₁]; exact (hcomplete _).1 h₁
      · rw [hγ₃]; exact (hcomplete _).1 h₃)
  refine ⟨hi, { exists_zero := ⟨0, isZero_zero _, (hcomplete _).2 ?_⟩ }⟩
  exact (isZero_zero _).isIso (F.map_isZero (isZero_zero _)) _

private theorem complete_scalar_single
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (DerivedNakayama.integerRing l E))
    (hP : Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) P) :
    IsDerivedComplete l E T ((DerivedCategory.singleFunctor _ 0).obj
      ((DerivedNakayama.pullback l E T).obj P)) := by
  rw [← DerivedCategory.Q_obj_single_obj]
  exact (FiniteScalarCompletion.finite_scalar_local_model_complete l E T).2.1 P hP

private theorem complete_cover_single
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T U V : Scheme.{u}} (f : T ⟶ U) (g : U ⟶ V)
    (M : AdicCompletion.Modules l E V)
    (h : ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (DerivedNakayama.integerRing l E),
      Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) P ∧
      Nonempty ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).obj
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).obj M) ≅
        (DerivedNakayama.pullback l E T).obj P)) :
    IsDerivedComplete l E T ((FiniteStrataCompletion.pull l E f).obj
      ((FiniteStrataCompletion.pull l E g).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := h
  have := (complete_triangulated l E T).1
  let F := CondensedRing.upperStar (DerivedNakayama.integerRing l E) g
  let G := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  apply ObjectProperty.prop_of_iso (IsDerivedComplete l E T)
    (G.mapDerivedCategory.mapIso ((F.mapDerivedCategorySingleFunctor 0).app M) ≪≫
      (G.mapDerivedCategorySingleFunctor 0).app (F.obj M) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eP).symm
  exact complete_scalar_single l E T P hP

private theorem complete_stratified_single
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : AdicCompletion.Modules l E V) (S : Scheme.Stratification V)
    (C : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
    (hC : ∀ (a : Fin S.n) (i : (C a).I₀),
      ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (DerivedNakayama.integerRing l E),
        Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) P ∧
        Nonempty ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
          ((C a).f i)).obj
            ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
              (S.immersion a)).obj M) ≅
            (DerivedNakayama.pullback l E ((C a).X i)).obj P)) :
    IsDerivedComplete l E V ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let S' : Scheme.FiniteLocallyClosedStratification V :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  apply ((FiniteStrataCompletion.finite_strata_completion_detection l E S' C
    S.isConstructible_stratum).1 _).1.mpr
  intro a i
  exact complete_cover_single l E ((C a).f i) (S.immersion a) M (hC a i)

private theorem models_on_qcqs
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    IsConstantModelConstructible Λ V M ↔ IsFiniteConstantStratified Λ V M := by
  unfold IsConstantModelConstructible
  rw [if_pos (show CompactSpace V ∧ QuasiSeparatedSpace V from
    ⟨inferInstance, inferInstance⟩)]

private theorem complete_sheaf
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : AdicCompletion.Modules l E V)
    (hM : IsConstantModelConstructible (DerivedNakayama.integerRing l E) V M) :
    IsDerivedComplete l E V ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨S, hS⟩ := (models_on_qcqs (DerivedNakayama.integerRing l E) V M).mp hM
  obtain ⟨C, hC⟩ := Classical.axiomOfChoice hS
  exact complete_stratified_single l E V M S C hC

/-- The actual positive reduction has bounded constructible ordinary coordinates and
an etale-origin pair. The existential encoding is the normalized section-action encoding,
not an arbitrary derived equivalence. The quotient carries the topology induced by the
spectral norm. Index n denotes the positive exponent n+1, as in derivedReduction.
Source: Bhatt--Scholze, Sections 6.5--6.6; blueprint finite-model criterion, finite reduction
clause (blueprint: lem-sfb-qcqs-integral-finite-model-completeness). -/
def HasClassicalFiniteReduction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (V : Scheme.{u})
    (J : DerivedCategory (AdicCompletion.Modules l E V)) (n : ℕ) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) V
      ((AdicCompletion.derivedReduction l E V n).obj J) ∧
    ∃ e : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) V,
    FiniteDiscreteOrdinary.ordinaryBoundedConstructible
        (Padic.coefficientExtensionRing l E (n + 1)) V
        (e.fixedDerived.functor.obj ((AdicCompletion.derivedReduction l E V n).obj J)) ∧
      ∃ h : DerivedCategory.TStructure.t.plus
          (e.fixedDerived.functor.obj ((AdicCompletion.derivedReduction l E V n).obj J)),
        Nonempty (Scheme.FixedEtaleOriginWitness V
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
          ⟨e.fixedDerived.functor.obj ((AdicCompletion.derivedReduction l E V n).obj J), h⟩)

/-- Integral finite-model constructible finite-Tor inputs on any qcqs scheme are
complete for the canonical strict quotient tower and have classical finite reductions.
No Noetherianity, dimension, characteristic or invertibility assumption is imposed.

Source: Bhatt--Scholze, Sections 6.5--6.6; the agent finite-constant-scalar-model qcqs
criterion, using the main-20261015 blueprint's finite-model argument
(blueprint: lem-sfb-qcqs-integral-finite-model-completeness).

Proof:
1. Finite scalar models are complete by
   `FiniteScalarCompletion.finite_scalar_local_model_complete`. The finite-stratum
   detection theorem tests the specified completion unit on the defining stratum
   covers. Exact inverse image commutes with degree-zero single objects, so model
   isomorphisms give completeness for every constructible sheaf.
2. The exact completion functor and its specified natural unit from
   `CompletionTriangle.completion_triangle_comparison` show that completeness is
   invariant under isomorphisms and shifts, contains zero, and is closed under
   extensions of distinguished triangles. The generic bounded truncation theorem
   `DerivedCategory.prop_of_bounded` therefore proves completeness of J.
3. Fix a positive quotient. The finite-model sheaf quotient theorem supplies its
   finiteness and discrete topology, and bounded constructibility of every reduced
   constructible sheaf. The normalized finite-discrete encoding identifies this with
   ordinary bounded constructibility. A small-index cover and its universe lift give
   the same local finite models. The fixed-module constructible-origin theorem and
   `DerivedCategory.boundedConstructible_of_homology` give bounded constructible
   etale origin for these reduced sheaves.
4. The quotient scalar-extension adjunction gives a triangulated derived reduction
   functor. Compose it with the exact normalized encoding. The fixed-module bounded
   constructible etale-origin subcategory is triangulated, so the same bounded
   truncation theorem proves that the encoded reduction of J belongs to it. Its
   intrinsic cohomology is constructible, giving ordinary constructibility and,
   through the encoding, internal constructibility. Finally retain its bounded
   etale antecedent and comparison isomorphism as the required origin witness.
The argument uses bounded constructible cohomology; finite Tor amplitude is not
needed separately. It adds no geometric hypotheses and retains the actual completion unit.
-/
theorem qcqs_integral_finite_model_completeness
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (J : ConstantModelConstructibleFiniteTor (DerivedNakayama.integerRing l E) V) :
    IsDerivedComplete l E V J.obj ∧
      ∀ n : ℕ, HasClassicalFiniteReduction l E V J.obj n := by
  have := (constantModelConstructibleFiniteTor_wellDefined
    (DerivedNakayama.integerRing l E) V).1
  obtain ⟨hi, ht⟩ := complete_triangulated l E V
  let := hi
  let := ht
  refine ⟨DerivedCategory.prop_of_bounded (IsDerivedComplete l E V)
    (IsConstantModelConstructible (DerivedNakayama.integerRing l E) V)
    (complete_sheaf l E V) J.obj J.property.1.1 J.property.1.2, ?_⟩
  intro n
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E (n + 1)
  obtain ⟨hf, hd, _⟩ :=
    FiniteModelQuotient.finite_model_sheaf_quotient_constructible l E V
      ((DerivedCategory.homologyFunctor _ 0).obj J.obj) (J.property.1.2 0) n
  let : Finite A := hf
  let : DiscreteTopology A := hd
  obtain ⟨e⟩ := FiniteDiscreteOrdinary.encoding_exists A V
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E V n)
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have : (AdicCompletion.derivedReduction l E V n).IsTriangulated :=
    adj.isTriangulated_leftAdjoint
  have : e.fixedDerived.functor.IsTriangulated := by
    change (e.ordinary.functor ⋙ e.fixed.functor).mapDerivedCategory.IsTriangulated
    infer_instance
  let F := AdicCompletion.derivedReduction l E V n ⋙ e.fixedDerived.functor
  let B := DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} A)) V
  have : F.IsTriangulated := by dsimp only [F]; infer_instance
  have : B.IsTriangulated := by dsimp only [B]; infer_instance
  have : B.IsClosedUnderIsomorphisms := by dsimp only [B]; infer_instance
  have hB : B (F.obj J.obj) := by
    apply _root_.DerivedCategory.prop_of_bounded (B.inverseImage F)
      (IsConstantModelConstructible (DerivedNakayama.integerRing l E) V) ?_
      J.obj J.property.1.1 J.property.1.2
    intro M hM
    obtain ⟨_, _, _, hred, _⟩ :=
      FiniteModelQuotient.finite_model_sheaf_quotient_constructible l E V M hM n
    have hord := (FiniteDiscreteOrdinary.encoding_constructibility A V e).2 _ |>.mp hred
    apply DerivedCategory.boundedConstructible_of_homology (ULift.{u + 1} A) hord.1
    intro q
    exact (isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _).mp
      ((ordinary_constructible_iff A V _).mp (hord.2 q))
  have hI := DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic _ hB
  have hord : FiniteDiscreteOrdinary.ordinaryBoundedConstructible A V (F.obj J.obj) :=
    ⟨hI.1, fun q ↦ (ordinary_constructible_iff A V _).mpr (hI.2 q)⟩
  refine ⟨(FiniteDiscreteOrdinary.encoding_constructibility A V e).2 _ |>.mpr hord,
    e, hord, hI.1.1, ?_⟩
  obtain ⟨L, hL, ⟨i⟩⟩ := hB
  exact ⟨⟨⟨L, hL.1.1⟩, i⟩⟩

end AlgebraicGeometry.ProEtale
