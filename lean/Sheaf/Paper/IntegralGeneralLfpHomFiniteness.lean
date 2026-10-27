/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

import Sheaf.Paper.IntegralHomComparisonNormalization
import Sheaf.Paper.IntegralHomReduction
import Sheaf.Paper.IntegralAdicInputNormalization
import Sheaf.Paper.IntegralAdicHomCompleteness
import Sheaf.Paper.IntegralAdicHomResidueOrigin

public import Sheaf.Paper.IntegralCriterionReductions
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.AdicStratifiedPerfectData
public import Sheaf.Paper.IntegralHomReductionComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-! # Complete residue witnesses for integral general-lfp internal Hom

Source: Bhatt--Scholze, Definition 6.5.1 and Proposition 6.8.11(3),
with Lemma 6.7.13 (blueprint: lem-sfb-integral-general-lfp-hom-finiteness).

## Main declarations

* `integralGeneralLfpPrimeDatum`: fill the unused characteristic datum of the reduction API.
* `integralGeneralLfpAdicImage`: canonical ordinary coefficient-presentation transport.
* `integral_general_lfp_hom_finiteness`: completeness, canonical reduction and etale witness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The prime-field datum only fills the unused characteristic parameter of the
published integral reduction interface; it imposes no finite-field condition on k.
Source: coefficient conventions of Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-general-lfp-hom-finiteness). -/
def integralGeneralLfpPrimeDatum (p : ℕ) [Fact p.Prime] :
    WeilConjectures.FiniteFieldDatum.{0} where
  p := p
  a := 1
  q := p
  prime := Fact.out
  exponent_pos := le_refl 1
  cardinality_eq := (pow_one p).symm
  k₀ := ZMod p
  card_base := by simp [Nat.card_eq_fintype_card]
  k := AlgebraicClosure (ZMod p)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Read the same internal-module derived object in the completed ring-sheaf
presentation. Both coefficient isomorphisms are fixed by all quotient projections;
this functor applies no completion to its input.
Source: Bhatt--Scholze, Definitions 6.5.1 and 6.8.10
(blueprint: lem-sfb-integral-general-lfp-hom-finiteness). -/
def integralGeneralLfpAdicImage :
    DerivedCategory (AdicCompletion.Modules l E X) ⥤
      DerivedCategory (Scheme.proEtaleRingModules X
        (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal)) :=
  (integralSectionDerivedEquivalence l E X).functor ⋙
    Scheme.integralDetailedTransport X l E ⋙
    Scheme.pbcDerivedRestrict (Scheme.pbcCompletedComparison X
      (Scheme.pbcIntegralDatum l E)).hom

/-- A cohomologically bounded etale complex has a strictly bounded representative with
its constructible homology. The displayed tensor tests are termwise, so their bounds
follow from the zero terms of the representative, for every test sheaf. In the application
the coefficients are a residue field, where these tests compute derived tensor.
Source: Mathlib's bounded representative theorem and preservation of zero objects. -/
private theorem boundedEtaleRepresentative
    (A : Type (u + 1)) [CommRing A]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a b : ℤ) (_hab : a ≤ b)
    (hC : ∀ q : ℤ, q < a ∨ b < q → IsZero (C.homology q))
    (hcons : ∀ q : ℤ, Scheme.IsConstructibleSheaf (C.homology q)) :
    ∃ D : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      D.IsStrictlyGE a ∧ D.IsStrictlyLE b ∧
      (∀ q : ℤ, Scheme.IsConstructibleSheaf (D.homology q)) ∧
      Nonempty (DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj D) ∧
      ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
        q < a ∨ b < q →
          IsZero ((Scheme.sfbEtaleTensorDegreeZero X A D N).homology q) := by
  have : C.IsGE a := (CochainComplex.isGE_iff C a).2 fun q hq ↦
    (HomologicalComplex.exactAt_iff_isZero_homology C q).2 (hC q (Or.inl hq))
  have : C.IsLE b := (CochainComplex.isLE_iff C b).2 fun q hq ↦
    (HomologicalComplex.exactAt_iff_isZero_homology C q).2 (hC q (Or.inr hq))
  obtain ⟨D, hDa, hDb, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE (DerivedCategory.Q.obj C) a b
  refine ⟨D, hDa, hDb, ?_, ⟨e⟩, ?_⟩
  · intro q
    have : Scheme.IsConstructibleSheaf (C.homology q) := hcons q
    exact Scheme.IsConstructibleSheaf.of_iso (F := C.homology q)
      (((DerivedCategory.homologyFunctorFactors _ q).app C).symm ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors _ q).app D)
  · intro N q hq
    let := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} A)
    let F := MonoidalCategory.tensorRight N
    have hGE : (Scheme.sfbEtaleTensorDegreeZero X A D N).IsStrictlyGE a := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact F.map_isZero (D.isZero_of_isStrictlyGE a i hi)
    have hLE : (Scheme.sfbEtaleTensorDegreeZero X A D N).IsStrictlyLE b := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact F.map_isZero (D.isZero_of_isStrictlyLE b i hi)
    rcases hq with hq | hq
    · exact (Scheme.sfbEtaleTensorDegreeZero X A D N).isZero_of_isGE a q hq
    · exact (Scheme.sfbEtaleTensorDegreeZero X A D N).isZero_of_isLE b q hq

/-- General-lfp bounded constructible integral inputs have complete internal Hom,
invertible canonical evaluation-transpose reduction, and a bounded constructible
finite-Tor etale residue witness. The Hom is the ambient ordinary unbounded Hom.
The canonical reduction comparison is written in its normalized ringed-site model,
under the fixed section-action equivalence; this equivalence preserves evaluation.

Source: Bhatt--Scholze, Definition 6.5.1, Proposition 6.8.11(3), Lemma 6.7.13;
Stacks Tags 099A and 09AL
(blueprint: lem-sfb-integral-general-lfp-hom-finiteness).

Proof:
1. Apply integralAdicInput_normalization to both inputs. It places the general-lfp
adic witnesses in the exact fixed section-action and completed coefficient presentation.
2. Apply integralHomReduction at the positive exponent 0+1, then rewrite its normalized
comparison by integralHomComparison_normalization. This proves invertibility of the
specified canonical evaluation-transpose map.
3. Apply integralAdicHom_complete to the completeness of the second input. No
perfectness condition on the first input is used.
4. Apply integralAdicHom_residue_origin to the two adic witnesses and the invertible
canonical reduction. It gives an etale residue complex with bounded constructible homology.
5. The private boundedEtaleRepresentative uses the standard derived t-structure to obtain
a strictly bounded complex D representing that residue origin. Its homology is constructible
by the homology functor applied to the derived isomorphism. Tensoring D termwise with any
degree-zero test sheaf preserves its zero terms, hence gives the required common interval.
Apply the derived comparisonUpperStar functor and its termwise factorization to the
representative isomorphism, and compose with the residue-origin isomorphism. -/
theorem integral_general_lfp_hom_finiteness
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (K L : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : boundedConstructible (AdicCompletion.ring l E X) K)
    (hL : boundedConstructible (AdicCompletion.ring l E X) L) :
    Scheme.IsSfbAdicComplete X (Scheme.pbcIntegralDatum l E).ideal
      ((integralGeneralLfpAdicImage l E X).obj
        (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj (op K)).obj L)) ∧
    IsIso (WeilConjectures.integralHomReductionComparison
      (integralGeneralLfpPrimeDatum (ringChar k)) l (Ne.symm (Fact.out : ringChar k ≠ l))
      E X 0 ((integralSectionDerivedEquivalence l E X).functor.obj K)
      ((integralSectionDerivedEquivalence l E X).functor.obj L)) ∧
    ∃ D : CochainComplex
        (Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E ⧸
            (Scheme.pbcIntegralDatum l E).ideal ^ (0 + 1)))) ℤ,
      (∃ a b : ℤ, a ≤ b ∧ D.IsStrictlyGE a ∧ D.IsStrictlyLE b) ∧
      (∀ q : ℤ, Scheme.IsConstructibleSheaf (D.homology q)) ∧
      Nonempty (DerivedCategory.Q.obj
          (((comparisonUpperStar
            (ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E ⧸
              (Scheme.pbcIntegralDatum l E).ideal ^ (0 + 1))) X).mapHomologicalComplex
                (.up ℤ)).obj D) ≅
        DerivedCategory.Q.obj (Scheme.sfbResidueComplex X
          (Scheme.pbcIntegralDatum l E).ideal
          ((integralGeneralLfpAdicImage l E X).obj
            (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
              (op K)).obj L)))) ∧
      ∃ a b : ℤ, a ≤ b ∧
        ∀ (N : Sheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E ⧸
              (Scheme.pbcIntegralDatum l E).ideal ^ (0 + 1)))) (q : ℤ),
          q < a ∨ b < q → IsZero
            ((Scheme.sfbEtaleTensorDegreeZero X _ D N).homology q) := by
  have hKadic := integralAdicInput_normalization l E X k K hK
  have hLadic := integralAdicInput_normalization l E X k L hL
  have hred : IsIso (WeilConjectures.integralHomReductionComparison
      (integralGeneralLfpPrimeDatum (ringChar k)) l (Ne.symm (Fact.out : ringChar k ≠ l))
      E X 0 ((integralSectionDerivedEquivalence l E X).functor.obj K)
      ((integralSectionDerivedEquivalence l E X).functor.obj L)) := by
    obtain ⟨a, _, hm⟩ := WeilConjectures.integralHomReduction l E X
      (integralGeneralLfpPrimeDatum (ringChar k)) (Ne.symm (Fact.out : ringChar k ≠ l))
    obtain ⟨m, hm⟩ := hm 0
    rw [WeilConjectures.integralHomComparison_normalization
      (integralGeneralLfpPrimeDatum (ringChar k)) l
      (Ne.symm (Fact.out : ringChar k ≠ l)) E X 0 a m]
    exact (hm _ _).1
  refine ⟨integralAdicHom_complete l E X K L hLadic.1, hred, ?_⟩
  obtain ⟨C, ⟨a, b, hab, hbound⟩, hcons, ⟨eC⟩⟩ :=
    integralAdicHom_residue_origin l E X k (integralGeneralLfpPrimeDatum (ringChar k))
      (Ne.symm (Fact.out : ringChar k ≠ l)) K L hKadic hLadic hred
  obtain ⟨D, hDa, hDb, hDcons, ⟨eD⟩, hDtor⟩ :=
    boundedEtaleRepresentative X _ C a b hab hbound hcons
  refine ⟨D, ⟨a, b, hab, hDa, hDb⟩, hDcons, ?_, a, b, hab, hDtor⟩
  let ν := comparisonUpperStar (ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E ⧸
    (Scheme.pbcIntegralDatum l E).ideal ^ (0 + 1))) X
  exact ⟨(ν.mapDerivedCategoryFactors.app D).symm ≪≫
    ν.mapDerivedCategory.mapIso eD.symm ≪≫ ν.mapDerivedCategoryFactors.app C ≪≫ eC⟩

end AlgebraicGeometry.ProEtale
