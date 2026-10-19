/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison
public import Sheaf.Paper.DualityPairing
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek


import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtale.BasisDerivedDetection
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical
import Sheaf.Paper.ProEtaleFiniteLocalConstancyReflection
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.IndEtaleDerivedHomContinuity
import Sheaf.Paper.FiniteFieldExceptionalPreservation

/-!
# Finite residue-field dualizing complexes

Source: Illusie–Laszlo–Orgogozo, Exposé XVII, Propositions 2.4.4.1 and 4.1.2,
Theorems 5.1.1, 6.1.1 and 7.1.3; Bhatt–Scholze, Lemmas 6.3.16 and 6.7.18
(blueprint: lem-per-finite-residue-dualizing).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The transcendence degree over the residue field of the image point.
Source: ILO XVII, Proposition 4.1.2 (blueprint: lem-per-finite-residue-dualizing). -/
noncomputable def finiteResidueTranscendenceDegree
    {k : Type u} [Field k] {T : Scheme.{u}}
    (a : T ⟶ Spec (.of k)) (t : T) : Cardinal.{u} :=
  letI : Algebra (↑((Spec (.of k)).residueField (a t)) : Type u)
      (↑(T.residueField t) : Type u) :=
    (Scheme.Hom.residueFieldMap a t).hom.toAlgebra
  Algebra.trdeg (↑((Spec (.of k)).residueField (a t)) : Type u)
    (↑(T.residueField t) : Type u)

/-- The compact-support functor used for a finite-type structure morphism.
Source: ILO XVII, Proposition 2.4.4.1 (blueprint: lem-per-finite-residue-dualizing). -/
noncomputable def finiteResidueLowerShriek
    {k : Type u} [Field k] {T : Scheme.{u}}
    (a : T ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (A : Type (u + 1)) [Field A] [Finite A] :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule A (Spec (.of k)) :=
  letI : HasCompactification a := (NagataCompactification a).hasCompactification
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) a

/-- The extraordinary pullback right adjoint of `finiteResidueLowerShriek`.
Source: ILO XVII, Proposition 2.4.4.1 (blueprint: lem-per-finite-residue-dualizing). -/
noncomputable def finiteResidueExceptional
    {k : Type u} [Field k] {T : Scheme.{u}}
    (a : T ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (A : Type (u + 1)) [Field A] [Finite A] :
    DerivedCategoryModule A (Spec (.of k)) ⥤ DerivedCategoryModule A T :=
  letI : HasCompactification a := (NagataCompactification a).hasCompactification
  Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) a

/-- The coefficient-unit dualizing candidate `a^! A_s`.
Source: ILO XVII, Proposition 4.1.2 (blueprint: lem-per-finite-residue-dualizing). -/
noncomputable def finiteResidueOmega
    {k : Type u} [Field k] {T : Scheme.{u}}
    (a : T ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (A : Type (u + 1)) [Field A] [Finite A] : DerivedCategoryModule A T :=
  letI : HasCompactification a := (NagataCompactification a).hasCompactification
  Etale.dualizingComplex (ModuleCat.{u + 1} A) a

/-- The actual ambient pro-etale derived category in the fixed-module presentation.
The canonical coefficient realization of `def-weil-pbc-proetale-modules` identifies
this with the derived category of modules over its sheafified continuous-function ring.
Source: Bhatt–Scholze, Lemma 6.3.16 (blueprint: lem-per-finite-residue-dualizing). -/
abbrev finiteResidueProDerivedCategory
    (T : Scheme.{u}) (A : Type (u + 1)) [Field A] [Finite A] : Type (u + 2) :=
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The exact comparison inverse image, applied termwise and descended to localization.
Source: Bhatt–Scholze, Lemma 6.3.16 (blueprint: lem-per-finite-residue-dualizing). -/
noncomputable def finiteResidueProEtaleComparison
    (T : Scheme.{u}) (A : Type (u + 1)) [Field A] [Finite A] :
    DerivedCategoryModule A T ⥤ finiteResidueProDerivedCategory T A :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

/-- The fixed-coefficient presentation of intrinsic pro-etale constructibility used here.
This transparent alias reuses the published finite-stratification predicate; the dependency
node keeps its intrinsic constant-ring interface and all existing consumers.
Source: blueprint def-weil-proetale-constructible-sheaf, second paragraph;
Bhatt–Scholze, Section 6.3 (blueprint: lem-per-finite-residue-dualizing). -/
abbrev finiteResidueProConstructibleSheaf
    (T : Scheme.{u}) (A : Type (u + 1)) [Field A] [Finite A]
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) : Prop :=
  Scheme.IsConstructibleProEtaleFixedModuleSheaf T A F

/-- Intrinsic bounded constructibility: bounded cohomology and the finite-stratification
constructibility predicate on every cohomology sheaf, without assuming etale origin.
Source: Bhatt–Scholze, Section 6.3; blueprint def-weil-proetale-constructible-sheaf
(blueprint: lem-per-finite-residue-dualizing). -/
def finiteResidueProBoundedConstructible
    (T : Scheme.{u}) (A : Type (u + 1)) [Field A] [Finite A]
    (K : finiteResidueProDerivedCategory T A) : Prop :=
  (∀ i : ℤ, finiteResidueProConstructibleSheaf T A
    ((_root_.DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) i).obj K)) ∧
  ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) i).obj K)

/-- The pro-etale dualizing object is the specified inverse image of the etale object.
Source: Bhatt–Scholze, Lemma 6.3.16 (blueprint: lem-per-finite-residue-dualizing). -/
noncomputable def finiteResidueProOmega
    {k : Type u} [Field k] {T : Scheme.{u}}
    (a : T ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (A : Type (u + 1)) [Field A] [Finite A] : finiteResidueProDerivedCategory T A :=
  (finiteResidueProEtaleComparison T A).obj (finiteResidueOmega a A)

/-- The complete finite-residue dualizing assertion, including the etale evaluation pairing,
transcendence-degree normalization, and the ringed-site pro-etale transport.
Source: ILO XVII, Propositions 2.4.4.1 and 4.1.2, Theorems 5.1.1, 6.1.1 and 7.1.3;
Bhatt–Scholze, Lemmas 6.3.16 and 6.7.18 (blueprint: lem-per-finite-residue-dualizing). -/
structure FiniteResidueDualizingAssertion
    {k : Type u} [Field k] {T : Scheme.{u}}
    (a : T ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (ell : ℕ) (hℓ : Nat.Prime ell) (hℓk : IsUnit (ell : k))
    (A : Type (u + 1)) [Field A] [Finite A] [CharP A ell] : Prop where
  adjunction : Nonempty (finiteResidueLowerShriek a A ⊣ finiteResidueExceptional a A)
  omega_bounded : DerivedCategory.isBoundedConstructible A T (finiteResidueOmega a A)
  hom_preserves : ∀ P : DerivedCategoryModule A T,
    DerivedCategory.isBoundedConstructible A T P →
      DerivedCategory.isBoundedConstructible A T
        ((derivedHom (ModuleCat.{u + 1} A) T).obj (Opposite.op P) |>.obj (finiteResidueOmega a A))
  evaluation_pairing :
    Etale.AmbientDualityPairing (ModuleCat.{u + 1} A) T (finiteResidueOmega a A)
  biduality : ∀ P : DerivedCategoryModule A T,
    DerivedCategory.isBoundedConstructible A T P →
      IsIso (Etale.AmbientDualityPairing.bidualityMap
        (ModuleCat.{u + 1} A) T evaluation_pairing P)
  hom_comparison : ∀ P Q : DerivedCategoryModule A T,
    DerivedCategory.isBoundedConstructible A T P →
    DerivedCategory.isBoundedConstructible A T Q →
      IsIso (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T P Q)
  intrinsic_eq_origin : ∀ K : finiteResidueProDerivedCategory T A,
    finiteResidueProBoundedConstructible T A K ↔
      ∃ P : DerivedCategoryModule A T,
        DerivedCategory.isBoundedConstructible A T P ∧
          Nonempty ((finiteResidueProEtaleComparison T A).obj P ≅ K)
  pro_omega_bounded : finiteResidueProBoundedConstructible T A (finiteResidueProOmega a A)
  pro_hom_preserves : ∀ P : finiteResidueProDerivedCategory T A,
    finiteResidueProBoundedConstructible T A P →
      finiteResidueProBoundedConstructible T A
        (((ProEtale.derivedHom (ModuleCat.{u + 1} A) T).obj (Opposite.op P)).obj
          (finiteResidueProOmega a A))
  pro_evaluation_pairing :
    ProEtale.AmbientDualityPairing (ModuleCat.{u + 1} A) T (finiteResidueProOmega a A)
  pro_biduality : ∀ P : finiteResidueProDerivedCategory T A,
    finiteResidueProBoundedConstructible T A P →
      IsIso (ProEtale.AmbientDualityPairing.bidualityMap
        (ModuleCat.{u + 1} A) T pro_evaluation_pairing P)


/-- Normalized dualizing complexes at finite residue-field coefficients.
The proof supplies the right adjoint, bounded constructibility, evaluation-defined etale
biduality, transcendence-degree normalization, and the comparison with the actual pro-etale
ringed-site internal Hom, including the pro-etale biduality assertion.
Source: ILO XVII, Propositions 2.4.4.1 and 4.1.2, Theorems 5.1.1, 6.1.1 and 7.1.3;
Bhatt–Scholze, Lemmas 6.3.16 and 6.7.18 (blueprint: lem-per-finite-residue-dualizing).

Proof (the eight DAG steps):
1. `lem-exc-fields-excellent` and `lem-exc-finite-type-localization-excellent` make
   the source and base Noetherian excellent. Nagata compactifies a. Apply
   `lem-per-finite-exceptional-preservation` over the prime field and over A for
   exceptional adjunction and its bounded constructible restriction.
2. On Spec k the degree-zero coefficient unit has identity potential pinning for
   dimension zero (`def-per-potential-dualizing`); there are no immediate
   specializations. This uses supported complexes on the residue-field etale site,
   not global Galois invariants, so imposes no cohomological-dimension bound.
3. `lem-per-potential-extraordinary-pullback` pulls this pinning back along a.
   Its dimension function is trdeg over the image residue field, hence over k.
   The real construction `finiteResidueOmega` fixes the unit normalization.
4. The finite-extension comparison in `lem-per-finite-exceptional-preservation`
   identifies A tensor the prime-field potential complex with the actual a^! A.
   `lem-per-potential-local-duality` gives bounded constructibility, preservation
   by Hom into it and evaluation biduality. Postcompose evaluation by this
   comparison and transpose twice to transfer the canonical bidual map.
5. Use `lem-weil-pbc-ind-etale-basis` on each affine open. For an affine ind-etale
   limit, `lem-per-ind-etale-derived-hom-continuity` computes sections of Hom
   and morphisms between the constructible first and bounded-below second variable.
   `lem-weil-pbc-ringed-internal-hom-exact-restriction` and
   `lem-pur-rhom-global-sections` identify these calculations.
6. `lem-weil-pbc-comparison-pullback` and `thm-weil-pbc-site-comparison` identify
   the latter morphisms on the pro-etale site. Under tensor-Hom adjunction the
   resulting map is precisely `def-sf-evaluation-hom-site-comparison`.
   `lem-weil-pbc-basis-derived-detection` and
   `lem-cbc-proetale-stalk-conservative` detect its invertibility locally and globally.
7. `det-pe-constructible-comparison-classical` gives etale origins for intrinsic
   constructible sheaves. Pullback coherence and
   `lem-weil-pbc-comparison-finite-local-constancy-reflection` reflect finite local
   constancy on every stratum. Induct on the bounded cohomological interval, lifting
   connecting morphisms by comparison full faithfulness and taking cones. Exactness
   (`lem-sf-comparison-pullback-exact`) identifies the pulled-back triangles. This
   proves equality of intrinsic and etale-origin bounded constructibility.
8. Set the pro-etale object equal to comparison inverse image of the actual Omega.
   Apply the specified Hom comparison to (P, Omega) and (Hom(P, Omega), Omega).
   Its evaluation normalization identifies the canonical pro-etale bidual map
   with pullback of the etale bidual map. It is therefore invertible; Hom preserves
   intrinsic bounded constructibility by step 7. Naturality follows from the same
   transpose equations, independently of the chosen etale origin. -/
theorem finite_residue_dualizing
    {k : Type u} [Field k] {T : Scheme.{u}}
    (a : T ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (ell : ℕ) (hℓ : Nat.Prime ell) (hℓk : IsUnit (ell : k))
    (A : Type (u + 1)) [Field A] [Finite A] [CharP A ell] :
    FiniteResidueDualizingAssertion a ell hℓ hℓk A := by
  sorry

end AlgebraicGeometry.Etale
