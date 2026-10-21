/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Algebra.Homology.InternalHomLocalizationComparison
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CompletedCondensedCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.IntegralLfpConstantModelComparison
import Sheaf.Paper.ConstructibleInternalHomContinuity
import Sheaf.Algebra.Homology.DerivedScalarLocalizationReflection
import Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore
import Sheaf.Algebra.Homology.KInjectiveHomScalarTelescope
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Integral internal Hom and inversion of ell

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62,
with the coefficient-specific general-lfp bridge and internal-sheaf extraction
(blueprint: lem-sfb-integral-general-lfp-hom-inversion).

The section-module presentation is the existing exact equivalence from internal modules.
The comparison is the existing evaluation transpose. Scalar telescopes are termwise
colimits of complexes, in the ordinary unbounded derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

attribute [local irreducible] derivedInternalHomOfUniverses SheafOfModules.monoidalCategory

namespace AlgebraicGeometry.ProEtale.IntegralHomInversion

variable (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u})

/-- The existing integral condensed coefficient object pulled to X.
Source: Bhatt--Scholze 6.8.11--6.8.14
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev integral := condensedRingObj (Profinite.padicIntegersRingObj l E.1) X

/-- Its reconstructed commutative section-ring sheaf, without changing coefficients.
Source: Bhatt--Scholze 6.8.14(2); Stacks 00YV
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev ring := ModuleObjectRingedComparison.ring (Profinite.padicIntegersRingObj l E.1) X

/-- The actual inclusion of integral into rational coefficients, on section rings.
Source: Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
def coefficientMap := sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
  (padicIntegersToPadicSubfield.{u} X l E)

/-- The fixed exact equivalence on ordinary derived categories.
Source: Stacks 00YV, 05RU; Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev forward := ModuleObjectRingedComparison.forward (Profinite.padicIntegersRingObj l E.1) X


/-- The existing locally-bijective description of sheafification equivalences.
Source: Stacks 00W1; the small-site sheafification instance
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
noncomputable instance locallyBijective :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u+1, u+1, u+2, u+1, u+1, u+1}
    (Scheme.ProEt.topology X) (A := AddCommGrpCat.{u + 1})

/-- The canonical small derived categories, supplied uniformly for the scalar models.
Source: Stacks 07A5; the existing section-module Grothendieck instance
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
noncomputable instance derivedCategories :
    ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{u + 1, u + 1, u + 2}
        (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) R) :=
  fun R ↦ HasDerivedCategory.ofIsGrothendieckAbelian
    (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) R)

/-- Repeated multiplication by ell, formed in complexes of sheaf modules.
Source: Bhatt--Scholze 6.8.12--6.8.14, scalar telescope extraction
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
def tower (A : CochainComplex
    (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (ring l E X)) ℤ) :
    ℕ ⥤ CochainComplex (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (ring l E X)) ℤ :=
  Functor.ofSequence (X := fun _ : ℕ ↦ A) (fun _ ↦ l • 𝟙 A)

variable (M : ScalarHomModels.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X))

/-- The nth localization leg: unit followed by inverse multiplication by ell^n.
Its pairing with K is ell^(-n) times scalar-extended evaluation.
Source: Bhatt--Scholze 6.8.14(2), telescope-stage normalization
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
def leg (A : DerivedCategory
    (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (ring l E X))) (n : ℕ)
    (h : IsIso ((l ^ n) • 𝟙 ((M.scalar (coefficientMap l E X)).derived.obj A))) :
    A ⟶ (scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} (coefficientMap l E X)).obj
      ((M.scalar (coefficientMap l E X)).derived.obj A) :=
  letI := h
  (M.scalar (coefficientMap l E X)).adjunction.unit.app A ≫
    (scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} (coefficientMap l E X)).map
      (inv ((l ^ n) • 𝟙 ((M.scalar (coefficientMap l E X)).derived.obj A)))

/-- The recorded ambient derived internal Hom on the sectionwise presentation.
Source: Stacks 08J9; Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev hom := derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
  (Scheme.ProEt.topology X) (ring l E X)

/-- Ordinary derived scalar extension along the actual integral inclusion.
Source: Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev extension := (M.scalar (coefficientMap l E X)).derived

/-- Ordinary exact derived restriction along the integral inclusion.
Source: Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev restriction := scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
  (coefficientMap l E X)

variable
  (μ : ∀ {A B : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (b : A ⟶ B),
    ScalarHomTensorComparison.{u + 1, u, u, u + 1} M b)
  (α : ScalarInternalHomAdjunction.{u + 1, u, u, u + 1} M μ)

/-- The canonical evaluation-transpose comparison, using the dependency's normalized map.
Source: Bhatt--Scholze 6.8.14(2), internal-sheaf extraction
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev comparison := localizationHomComparison.{u + 1, u, u, u + 1}
  M (coefficientMap l E X) (μ (coefficientMap l E X))

/-- Restriction followed by the evaluation-normalized scalar internal-Hom adjunction.
Source: Bhatt--Scholze 6.8.14(2), internal-sheaf extraction
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev restrictedComparison := localizationHomRestrictedComparison.{u + 1, u, u, u + 1}
  M (coefficientMap l E X) μ α

/-- The integral module derived category, in its sectionwise sheaf presentation.
Source: Stacks 00YV, 05RU; Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev D := DerivedCategory (scalarModules.{u + 1, u, u + 1}
  (Scheme.ProEt.topology X) (ring l E X))

/-- The exact inverse to the recorded internal-to-sectionwise equivalence.
Source: Stacks 00YV, 05RU
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev internal :=
  (ModuleObjectRingedComparison.equivalence (Profinite.padicIntegersRingObj l E.1) X).inverse
    |>.mapDerivedCategory

attribute [local irreducible] localizationHomComparison localizationHomRestrictedComparison
  CoefficientClosedStructure.tensor CoefficientClosedStructure.evaluation

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Scalar inversion for general-lfp bounded constructible first inputs, with an arbitrary
bounded-below second input. All scalar and closed models are the already normalized ones.
The existential inverse-scalar proofs only make the explicit nth-leg notation typeable;
they are conclusions, not extra hypotheses. The two beta maps identify termwise scalar
colimits with restricted localization, and gamma is the evaluation-induced comparison.
Its square with beta identifies the actual restricted comparison on every representative.
The final equation is the categorical pairing formula
`(h,k) ↦ ell^(-n) (1 tensor h(k))`, for every n including zero.

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62,
with the internal-sheaf extraction and coefficient-specific general-lfp bridge
(blueprint: lem-sfb-integral-general-lfp-hom-inversion).

Proof:
1. The locally Noetherian, quasi-compact scheme has Noetherian underlying topology by
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal: a minimal member of the set of
members of a descending closed chain forces that chain to stabilize.
2. Apply lem-sfb-integral-lfp-constant-model-comparison to each of the finitely many
nonzero cohomology modules of K. Arbitrary local presentation matrices are permitted.
It gives finite constant models, including torsion models, without completeness.
3. On the small pro-etale site, filtered module colimits are exact by
lem-pur-ringed-site-grothendieck-abelian. Apply
lem-sfb-constructible-internal-hom-continuity to the repeated-ell tower, after the
existing evaluation-preserving module-object/ringed-site equivalence. This supplies
the sequential-continuity hypothesis of lem-sfb-internal-hom-localization-comparison.
4. If L has cohomology zero below c, replace any representative C by its lower
truncation: zero below c, coker(d^(c-1)) in degree c, and C above c. The quotient is a
quasi-isomorphism, and its scalar tower has a common termwise lower bound.
5. sk-prop-sfb-qlbar-colimit-x identifies the actual rational coefficient inclusion
with inversion of ell. Apply lem-sfb-internal-hom-localization-comparison to obtain
invertibility of the evaluation transpose, its restriction, and two-variable naturality.
6. lem-sfb-derived-scalar-localization-reflection and
lem-weil-pbc-scalar-localization-complex-colimit identify the two scalar telescopes
with restricted localization, with nth leg ell^(-n) times the unit.
lem-sfb-kinjective-hom-scalar-telescope replaces the functorial-resolution transition
by the literal scalar transition, preserving every derived colimit leg. Exact
colimits preserve quasi-isomorphisms, so arbitrary representatives A and P are allowed,
with no lower bound on the Hom representative A.
7. The evaluation normalization of lem-sfb-dc-hom-scalar-adjunction identifies the
restricted target with Hom(K,U(L_E)). On stage n scalar linearity gives the last
pairing equation; ell^(-(n+1)) times ell agrees with ell^(-n), so these are a cocone.
The beta square and stage equations identify gamma with the canonical continuity map,
independently of representatives. No completed category is used. -/
theorem integralGeneralLfpHomInversion
    [CompactSpace X] [IsLocallyNoetherian X]
    (K L : D l E X)
    (_hK : boundedConstructible (integral l E X)
      ((internal l E X).obj K))
    (_hL : ∃ c : ℤ, L.IsGE c) :
    IsIso (comparison l E X M μ K L) ∧
    IsIso (restrictedComparison l E X M μ α K L) ∧
    (∀ (K' L' : D l E X) (f : K' ⟶ K) (g : L ⟶ L'),
      (extension l E X M).map ((hom l E X).map (Prod.mkHom f.op g)) ≫
          comparison l E X M μ K' L' =
        comparison l E X M μ K L ≫
          (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
            (Scheme.ProEt.topology X)
            (ModuleObjectRingedComparison.ring (Profinite.continuousMapRingObj E.1) X)).map
              (Prod.mkHom ((extension l E X M).map f).op ((extension l E X M).map g))) ∧
    ∃ h : ∀ (T : D l E X) (n : ℕ),
        IsIso ((l ^ n) • 𝟙 ((extension l E X M).obj T)),
      (∀ (A P : CochainComplex
          (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (ring l E X)) ℤ)
        (eA : DerivedCategory.Q.obj A ≅ (hom l E X).obj (op K, L))
        (eP : DerivedCategory.Q.obj P ≅ L),
        ∃ (βA : DerivedCategory.Q.obj (colimit (tower l E X A)) ≅
            (restriction l E X).obj
              ((extension l E X M).obj ((hom l E X).obj (op K, L))))
          (βP : DerivedCategory.Q.obj (colimit (tower l E X P)) ≅
            (restriction l E X).obj ((extension l E X M).obj L)),
          (∀ n : ℕ, DerivedCategory.Q.map (colimit.ι (tower l E X A) n) ≫ βA.hom =
            eA.hom ≫ leg l E X M ((hom l E X).obj (op K, L)) n (h _ n)) ∧
          (∀ n : ℕ, DerivedCategory.Q.map (colimit.ι (tower l E X P) n) ≫ βP.hom =
            eP.hom ≫ leg l E X M L n (h _ n)) ∧
          ∃ γ : DerivedCategory.Q.obj (colimit (tower l E X A)) ≅
              (hom l E X).obj (op K, DerivedCategory.Q.obj (colimit (tower l E X P))),
            γ.hom ≫ (hom l E X).map (Prod.mkHom (𝟙 (op K)) βP.hom) =
              βA.hom ≫ restrictedComparison l E X M μ α K L ∧
            ∀ n : ℕ, DerivedCategory.Q.map (colimit.ι (tower l E X A) n) ≫ γ.hom =
              eA.hom ≫ (hom l E X).map
                (Prod.mkHom (𝟙 (op K))
                  (eP.inv ≫ DerivedCategory.Q.map (colimit.ι (tower l E X P) n)))) ∧
      ∀ n : ℕ,
        (M.closed (ring l E X)).tensor.map
            (Prod.mkHom
              (leg l E X M ((hom l E X).obj (op K, L)) n (h _ n) ≫
                restrictedComparison l E X M μ α K L) (𝟙 K)) ≫
          (M.closed (ring l E X)).evaluation K
            ((restriction l E X).obj ((extension l E X M).obj L)) =
        (M.closed (ring l E X)).evaluation K L ≫ leg l E X M L n (h _ n) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralHomInversion
