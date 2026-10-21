/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Paper.CompletedConstantSheafReduction
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Module.FinitePresentation
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Paper.CompletedConstantAlgebraFlatQuotients
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Noetherian.Basic

/-! # Cohomology of a local integral perfect scalar model

Source: Bhatt--Scholze, The pro-etale topology for schemes, Proposition 6.8.11(3),
final sentence via Proposition 6.6.11; Stacks Tags 09AA, 093J, 093M and 00IK
(blueprint: lem-sfb-local-integral-perfect-model-cohomology).

The inverse-limit coefficient ring is `adicLisseCompletedRing`. The index `n : ℕ`
means exponent `n + 1`. The coefficient comparison is fixed by every quotient projection.
The conclusion specifies the map induced by the given derived model isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u

open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Scalar extension of a constant module, restricted to the actual localized ringed site.
Source: Bhatt--Scholze 6.8.11(3); Stacks 093J--093M
(blueprint: lem-sfb-local-integral-perfect-model-cohomology). -/
abbrev localIntegralScalarRealization (S : Scheme.{u}) {R : Type (u + 1)}
    [CommRing R] (I : Ideal R) (U : S.ProEt) :=
  adicLisseConstantModules S R ⋙ completedAdicChange S (CompletedConstantReduction.base S I) ⋙
    SheafOfModules.localizedSystemRestriction.{u + 1, u, 0} (adicLisseCompletedRing S I) U

/-- Inverse image followed by extension along the specified coefficient isomorphism,
then restriction to the slice. Source: Stacks 09AA and 03DJ
(blueprint: lem-sfb-local-integral-perfect-model-cohomology). -/
abbrev localIntegralModelRestriction {X S : Scheme.{u}} (g : S ⟶ X)
    {R : Type (u + 1)} [CommRing R] (I : Ideal R)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (adicLisseCompletedRing X I) ≅ adicLisseCompletedRing S I) (U : S.ProEt) :=
  proEtaleRingModulePullback g (adicLisseCompletedRing X I) (adicLisseCompletedRing S I) c ⋙
    SheafOfModules.localizedSystemRestriction.{u + 1, u, 0} (adicLisseCompletedRing S I) U

/-- The standard localization for modules on the localized coefficient site.
Source: Stacks 05RU (blueprint: lem-sfb-local-integral-perfect-model-cohomology). -/
instance localIntegralSliceHasDerivedCategory (S : Scheme.{u}) {R : Type (u + 1)}
    [CommRing R] (I : Ideal R) (U : S.ProEt) :
    HasDerivedCategory (SheafOfModules.{u + 1}
      (((adicLisseForget S).obj (adicLisseCompletedRing S I)).over U)) :=
  HasDerivedCategory.standard _

/-- The completed coefficient identification and the cohomology of every local perfect
scalar model, with the comparison induced by the specified model isomorphism.
Source: Bhatt--Scholze 6.8.11(3), final sentence via 6.6.11; Stacks 09AA, 093J, 093M, 00IK
(blueprint: lem-sfb-local-integral-perfect-model-cohomology).

Proof:
1. The coefficient DVR theorem lem-weil-l-adic-extension-integers-dvr makes R a PID;
   lem-weil-pbc-pid-noetherian-normal makes it Noetherian. Neither scheme is restricted.
2. Constant inverse image identifies each finite quotient ring sheaf, by
   lem-pe-constant-left-module-inverse-image. These identifications commute with reductions.
   By lem-weil-pbc-proetale-immersion-limit-preservation, inverse image along g preserves
   the countable limit. The resulting ring isomorphism c has the displayed projections,
   which uniquely determine it. The same lemma makes the specified module pullback exact;
   lem-pur-site-restriction-module-adjunction-exact gives exact slice restriction.
3. By lem-weil-pbc-constant-module-section-properties, constant realization is exact.
   Apply lem-weil-pbc-completed-constant-algebra-flat-quotients to A=R and I=(pi), with
   the presentation B_S itself and its canonical base map. Scalar extension is exact.
   Hence its composite with constant realization and slice restriction is exact.
4. By lem-weil-pbc-exact-functor-derived-factorization, the exact restriction acts
   termwise on unbounded derived categories. Apply cohomology to alpha. Compose with
   the exact-functor comparison and the complex comparison of
   lem-weil-pbc-exact-functor-complex-cohomology. This is the displayed map; all its
   factors are isomorphisms. No completeness or boundedness of K is needed.
5. For each q, the cycles in the finite module P^q are finite by
   lem-weil-pbc-noetherian-submodule-finite. Their quotient by boundaries is finite.
   Lemma lem-sc-noetherian-finite-module-finite-presentation then gives finite presentation
   of H^q(P). This includes zero and torsion cohomology. -/
theorem local_integral_perfect_model_cohomology
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X S : Scheme.{u}} (g : S ⟶ X) [IsImmersion g] :
    ∃ c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (adicLisseCompletedRing X (Padic.coefficientExtensionIdeal l E 1)) ≅
          adicLisseCompletedRing S (Padic.coefficientExtensionIdeal l E 1),
      (∀ n : ℕ,
        c.hom ≫ limit.π (adicLisseRingSystem S (Padic.coefficientExtensionIdeal l E 1))
            (op n) =
          (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
            (limit.π (adicLisseRingSystem X (Padic.coefficientExtensionIdeal l E 1)) (op n)) ≫
          proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
            (CommRingCat.of
              (Padic.coefficientExtensionIntegers l E ⧸
                Padic.coefficientExtensionIdeal l E 1 ^ (n + 1)))) ∧
      ∀ U : S.ProEt,
        ∃ (_ : (localIntegralModelRestriction g (Padic.coefficientExtensionIdeal l E 1)
              c U).Additive)
          (_ : PreservesFiniteLimits
            (localIntegralModelRestriction g (Padic.coefficientExtensionIdeal l E 1) c U))
          (_ : PreservesFiniteColimits
            (localIntegralModelRestriction g (Padic.coefficientExtensionIdeal l E 1) c U))
          (_ : (localIntegralScalarRealization S (Padic.coefficientExtensionIdeal l E 1)
              U).Additive)
          (_ : PreservesFiniteLimits
            (localIntegralScalarRealization S (Padic.coefficientExtensionIdeal l E 1) U))
          (_ : PreservesFiniteColimits
            (localIntegralScalarRealization S (Padic.coefficientExtensionIdeal l E 1) U)),
        ∀ (K : DerivedCategory
            (proEtaleRingModules X
              (adicLisseCompletedRing X (Padic.coefficientExtensionIdeal l E 1))))
          (P : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
          (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
          (_hP : ∀ i : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
            Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i))
          (α : (localIntegralModelRestriction g (Padic.coefficientExtensionIdeal l E 1)
                c U).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj
              (((localIntegralScalarRealization S (Padic.coefficientExtensionIdeal l E 1)
                U).mapHomologicalComplex (.up ℤ)).obj P)) (q : ℤ),
        Module.FinitePresentation (Padic.coefficientExtensionIntegers l E) (P.homology q) ∧
        IsIso
          (((localIntegralModelRestriction g (Padic.coefficientExtensionIdeal l E 1)
              c U).mapDerivedCategoryHomologyFunctorIso q).hom.app K ≫
            (DerivedCategory.homologyFunctor _ q).map α.hom ≫
            (DerivedCategory.homologyFunctorFactors _ q).hom.app _ ≫
            ((localIntegralScalarRealization S (Padic.coefficientExtensionIdeal l E 1)
              U).mapHomologicalComplexHomologyIso (.up ℤ) q).hom.app P) := by
  sorry

end AlgebraicGeometry.Scheme
