/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteDualitySiteComparison
public import WeilConjectures.AlgebraicGeometry.FinitePointInternalHomEvaluation
public import WeilConjectures.AlgebraicGeometry.CoefficientDuality
public import WeilConjectures.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.EtaleConstantProjectionMap
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint
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
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
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

public import WeilConjectures.SixFunctors.FiniteMappingAdjunctionData
import WeilConjectures.SixFunctors.FiniteMappingEtaleDescent
import WeilConjectures.SixFunctors.FiniteMappingEtaleDescentIsIso
import WeilConjectures.SixFunctors.FiniteMappingEtaleDescentTranspose

/-!
# Finite-level mapping-complex adjunction

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-tower,
prop-coef-integral-dualizing.proof.md, paragraph 2
(blueprint: lem-coef-finite-mapping-adjunction).

We use the published fixed-scalar presentation of ordinary constant-ring module sheaves.
Two equations fix the map: agreement with ordinary etale internal exceptional adjunction,
and equality of its tensor-Hom transpose with projection, evaluation and the exceptional
counit for the fixed compactification. The point scalar isomorphism is uniquely normalized
by the derived constant-sheaf adjunction unit. All global comparison arrows are derived
comparison units followed by the canonical Leray comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  (c : Compactification (X ↘ Spec (.of D.k)))

set_option linter.unusedVariables false in
/-- The finite mapping-complex adjunction is a natural isomorphism, characterized on
EVERY etale representative by the canonical comparison square. Its tensor-Hom transpose
is explicitly required, for EVERY M in the full intrinsic domain, to equal the compact-support
projection/evaluation/exceptional-counit pairing. The point scalar isomorphism has the
specified derived constant-unit normalization. Both arrow-list equations are ordinary
equality of composites, with endpoints included.
No ambient unbounded pro-etale exceptional adjunction is assumed.
Source: main-20261015, prop-coef-integral-dualizing.proof.md, paragraph 2
(blueprint: lem-coef-finite-mapping-adjunction).

Proof plan:
1. Finite type over the geometric field makes a compactifiable Noetherian morphism.
General biduality puts both dualizing objects in D^b_ctf by dualizing the constant unit.
2. Choose a bounded constructible etale origin of M. Tor-amplitude comparison reflects
its finite Tor interval. Finite duality site comparison identifies its internal Hom and
its dualizing object, and preserves evaluation.
3. Direct-image finite-Tor stability makes F_n M bounded constructible of finite Tor
amplitude. Compact-support comparison gives its etale origin. Full faithfulness and
Tor-amplitude reflection show that the etale compact-support object is also D^b_ctf.
The evaluation-defined finite point internal-Hom theorem consequently applies.
4. Apply prop-asd-internal-adjunction to the etale origin and the base coefficient unit.
Take ordinary global sections using Leray. Transport by the derived-unit global
comparison, finite duality comparison, and compact-support comparison. The point
comparison is evaluation-defined, giving exactly finiteMappingEtaleGammaArrows.
5. InternalAdjunctionEvaluation identifies the transpose with projection, evaluation and
the etale exceptional counit. Projection comparison on etale origins and bounded-site
adjunction-transpose compatibility transport this counit to the comparison-class
exceptional counit. Point evaluation compatibility therefore gives the stated canonical
transpose, with no scalar ambiguity. The etale exceptional value on the comparison direct
image of the constant unit is bounded below, supplying homega. At the algebraically closed
point, finite comparison and exact point sections identify the derived constant adjunction
unit with an isomorphism; its normalized composite is scalar. Consequently the transpose
is exactly finiteMappingPairing, with its final scalar inverse.
6. Every constituent comparison is natural and the origin functor is fully faithful.
Thus the square descends independently of the chosen origin to the displayed natural
isomorphism. Its equation holds for every etale representative and every morphism.
-/
theorem finiteMappingAdjunction (hl : l ≠ D.p)
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∃ γ : finiteMappingGlobalHom D l E n X c ≅
        (finiteMappingCompactSections D l E n X c).op ⋙
          coefficientDerivedDual
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))),
      (∀ (J : Etale.DerivedCategoryModule
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X)
        (hJ : finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X J),
        ∃ (hplus : DerivedCategory.TStructure.t.plus J)
          (hpro : finiteTorConstructibleProEtaleModule l E (n + 1) (Nat.succ_pos n) X
            ((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u}
                (Padic.coefficientExtensionRing l E (n + 1)))) X).mapDerivedCategory.obj J)),
          FiniteMappingSameComposite
            (finiteMappingHomComparisonArrows
                (Padic.coefficientExtensionRing l E (n + 1)) c J ++
              [Arrow.mk (γ.hom.app (op ⟨_, hpro⟩))] ++
                finiteMappingDualTransportArrows
                  (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
                  c ⟨J, hplus⟩)
            (finiteMappingEtaleGammaArrows
              (Padic.coefficientExtensionRing l E (n + 1)) D.k c J)) ∧
      ∃ (homega : DerivedCategory.TStructure.t.plus
          (finiteMappingCounitInput (Padic.coefficientExtensionRing l E (n + 1)) c))
        (scalar :
          𝟙_ (DerivedCategory (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ≅
          (ProEtale.rightDerivedGlobalSections
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
            (Spec (.of D.k))).obj (𝟙_ _)),
        FiniteMappingComposite
          (finiteMappingScalarUnitArrows
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
            (Spec (.of D.k))) (Arrow.mk scalar.hom) ∧
        ∀ M : (finiteTorConstructibleProEtaleModule
            l E (n + 1) (Nat.succ_pos n) X).FullSubcategory,
          FiniteMappingSameComposite
            (finiteMappingTransposeArrows
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
              (γ.hom.app (op M)))
            (finiteMappingPairing (Padic.coefficientExtensionRing l E (n + 1))
              c homega scalar M.obj) := by
  obtain ⟨τ, hτ⟩ := finiteMappingEtaleDescent D l E n X c hl
  have hIso := finiteMappingEtaleDescent_isIso D l E n X c hl τ hτ
  let γ := NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ (τ.app M) (hIso M))
    (fun f ↦ τ.naturality f)
  refine ⟨γ, ?_, ?_⟩
  · exact hτ
  · exact finiteMappingEtaleDescent_transpose D l E n X c hl τ hτ

end WeilConjectures
