/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Normalized.NormalizedComparisonWord
public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleLocallyClosedShriek
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
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
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
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
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
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
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.Locally.LocallyProjectiveCoefficientHom
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedInternalAdjunctionIso
import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.LocallyClosedPairingCancellation
import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedOrdinaryComparisonIso

/-! # Evaluation-normalized Hom comparison on locally closed generators

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
thm-coef-finite-hom, proof paragraphs 3--4
(blueprint: lem-coef-locally-closed-hom-generator).

Every arrow below uses the published ordinary small-etale construction. Ordinary
pushforward is written in the canonical composition coordinates Rg_* Rj_*.
The internal adjunction uses the open and closed proper projection pairing of
CoefficientPairingChange.internalAdjunction. No arbitrary endpoint isomorphism is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.LocallyClosedHomGenerator
open CoefficientPairingChange
attribute [local irreducible] CategoryTheory.NormalizedComparisonWord

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
variable {S Z X : Scheme.{u}}

/-- The object N = s_A^! M, using the fixed ordinary closed-support right adjoint.
Source: thm-coef-finite-hom, paragraph 3
(blueprint: lem-coef-locally-closed-hom-generator). -/
abbrev exceptionalObject (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] (M : DerivedCategoryModule A X) :=
  (exceptional A g j).obj M

/-- The inner object Q = RHom_A(L,s_A^! M), without changing the internal Hom.
Source: thm-coef-finite-hom, paragraph 3
(blueprint: lem-coef-locally-closed-hom-generator). -/
abbrev innerHom (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) :=
  ((derivedHom (ModuleCat A) S).obj (op L)).obj (exceptionalObject g j M)

attribute [local irreducible] derivedHom derivedTensor upperStar lowerStar
attribute [local irreducible] internalAdjunction evaluationComparison
  ordinaryComparison compactComparison etaleShriekLocallyClosedCoefficientMap

/-- The displayed factors, their invertibility, and the equality to the evaluation transpose.
Here b is the published exceptional comparison, q the open-then-closed scalar map,
c the ordinary counit-defined map, and u the coefficient change of evaluation.
Source: thm-coef-finite-hom, paragraphs 3--4
(blueprint: lem-coef-locally-closed-hom-generator). -/
def IsNormalizedComparison (φ : A →+* B) (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) : Prop :=
  letI := locallyClosedInternalAdjunction_isIso A g j L M
  MappedComparisonWord (scalarExtension φ X) (star B g j)
    (derivedHom (ModuleCat B) X) (internalAdjunction A g j L M)
    (ordinaryComparison φ g j (innerHom g j L M))
    (evaluationComparison φ S L (exceptionalObject g j M))
    (((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj L))).map
      (etaleShriekLocallyClosedCoefficientMap φ g j M))
    (compactComparison φ g j L) ((scalarExtension φ X).obj M)
    (internalAdjunction B g j ((scalarExtension φ S).obj L) ((scalarExtension φ X).obj M))
    (evaluationComparison φ X ((shriek A g j).obj L) M)

private lemma normalized_of_pairing
    (φ : A →+* B) (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X)
    [IsIso (internalAdjunction A g j L M)]
    [IsIso (internalAdjunction B g j ((scalarExtension φ S).obj L)
      ((scalarExtension φ X).obj M))]
    [IsIso (ordinaryComparison φ g j (innerHom g j L M))]
    [IsIso (evaluationComparison φ S L (exceptionalObject g j M))]
    [IsIso (etaleShriekLocallyClosedCoefficientMap φ g j M)]
    [IsIso (compactComparison φ g j L)]
    (hp : PairingChangeEquation φ g j L M
      (asIso (etaleShriekLocallyClosedCoefficientMap φ g j M))) :
    IsNormalizedComparison φ g j L M := by
  exact MappedComparisonWord.mk (scalarExtension φ X) (star B g j)
    (derivedHom (ModuleCat B) X) (internalAdjunction A g j L M)
    (ordinaryComparison φ g j (innerHom g j L M))
    (evaluationComparison φ S L (exceptionalObject g j M))
    (((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj L))).map
      (etaleShriekLocallyClosedCoefficientMap φ g j M))
    (compactComparison φ g j L) ((scalarExtension φ X).obj M)
    (internalAdjunction B g j ((scalarExtension φ S).obj L) ((scalarExtension φ X).obj M))
    (evaluationComparison φ X ((shriek A g j).obj L) M)
    (pairingCancellation φ g j L M hp)

/-- For a degree-zero finite-projective local system, N and Q are finite-Tor bounded
constructible and the specified displayed-arrow composite is invertible and equals v.
Source: thm-coef-finite-hom, proof paragraphs 3--4
(blueprint: lem-coef-locally-closed-hom-generator).

Proof:
1. Finite type over the field makes X Noetherian (lem-coef-finite-hom-domain-calculus).
   Its underlying space is Noetherian (lem-weil-pbc-noetherian-scheme-closed-subsets-minimal)
   and every subset is quasi-compact (lem-sfb-noetherian-space-compact-subsets).
   On an affine of X, S is covered by distinguished opens in a closed subscheme;
   choose finitely many. Their rings are generated by the quotient ring and one inverse,
   so s and S over k are finite type. The immersion is separated, and S over k is separated.
2. Bound dim X by d using lem-kun-dimension-finite-type, choosing d = 0 if X is empty.
   Taking closures of irreducible closed subsets of S preserves strict chains, so
   dim S is at most dim X (def-kun-topological-krull-dimension).
   Apply lem-coef-etale-lisse-hom-reduction: L has Tor interval [0,0], N and Q have
   finite Tor intervals and bounded constructible cohomology, and u is invertible.
   This is local in L and includes the zero-rank constant model.
3. The coefficient ring is finite (def-weil-l-adic-coefficient-extension), and a finite
   projective module is a summand of a finite free module, hence finite. Thus L in
   degree zero is bounded constructible and finite-Tor. Apply
   lem-coef-etale-locally-closed-shriek to M and to L,N. It gives q and b with exactly
   the pasted exceptional-counit normalization in the statement.
4. B is cyclic as an A-module. Apply lem-coef-finite-direct-image to s,Q: its canonical
   ordinary counit comparison c is invertible, using the geometric checks of step 1.
5. Apply lem-coef-internal-adjunction-pairing-change. Its internal adjunctions use the
   open and closed proper projection pairing. Functors preserve isomorphisms, so the
   factors involving u,b,q and the inverse of I_A are invertible, as is I_B.
6. The pairing-change equality reads D = F(I_A) followed by v. Precompose it with
   F(I_A inverse), cancel the inverse pair, and expand functoriality of Rs_* to obtain
   exactly the displayed factors and equality to v. No inverse of v is used.
-/
theorem normalizedComparison
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n m : ℕ+) (hmn : m ≤ n)
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    {S Z : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : Sheaf S.smallEtaleTopology (ModuleCat (coefficient l E n)))
    (_hL : ∃ d : Scheme.LocallyConstantDatum L, ∀ i : d.cover.I₀,
      ∃ P : ModuleCat (coefficient l E n),
        Module.Finite (coefficient l E n) P ∧ Module.Projective (coefficient l E n) P ∧
        Nonempty (L.over (d.cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (S.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat (coefficient l E n))).obj P))
    (M : DerivedCategoryModule (coefficient l E n) X)
    (_hM : WeilConjectures.finiteTorConstructibleEtale l E n n.property X M) :
    WeilConjectures.finiteTorConstructibleEtale l E n n.property S
      (exceptionalObject g j M) ∧
    WeilConjectures.finiteTorConstructibleEtale l E n n.property S
      (innerHom g j ((_root_.DerivedCategory.singleFunctor _ 0).obj L) M) ∧
    IsNormalizedComparison (reduction l E n m hmn) g j
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L) M := by
  classical
  let φ := reduction l E n m hmn
  let P := (_root_.DerivedCategory.singleFunctor _ 0).obj L
  have hs := etaleLocallyClosedShriekComparisons D l _hl E n m hmn m.property X g j
  change EtaleLocallyClosedShriekComparisons φ
    (WeilConjectures.finiteTorConstructibleEtale l E n n.property) g j at hs
  obtain ⟨hNg, hN, hcNg, hbg, hb, he⟩ := hs.2.1 M _hM
  obtain ⟨hP, hQ, hu⟩ := locallyProjectiveCoefficientHom φ S L _hL
    (exceptionalObject g j M) hN
  have hq : IsIso (compactComparison φ g j P) := by
    simpa only [compactComparison, etaleShriekLocallyClosedSupportMap] using hs.2.2.1 P hP
  have hI : IsIso (internalAdjunction (coefficient l E n) g j P M) :=
    locallyClosedInternalAdjunction_isIso (coefficient l E n) g j P M
  have hIB : IsIso (internalAdjunction (coefficient l E m) g j ((scalarExtension φ S).obj P)
      ((scalarExtension φ X).obj M)) :=
    locallyClosedInternalAdjunction_isIso (coefficient l E m) g j _ _
  have hc : IsIso (ordinaryComparison φ g j (innerHom g j P M)) :=
    locallyClosedOrdinaryComparison_isIso D l _hl E n m hmn g j (innerHom g j P M) hQ
  have hb' : CounitCompatible φ g j M
      (asIso (etaleShriekLocallyClosedCoefficientMap φ g j M)) := by
    simpa only [CounitCompatible, compactComparison, etaleShriekLocallyClosedSupportMap,
      asIso_hom, counit, etaleShriekLocallyClosedAdjunction, etaleShriekClosedAdjunction,
      shriek, exceptional, etaleShriekClosedExceptional, Functor.comp_obj]
      using he
  have hp := internalAdjunction_pairing_change D l _hl E n m hmn g j M P
    _hM hP hN hQ (asIso (etaleShriekLocallyClosedCoefficientMap φ g j M)) hb'
  exact ⟨hN, hQ, normalized_of_pairing φ g j P M hp⟩

end AlgebraicGeometry.Etale.LocallyClosedHomGenerator
