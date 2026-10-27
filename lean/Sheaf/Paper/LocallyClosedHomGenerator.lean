/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.Paper.NormalizedComparisonWord
public import Sheaf.Paper.InternalAdjunctionPairingChange
public import Sheaf.Paper.EtaleLocallyClosedShriek
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.Paper.LocallyProjectiveCoefficientHom
public import Sheaf.Paper.LocallyClosedInternalAdjunctionIso
import Sheaf.Paper.LocallyClosedPairingCancellation
import Sheaf.Paper.LocallyClosedOrdinaryComparisonIso

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

/-- Inverse of the specified internal-adjunction arrow on its isomorphism locus.
The zero value elsewhere only totalizes the construction. The result below asserts
invertibility of the original arrow as well as of every factor using this inverse.
Source: thm-coef-finite-hom, paragraphs 3--4
(blueprint: lem-coef-locally-closed-hom-generator). -/
def inverseInternalAdjunction (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) :
    ((derivedHom (ModuleCat A) X).obj (op ((shriek A g j).obj L))).obj M ⟶
      (star A g j).obj (innerHom g j L M) :=
  @inv _ _ _ _ (internalAdjunction A g j L M)
    (locallyClosedInternalAdjunction_isIso A g j L M)

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
