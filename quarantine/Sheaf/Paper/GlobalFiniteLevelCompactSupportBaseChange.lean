/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Compactification.NagataCompactification

/-! # Finite-level pro-etale compact-support base change

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
thm-cbc-finite-level-proetale.proof.md, steps 1--8; human-authorized global
compactification restatement, 2026-10-18 (blueprint: thm-cbc-finite-level-proetale).

All operations below are the ordinary bounded below operations. The canonical
coefficient realization identifies fixed-scalar module sheaves with the prescribed
continuous-function coefficient modules. No local compact-support extension is used.
This interface was revalidated by N4 against the released 2026-10-18 repair note.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Inverse of the canonical coefficient realization, applied termwise to D-plus.
Source: blueprint finite-level compact-support proof, coefficient convention
(blueprint: thm-cbc-finite-level-proetale). -/
abbrev cbcFixedCoefficients (T : Scheme.{u}) :=
  letI := @Equivalence.inverse_additive _ _ _ _ _ _
    (finiteCoefficientRealization T Λ).asEquivalence
      (finiteCoefficientRealization_additive T Λ)
  (finiteCoefficientRealization T Λ).asEquivalence.inverse.mapDerivedCategoryPlus

/-- The retained witness in fixed-scalar coordinates, using the actual equivalence
unit and the derived composition comparison. Source: blueprint finite-level
compact-support proof, step 2 (blueprint: thm-cbc-finite-level-proetale). -/
def cbcFixedWitness {T : Scheme.{u}} (K : FiniteCoefficientDerivedCategoryPlus T Λ)
    (W : EtaleOriginWitness T Λ K) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus.obj W.L ≅
      (cbcFixedCoefficients Λ T).obj K := by
  letI := @Equivalence.inverse_additive _ _ _ _ _ _
    (finiteCoefficientRealization T Λ).asEquivalence
      (finiteCoefficientRealization_additive T Λ)
  exact (Functor.mapDerivedCategoryPlusIdIso _).symm.app _ ≪≫
    (Functor.mapDerivedCategoryPlusNatIso
      (G := finiteCoefficientRealization T Λ ⋙
        (finiteCoefficientRealization T Λ).asEquivalence.inverse)
      (finiteCoefficientRealization T Λ).asEquivalence.unitIso).app _ ≪≫
    (Functor.mapDerivedCategoryPlusCompIso (finiteCoefficientRealization T Λ)
      (finiteCoefficientRealization T Λ).asEquivalence.inverse).app _ ≪≫
    (cbcFixedCoefficients Λ T).mapIso
      ((Functor.mapDerivedCategoryPlusCompIso
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
        (finiteCoefficientRealization T Λ)).symm.app W.L ≪≫ W.alpha)

/-- The exact inverse-image comparison applied degreewise.
Source: blueprint finite-level compact-support proof, step 4
(blueprint: thm-cbc-finite-level-proetale). -/
def cbcGlobalPullbackComparison {U V : Scheme.{u}} (g : U ⟶ V) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (F := Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
      (G := comparisonUpperStar (ModuleCat.{u + 1} Λ) V ⋙
        upperStar (ModuleCat.{u + 1} Λ) g)
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) g) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The source endpoint comparison S_c, from etale exchange to the actual
proper/open pro-etale compactification formula. Source: blueprint finite-level
compact-support proof, step 4 (blueprint: thm-cbc-finite-level-proetale). -/
def cbcGlobalSource {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (g : Y' ⟶ Y) (c : Compactification f) :
    (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ⋙
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus) ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategoryPlus ≅
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c) ⋙
          (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (cbcGlobalPullbackComparison Λ g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (compactSupportSiteComparisonPlus Λ c) _

/-- The target endpoint comparison T_c, with the base-changed compactification.
Source: blueprint finite-level compact-support proof, step 4
(blueprint: thm-cbc-finite-level-proetale). -/
def cbcGlobalTarget {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (c : Compactification f) :
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus ⋙
        Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
          (c.ofIsPullback sq)) ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategoryPlus ≅
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus) ⋙
          rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
            (c.ofIsPullback sq) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (compactSupportSiteComparisonPlus Λ (c.ofIsPullback sq)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (cbcGlobalPullbackComparison Λ g') _

/-- The source operation g⁻¹ Rp_* j_!, in the specified finite coefficient category.
The inverse coefficient realization is followed by the ordinary proper/open formula
and the exact pullback, then by coefficient realization. Source: blueprint finite-level
compact-support proof, steps 3--5 (blueprint: thm-cbc-finite-level-proetale). -/
def cbcGlobalSourceFunctor {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (g : Y' ⟶ Y) (c : Compactification f) :
    FiniteCoefficientDerivedCategoryPlus X Λ ⥤ FiniteCoefficientDerivedCategoryPlus Y' Λ :=
  cbcFixedCoefficients Λ X ⋙
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ⋙
      (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus) ⋙
        (finiteCoefficientRealization Y' Λ).mapDerivedCategoryPlus

/-- The target operation Rp'_* j'_! g'⁻¹ with the base-changed compactification,
using the same coefficient realization as the source.
Source: blueprint finite-level compact-support proof, steps 3--5
(blueprint: thm-cbc-finite-level-proetale). -/
def cbcGlobalTargetFunctor {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (c : Compactification f) :
    FiniteCoefficientDerivedCategoryPlus X Λ ⥤ FiniteCoefficientDerivedCategoryPlus Y' Λ :=
  cbcFixedCoefficients Λ X ⋙
    ((upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus ⋙
      rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
        (c.ofIsPullback sq)) ⋙ (finiteCoefficientRealization Y' Λ).mapDerivedCategoryPlus

/-- The prescribed exchange Q(alpha) T A(E) S⁻¹ P(alpha)⁻¹. Its middle arrow is the
specified etale compactification exchange, and its endpoint comparisons are the canonical
proper/open and pullback comparisons. Source: blueprint finite-level compact-support
proof, steps 4--5 (blueprint: thm-cbc-finite-level-proetale). -/
def cbcGlobalExchange {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (c : Compactification f) (K : FiniteCoefficientDerivedCategoryPlus X Λ)
    (W : EtaleOriginWitness X Λ K) :
    (cbcGlobalSourceFunctor Λ g c).obj K ⟶ (cbcGlobalTargetFunctor Λ sq c).obj K :=
  (finiteCoefficientRealization Y' Λ).mapDerivedCategoryPlus.map
    ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ⋙
        (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus).map
          (cbcFixedWitness Λ K W).inv ≫
      (cbcGlobalSource Λ g c).inv.app W.L ≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategoryPlus.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c).app W.L) ≫
      (cbcGlobalTarget Λ sq c).hom.app W.L ≫
      ((upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
          (c.ofIsPullback sq)).map (cbcFixedWitness Λ K W).hom)

/-- The source compactification comparison, transported from the canonical etale
shriekIso c d and conjugated by the retained witness. It is the composite U in step 8,
including the outside witness maps. No common refinement is chosen here.
Source: blueprint finite-level compact-support proof, step 8
(blueprint: thm-cbc-finite-level-proetale). -/
def cbcGlobalSourceComparison {X Y Y' : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (g : Y' ⟶ Y) (c d : Compactification f) (K : FiniteCoefficientDerivedCategoryPlus X Λ)
    (W : EtaleOriginWitness X Λ K) :
    (cbcGlobalSourceFunctor Λ g c).obj K ≅ (cbcGlobalSourceFunctor Λ g d).obj K :=
  (finiteCoefficientRealization Y' Λ).mapDerivedCategoryPlus.mapIso
    ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ⋙
        (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus).mapIso
          (cbcFixedWitness Λ K W).symm ≪≫
      (cbcGlobalSource Λ g c).symm.app W.L ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategoryPlus.mapIso
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.mapIso
          (((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekIso c d).app W.L)) ≪≫
      (cbcGlobalSource Λ g d).app W.L ≪≫
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) d ⋙
        (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus).mapIso
          (cbcFixedWitness Λ K W))

/-- The target compactification comparison, transported from the canonical primed
etale shriekIso at g'⁻¹L and conjugated by the retained witness. This is V of step 8.
Source: blueprint finite-level compact-support proof, step 8
(blueprint: thm-cbc-finite-level-proetale). -/
def cbcGlobalTargetComparison {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [QuasiCompact f]
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (c d : Compactification f) (K : FiniteCoefficientDerivedCategoryPlus X Λ)
    (W : EtaleOriginWitness X Λ K) :
    (cbcGlobalTargetFunctor Λ sq c).obj K ≅ (cbcGlobalTargetFunctor Λ sq d).obj K := by
  letI : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq
    inferInstance
  exact (finiteCoefficientRealization Y' Λ).mapDerivedCategoryPlus.mapIso
    (((upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
          (c.ofIsPullback sq)).mapIso (cbcFixedWitness Λ K W).symm ≪≫
      (cbcGlobalTarget Λ sq c).symm.app W.L ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategoryPlus.mapIso
        (((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekIso
          (c.ofIsPullback sq) (d.ofIsPullback sq)).app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus.obj W.L)) ≪≫
      (cbcGlobalTarget Λ sq d).app W.L ≪≫
      ((upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
          (d.ofIsPullback sq)).mapIso (cbcFixedWitness Λ K W))

/-- Finite-level pro-etale compact-support base change, with the global
compactification alternative and all choices retained.
Source: blueprint main-20261015, thm-cbc-finite-level-proetale.proof.md, steps 1--8;
restatement authorized by the human, 2026-10-18
(blueprint: thm-cbc-finite-level-proetale).

Proof:
1. Retain the supplied compactification, or apply Nagata when Y is qcqs. Its open
part is quasi-compact because f is finite type and the proper part is separated.
Base change gives c' without imposing qcqs on Y'. Both proper parts are relatively
qcqs, by properness and separatedness.
2. Apply thm-cbc-finite-torsion to the bounded below etale representative W.L and c.
Exact inverse image keeps the primed representative bounded below.
3. Apply the exact open site comparison degreewise. Compose it with the normalized
proper direct-image counit mate to obtain C_c, namely compactSupportSiteComparisonPlus.
This also gives C_c' for the pulled-back representative.
4. Combine C_c and C_c' with the pullback comparison to form S and T, precisely
cbcGlobalSource and cbcGlobalTarget. The transported exchange is S⁻¹ A(E) T.
5. Conjugate by the two images of alpha, exactly as in cbcGlobalExchange. Every
factor is invertible, since E is the finite-torsion exchange. Coefficient realization
and its inverse preserve the construction and invertibility.
6. Full faithfulness of comparison on all D-plus lifts the isomorphism between two
witnesses uniquely to an isomorphism between their etale representatives.
7. Naturality of S, T and E in this isomorphism, followed by cancellation of alpha,
proves equality of the exchange for every pair of witnesses.
8. For c,d the finite-torsion theorem gives r:H_c≅H_d and r':H_c'≅H_d' with
r' E_c = E_d g⁻¹r. Conjugating this square by S,T and alpha gives exactly the
source/target comparisons below. Naturality of the pullback comparison and cancellation
give E_c V = U E_d. Full faithfulness makes these comparisons independent of the
witness too. Independence of the common refinement follows because shriekIso already
has this independence. No constructibility or residue-characteristic assumption enters.
-/
theorem globalFiniteLevelCompactSupportBaseChange
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g)
    (h : (CompactSpace Y ∧ QuasiSeparatedSpace Y) ∨ Nonempty (Compactification f))
    (K : FiniteCoefficientDerivedCategoryPlus X Λ) (W : EtaleOriginWitness X Λ K) :
    Nonempty (Compactification f) ∧
      ∀ c : Compactification f,
        IsIso (cbcGlobalExchange Λ sq c K W) ∧
        (∀ W' : EtaleOriginWitness X Λ K,
          cbcGlobalExchange Λ sq c K W = cbcGlobalExchange Λ sq c K W') ∧
        (∀ d : Compactification f,
          cbcGlobalExchange Λ sq c K W ≫ (cbcGlobalTargetComparison Λ sq c d K W).hom =
            (cbcGlobalSourceComparison Λ g c d K W).hom ≫ cbcGlobalExchange Λ sq d K W) ∧
        (∀ (d : Compactification f) (W' : EtaleOriginWitness X Λ K),
          cbcGlobalSourceComparison Λ g c d K W = cbcGlobalSourceComparison Λ g c d K W' ∧
          cbcGlobalTargetComparison Λ sq c d K W =
            cbcGlobalTargetComparison Λ sq c d K W') := by
  sorry

end AlgebraicGeometry.ProEtale
