# FiniteAdjunctionTransition construction declarations

## Reason

Two proper-part lemmas need the defined horizontal maps. Keeping those definitions
in the theorem module would make imports cyclic. Relocate the existing construction
block verbatim to FiniteAdjunctionTransitionData and publicly re-export it from the
original module. This is an interface-preserving relocation, not a change of data.

## Old

The following verbatim construction block was in
lean/Sheaf/SixFunctors/FiniteAdjunctionTransition.lean:

```lean
/-- The actual integral global mapping complex, with its R-module action.
Source: integral-dualizing proof, paragraph 2, first finite mapping complex
(blueprint: lem-coef-finite-adjunction-transition). -/
def H (r : ℕ) :=
  coefPairingIntegralHom l E X r (integralDualizingFiniteTerm l E D X r)

/-- Restrict the counit-defined tau to completed integral coefficients. The final
comparison is the section-normalized composition of actual restrictions.
Source: integral-dualizing proof, paragraph 2, left vertical map
(blueprint: lem-coef-finite-adjunction-transition). -/
def restrictedTau (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :=
  (scalarReductionDerivedRestriction l E X m).map
      (integralDualizingExceptionalTransition l E D X hl h) ≫
    (normalizedDVRResCompletedComp l E X D hl h).hom.app
      (integralDualizingFiniteTerm l E D X n)

/-- H_m to H_n is postcomposition by the actual restricted exceptional transition.
Source: integral-dualizing proof, paragraph 2, left vertical map
(blueprint: lem-coef-finite-adjunction-transition). -/
def HTransition (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (H D l E X m).obj (op K) ⟶ (H D l E X n).obj (op K) :=
  (coefPairingIntegralSections l E X).map
    ((coefficientIntegralInternalHom l E X).map
      (Prod.mkHom (𝟙 (op K)) (restrictedTau D l E X hl h)))

/-- C is exact coefficient-point sections of the integral compact-support Roos limit.
T and e below present the actual finite compact-support reduction tower, including
its transitions. This is the value to which prescribedReductions applies.
Source: integral-dualizing proof, paragraph 2, C=Gamma(s,Ra_!K)
(blueprint: lem-coef-finite-adjunction-transition). -/
abbrev C
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))))) :=
  coefCurryingIntegralSections l E D X T

/-- The coefficient-point dual J_r=RHom_R(C,A_r), contravariant in K.
Source: integral-dualizing proof, paragraph 2, right mapping complex
(blueprint: lem-coef-finite-adjunction-transition). -/
def J
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))))) (r : ℕ) :=
  (C D l E X T).op ⋙ coefCurryingPointHom l E r

/-- Postcomposition in RHom_R(C,-) by the genuine R-linear quotient A_m to A_n.
Source: integral-dualizing proof, paragraph 2, right vertical map
(blueprint: lem-coef-finite-adjunction-transition). -/
def JTransition
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))))
    {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (J D l E X T m).obj (op K) ⟶ (J D l E X T n).obj (op K) :=
  (ihom ((C D l E X T).obj K)).map
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).map
      (coefTraceQuotientMap l E h))

variable
  (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
  (a₀ b₀ : ℤ)
  (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
    DerivedCategory (pbcTowers (Spec (.of D.k))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))))
  (e : ∀ n : ℕ, T ⋙ pbcTowerEvaluation (Spec (.of D.k))
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) n ≅
      compactSupportRestrictedLevel l E (finiteDualizingCompactification D X) n)
  (M : CoefCurryingModels l E D X Q a₀ b₀ T e)

/-- The point-section reduction comparison alpha_r is the scalar adjunct of the
actual Roos projection. Its adjunction has unit x mapped to 1 tensor x; the tower
transition equation fixes its successive-reduction normalization. In particular
this does not choose from point_sections_derived_reduction's Nonempty isomorphism.
Source: integral-dualizing proof, paragraph 2, prescribed reductions
(blueprint: lem-coef-finite-adjunction-transition). -/
def alpha (r : ℕ) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
  CoefTower.reductionComparison D l E (finiteDualizingCompactification D X) T e r K

/-- Scalar adjunction on the full mapping complex, defined by base change of
normalized evaluation and the actual scalar adjunction counit. The finite tensor
comparison is normalized on K-flat representatives by M.calculus.
Source: integral-dualizing proof, paragraph 2, scalar-Hom identification
(blueprint: lem-coef-finite-adjunction-transition). -/
def scalarHom (r : ℕ) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (H D l E X r).obj (op K) ⟶
      (coefPairingFiniteHom l E X r (integralDualizingFiniteTerm l E D X r)).obj (op K) :=
  (coefPairingIntegralSections l E X).map
    (coefficientEnrichedAdjunctionMap M.calculus.integralClosed (M.calculus.finiteClosed r)
      (coefficientFiniteDerivedExtension l E X r) (coefficientFiniteAdjunction l E X r)
      (M.calculus.finiteTensor r) K (integralDualizingFiniteTerm l E D X r))

/-- The specified horizontal map. The first factor is the evaluation-defined scalar
adjunction from integral Hom to finite Hom. The second factor is the finite mapping
adjunction pairing characterization: insert the
actual compact-support projection, balance scalars, apply projection and evaluation,
then the finite exceptional counit, and curry. In particular no independent alpha_r
is chosen from the point-reduction theorem's Nonempty statement.
Source: integral-dualizing proof, paragraph 2, gamma tilde
(blueprint: lem-coef-finite-adjunction-transition). -/
def finiteHorizontal (r : ℕ)
    (K : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory) :
    (H D l E X r).obj (op K.obj) ⟶ (J D l E X T r).obj (op K.obj) :=
  scalarHom D l E X Q a₀ b₀ T e M r K.obj ≫
    M.finiteArrow l E D X Q a₀ b₀ T e r K

```

## New

Exactly the Old block, byte for byte, is now in
lean/Sheaf/SixFunctors/FiniteAdjunctionTransitionData.lean.
The original module contains `public import Sheaf.SixFunctors.FiniteAdjunctionTransitionData`.
All names, signatures, attributes and bodies are preserved. The target theorem
signature and all original public imports are unchanged. No target meaning changes.

## Users

`python3 tools/downstream.py Sheaf.SixFunctors.FiniteAdjunctionTransition`
reported zero current Lean module importers. Unfinished parent DAG references are
preserved: the original item node remains attached to the original theorem.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.FiniteAdjunctionTransition | N3 | definitions re-exported verbatim; proof combines proper parts |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | new | owns the unchanged construction block |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | new | uses construction data; transition equation only |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | new | uses construction data; input naturality only |

## Status

landed 20261025T123429-L-1870654 2026-10-25 (merge of deliver/N3/Sheaf.SixFunctors.FiniteAdjunctionTransition)
