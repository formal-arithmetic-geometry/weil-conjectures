/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.SectionCentredChartData
public import Sheaf.Paper.SectionNormalFibreMap
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import WeilConjectures.Compactification.NagataCompactification

/-! # Local shifted dualizing lines and normalized section-chart comparisons

Source: main-20261015, sk-thm-dnc, opening paragraph and Local construction
(blueprint: lem-trf-section-local-dualizing-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
open SectionComparisonArrows

/-- The full local comparison statement. Each chart is arbitrary, with its Cartesian
centre, and c and f are constrained to be the counit-defined chart maps themselves.
The affine adjunctions are exhibited, never chosen from a bare isomorphism existence.
Source: main-20261015, sk-thm-dnc, opening paragraph and Local construction
(blueprint: lem-trf-section-local-dualizing-comparisons).

Proof:
1. Finite-type Noetherian permanence applies to V and the affine line. Pulling back
smooth tensor duality along s and sigma preserves shifts, degree-zero sheaves and
etale covers. This gives the two locally constant rank-one shifted sheaves.
2. Apply exceptional smooth base change to the actual Rees fibre squares at 1 and 0.
Pull to their sections and use inverse-image composition. These are precisely atOne
and normalFibreMap, because sectionMap uses the counit transpose itself.
3. On any affine centred chart the Cartesian centre square identifies the ideal with
the coordinate ideal. Etale flat base change of Rees algebras gives the deformed chart;
R[x][t,(x)/t]=R[t,u] with x_j=t*u_j by independence of Laurent monomials.
The chartGeometry domain checks justify every use of locality and affine adjunction.
4. Exhibit the affine-space adjunctions over T and A1_T. Compare their right adjoints
with the chosen compact-support adjoints by rightAdjointUniq, respecting counits.
Pull to the sections and apply canonical Tate pullback, giving affineSectionIso.
5. Smooth base change to T, followed by sectionLocality for the open chart and its
etale coordinate map, is exactly localSourceMap. The same operations on the actual
Rees chart give localFamilyMap. Thus both maps are isomorphisms c and f.
6. rawComparison is f followed by inverse Tate pullback and a*(c inverse). Its value
at 1 need not yet be theta. Define h by discrepancy: theta inverse followed by that
value. normalizedComparison is lambda followed by a*(h inverse). Naturality of the
section compositor gives i1*(lambda_norm)=h inverse h theta=theta. No fibre
identification or orientation was substituted. Zero rank, zero coefficients and empty
bases satisfy the same formulas. -/
theorem section_local_dualizing_comparisons
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (normalProjection d g s hs)]
    [IsNoetherian s.ker.deformationSpace]
    [SmoothOfRelativeDimension d (Scheme.Hom.deformationSpaceProj g s)]
    [IsSeparated (Scheme.Hom.deformationSpaceProj g s)] :
    (∃ L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty ((sectionInvariant A g s)⟦-(2 * (d : ℤ))⟧ ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage S,
        ∀ i : cover.I₀, Nonempty (L.over (cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (S.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) ∧
    (∃ L : Sheaf (AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty ((family A g s)⟦-(2 * (d : ℤ))⟧ ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage (AffineSpace (ULift.{u} (Fin 1)) S),
        ∀ i : cover.I₀, Nonempty (L.over (cover.etalePrecoverageToEtale i) ≅
          (constantSheaf ((AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology.over
            (cover.etalePrecoverageToEtale i)) (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) ∧
    IsIso (atOne A g s hs) ∧ IsIso (normalFibreMap A d g s hs) ∧
    ∀ c : Chart d g s hs,
      ∃ adjT : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin d)) c.T ↘ c.T) ⊣ affineRight A N hA c.T d,
      ∃ adjL : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) c.T) ↘ _) ⊣
            affineRight A N hA (AffineSpace (ULift.{u} (Fin 1)) c.T) d,
      ∃ cIso : (upperStar (ModuleCat.{u + 1} A) c.b).leftDerivedFunctor.obj
          (sectionInvariant A g s) ≅ tateObject A N hA c.T d,
      ∃ fIso : (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace.map (ULift.{u} (Fin 1)) c.b)).leftDerivedFunctor.obj (family A g s) ≅
            tateObject A N hA (AffineSpace (ULift.{u} (Fin 1)) c.T) d,
      cIso.hom = localSourceMap A N hN hA hS d g s hs c adjT ∧
      fIso.hom = localFamilyMap A N hN hA hS d g s hs c adjL ∧
      ∃ theta : (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) c.T)).leftDerivedFunctor.obj
            ((upperStar (ModuleCat.{u + 1} A)
              (AffineSpace.map (ULift.{u} (Fin 1)) c.b)).leftDerivedFunctor.obj (family A g s)) ≅
          (upperStar (ModuleCat.{u + 1} A) c.b).leftDerivedFunctor.obj (sectionInvariant A g s),
        theta.hom = restrictedTheta A g s hs c.b ∧
        restrictionAtOne A c.T (normalizedComparison A c.T
          (rawComparison A N hN hA c.T (invertibleOnSource N c.b hS) d _ _ cIso fIso) theta) =
          theta := by
  sorry

end AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
