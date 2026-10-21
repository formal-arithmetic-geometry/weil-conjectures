/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.SectionCentredChartData
public import Sheaf.Paper.SectionNormalFibreMap
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import WeilConjectures.ConstructibleSheaf.Pullback

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

private theorem section_line
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] [HasInvertibleExponent A X]
    (t : T ⟶ X) :
    ∃ L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty (((upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor.obj
        (dualizingComplex (ModuleCat.{u + 1} A) f))⟦-(2 * (d : ℤ))⟧ ≅
          (_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage T,
        ∀ i : cover.I₀, Nonempty (L.over (cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) := by
  classical
  obtain ⟨L₀, hLC₀, hStalk₀, ⟨e₀⟩, _⟩ := exists_dualizingComplex_iso_and_tensor A f d
  let L := (upperStar (ModuleCat.{u + 1} A) t).obj L₀
  have hLC : Scheme.IsLocallyConstantSheaf L :=
    Scheme.IsLocallyConstantSheaf.upperStar t L₀
  have hStalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ T),
      Nonempty ((Scheme.pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of A A) := by
    intro Ω _ _ x
    exact ⟨(upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) t x).app L₀ ≪≫
      (hStalk₀ Ω (x ≫ t)).some⟩
  refine ⟨L, ?_, ?_⟩
  · let P := (upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor
    let e : P.obj (dualizingComplex (ModuleCat.{u + 1} A) f) ≅
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)⟦(2 * (d : ℤ))⟧ :=
      P.mapIso e₀ ≪≫ (P.commShiftIso (2 * (d : ℤ))).app _ ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) t).app L₀)
    exact ⟨(shiftFunctor _ (-(2 * (d : ℤ)))).mapIso e ≪≫
      shiftShiftNeg _ (2 * (d : ℤ))⟩
  · obtain ⟨datum⟩ := hLC.nonempty_locallyConstantDatum
    let cover : Scheme.Cover.{u} Scheme.etalePrecoverage T :=
      Scheme.Cover.mkOfCovers (Σ i : datum.cover.I₀, datum.cover.X i)
        (fun i ↦ datum.cover.X i.1) (fun i ↦ datum.cover.f i.1)
        (by
          intro x
          obtain ⟨i, y, hy⟩ := datum.cover.exists_eq x
          exact ⟨⟨i, y⟩, y, hy⟩)
        (fun i ↦ datum.cover.map_prop i.1)
    refine ⟨cover, ?_⟩
    intro i
    let U := datum.cover.etalePrecoverageToEtale i.1
    have hC := datum.isConstant i.1
    obtain ⟨M, ⟨eM⟩⟩ := (L.over U).mem_essImage_of_isConstant
    let x := (datum.cover.X i.1).algClosurePoint i.2
    let P := upperStar (ModuleCat.{u + 1} A) U.hom
    let eP : (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ≅ P.obj L :=
      ((Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
        (T.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} A)
        Over.mkIdTerminal).symm.app M ≪≫
      (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} A)).functor.mapIso eM ≪≫
      Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U L
    have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let eFree : M ≅ ModuleCat.of A A :=
      ((Scheme.pointSmallEtale x).sheafFiberConstantSheafIso M).symm ≪≫
      (Scheme.pointSmallEtale x).sheafFiber.mapIso eP ≪≫
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) U.hom x).app L ≪≫
      (hStalk _ (x ≫ U.hom)).some
    exact ⟨eM.symm ≪≫
      (constantSheaf (T.smallEtaleTopology.over U) (ModuleCat.{u + 1} A)).mapIso eFree⟩

private theorem isIso_sectionMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] [HasInvertibleExponent A X]
    (f' : X' ⟶ Y') [HasCompactification f'] [QuasiCompact f']
    (b : Y' ⟶ Y) (v : X' ⟶ X) (sq : IsPullback v f' f b)
    (s : Y ⟶ X) (s' : Y' ⟶ X') (hs : s' ≫ v = b ≫ s) :
    IsIso (sectionMap A f f' b v sq s s' hs) := by
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general A f d sq
  have : IsIso (dualizingComplexBaseChangeMap A sq) := by
    rw [isIso_dualizingComplexBaseChangeMap_iff]
    infer_instance
  unfold sectionMap
  infer_instance

private theorem isIso_chartMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) (f : X ⟶ T) [HasCompactification f]
    (r : T ⟶ X) (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) T)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = f)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ⊣ affineRight A N hA T d) :
    IsIso (chartMap A N hN hA hT d f r e w adj) := by
  unfold chartMap
  infer_instance

private theorem restriction_normalized
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {C : DerivedCategoryModule A T}
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) T)}
    (l : F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj C)
    (theta : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.obj F ≅ C) :
    restrictionAtOne A T (normalizedComparison A T l theta) = theta := by
  let P := (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor
  let Q := (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor
  let ε := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)
    (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T)
  let h := discrepancy A T l theta
  apply Iso.ext
  unfold restrictionAtOne normalizedComparison
  change P.map (l.hom ≫ Q.map h.inv) ≫ ε.hom.app C = theta.hom
  rw [Functor.map_comp, Category.assoc, ← Functor.comp_map]
  rw [ε.hom.naturality h.inv]
  change P.map l.hom ≫ ε.hom.app C ≫ h.inv = theta.hom
  dsimp only [h]
  unfold discrepancy restrictionAtOne
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv]
  change P.map l.hom ≫ ε.hom.app C ≫ (ε.inv.app C ≫ P.map l.inv) ≫ theta.hom = _
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← P.map_comp_assoc,
    Iso.hom_inv_id, P.map_id, Category.id_comp]

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
  classical
  let : HasInvertibleExponent A S := ⟨N, hN, hA, hS⟩
  let : HasInvertibleExponent A V := HasInvertibleExponent.of_hom g
  let : HasInvertibleExponent A s.ker.deformationSpace :=
    HasInvertibleExponent.of_hom (s.ker.deformationSpaceProj ≫ g)
  have hOne : IsIso (atOne A g s hs) := by
    exact isIso_sectionMap A (Scheme.Hom.deformationSpaceProj g s) d g
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
      (Scheme.Hom.deformationSpaceOneFibre g s)
      (Scheme.Hom.isPullback_deformationSpaceOneFibre g s)
      s.deformationSpaceSection s (Scheme.Hom.comp_deformationSpaceOneFibre hs)
  have hZero : IsIso (normalFibreMap A d g s hs) := by
    let := normalProjectionQuasiCompact d g s hs
    unfold normalFibreMap
    exact isIso_sectionMap A (Scheme.Hom.deformationSpaceProj g s) d
      (normalProjection d g s hs) (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
      (normalFibreInclusion d g s hs) (normalFibre_spec d g s hs).1
      s.deformationSpaceSection (normalZero d g s hs) (normalFibre_spec d g s hs).2
  refine ⟨section_line A g d s,
    section_line A (Scheme.Hom.deformationSpaceProj g s) d s.deformationSpaceSection,
    hOne, hZero, ?_⟩
  intro c
  let := chartGeometry d g s hs c
  let hT := invertibleOnSource N c.b hS
  let hL := invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T) hT
  obtain ⟨adjT⟩ := nonempty_affineSpaceAmbientAdjunction N hN A hA c.T hT d
  obtain ⟨adjL⟩ := nonempty_affineSpaceAmbientAdjunction N hN A hA
    (AffineSpace (ULift.{u} (Fin 1)) c.T) hL d
  have hSource : IsIso (localSourceMap A N hN hA hS d g s hs c adjT) := by
    have := isIso_sectionMap A g d (pullback.snd g c.b) c.b (pullback.fst g c.b)
      (IsPullback.of_hasPullback g c.b) s (Scheme.Hom.baseChangeSection g s hs c.b)
      (Scheme.Hom.baseChangeSection_fst g s hs c.b)
    have := isIso_chartMap A N hN hA hT d (c.j ≫ pullback.snd g c.b)
      c.r c.e c.overE adjT
    unfold localSourceMap
    infer_instance
  have hFamily : IsIso (localFamilyMap A N hN hA hS d g s hs c adjL) := by
    have := isIso_sectionMap A (Scheme.Hom.deformationSpaceProj g s) d
      (Scheme.Hom.deformationSpaceProj (pullback.snd g c.b)
        (Scheme.Hom.baseChangeSection g s hs c.b))
      (AffineSpace.map (ULift.{u} (Fin 1)) c.b) c.reesBase Chart.Geometry.baseSquare
      s.deformationSpaceSection (Scheme.Hom.baseChangeSection g s hs c.b).deformationSpaceSection
      Chart.Geometry.baseSections
    have := isIso_chartMap A N hN hA hL d
      (Scheme.Hom.deformationSpaceProj (c.j ≫ pullback.snd g c.b) c.r)
      c.r.deformationSpaceSection c.reesCoordinates Chart.Geometry.coordinatesOver adjL
    unfold localFamilyMap
    infer_instance
  have : IsIso (restrictedTheta A g s hs c.b) := by
    unfold restrictedTheta
    infer_instance
  refine ⟨adjT, adjL, asIso (localSourceMap A N hN hA hS d g s hs c adjT),
    asIso (localFamilyMap A N hN hA hS d g s hs c adjL), rfl, rfl,
    asIso (restrictedTheta A g s hs c.b), rfl, ?_⟩
  exact restriction_normalized A c.T _ _

end AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
