/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernLocalFactorization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernHorizontalRealization
public import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstScalarTrace
public import WeilConjectures.AlgebraicGeometry.RationalP1.FlatCoefficientExchange
public import WeilConjectures.AlgebraicGeometry.RationalP1.FlatCoefficientPullbackCube

/-! # Pullback of the local scalar Chern classes

Source: geometric tower classes (2), and diagonal coefficient changes (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

private theorem transport_inverse_local_square
    (DA : A ⥤ A') (DB : B ⥤ B') (DC : C ⥤ C')
    (F : A ⥤ B) (G H : B ⥤ C) (F' : A' ⥤ B') (G' H' : B' ⥤ C')
    (alphaF : F ⋙ DB ⟶ DA ⋙ F') (alphaG : G ⋙ DC ⟶ DB ⋙ G')
    (alphaH : H ⋙ DC ⟶ DB ⋙ H') [IsIso alphaF] [IsIso alphaG]
    (theta : F ⋙ G ≅ F ⋙ H) (theta' : F' ⋙ G' ≅ F' ⋙ H')
    {U : A} {V L : B} {W N : C} {U' : A'} {V' L' : B'} {W' N' : C'}
    (eU : DA.obj U ≅ U') (eV : DB.obj V ≅ V') (eW : DC.obj W ≅ W')
    (eL : DB.obj L ⟶ L') (eN : DC.obj N ⟶ N')
    (u : F.obj U ⟶ V) (v : G.obj V ⟶ W) (lam : H.obj L ⟶ N)
    (u' : F'.obj U' ⟶ V') (v' : G'.obj V' ⟶ W') (lam' : H'.obj L' ⟶ N')
    (z : V ⟶ L) (w : W ⟶ N)
    (hc : DC.map (theta.hom.app U) ≫ alphaH.app (F.obj U) ≫
        H'.map (alphaF.app U) = alphaG.app (F.obj U) ≫
        G'.map (alphaF.app U) ≫ theta'.hom.app (DA.obj U))
    (hu : alphaF.app U ≫ F'.map eU.hom ≫ u' = DB.map u ≫ eV.hom)
    (hv : alphaG.app V ≫ G'.map eV.hom ≫ v' = DC.map v ≫ eW.hom)
    (hl : alphaH.app L ≫ H'.map eL ≫ lam' = DC.map lam ≫ eN)
    (h : theta.hom.app U ≫ H.map (u ≫ z) ≫ lam = G.map u ≫ v ≫ w) :
    theta'.hom.app U' ≫ H'.map (u' ≫ eV.inv ≫ DB.map z ≫ eL) ≫ lam' =
      G'.map u' ≫ v' ≫ eW.inv ≫ DC.map w ≫ eN := by
  have huz : alphaF.app U ≫ F'.map eU.hom ≫
        (u' ≫ eV.inv ≫ DB.map z ≫ eL) = DB.map (u ≫ z) ≫ eL := by
    rw [reassoc_of% hu]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  have hum : H'.map (alphaF.app U) ≫ H'.map (F'.map eU.hom) ≫
        H'.map (u' ≫ eV.inv ≫ DB.map z ≫ eL) =
      H'.map (DB.map (u ≫ z)) ≫ H'.map eL := by
    simpa only [Functor.map_comp, Category.assoc] using congrArg H'.map huz
  apply (cancel_epi (alphaG.app (F.obj U) ≫
    G'.map (alphaF.app U) ≫ G'.map (F'.map eU.hom))).1
  simp only [Category.assoc]
  have ht := theta'.hom.naturality eU.hom
  dsimp only [Functor.comp_map] at ht
  rw [reassoc_of% ht, ← reassoc_of% hc, reassoc_of% hum]
  have hn := alphaH.naturality (u ≫ z)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, hl]
  rw [← DC.map_comp_assoc, ← DC.map_comp_assoc, Category.assoc, h]
  simp only [Functor.map_comp, Category.assoc]
  have hmu := congrArg G'.map hu
  simp only [Functor.map_comp, Category.assoc] at hmu
  rw [reassoc_of% hmu]
  have hnu := alphaG.naturality u
  dsimp only [Functor.comp_map] at hnu
  rw [← reassoc_of% hnu, reassoc_of% hv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem change_local_endpoints
    (G H : B ⥤ C) {A V L : B} {W N : C}
    (theta theta' : G.obj A ⟶ H.obj A)
    (u u' : A ⟶ V) (v v' : G.obj V ⟶ W) (lam lam' : H.obj L ⟶ N)
    (z z' : V ⟶ L) (w w' : W ⟶ N)
    (htheta : theta = theta') (hu : u = u') (hv : v = v')
    (hl : lam = lam') (hz : z = z') (hw : w = w')
    (h : theta ≫ H.map (u ≫ z) ≫ lam = G.map u ≫ v ≫ w) :
    theta' ≫ H.map (u' ≫ z') ≫ lam' = G.map u' ≫ v' ≫ w' := by
  cases htheta
  cases hu
  cases hv
  cases hl
  cases hz
  cases hw
  exact h

private theorem flat_scalar_local_square
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    (Y : Scheme.{u})
    (eY : Endpoint a (Mod.regular (condensedRingObj R Y))
      (Mod.regular (condensedRingObj T Y)) (coefficientMap a Y))
    (eP : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y)))
    (eW : Endpoint a (Mod.regular (condensedRingObj R (diagonalSurface Y)))
      (Mod.regular (condensedRingObj T (diagonalSurface Y)))
      (coefficientMap a (diagonalSurface Y)))
    {MP : Modules R (ProjectiveLine Y)} {MW : Modules R (diagonalSurface Y)}
    {NP : Modules T (ProjectiveLine Y)} {NW : Modules T (diagonalSurface Y)}
    {mP : MP.X ⟶ NP.X} {mW : MW.X ⟶ NW.X}
    (eLP : Endpoint a MP NP mP) (eLW : Endpoint a MW NW mW)
    {r₀ : (upperStar Ab.{u + 1} (firstProjection Y)).obj MP.X ⟶ MW.X}
    {r₁ : (upperStar Ab.{u + 1} (firstProjection Y)).obj NP.X ⟶ NW.X}
    (lineR : PullEndpoint R (firstProjection Y) MP MW r₀)
    (lineT : PullEndpoint T (firstProjection Y) NP NW r₁)
    (hr : (upperStar Ab.{u + 1} (firstProjection Y)).map mP ≫ r₁ = r₀ ≫ mW)
    (z : unit R (ProjectiveLine Y) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj MP) ⟦(2 : ℤ)⟧)
    (w : unit R (diagonalSurface Y) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj MW) ⟦(2 : ℤ)⟧)
    (h : (condensedAmbientPullbackComparison R (square Y)).hom.app (unit R Y) ≫
      (moduleObjectDerivedPullback R (firstProjection Y)).map
        ((nativeUnitPullEndpoint R (ProjectiveLine Y ↘ Y)).derived ≫ z) ≫ lineR.shift =
      (moduleObjectDerivedPullback R (secondProjection Y)).map
        (nativeUnitPullEndpoint R (ProjectiveLine Y ↘ Y)).derived ≫
      (nativeUnitPullEndpoint R (secondProjection Y)).derived ≫ w) :
    (condensedAmbientPullbackComparison T (square Y)).hom.app (unit T Y) ≫
      (moduleObjectDerivedPullback T (firstProjection Y)).map
        ((nativeUnitPullEndpoint T (ProjectiveLine Y ↘ Y)).derived ≫
          extendLocalChern a _ eP eLP z) ≫ lineT.shift =
      (moduleObjectDerivedPullback T (secondProjection Y)).map
        (nativeUnitPullEndpoint T (ProjectiveLine Y ↘ Y)).derived ≫
      (nativeUnitPullEndpoint T (secondProjection Y)).derived ≫
        extendLocalChern a _ eW eLW w := by
  have hu := endpoint_pull_square a (ProjectiveLine Y ↘ Y) eY eP
    (nativeUnitPullEndpoint R _) (nativeUnitPullEndpoint T _)
    (map_coefficientMap_comp_condensedPullbackHom a (ProjectiveLine Y ↘ Y))
  have hv := endpoint_pull_square a (secondProjection Y) eP eW
    (nativeUnitPullEndpoint R _) (nativeUnitPullEndpoint T _)
    (map_coefficientMap_comp_condensedPullbackHom a (secondProjection Y))
  have hl := endpoint_pull_square_shift a (firstProjection Y) eLP eLW lineR lineT hr
  unfold PullEndpointSquare at hl
  have hc := flat_coefficient_pullback_cube a (square Y) (unit R Y)
  unfold Adjunction.coefficientPullbackSquare at hc
  unfold extendLocalChern
  have ht := transport_inverse_local_square (derivedScalars a Y)
    (derivedScalars a (ProjectiveLine Y)) (derivedScalars a (diagonalSurface Y))
    (moduleObjectDerivedPullback R (ProjectiveLine Y ↘ Y))
    (moduleObjectDerivedPullback R (secondProjection Y))
    (moduleObjectDerivedPullback R (firstProjection Y))
    (moduleObjectDerivedPullback T (ProjectiveLine Y ↘ Y))
    (moduleObjectDerivedPullback T (secondProjection Y))
    (moduleObjectDerivedPullback T (firstProjection Y))
    (derivedPullIso a (ProjectiveLine Y ↘ Y)).hom
    (derivedPullIso a (secondProjection Y)).hom (derivedPullIso a (firstProjection Y)).hom
    (condensedAmbientPullbackComparison R (square Y))
    (condensedAmbientPullbackComparison T (square Y))
    eY.iso eP.iso eW.iso (eLP.shift a) (eLW.shift a)
    (nativeUnitPullEndpoint R (ProjectiveLine Y ↘ Y)).derived
    (nativeUnitPullEndpoint R (secondProjection Y)).derived lineR.shift
    (nativeUnitPullEndpoint T (ProjectiveLine Y ↘ Y)).derived
    (nativeUnitPullEndpoint T (secondProjection Y)).derived lineT.shift z w
    (by coefficient_finish hc) (by coefficient_finish hu) (by coefficient_finish hv)
    (by coefficient_finish hl) (by coefficient_finish h)
  coefficient_finish ht

private theorem p2_unit_endpoint
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (Y : Scheme.{u}) :
    (nativeUnitPullEndpoint R (secondProjection Y)).derived =
      (scalarP2UnitIso R Y).hom := by
  unfold PullEndpoint.derived nativeUnitPullEndpoint
  dsimp only [Iso.symm_hom]
  erw [singlePullback_unit]
  unfold scalarP2UnitIso
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  erw [singleUnitIso_hom, singleUnitIso_inv]
  erw [(moduleObjectDerivedPullback R (secondProjection Y)).map_id (unit R (ProjectiveLine Y))]
  erw [Category.id_comp, Category.comp_id]
  unfold moduleObjectDerivedPullback
  rfl

private theorem native_square_publish
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (Y : Scheme.{u})
    {M : Modules R (ProjectiveLine Y)} {N : Modules R (diagonalSurface Y)}
    (lam lam' : (moduleObjectDerivedPullback R (firstProjection Y)).obj
      (((DerivedCategory.singleFunctor _ 0).obj M) ⟦(2 : ℤ)⟧) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj N) ⟦(2 : ℤ)⟧)
    (z z' : unit R (ProjectiveLine Y) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj M) ⟦(2 : ℤ)⟧)
    (w w' : unit R (diagonalSurface Y) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj N) ⟦(2 : ℤ)⟧)
    (hl : lam = lam') (hz : z = z') (hw : w = w')
    (h : (condensedAmbientPullbackComparison R (square Y)).hom.app (unit R Y) ≫
      (moduleObjectDerivedPullback R (firstProjection Y)).map
        ((nativeUnitPullEndpoint R (ProjectiveLine Y ↘ Y)).derived ≫ z) ≫ lam =
      (moduleObjectDerivedPullback R (secondProjection Y)).map
        (nativeUnitPullEndpoint R (ProjectiveLine Y ↘ Y)).derived ≫
      (nativeUnitPullEndpoint R (secondProjection Y)).derived ≫ w) :
    (ambientPullbackComparison R (square Y)).hom.app (unit R Y) ≫
      (moduleObjectDerivedPullback R (firstProjection Y)).map
        ((scalarUnitPullIso R Y).hom ≫ z') ≫ lam' =
      (moduleObjectDerivedPullback R (secondProjection Y)).map
        (scalarUnitPullIso R Y).hom ≫ (scalarP2UnitIso R Y).hom ≫ w' := by
  have htheta : (condensedAmbientPullbackComparison R (square Y)).hom.app (unit R Y) =
      (ambientPullbackComparison R (square Y)).hom.app (unit R Y) := by
    unfold ambientPullbackComparison
    coefficient_congr
  have hu := unitPullEndpoint_eq R Y (nativeUnitPullEndpoint R (ProjectiveLine Y ↘ Y))
  have hv := p2_unit_endpoint R Y
  have hh := change_local_endpoints
    (moduleObjectDerivedPullback R (secondProjection Y))
    (moduleObjectDerivedPullback R (firstProjection Y))
    (A := (moduleObjectDerivedPullback R (ProjectiveLine Y ↘ Y)).obj (unit R Y))
    (V := unit R (ProjectiveLine Y))
    (L := ((DerivedCategory.singleFunctor _ 0).obj M) ⟦(2 : ℤ)⟧)
    (W := unit R (diagonalSurface Y))
    (N := ((DerivedCategory.singleFunctor _ 0).obj N) ⟦(2 : ℤ)⟧)
    ((condensedAmbientPullbackComparison R (square Y)).hom.app (unit R Y))
    ((ambientPullbackComparison R (square Y)).hom.app (unit R Y))
    (nativeUnitPullEndpoint R (ProjectiveLine Y ↘ Y)).derived (scalarUnitPullIso R Y).hom
    (nativeUnitPullEndpoint R (secondProjection Y)).derived (scalarP2UnitIso R Y).hom
    lam lam' z z' w w' htheta hu hv hl hz hw h
  coefficient_finish hh

/-- Pulling the local section class along p1 gives the section class of p2.
This is an equation of local classes on the product; it has no direct images,
exchange mate, completed Chern adjuncts, traces, or splitting maps.

Source: geometric tower classes (2), Chern pullback; diagonal coefficient changes
(1), whole-system unit and root comparisons; rational P1 second triangle.
(blueprint: lem-sfb-rational-p1-scalar-local-chern-pullback).

Proof: q_model identifies the q model bundle with O(1). The factor-swapped product
model p2_model identifies its bundle with p1*O(1), by the base-change identification
of the tautological invertible module. Apply tower_firstChern_pullback to that
bundle, using the coefficient-one and root-normalized comparisons. Its proof uses
the pullback square for the integral line-bundle extension and the positive
Kummer boundary, so it is an equality of entire systems. Apply constant-scalar
restriction and the inverse-image/derived-limit comparison. The unit and root
limit comparisons make that comparison invertible on these endpoints; naturality
and the two CompletedLocalChernNormalized equations give the local completed
square. Transport it through eP and eW. Their underlying-sheaf normalizations
identify the ordinary inverse-image comparisons; their unit projections and root
projections identify the two endpoints. Apply scalar extension Z_l -> O_E -> E
to this local square. Scalar/inverse-image composition is fixed on the units by
one and on the Tate lines by the balanced tensor root map, so the endpoint
normalizations identify the result with scalarQLocalChern and scalarP2LocalChern.
The coefficient-unit composition law around the self-square identifies the source
comparison with the displayed ambientPullbackComparison followed by the q unit
comparison; its other side is the p2 pullback of the q unit comparison followed by
the p2 unit comparison. The target comparison is firstLineComparisonForTrace by
its root normalization, with the canonical degree-two shift. This gives the
displayed equation. This uses no faithfulness of finite-level evaluation, and
works on the empty scheme and for arbitrary base changes. -/
theorem scalar_local_chern_pullback
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧)
    (hz : CompletedLocalChernNormalized l r.tq.toPresentation z)
    (w : DiagonalTrace.completedUnit l (diagonalSurface Y) ⟶
      (DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧)
    (hw : CompletedLocalChernNormalized l r.t₂.toPresentation w) :
    let Λ := (coefficient l (some E)).X
    (ambientPullbackComparison Λ (square Y)).hom.app (unit Λ Y) ≫
        (moduleObjectDerivedPullback Λ (firstProjection Y)).map
          ((scalarUnitPullIso Λ Y).hom ≫ scalarQLocalChern l E Y r z) ≫
        (firstLineComparisonForTrace l (some E) k p hpl Y).hom =
      (moduleObjectDerivedPullback Λ (secondProjection Y)).map
          (scalarUnitPullIso Λ Y).hom ≫
        (scalarP2UnitIso Λ Y).hom ≫ scalarP2LocalChern l E Y r w := by
  classical
  let : ∀ x : Y, Invertible (l : Y.residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _ (Y ↘ Spec (.of k)) x).invertible
  let : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  let : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  have hY : IsUnit (l : Γ(Y, ⊤)) := by
    have hl : IsUnit (l : k) :=
      (CharP.isUnit_natCast_iff (Fact.out : p.Prime)).2
        (fun h ↦ hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
          (Fact.out : l.Prime)).1 h))
    simpa only [map_natCast] using
      hl.map ((Y ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hgeo : (diagonalTraceSecondModel Y).hom ≫
      ProjectiveSpace.map (ULift.{u} (Fin 2)) (ProjectiveLine Y ↘ Y) =
      firstProjection Y := by
    simp only [diagonalTraceSecondModel, diagonalTraceFirstModel, Iso.trans_hom,
      Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_snd,
      pullbackSymmetry_hom_comp_snd]
    rfl
  have hj : Scheme.Pic.map
      (ProjectiveSpace.map (ULift.{u} (Fin 2)) (ProjectiveLine Y ↘ Y))
      (SpTowerClasses.hyperplanePic Y) =
      SpTowerClasses.hyperplanePic (ProjectiveLine Y) := by
    change Scheme.Pic.map _ (Scheme.Pic.ofIsInvertible _) = Scheme.Pic.ofIsInvertible _
    have hm {X S : Scheme.{u}} (f : X ⟶ S)
        (L : S.Modules) [Scheme.Modules.IsInvertible L] :
        Scheme.Pic.map f (Scheme.Pic.ofIsInvertible L) =
          Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L) := by
      apply (Scheme.Pic.eq_ofIsInvertible_iff _ _).2
      exact ⟨fromSkeletonToSkeletonIso _ ≪≫
        (Scheme.Modules.pullback f).mapIso (Scheme.Pic.ofIsInvertibleIso L)⟩
    rw [hm]
    exact Scheme.Pic.ofIsInvertible_eq_of_iso
      (ProjectiveSpace.pullbackMapTwistIso (ULift.{u} (Fin 2)) (ProjectiveLine Y ↘ Y) 1)
  have hpic : Scheme.Pic.map (firstProjection Y)
      (Scheme.Pic.map r.tq.model.model.hom (SpTowerClasses.hyperplanePic Y)) =
      Scheme.Pic.map r.t₂.model.model.hom
        (SpTowerClasses.hyperplanePic (ProjectiveLine Y)) := by
    rw [r.q_model, r.p₂_model, Iso.refl_hom, Scheme.Pic.map_id, ← hgeo,
      Scheme.Pic.map_comp, hj]
  obtain ⟨lineR⟩ := zlPullEndpoint_nonempty l (firstProjection Y)
  let lineI := integralPullEndpoint l E (firstProjection Y)
  let lineE := nativeRationalEndpoint l E (firstProjection Y)
  have hz' : ModelLocalChernNormalized l r.tq.toPresentation z := by
    simpa only [ModelLocalChernNormalized, CompletedLocalChernNormalized,
      Scheme.Pic.mapHom_apply] using hz
  have hR := diagonalLocalChern_horizontal_realization l
    (ProjectiveLine Y ↘ Y) (secondProjection Y) (firstProjection Y)
    (ProjectiveLine Y ↘ Y) (square Y).toCommSq.w.symm hY hP
    r.tq.toPresentation r.t₂.toPresentation r.eP r.eW
    (nativeUnitPullEndpoint _ _) (nativeUnitPullEndpoint _ _) lineR
    (nativeUnitPullEndpoint _ _) z w hz' (by
      simpa only [CompletedLocalChernNormalized, Scheme.Pic.mapHom_apply, hpic] using hw)
  have hR' : (condensedAmbientPullbackComparison _ (square Y)).hom.app
      (unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y) ≫
      (moduleObjectDerivedPullback _ (firstProjection Y)).map
        ((nativeUnitPullEndpoint _ (ProjectiveLine Y ↘ Y)).derived ≫
          realizeLocalChern l _ r.eP z) ≫ lineR.shift =
      (moduleObjectDerivedPullback _ (secondProjection Y)).map
        (nativeUnitPullEndpoint _ (ProjectiveLine Y ↘ Y)).derived ≫
      (nativeUnitPullEndpoint _ (secondProjection Y)).derived ≫
        realizeLocalChern l _ r.eW w := by
    have hh := hR
    simp only [derivedCongr_eq, condensedAmbientPullbackComparison,
      moduleObjectDerivedPullback, derivedUpper, id_eq, Category.assoc,
      CompletedRealization.localChern, realizeLocalChern] at hh ⊢
    coefficient_finish hh
  let : ∀ S : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralMap l E) S)) :=
    (integralScalarComparison_isIso l E (ProjectiveLine Y ↘ Y)).choose
  have hI := flat_scalar_local_square (integralMap l E) Y
    ((family.toIntegral E).units Y)
    ((family.toIntegral E).units (ProjectiveLine Y))
    ((family.toIntegral E).units (diagonalSurface Y))
    (family.toIntegral E).lineP (family.toIntegral E).lineW lineR lineI
    ((adicComparison l (firstProjection Y)).integral_inclusion (bottomField l) E (by
      change (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≤ E.1
      exact bot_le))
    (realizeLocalChern l _ r.eP z) (realizeLocalChern l _ r.eW w) hR'
  let : ∀ S : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars
        (coefficientMap (padicIntegersRingObjToContinuousMapRingObj l E) S)) :=
    fun S ↦ preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield l E S
  let zI := extendLocalChern (integralMap l E) (ProjectiveLine Y)
    ((family.toIntegral E).units (ProjectiveLine Y)) (family.toIntegral E).lineP
    (realizeLocalChern l (ProjectiveLine Y) r.eP z)
  let wI := extendLocalChern (integralMap l E) (diagonalSurface Y)
    ((family.toIntegral E).units (diagonalSurface Y)) (family.toIntegral E).lineW
    (realizeLocalChern l (diagonalSurface Y) r.eW w)
  have hE := flat_scalar_local_square (padicIntegersRingObjToContinuousMapRingObj l E) Y
    ((family.toRational E).units Y)
    ((family.toRational E).units (ProjectiveLine Y))
    ((family.toRational E).units (diagonalSurface Y))
    (family.toRational E).lineP (family.toRational E).lineW lineI lineE
    (rational_root_scalar_square l E (firstProjection Y))
    zI wI hI
  have hline : lineE.shift = (firstLineComparisonForTrace l (some E) k p hpl Y).hom := by
    unfold firstLineComparisonForTrace
    dsimp only [lineE, nativeRationalEndpoint]
    exact rationalPullEndpoint_shift l E (firstProjection Y)
  have hzE : extendLocalChern (padicIntegersRingObjToContinuousMapRingObj l E)
      (ProjectiveLine Y) ((family.toRational E).units (ProjectiveLine Y))
      (family.toRational E).lineP zI = scalarQLocalChern l E Y r z := by
    unfold scalarQLocalChern
    coefficient_congr
  have hwE : extendLocalChern (padicIntegersRingObjToContinuousMapRingObj l E)
      (diagonalSurface Y) ((family.toRational E).units (diagonalSurface Y))
      (family.toRational E).lineW wI = scalarP2LocalChern l E Y r w := by
    unfold scalarP2LocalChern
    coefficient_congr
  have hE' := native_square_publish (Profinite.continuousMapRingObj.{u} E.1) Y
    (M := spRationalTwist (ProjectiveLine Y) l E)
    (N := spRationalTwist (diagonalSurface Y) l E)
    _ _ _ _ _ _ hline hzE hwE (by coefficient_finish hE)
  coefficient_finish hE'

end AlgebraicGeometry.ProEtale.RationalP1
