/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceLimit
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullback
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback

import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedPullbackCompatibility
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedClassPullback
import all WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstScalarTrace
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteScalarSquares
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarExchangeCube
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarClosedSourceExchange
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedPullbackScalarNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate

/-!
# Base change of the diagonal coefficient families

Let `g : Y' ⟶ Y`. We show that the members of two diagonal coefficient families on `Y` and `Y'`
are compatible with base change along `g` (`PullbackCompatibility`), stage by stage: first the
`ℤ_ℓ`-members built from derived limits of the Cartier–Kummer systems, then the `𝒪_E`-, `E`- and
`ℚ̄_ℓ`-members, through the flat changes of coefficients `ℤ_ℓ ⟶ 𝒪_E ⟶ E` and `ℚ_ℓ ⟶ ℚ̄_ℓ`.

## Main statements

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.nonempty_pullbackCompatibility_zl`
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.nonempty_pullbackCompatibility_integral`
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.nonempty_pullbackCompatibility_rational`
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.nonempty_pullbackCompatibility_closure`

## Implementation details

A pullback compatibility for a flat change of coefficients `a : R ⟶ T` is transported from the
`R`-family to the `T`-family (`scalarPullbackCompatibility`): the scalar mate of the
restriction/pullback commutation is the comparison `CondensedRing.derivedPullIso`, the endpoint
squares come from the naturality of the lines, and the class and trace squares are pasted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable {l : ℕ} [Fact l.Prime]

section PullbackCompatibility

attribute [local instance] completedRealization_shiftedLine_isIso

/-- The three commutative squares of the base change of `ℙ¹_Y ×_Y ℙ¹_Y` along `g`. -/
private theorem diagonalBaseSquares {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) : BaseSquares g where
  diagonal_square := by
    apply pullback.hom_ext <;>
      simp [diagonalImmersion, baseW, Category.assoc]
  first_square := by
    simp [baseW]
  second_square := by
    simp [baseW]

private theorem firstProjection_isPullback {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    IsPullback (baseW g)
      (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) (baseP g) :=
  IsPullback.paste_twist_right
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g)
    (IsPullback.of_hasPullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)).flip
    (ProjectiveLine Y' ↘ Y') (baseP g)
    (ProjectiveSpace.map_over (ULift.{u} (Fin 2)) g).symm
    (pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (IsPullback.of_hasPullback (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y')).flip
    (by simp [baseW, baseP]) (by simp [baseW, baseP])

private theorem secondProjection_isPullback {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    IsPullback (baseW g)
      (pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) (baseP g) :=
  IsPullback.paste_twist_right
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g)
    (IsPullback.of_hasPullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (ProjectiveLine Y' ↘ Y') (baseP g)
    (ProjectiveSpace.map_over (ULift.{u} (Fin 2)) g).symm
    (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (IsPullback.of_hasPullback (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (by simp [baseW, baseP]) (by simp [baseW, baseP])

/-- The `ℤ_ℓ`-members of two families built from derived limits `δ, δ'` of the Cartier–Kummer
systems (recorded by `Reference`) are compatible with base change along `g`. -/
theorem nonempty_pullbackCompatibility_zl {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [IsNoetherian Y'] [IsNoetherian (ProjectiveLine Y')] [IsNoetherian (diagonalSurface Y')]
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    [DiagonalTraceLocalizations l Y] [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)] [DiagonalTraceLocalizations l Y']
    [DiagonalTraceLocalizations l (ProjectiveLine Y')]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (δ' : diagonalCompletedDomain l Y' ⟶ diagonalCompletedCodomain l Y')
    (hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (hδ' : DiagonalTrace.IsDiagonalLimit l Y' hY' D' δ')
    {family : Family l Y} {family' : Family l Y'}
    (reference : Reference l Y δ family) (reference' : Reference l Y' δ' family') :
    Nonempty (PullbackCompatibility (Profinite.continuousMapRingObj.{u} ℤ_[l]) g
      (zlLine l) family.zl family'.zl
      (spIntegralComparison (baseP g) l (bottomField l))
      (spIntegralComparison (baseW g) l (bottomField l))) := by
  obtain ⟨data, hclass⟩ := diagonalCompletedClass_pullback l Y Y' g (diagonalBaseSquares g)
    hY hY' D D' δ δ' hδ hδ' reference.eP reference.eW reference'.eP reference'.eW
    reference.sourceIso reference'.sourceIso
    reference.source_normalization reference'.source_normalization
  rw [reference.delta, reference'.delta] at hclass
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hP' : IsUnit (l : Γ(ProjectiveLine Y', ⊤)) := by
    simpa only [map_natCast] using hY'.map (ProjectiveLine Y' ↘ Y').appTop.hom
  refine ⟨{ sourceData := data, delta := hclass, traceq := ?_, trace₁ := ?_, trace₂ := ?_ }⟩
  · exact tracePullback_of_realized l
      (ProjectiveLine Y ↘ Y) (ProjectiveLine Y' ↘ Y') (baseP g) g
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g) hY hY'
      reference.eP reference.eY reference'.eP reference'.eY
      reference.tq reference'.tq family.zl.Rq family'.zl.Rq
      family.zl.q_canonical family'.zl.q_canonical family.zl.q_unit family'.zl.q_unit
      reference.q_square reference'.q_square data.endpoints.lineP data.endpoints.cY
      _ _ reference.q_trace reference'.q_trace
  · exact tracePullback_of_realized l
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
      (baseW g) (baseP g) (firstProjection_isPullback g) hP hP'
      reference.eW reference.eP reference'.eW reference'.eP
      reference.t₁ reference'.t₁ family.zl.R₁ family'.zl.R₁
      family.zl.p₁_canonical family'.zl.p₁_canonical family.zl.p₁_unit family'.zl.p₁_unit
      reference.p₁_square reference'.p₁_square data.endpoints.lineW data.endpoints.cP
      _ _ reference.p₁_trace reference'.p₁_trace
  · exact tracePullback_of_realized l
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      (pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
      (baseW g) (baseP g) (secondProjection_isPullback g) hP hP'
      reference.eW reference.eP reference'.eW reference'.eP
      reference.t₂ reference'.t₂ family.zl.R₂ family'.zl.R₂
      family.zl.p₂_canonical family'.zl.p₂_canonical family.zl.p₂_unit family'.zl.p₂_unit
      reference.p₂_square reference'.p₂_square data.endpoints.lineW data.endpoints.cP
      _ _ reference.p₂_trace reference'.p₂_trace

end PullbackCompatibility

section ScalarPullback

attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures
attribute [local instance 20000] ProEtale.sheafBraidedCategory ProEtale.sheafMonoidalCategory

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.upperStarLowerStarAdjunction
  ProEtale.upperStar ProEtale.lowerStar ProEtale.upperStarLowerStarAdjunction
  ProEtale.upperStarComp

/-- For a flat change of coefficients `a`, the scalar mate `scalarPullbackComparison` of the
restriction/pullback commutation is the comparison `CondensedRing.derivedPullIso`. -/
private theorem scalarPullbackComparison_eq_derivedPullIso
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    scalarPullbackComparison a f = (CondensedRing.derivedPullIso a f).hom := by
  have h := CondensedRing.mateEquiv_derivedPullIso_hom a f
  have he : (CondensedRing.derivedComapLeftDerivedUpperStarIso a f).hom =
      (scalarRestrictionPullbackIso a f).inv := by
    simp only [CondensedRing.derivedComapLeftDerivedUpperStarIso,
      scalarRestrictionPullbackIso, CondensedRing.derivedComapUpperStarIso,
      CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
      Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.mapDerivedCategoryNatIso_symm,
      Category.assoc]
  rw [he] at h
  let e := mateEquiv (G := derivedUpper R f) (H := derivedUpper T f)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
  exact (e.symm_apply_eq).mpr h.symm


private theorem scalar_endpoint_square
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules R S} {N : Modules R X} {M' : Modules T S} {N' : Modules T X}
    {v : M.X ⟶ M'.X} {v' : N.X ⟶ N'.X}
    {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    {m' : (upperStar Ab.{u + 1} f).obj M'.X ⟶ N'.X}
    (p : PullEndpoint R f M N m) (e : Endpoint a M M' v)
    (e' : Endpoint a N N' v') (p' : PullEndpoint T f M' N' m')
    (h : (upperStar Ab.{u + 1} f).map v ≫ m' = m ≫ v') :
    (scalarPullbackComparison a f).app
        (((DerivedCategory.singleFunctor (Modules R S) 0).obj M)⟦(2 : ℤ)⟧) ≫
      (derivedUpper T f).map (e.shift a) ≫ p'.shift =
    (derivedScalars a X).map p.shift ≫ e'.shift a := by
  rw [scalarPullbackComparison_eq_derivedPullIso]
  exact RationalP1.endpoint_pull_square_shift a f e e' p p' h

private theorem scalar_unit_square
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eS : Endpoint a (Mod.regular (condensedRingObj R S))
      (Mod.regular (condensedRingObj T S)) (coefficientMap a S))
    (eX : Endpoint a (Mod.regular (condensedRingObj R X))
      (Mod.regular (condensedRingObj T X)) (coefficientMap a X))
    (p₀ : UnitPullEndpoint R f) (p : UnitPullEndpoint T f) :
    (scalarPullbackComparison a f).app (unit R S) ≫
        (derivedUpper T f).map eS.iso.hom ≫ p.derived =
      (derivedScalars a X).map p₀.derived ≫ eX.iso.hom := by
  rw [scalarPullbackComparison_eq_derivedPullIso]
  exact RationalP1.endpoint_pull_square a f eS eX p₀ p
    (map_coefficientMap_comp_condensedPullbackHom a f)

private def canonicalPullbackEndpoints
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (L : ∀ X : Scheme.{u}, Modules R X)
    {mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X}
    {mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X}
    (p : PullEndpoint R (baseP g) (L (ProjectiveLine Y)) (L (ProjectiveLine Y')) mP)
    (w : PullEndpoint R (baseW g) (L (diagonalSurface Y)) (L (diagonalSurface Y')) mW) :
    PullbackEndpoints R g L mP mW :=
  ⟨RationalP1.nativeUnitPullEndpoint R g, RationalP1.nativeUnitPullEndpoint R (baseP g), p, w⟩

private def canonicalSourcePullback
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    (L : ∀ X : Scheme.{u}, Modules R X)
    {mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X}
    {mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X}
    (p : PullEndpoint R (baseP g) (L (ProjectiveLine Y)) (L (ProjectiveLine Y')) mP)
    (w : PullEndpoint R (baseW g) (L (diagonalSurface Y)) (L (diagonalSurface Y')) mW) :
    SourcePullback R g L mP mW :=
  letI := diagonalScalar_source_map_isIso R g (diagonalBaseSquares g)
    (canonicalPullbackEndpoints R g L p w).cP
  { geometry := diagonalBaseSquares g
    endpoints := canonicalPullbackEndpoints R g L p w
    supported := asIso (sourcePullbackMap R g (diagonalBaseSquares g).diagonal_square
      (canonicalPullbackEndpoints R g L p w).cP)
    supported_normalization := rfl }

attribute [local irreducible] canonicalSourcePullback

private theorem scalar_pullback_paste
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (U : A ⥤ B) (V : C ⥤ D) (T : A ⥤ C) (S : B ⥤ D)
    (χ : U ⋙ S ⟶ T ⋙ V)
    {A₀ A₁ : A} {B₀ B₁ : B} {C₀ C₁ : C} {D₀ D₁ : D}
    (δ₀ : A₀ ⟶ A₁) (δ₀' : B₀ ⟶ B₁) (δ : C₀ ⟶ C₁) (δ' : D₀ ⟶ D₁)
    (i : U.obj A₀ ≅ B₀) (j : U.obj A₁ ⟶ B₁)
    (e : T.obj A₀ ≅ C₀) (f : T.obj A₁ ⟶ C₁)
    (e' : S.obj B₀ ≅ D₀) (f' : S.obj B₁ ⟶ D₁)
    (k : V.obj C₀ ≅ D₀) (t : V.obj C₁ ⟶ D₁)
    (hi : U.map δ₀ ≫ j = i.hom ≫ δ₀')
    (he : T.map δ₀ ≫ f = e.hom ≫ δ)
    (he' : S.map δ₀' ≫ f' = e'.hom ≫ δ')
    (hs : χ.app A₀ ≫ V.map e.hom ≫ k.hom = S.map i.hom ≫ e'.hom)
    (hl : χ.app A₁ ≫ V.map f ≫ t = S.map j ≫ f') :
    V.map δ ≫ t = k.hom ≫ δ' := by
  have hh : IsIso ((χ.app A₀ ≫ V.map e.hom) ≫ k.hom) := by
    rw [Category.assoc, hs]
    infer_instance
  have : IsIso (χ.app A₀ ≫ V.map e.hom) := IsIso.of_isIso_comp_right _ k.hom
  apply (cancel_epi (χ.app A₀ ≫ V.map e.hom)).mp
  calc
    (χ.app A₀ ≫ V.map e.hom) ≫ (V.map δ ≫ t) =
        χ.app A₀ ≫ V.map (T.map δ₀) ≫ V.map f ≫ t := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ χ.app A₀ ≫ V.map z ≫ t) he.symm
    _ = S.map (U.map δ₀) ≫ χ.app A₁ ≫ V.map f ≫ t := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (· ≫ V.map f ≫ t) (χ.naturality δ₀).symm
    _ = S.map (U.map δ₀) ≫ S.map j ≫ f' := by rw [hl]
    _ = S.map i.hom ≫ S.map δ₀' ≫ f' := by
      rw [← S.map_comp_assoc, hi, S.map_comp, Category.assoc]
    _ = S.map i.hom ≫ e'.hom ≫ δ' := by rw [he']
    _ = (χ.app A₀ ≫ V.map e.hom) ≫ (k.hom ≫ δ') := by
      simpa only [Category.assoc] using congrArg (· ≫ δ') hs.symm

private theorem trace_scalar_paste
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (U : A ⥤ B) (V : C ⥤ D) (T : A ⥤ C) (S : B ⥤ D)
    (χ : U ⋙ S ⟶ T ⋙ V)
    {A₀ A₁ : A} {B₀ B₁ : B} {C₀ C₁ : C} {D₀ D₁ : D}
    (t₀ : A₀ ⟶ A₁) (t₀' : B₀ ⟶ B₁) (t : C₀ ⟶ C₁) (t' : D₀ ⟶ D₁)
    (i : U.obj A₀ ≅ B₀) (p : U.obj A₁ ≅ B₁)
    (e : T.obj A₀ ≅ C₀) (c : T.obj A₁ ≅ C₁)
    (e' : S.obj B₀ ≅ D₀) (c' : S.obj B₁ ≅ D₁)
    (j : V.obj C₀ ⟶ D₀) (q : V.obj C₁ ≅ D₁)
    [IsIso (χ.app A₀)]
    (hi : U.map t₀ ≫ p.hom = i.hom ≫ t₀')
    (he : T.map t₀ ≫ c.hom = e.hom ≫ t)
    (he' : S.map t₀' ≫ c'.hom = e'.hom ≫ t')
    (hpush : χ.app A₀ ≫ V.map e.hom ≫ j = S.map i.hom ≫ e'.hom)
    (hunit : χ.app A₁ ≫ V.map c.hom ≫ q.hom = S.map p.hom ≫ c'.hom) :
    IsIso j ∧ V.map t ≫ q.hom = j ≫ t' := by
  have hj : IsIso (χ.app A₀ ≫ V.map e.hom ≫ j) := by
    rw [hpush]
    infer_instance
  have hj' : IsIso (V.map e.hom ≫ j) := IsIso.of_isIso_comp_left (χ.app A₀) _
  have : IsIso j := IsIso.of_isIso_comp_left (V.map e.hom) j
  refine ⟨inferInstance, ?_⟩
  apply (cancel_epi (χ.app A₀ ≫ V.map e.hom)).mp
  calc
    (χ.app A₀ ≫ V.map e.hom) ≫ (V.map t ≫ q.hom) =
        χ.app A₀ ≫ V.map (T.map t₀) ≫ V.map c.hom ≫ q.hom := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ χ.app A₀ ≫ V.map z ≫ q.hom) he.symm
    _ = S.map (U.map t₀) ≫ χ.app A₁ ≫ V.map c.hom ≫ q.hom := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (· ≫ V.map c.hom ≫ q.hom) (χ.naturality t₀).symm
    _ = S.map (U.map t₀) ≫ S.map p.hom ≫ c'.hom := by rw [hunit]
    _ = S.map i.hom ≫ S.map t₀' ≫ c'.hom := by
      rw [← S.map_comp_assoc, hi, S.map_comp, Category.assoc]
    _ = S.map i.hom ≫ e'.hom ≫ t' := by rw [he']
    _ = (χ.app A₀ ≫ V.map e.hom) ≫ (j ≫ t') := by
      simpa only [Category.assoc] using congrArg (· ≫ t') hpush.symm

private theorem modelExchange_naturality
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (D : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar R f'))
    (e : D.R = derivedLower R f) (e' : D'.R = derivedLower R f')
    {K J : DerivedCategory (Modules R X)} (v : K ⟶ J) :
    (derivedUpper R hS).map (D.R.map v) ≫ modelExchange R f f' hX hS h D D' e e' J =
      modelExchange R f f' hX hS h D D' e e' K ≫
        D'.R.map ((derivedUpper R hX).map v) := by
  let α : D.R ⋙ derivedUpper R hS ⟶ derivedUpper R hX ⋙ D'.R :=
    Functor.whiskerRight (eqToIso e).hom (derivedUpper R hS) ≫
      derivedExchange R f f' hX hS h ≫
      Functor.whiskerLeft (derivedUpper R hX) (eqToIso e').inv
  simpa only [α, modelExchange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, Category.assoc] using α.naturality v

private theorem scalar_trace_transfer
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (D₀ : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D₀' : DiagonalRightDerived (CondensedRing.lowerStar R f'))
    (D : DiagonalRightDerived (CondensedRing.lowerStar T f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar T f'))
    (e₀ : D₀.R = derivedLower R f) (e₀' : D₀'.R = derivedLower R f')
    (e : D.R = derivedLower T f) (e' : D'.R = derivedLower T f')
    (he₀ : IsCanonicalRightDerived (CondensedRing.lowerStar R f) D₀ e₀)
    (he₀' : IsCanonicalRightDerived (CondensedRing.lowerStar R f') D₀' e₀')
    (he : IsCanonicalRightDerived (CondensedRing.lowerStar T f) D e)
    (he' : IsCanonicalRightDerived (CondensedRing.lowerStar T f') D' e')
    {L₀ : Modules R X} {L₀' : Modules R X'} {L : Modules T X} {L' : Modules T X'}
    {m₀ : (upperStar Ab.{u + 1} hX).obj L₀.X ⟶ L₀'.X}
    {m : (upperStar Ab.{u + 1} hX).obj L.X ⟶ L'.X}
    {v : L₀.X ⟶ L.X} {v' : L₀'.X ⟶ L'.X}
    (line₀ : PullEndpoint R hX L₀ L₀' m₀) (line : PullEndpoint T hX L L' m)
    (c₀ : UnitPullEndpoint R hS) (c : UnitPullEndpoint T hS)
    (u : Endpoint a (Mod.regular (condensedRingObj R S))
      (Mod.regular (condensedRingObj T S)) (coefficientMap a S))
    (u' : Endpoint a (Mod.regular (condensedRingObj R S'))
      (Mod.regular (condensedRingObj T S')) (coefficientMap a S'))
    (l : Endpoint a L₀ L v) (l' : Endpoint a L₀' L' v')
    (hl : (scalarPullbackComparison a hX).app
        (((DerivedCategory.singleFunctor (Modules R X) 0).obj L₀)⟦(2 : ℤ)⟧) ≫
      (derivedUpper T hX).map (l.shift a) ≫ line.shift =
      (derivedScalars a X').map line₀.shift ≫ l'.shift a)
    (t₀ : D₀.R.obj (((DerivedCategory.singleFunctor (Modules R X) 0).obj L₀)⟦(2 : ℤ)⟧) ⟶
      unit R S)
    (t₀' : D₀'.R.obj (((DerivedCategory.singleFunctor (Modules R X') 0).obj L₀')⟦(2 : ℤ)⟧) ⟶
      unit R S')
    (t : D.R.obj (((DerivedCategory.singleFunctor (Modules T X) 0).obj L)⟦(2 : ℤ)⟧) ⟶
      unit T S)
    (t' : D'.R.obj (((DerivedCategory.singleFunctor (Modules T X') 0).obj L')⟦(2 : ℤ)⟧) ⟶
      unit T S')
    (ht₀ : TracePullback R f f' hX hS h D₀ D₀' e₀ e₀' line₀ c₀ t₀ t₀')
    (ht : TraceCompatibility a f u l D₀ D t₀ t)
    (ht' : TraceCompatibility a f' u' l' D₀' D' t₀' t') :
    TracePullback T f f' hX hS h D D' e e' line c t t' := by
  let K := ((DerivedCategory.singleFunctor (Modules R X) 0).obj L₀)⟦(2 : ℤ)⟧
  let K' := ((DerivedCategory.singleFunctor (Modules R X') 0).obj L₀')⟦(2 : ℤ)⟧
  let E₀ := modelExchange R f f' hX hS h D₀ D₀' e₀ e₀' K
  let E := modelExchange T f f' hX hS h D D' e e'
    (((DerivedCategory.singleFunctor (Modules T X) 0).obj L)⟦(2 : ℤ)⟧)
  have : IsIso line₀.shift := by
    unfold PullEndpoint.shift PullEndpoint.derived
    infer_instance
  have : IsIso line.shift := by
    unfold PullEndpoint.shift PullEndpoint.derived
    infer_instance
  have : IsIso c₀.derived := by
    unfold PullEndpoint.derived
    infer_instance
  have : IsIso c.derived := by
    unfold PullEndpoint.derived
    infer_instance
  have : IsIso (l.shift a) := by
    unfold Endpoint.shift
    infer_instance
  have : IsIso (l'.shift a) := by
    unfold Endpoint.shift
    infer_instance
  have : IsIso E₀ := ht₀.1
  have : IsIso ((ht.square.mate a).app K) := ht.comparison_iso
  have : IsIso ((ht'.square.mate a).app K') := ht'.comparison_iso
  have : IsIso (scalarPullbackComparison a hS) := by
    rw [scalarPullbackComparison_eq_derivedPullIso]
    infer_instance
  let i := asIso (E₀ ≫ D₀'.R.map line₀.shift)
  let eL := asIso ((ht.square.mate a).app K ≫ D.R.map (l.shift a))
  let eL' := asIso ((ht'.square.mate a).app K' ≫ D'.R.map (l'.shift a))
  have hpush : (scalarPullbackComparison a hS).app (D₀.R.obj K) ≫
      (derivedUpper T hS).map eL.hom ≫ (E ≫ D'.R.map line.shift) =
      (derivedScalars a S').map i.hom ≫ eL'.hom := by
    dsimp only [eL, eL', i, asIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% modelExchange_naturality T f f' hX hS h D D' e e' (l.shift a)]
    rw [reassoc_of% scalar_model_exchange_cube a f f' hX hS h D₀ D₀' D D'
      e₀ e₀' e e' he₀ he₀' he he' ht.square ht'.square K]
    simp only [← D'.R.map_comp]
    rw [hl]
    simp only [D'.R.map_comp]
    have hn := (ht'.square.mate a).naturality line₀.shift
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn]
  obtain ⟨hj, htrace⟩ := trace_scalar_paste
    (derivedUpper R hS) (derivedUpper T hS)
    (derivedScalars a S) (derivedScalars a S') (scalarPullbackComparison a hS)
    t₀ t₀' t t' i (asIso c₀.derived) eL u.iso eL' u'.iso
    (E ≫ D'.R.map line.shift) (asIso c.derived)
    (by simpa only [i, E₀, asIso_hom, Category.assoc] using ht₀.2)
    (by simpa only [eL, asIso_hom, Category.assoc] using ht.trace)
    (by simpa only [eL', asIso_hom, Category.assoc] using ht'.trace) hpush
    (scalar_unit_square a hS u u' c₀ c)
  have : IsIso (E ≫ D'.R.map line.shift) := hj
  have : IsIso E := IsIso.of_isIso_comp_right E (D'.R.map line.shift)
  exact ⟨inferInstance, by simpa only [E, asIso_hom, Category.assoc] using htrace⟩

private theorem diagonal_scalar_paste
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {L₀ : ∀ X : Scheme.{u}, Modules R X} {L : ∀ X : Scheme.{u}, Modules T X}
    {v : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L X).X}
    {d₀ : Diagram R Y L₀} {d₀' : Diagram R Y' L₀}
    {d : Diagram T Y L} {d' : Diagram T Y' L}
    {m₀P : (upperStar Ab.{u + 1} (baseP g)).obj (L₀ (ProjectiveLine Y)).X ⟶
      (L₀ (ProjectiveLine Y')).X}
    {m₀W : (upperStar Ab.{u + 1} (baseW g)).obj (L₀ (diagonalSurface Y)).X ⟶
      (L₀ (diagonalSurface Y')).X}
    {mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X}
    {mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X}
    (integral : PullbackCompatibility R g L₀ d₀ d₀' m₀P m₀W)
    (scalar : ScalarCompatibility a Y L₀ L v d₀ d)
    (scalar' : ScalarCompatibility a Y' L₀ L v d₀' d')
    (s : SourcePullback T g L mP mW)
    (hline : (scalarPullbackComparison a (baseW g)).app
        (((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj
          (L₀ (diagonalSurface Y)))⟦(2 : ℤ)⟧) ≫
      (derivedUpper T (baseW g)).map (scalar.lineW.shift a) ≫ s.endpoints.lineW.shift =
      (derivedScalars a (diagonalSurface Y')).map integral.sourceData.endpoints.lineW.shift ≫
        scalar'.lineW.shift a)
    (hsource : (scalarPullbackComparison a (baseW g)).app
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj (source R Y)) ≫
      (derivedUpper T (baseW g)).map scalar.supported.iso.hom ≫
      (singlePullback T (baseW g) (source T Y)).hom ≫
      (DerivedCategory.singleFunctor (Modules T (diagonalSurface Y')) 0).map s.supported.hom =
    (derivedScalars a (diagonalSurface Y')).map
      ((singlePullback R (baseW g) (source R Y)).hom ≫
        (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          integral.sourceData.supported.hom) ≫ scalar'.supported.iso.hom) :
    (derivedUpper T (baseW g)).map d.delta ≫ s.endpoints.lineW.shift =
      (singlePullback T (baseW g) (source T Y)).hom ≫
        (DerivedCategory.singleFunctor (Modules T (diagonalSurface Y')) 0).map
          s.supported.hom ≫ d'.delta := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
    scalar_pullback_paste
      (derivedUpper R (baseW g)) (derivedUpper T (baseW g))
      (derivedScalars a (diagonalSurface Y)) (derivedScalars a (diagonalSurface Y'))
      (scalarPullbackComparison a (baseW g)) d₀.delta d₀'.delta d.delta d'.delta
      ((singlePullback R (baseW g) (source R Y)) ≪≫
        (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).mapIso
          integral.sourceData.supported)
      integral.sourceData.endpoints.lineW.shift scalar.supported.iso
      (scalar.lineW.shift a) scalar'.supported.iso (scalar'.lineW.shift a)
      ((singlePullback T (baseW g) (source T Y)) ≪≫
        (DerivedCategory.singleFunctor (Modules T (diagonalSurface Y')) 0).mapIso s.supported)
      s.endpoints.lineW.shift
      (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using integral.delta)
      scalar.delta scalar'.delta
      (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using hsource)
      hline

/-- Base change compatibility of diagonal coefficient diagrams propagates along a flat change
of coefficients `a`, given base-change endpoints of the new lines compatible with those of the
old lines. -/
private def scalarPullbackCompatibility
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsNoetherian Y] [IsNoetherian Y']
    {L₀ : ∀ X : Scheme.{u}, Modules R X} {L : ∀ X : Scheme.{u}, Modules T X}
    {v : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L X).X}
    {d₀ : Diagram R Y L₀} {d₀' : Diagram R Y' L₀}
    {d : Diagram T Y L} {d' : Diagram T Y' L}
    {m₀P : (upperStar Ab.{u + 1} (baseP g)).obj (L₀ (ProjectiveLine Y)).X ⟶
      (L₀ (ProjectiveLine Y')).X}
    {m₀W : (upperStar Ab.{u + 1} (baseW g)).obj (L₀ (diagonalSurface Y)).X ⟶
      (L₀ (diagonalSurface Y')).X}
    {mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X}
    {mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X}
    (old : PullbackCompatibility R g L₀ d₀ d₀' m₀P m₀W)
    (scalar : ScalarCompatibility a Y L₀ L v d₀ d)
    (scalar' : ScalarCompatibility a Y' L₀ L v d₀' d')
    (p : PullEndpoint T (baseP g) (L (ProjectiveLine Y)) (L (ProjectiveLine Y')) mP)
    (w : PullEndpoint T (baseW g) (L (diagonalSurface Y)) (L (diagonalSurface Y')) mW)
    (hp : (upperStar Ab.{u + 1} (baseP g)).map (v (ProjectiveLine Y)) ≫ mP =
      m₀P ≫ v (ProjectiveLine Y'))
    (hw : (upperStar Ab.{u + 1} (baseW g)).map (v (diagonalSurface Y)) ≫ mW =
      m₀W ≫ v (diagonalSurface Y')) :
    PullbackCompatibility T g L d d' mP mW := by
  let s := canonicalSourcePullback T g L p w
  have hP := scalar_endpoint_square a (baseP g) old.sourceData.endpoints.lineP
    scalar.lineP scalar'.lineP s.endpoints.lineP hp
  have hW := scalar_endpoint_square a (baseW g) old.sourceData.endpoints.lineW
    scalar.lineW scalar'.lineW s.endpoints.lineW hw
  have hs := diagonalSupported_pullbackScalarNormalization a g L₀ L m₀P m₀W mP mW
    old.sourceData s (scalar.units (ProjectiveLine Y))
    (scalar'.units (ProjectiveLine Y')) scalar.supported scalar'.supported
  refine ⟨s, diagonal_scalar_paste a g old scalar scalar' s hW hs, ?_, ?_, ?_⟩
  · exact scalar_trace_transfer a _ _ _ _ _
      d₀.Rq d₀'.Rq d.Rq d'.Rq
      d₀.q_canonical d₀'.q_canonical d.q_canonical d'.q_canonical
      d₀.q_unit d₀'.q_unit d.q_unit d'.q_unit
      old.sourceData.endpoints.lineP s.endpoints.lineP
      old.sourceData.endpoints.cY s.endpoints.cY
      (scalar.units Y) (scalar'.units Y') scalar.lineP scalar'.lineP hP
      d₀.traceq d₀'.traceq d.traceq d'.traceq old.traceq scalar.q scalar'.q
  · exact scalar_trace_transfer a _ _ _ _ _
      d₀.R₁ d₀'.R₁ d.R₁ d'.R₁
      d₀.p₁_canonical d₀'.p₁_canonical d.p₁_canonical d'.p₁_canonical
      d₀.p₁_unit d₀'.p₁_unit d.p₁_unit d'.p₁_unit
      old.sourceData.endpoints.lineW s.endpoints.lineW
      old.sourceData.endpoints.cP s.endpoints.cP
      (scalar.units (ProjectiveLine Y)) (scalar'.units (ProjectiveLine Y'))
      scalar.lineW scalar'.lineW hW
      d₀.trace₁ d₀'.trace₁ d.trace₁ d'.trace₁ old.trace₁ scalar.p₁ scalar'.p₁
  · exact scalar_trace_transfer a _ _ _ _ _
      d₀.R₂ d₀'.R₂ d.R₂ d'.R₂
      d₀.p₂_canonical d₀'.p₂_canonical d.p₂_canonical d'.p₂_canonical
      d₀.p₂_unit d₀'.p₂_unit d.p₂_unit d'.p₂_unit
      old.sourceData.endpoints.lineW s.endpoints.lineW
      old.sourceData.endpoints.cP s.endpoints.cP
      (scalar.units (ProjectiveLine Y)) (scalar'.units (ProjectiveLine Y'))
      scalar.lineW scalar'.lineW hW
      d₀.trace₂ d₀'.trace₂ d.trace₂ d'.trace₂ old.trace₂ scalar.p₂ scalar'.p₂

attribute [local irreducible] scalarPullbackCompatibility derivedUpper derivedLower
  derivedScalars singlePullback
attribute [local semireducible] ProEtale.upperStar

section CoefficientStages

variable {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsNoetherian Y] [IsNoetherian Y']
  [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
  [∀ x : ProjectiveLine Y', Invertible (l : (ProjectiveLine Y').residueField x)]
  [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
  [∀ x : diagonalSurface Y', Invertible (l : (diagonalSurface Y').residueField x)]

/-- A base-change compatibility of the `ℤ_ℓ`-members gives one of the `𝒪_E`-members, with the
Tate twists compared by `spIntegralComparison`. -/
theorem nonempty_pullbackCompatibility_integral (family : Family l Y) (family' : Family l Y')
    (zl : PullbackCompatibility (Profinite.continuousMapRingObj.{u} ℤ_[l]) g
      (zlLine l) family.zl family'.zl
      (spIntegralComparison (baseP g) l (bottomField l))
      (spIntegralComparison (baseW g) l (bottomField l)))
    (E : PadicAlgCl.FiniteIntermediateField l) :
    Nonempty (PullbackCompatibility (Profinite.padicIntegersRingObj.{u} l E.1) g
      (fun X ↦ spIntegralTwist X l E) (family.integral E) (family'.integral E)
      (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E)) := by
  let : ∀ S : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralMap l E) S)) :=
    (integralScalarComparison_isIso l E g).choose
  have hE : (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≤ E.1 := bot_le
  exact ⟨scalarPullbackCompatibility (integralMap l E) g zl
    (family.toIntegral E) (family'.toIntegral E)
    (RationalP1.cartesianPullEndpoint (Profinite.padicIntegersRingObj.{u} l E.1) (baseP g)
      (spIntegralTwist (ProjectiveLine Y) l E)
      (spIntegralTwist (ProjectiveLine Y') l E) (spIntegralComparison (baseP g) l E)
      ((RationalP1.adicComparison l (baseP g)).integral_rational_cartesian E).1)
    (RationalP1.cartesianPullEndpoint (Profinite.padicIntegersRingObj.{u} l E.1) (baseW g)
      (spIntegralTwist (diagonalSurface Y) l E)
      (spIntegralTwist (diagonalSurface Y') l E) (spIntegralComparison (baseW g) l E)
      ((RationalP1.adicComparison l (baseW g)).integral_rational_cartesian E).1)
    ((RationalP1.adicComparison l (baseP g)).integral_inclusion (bottomField l) E hE)
    ((RationalP1.adicComparison l (baseW g)).integral_inclusion (bottomField l) E hE)⟩

/-- A base-change compatibility of the `𝒪_E`-members gives one of the `E`-members, with the
Tate twists compared by `RationalP1.adicComparison`. -/
theorem nonempty_pullbackCompatibility_rational (family : Family l Y) (family' : Family l Y')
    (E : PadicAlgCl.FiniteIntermediateField l)
    (hi : PullbackCompatibility (Profinite.padicIntegersRingObj.{u} l E.1) g
      (fun X ↦ spIntegralTwist X l E) (family.integral E) (family'.integral E)
      (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E)) :
    Nonempty (PullbackCompatibility (Profinite.continuousMapRingObj.{u} E.1) g
      (fun X ↦ spRationalTwist X l E) (family.rational E) (family'.rational E)
      ((RationalP1.adicComparison l (baseP g)).rational E)
      ((RationalP1.adicComparison l (baseW g)).rational E)) := by
  let : ∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj l E) S)) :=
    fun S ↦ preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield l E S
  exact ⟨scalarPullbackCompatibility (padicIntegersRingObjToContinuousMapRingObj l E) g hi
    (family.toRational E) (family'.toRational E)
    (RationalP1.cartesianPullEndpoint (Profinite.continuousMapRingObj.{u} E.1) (baseP g)
      (spRationalTwist (ProjectiveLine Y) l E)
      (spRationalTwist (ProjectiveLine Y') l E)
      ((RationalP1.adicComparison l (baseP g)).rational E)
      ((RationalP1.adicComparison l (baseP g)).integral_rational_cartesian E).2)
    (RationalP1.cartesianPullEndpoint (Profinite.continuousMapRingObj.{u} E.1) (baseW g)
      (spRationalTwist (diagonalSurface Y) l E)
      (spRationalTwist (diagonalSurface Y') l E)
      ((RationalP1.adicComparison l (baseW g)).rational E)
      ((RationalP1.adicComparison l (baseW g)).integral_rational_cartesian E).2)
    (RationalP1.rational_root_scalar_square l E (baseP g))
    (RationalP1.rational_root_scalar_square l E (baseW g))⟩

/-- A base-change compatibility of the `ℚ_ℓ`-members gives one of the `ℚ̄_ℓ`-members, with the
Tate twists compared by `RationalP1.adicComparison`. -/
theorem nonempty_pullbackCompatibility_closure (family : Family l Y) (family' : Family l Y')
    (hr : PullbackCompatibility (Profinite.continuousMapRingObj.{u} (bottomField l).1) g
      (fun X ↦ spRationalTwist X l (bottomField l)) (family.rational (bottomField l))
      (family'.rational (bottomField l))
      ((RationalP1.adicComparison l (baseP g)).rational (bottomField l))
      ((RationalP1.adicComparison l (baseW g)).rational (bottomField l))) :
    Nonempty (PullbackCompatibility (Profinite.padicAlgClRingObj.{u} l) g
      (fun X ↦ spQbarTwist X l) family.closure family'.closure
      (RationalP1.adicComparison l (baseP g)).qbar
      (RationalP1.adicComparison l (baseW g)).qbar) := by
  let : ∀ S : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl l (bottomField l)) S)) :=
    fun S ↦ CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
      l S (bottomField l)
  exact ⟨scalarPullbackCompatibility
    (Profinite.padicSubfieldRingObjToPadicAlgCl l (bottomField l)) g hr
    (family.toClosure (bottomField l)) (family'.toClosure (bottomField l))
    (RationalP1.cartesianPullEndpoint (Profinite.padicAlgClRingObj.{u} l)
      (baseP g) (spQbarTwist (ProjectiveLine Y) l)
      (spQbarTwist (ProjectiveLine Y') l) (RationalP1.adicComparison l (baseP g)).qbar
      (RationalP1.adicComparison l (baseP g)).qbar_cartesian)
    (RationalP1.cartesianPullEndpoint (Profinite.padicAlgClRingObj.{u} l)
      (baseW g) (spQbarTwist (diagonalSurface Y) l)
      (spQbarTwist (diagonalSurface Y') l) (RationalP1.adicComparison l (baseW g)).qbar
      (RationalP1.adicComparison l (baseW g)).qbar_cartesian)
    ((RationalP1.adicComparison l (baseP g)).qbar_coprojection (bottomField l))
    ((RationalP1.adicComparison l (baseW g)).qbar_coprojection (bottomField l))⟩


/-- The members of two families built from derived limits `δ, δ'` of the Cartier–Kummer systems
(recorded by `Reference`) are compatible with base change along `g`, for `Λ = 𝒪_E, E, ℚ̄_ℓ`, with
the Tate twists compared by `spIntegralComparison` and `RationalP1.adicComparison`. -/
theorem pullbackCompatibility_of_isDiagonalLimit
    [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [IsNoetherian (ProjectiveLine Y')] [IsNoetherian (diagonalSurface Y')]
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    [DiagonalTraceLocalizations l Y] [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)] [DiagonalTraceLocalizations l Y']
    [DiagonalTraceLocalizations l (ProjectiveLine Y')]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (δ' : diagonalCompletedDomain l Y' ⟶ diagonalCompletedCodomain l Y')
    (hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (hδ' : DiagonalTrace.IsDiagonalLimit l Y' hY' D' δ')
    {family : Family l Y} {family' : Family l Y'}
    (reference : Reference l Y δ family) (reference' : Reference l Y' δ' family') :
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (PullbackCompatibility (Profinite.padicIntegersRingObj.{u} l E.1) g
        (fun X ↦ spIntegralTwist X l E) (family.integral E) (family'.integral E)
        (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E))) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (PullbackCompatibility (Profinite.continuousMapRingObj.{u} E.1) g
        (fun X ↦ spRationalTwist X l E) (family.rational E) (family'.rational E)
        ((RationalP1.adicComparison l (baseP g)).rational E)
        ((RationalP1.adicComparison l (baseW g)).rational E))) ∧
    Nonempty (PullbackCompatibility (Profinite.padicAlgClRingObj.{u} l) g
      (fun X ↦ spQbarTwist X l) family.closure family'.closure
      (RationalP1.adicComparison l (baseP g)).qbar
      (RationalP1.adicComparison l (baseW g)).qbar) := by
  obtain ⟨zl⟩ := nonempty_pullbackCompatibility_zl g hY hY' D D' δ δ' hδ hδ' reference reference'
  have hi (E : PadicAlgCl.FiniteIntermediateField l) :=
    nonempty_pullbackCompatibility_integral g family family' zl E
  have hr (E : PadicAlgCl.FiniteIntermediateField l) :=
    nonempty_pullbackCompatibility_rational g family family' E (hi E).some
  exact ⟨hi, hr, nonempty_pullbackCompatibility_closure g family family' (hr (bottomField l)).some⟩

end CoefficientStages

end ScalarPullback

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
