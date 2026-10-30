/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.Compactification.BaseChange
public import Sheaf.Paper.PurityConventions
public import Sheaf.Paper.CompactSupportExchangeTransport
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence
import Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal

/-! # The counit-defined diagonal-exchange cube

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-purity-bc,
`sk-prop-sp-purity-bc-factors.proof.md`, Proof (1), expanded six-step DAG interface
(blueprint: lem-sp-diagonal-exchange-cube).

The displayed equations live in the ordinary uncompleted pro-etale module derived
categories. We write them through canonical etale-origin comparison coordinates;
every arrow is the comparison image of the specified counit mate. The equalities
include the pullback compositors and the inverse-mate diagonal restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor


namespace WeilConjectures

/-- The map on self-products induced by a change of base.
Source: diagonal cube, Proof (1) (blueprint: lem-sp-diagonal-exchange-cube). -/
def diagonalCubeMap {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) :
    pullback (pullback.snd f v) (pullback.snd f v) ⟶ pullback f f :=
  pullback.map (pullback.snd f v) (pullback.snd f v) f f
    (pullback.fst f v) (pullback.fst f v) v
    (pullback.condition (f := f) (g := v)).symm (pullback.condition (f := f) (g := v)).symm

/-- The two pullbacks associated to equal composite maps, with the specified compositors.
Source: diagonal cube, canonical pullback compositors
(blueprint: lem-sp-diagonal-exchange-cube). -/
def diagonalCubePullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (e : C ⟶ D) (h : a ≫ b = c ≫ e) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) b).leftDerivedFunctor ⋙
        (Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor ⋙
        (Etale.upperStar (ModuleCat.{u + 1} Λ) c).leftDerivedFunctor :=
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a b).symm ≪≫
    Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c e (a ≫ b) h

/-- On the constructible finite-Tor domain, retain an etale antecedent and identify the
specified compact-support exchange with its witnessed proper/open transport, for every
compactification. Source: diagonal cube, etale-origin and exchange-normalization paragraph
(blueprint: lem-sp-diagonal-exchange-cube). -/
def diagonalCubeWitnessed (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback a f' f v) : Prop :=
  ∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)),
    (∃ a b : ℤ,
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X Λ
        ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      (∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      Scheme.HasFixedCoefficientProEtaleTorAmplitude X Λ K a b) →
    ∃ L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X L.obj ∧
      ∃ alpha : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj ≅ K,
        ∀ c : Compactification f,
          IsIso ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} Λ) sq c).app K) ∧
          ProEtale.compactExchangeTransportAtWitness Λ sq c L K alpha =
            (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
              (ModuleCat.{u + 1} Λ) sq c).app K

/-- The two equations on the specified mates, read in the canonical etale-origin
coordinates of the ordinary pro-etale derived categories. The four isomorphisms are
required to have exactly the specified counit-mate homomorphisms; they are not supplied
as independent data. Source: diagonal cube, its two displayed equations
(blueprint: lem-sp-diagonal-exchange-cube). -/
def diagonalCubeComparisons (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y)
    [HasCompactification f] [QuasiCompact f] [IsSeparated f] (d : ℕ) : Prop :=
  ∃ (sq₁ : IsPullback (diagonalCubeMap f v) (pullback.fst (pullback.snd f v) (pullback.snd f v))
        (pullback.fst f f) (pullback.fst f v))
    (sq₂ : IsPullback (diagonalCubeMap f v) (pullback.snd (pullback.snd f v) (pullback.snd f v))
        (pullback.snd f f) (pullback.fst f v))
    (hΔ : (pullback.diagonal (pullback.snd f v)) ≫ (diagonalCubeMap f v) = (pullback.fst f v) ≫
        (pullback.diagonal f)),
    SmoothOfRelativeDimension d (pullback.snd f v) ∧
    SmoothOfRelativeDimension d (pullback.fst f f) ∧
    SmoothOfRelativeDimension d (pullback.snd f f) ∧
    SmoothOfRelativeDimension d (pullback.fst (pullback.snd f v) (pullback.snd f v)) ∧
    SmoothOfRelativeDimension d (pullback.snd (pullback.snd f v) (pullback.snd f v)) ∧
    PurityConventions.IsRegularOfPureCodimension (pullback.diagonal f) d ∧
    PurityConventions.IsRegularOfPureCodimension (pullback.diagonal (pullback.snd f v)) d ∧
    diagonalCubeWitnessed Λ (IsPullback.of_hasPullback f f).flip ∧
    diagonalCubeWitnessed Λ (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip ∧
    diagonalCubeWitnessed Λ sq₁ ∧
    diagonalCubeWitnessed Λ (IsPullback.of_hasPullback f v) ∧
    ∃ (b : (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.snd f f)).leftDerivedFunctor.obj
        (Etale.dualizingComplex Λ f) ≅ (Etale.dualizingComplex Λ (pullback.fst f f)))
      (b' : (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.snd (pullback.snd f v) (pullback.snd
        f v))).leftDerivedFunctor.obj (Etale.dualizingComplex Λ (pullback.snd
        f v)) ≅ (Etale.dualizingComplex Λ (pullback.fst (pullback.snd f v)
        (pullback.snd f v))))
      (bp : (Etale.upperStar (ModuleCat.{u + 1} Λ) (diagonalCubeMap f v)).leftDerivedFunctor.obj
        (Etale.dualizingComplex Λ (pullback.fst f f)) ≅
        (Etale.dualizingComplex Λ (pullback.fst (pullback.snd f v)
        (pullback.snd f v))))
      (e : (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f v)).leftDerivedFunctor.obj
        (Etale.dualizingComplex Λ f) ≅ (Etale.dualizingComplex Λ (pullback.snd f v))),
      b.hom = Etale.dualizingComplexBaseChangeMap Λ
        (IsPullback.of_hasPullback f f).flip ∧
      b'.hom = Etale.dualizingComplexBaseChangeMap Λ
        (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip ∧
      bp.hom = Etale.dualizingComplexBaseChangeMap Λ sq₁ ∧
      e.hom = Etale.dualizingComplexBaseChangeMap Λ (IsPullback.of_hasPullback f v) ∧
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) (pullback (pullback.snd f v)
        (pullback.snd f v))).mapDerivedCategory.map
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (diagonalCubeMap f v)).leftDerivedFunctor.map
        b.hom ≫ bp.hom) =
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) (pullback (pullback.snd f v)
        (pullback.snd f v))).mapDerivedCategory.map
        ((diagonalCubePullbackIso Λ (diagonalCubeMap f v) (pullback.snd f f)
          (pullback.snd (pullback.snd f v) (pullback.snd f v)) (pullback.fst f v) sq₂.w).hom.app
        (Etale.dualizingComplex Λ f) ≫
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.snd (pullback.snd f v) (pullback.snd f
        v))).leftDerivedFunctor.map e.hom ≫ b'.hom) ∧
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) (pullback f v)).mapDerivedCategory.map
        ((diagonalCubePullbackIso Λ (pullback.fst f v) (pullback.diagonal f)
          (pullback.diagonal (pullback.snd f v)) (diagonalCubeMap f v) hΔ.symm).hom.app
        (Etale.dualizingComplex Λ (pullback.fst f f)) ≫
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.diagonal (pullback.snd f
        v))).leftDerivedFunctor.map bp.hom ≫
          ((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (pullback.diagonal (pullback.snd f v))).leftDerivedFunctor.mapIso b'.symm ≪≫
            (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ)
              (pullback.diagonal (pullback.snd f v))
              (pullback.snd (pullback.snd f v) (pullback.snd f v))
              (pullback.diagonal_snd (pullback.snd f v))).app _).hom) =
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) (pullback f v)).mapDerivedCategory.map
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f v)).leftDerivedFunctor.map
          ((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (pullback.diagonal f)).leftDerivedFunctor.mapIso b.symm ≪≫
            (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ)
              (pullback.diagonal f) (pullback.snd f f)
              (pullback.diagonal_snd f)).app _).hom ≫ e.hom)

/-- The ordinary finite-coefficient diagonal-exchange cube in the finite-type field
setting, with compactifiability obtained from Nagata, not imposed as a hypothesis.
Source: diagonal cube, fixed setting and R = Z/ell^r
(blueprint: lem-sp-diagonal-exchange-cube). -/
def diagonalExchangeCubeStatement (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (r : ℕ) (d : ℕ) {X Y Y' : Scheme.{u}}
    (aY : Y ⟶ Spec (.of D.k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [QuasiCompact f]
    (v : Y' ⟶ Y) : Prop :=
  letI : Smooth f := SmoothOfRelativeDimension.smooth d f
  letI := LocallyOfFiniteType.isLocallyNoetherian aY
  letI := QuasiCompact.compactSpace_of_compactSpace aY
  letI : NeZero (C.l ^ r) := ⟨pow_ne_zero r (Fact.out : C.l.Prime).ne_zero⟩
  diagonalCubeComparisons (ULift.{u + 1} (ZMod (C.l ^ r))) f v d

-- Keep the derived functors and canonical maps abstract during the categorical calculations.
attribute [local irreducible] Etale.rightDerivedLowerShriekBaseChangeMap
  Etale.rightDerivedUpperShriekBaseChangeMap Etale.leftDerivedUpperStarComp

private theorem cube_diagonal_regular {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] (d : ℕ) [SmoothOfRelativeDimension d f] :
    PurityConventions.IsRegularOfPureCodimension (pullback.diagonal f) d := by
  let W := pullback f f
  let i := pullback.diagonal f
  by_cases hd : d = 0
  · subst d
    have : Etale f := (Etale.iff_smoothOfRelativeDimension_zero (f := f)).mpr inferInstance
    intro z
    obtain ⟨U, hU, hz, hle⟩ := exists_isAffineOpen_mem_and_subset
      (X := W) (U := i.opensRange) (show i z ∈ i.opensRange from ⟨z, rfl⟩)
    have : IsIso (i.app U) := i.isIso_app U hle
    have : Nontrivial Γ(W, U) := (W.presheaf.germ U (i z) hz).hom.domain_nontrivial
    refine ⟨⟨U, hU⟩, hz, [], rfl, RingTheory.Sequence.IsRegular.nil _ _, ?_⟩
    rw [Ideal.ofList_nil, Scheme.Hom.ker_apply]
    exact ((RingHom.injective_iff_ker_eq_bot _).mp
      (ConcreteCategory.bijective_of_isIso (i.app U)).injective).symm
  · have : NeZero d := ⟨hd⟩
    have : IsRegularImmersion d i := inferInstance
    intro z
    obtain ⟨U, hz, r, hr, hreg, hI⟩ :=
      IsRegularImmersion.exists_isWeaklyRegular_generators (c := d) (i := i) (i z)
    have hs : i z ∈ W.zeroLocus (U := U.1) (i.ker.ideal U) :=
      (Scheme.IdealSheafData.mem_support_iff_of_mem hz).mp
        (i.range_subset_ker_support ⟨z, rfl⟩)
    have hproper : i.ker.ideal U ≠ ⊤ := by
      intro htop
      have hmem : (1 : Γ(W, U.1)) ∈ i.ker.ideal U := by rw [htop]; trivial
      have h1 := (W.mem_zeroLocus_iff _ _).mp hs 1 hmem
      exact h1 (by simpa using hz)
    refine ⟨U, hz, r, hr, ⟨hreg, ?_⟩, hI⟩
    simpa only [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id,
      Submodule.restrictScalars_self, hI, ne_eq, eq_comm] using hproper

private theorem cube_projection_squares {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (v : Y' ⟶ Y) :
    IsPullback (diagonalCubeMap f v)
      (pullback.fst (pullback.snd f v) (pullback.snd f v))
      (pullback.fst f f) (pullback.fst f v) ∧
    IsPullback (diagonalCubeMap f v)
      (pullback.snd (pullback.snd f v) (pullback.snd f v))
      (pullback.snd f f) (pullback.fst f v) := by
  constructor
  · apply IsPullback.of_right (t := (IsPullback.of_hasPullback f f).flip)
    · convert (IsPullback.of_hasPullback (pullback.snd f v)
        (pullback.snd f v)).flip.paste_horiz (IsPullback.of_hasPullback f v) using 1
      · simp [diagonalCubeMap]
      · exact pullback.condition
    · simp [diagonalCubeMap]
  · apply IsPullback.of_right (t := IsPullback.of_hasPullback f f)
    · convert (IsPullback.of_hasPullback (pullback.snd f v)
        (pullback.snd f v)).paste_horiz (IsPullback.of_hasPullback f v) using 1
      · simp [diagonalCubeMap]
      · exact pullback.condition
    · simp [diagonalCubeMap]

private theorem cube_diagonal {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) :
    pullback.diagonal (pullback.snd f v) ≫ diagonalCubeMap f v =
      pullback.fst f v ≫ pullback.diagonal f := by
  apply pullback.hom_ext <;> simp [diagonalCubeMap]

private theorem cube_witnessed (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback a f' f v) : diagonalCubeWitnessed Λ sq := by
  intro K hK
  obtain ⟨a, b, hc, hv, _⟩ := hK
  have hb : DerivedCategory.TStructure.t.bounded K := by
    exact ⟨⟨a, (DerivedCategory.isGE_iff K a).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).mpr (fun i hi ↦ hv i (Or.inr hi))⟩⟩
  have hH (i : ℤ) : ProEtale.IsConstructible Λ
      ((DerivedCategory.homologyFunctor _ i).obj K) := by
    obtain ⟨S, _, _, hS⟩ := hc i
    exact ⟨S, fun j ↦ Scheme.finite_models_of_fixed_lisse (S.domain j) Λ _ (hS j)⟩
  obtain ⟨L, hL, ⟨alpha⟩⟩ := ProEtale.DerivedCategory.boundedConstructible_of_homology
    Λ hb (fun i ↦ ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj Λ (hH i))
  refine ⟨⟨L, hL.1.1⟩, hL, alpha, fun c ↦ ?_⟩
  constructor
  · exact ProEtale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app
      Λ sq c K ⟨L, hL.1.1, ⟨alpha⟩⟩
  · exact (ProEtale.compactSupport_exchange_transport Λ sq c).2 ⟨L, hL.1.1⟩ K alpha

open AlgebraicGeometry.Etale CategoryTheory.MonoidalCategory in
private theorem cube_exceptional_base_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (K : DerivedCategoryModule A Y) :
    (rightDerivedUpperShriekBaseChangeMap A (sq₂.paste_horiz sq₁)).app K =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app
        ((rightDerivedUpperShriek A f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        ((rightDerivedUpperShriekBaseChangeMap A sq₁).app K) ≫
      (rightDerivedUpperShriekBaseChangeMap A sq₂).app
        ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K) ≫
      (rightDerivedUpperShriek A f'').map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).inv.app K) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₁
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₂
  have := isIso_rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)
  let E₁ := rightDerivedLowerShriekBaseChangeMap A sq₁
  let E₂ := rightDerivedLowerShriekBaseChangeMap A sq₂
  let E₃ := rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)
  let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v
  let c' := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v'
  let δ₁ := TwoSquare.mk _ _ _ _ (inv E₁)
  let δ₂ := TwoSquare.mk _ _ _ _ (inv E₂)
  have h : TwoSquare.mk _ _ _ _ (inv E₃) =
      ((δ₁.hComp δ₂).whiskerTop c'.hom).whiskerBottom c.inv := by
    apply TwoSquare.ext
    intro M
    dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    let Vw := (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor
    let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f''
    have he : (asIso E₃).app M =
        c.app _ ≪≫ Vw.mapIso ((asIso E₁).app M) ≪≫
          (asIso E₂).app _ ≪≫ F.mapIso (c'.symm.app M) := by
      apply Iso.ext
      apply (cancel_epi (c.inv.app _)).mp
      apply (cancel_mono (F.map (c'.hom.app M))).mp
      simp only [Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        asIso_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
        ← F.map_comp, Iso.inv_hom_id_app]
      have hid := CategoryTheory.Functor.map_id F
        (((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctor ⋙
          (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor).obj M)
      rw [hid]
      erw [Category.comp_id]
      exact (affineLinearExchange_paste A sq₁ sq₂ M).symm
    have hi := congrArg Iso.inv he
    simpa only [Iso.app_inv, asIso_inv, Iso.trans_inv, Functor.mapIso_inv,
      Iso.symm_inv, Category.assoc, Vw, F] using hi
  have hm := congrArg (fun z ↦ z.natTrans.app K)
    (congrArg (mateEquiv
      (rightDerivedUpperShriekAdjunction A f)
      (rightDerivedUpperShriekAdjunction A f'')) h)
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp] at hm
  simpa only [rightDerivedUpperShriekBaseChangeMap, δ₁, δ₂, E₁, E₂, E₃,
    TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.natTrans, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, c, c'] using hm

open AlgebraicGeometry.Etale CategoryTheory.MonoidalCategory in
private theorem cube_dualizing_base_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w) :
    dualizingComplexBaseChangeMap A (sq₂.paste_horiz sq₁) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app
        (dualizingComplex A f) ≫
      (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A sq₁) ≫ dualizingComplexBaseChangeMap A sq₂ := by
  have hu := (canonicalDerivedPullbackCompositionMonoidal A v w (𝟙 Y'')
    (𝟙_ _) (𝟙_ _)).2.1
  have hn := (rightDerivedUpperShriekBaseChangeMap A sq₂).naturality
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) v).hom
  simp only [Functor.comp_map] at hn
  unfold dualizingComplexBaseChangeMap dualizingComplex
  rw [cube_exceptional_base_comp A sq₁ sq₂]
  simp only [Category.assoc, Functor.map_comp]
  erw [reassoc_of% hn]
  rw [← hu]
  simp only [Functor.map_comp]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]


open AlgebraicGeometry.Etale in
private theorem cube_dualizing_base_comp_chosen
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (a : X'' ⟶ X) (b : Y'' ⟶ Y) (ha : a = w' ≫ v') (hb : b = w ≫ v)
    (sq : IsPullback a f'' f b) :
    dualizingComplexBaseChangeMap A sq =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' a ha).hom.app
        (dualizingComplex A f) ≫
      (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A sq₁) ≫ dualizingComplexBaseChangeMap A sq₂ := by
  subst a
  subst b
  exact cube_dualizing_base_comp A sq₁ sq₂

private theorem cube_pullback_endpoint (Λ : Type (u + 1)) [CommRing Λ]
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (e : C ⟶ D)
    (z z' : A ⟶ D) (ha : z = a ≫ b) (hc : z = c ≫ e)
    (ha' : z' = a ≫ b) (hc' : z' = c ≫ e) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a b z ha).symm ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c e z hc =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a b z' ha').symm ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c e z' hc' := by
  subst z
  subst z'
  rfl

/-- Cancellation and section-compositor coherence for the second cube equation.
Source: the section cancellation step (blueprint: lem-sp-diagonal-exchange-cube). -/
private theorem cube_section_equation (Λ : Type (u + 1)) [CommRing Λ]
    {B B' P P' : Scheme.{u}} (u : B' ⟶ B) (a : P ⟶ B) (a' : P' ⟶ B')
    (q : P' ⟶ P) (i : B ⟶ P) (i' : B' ⟶ P')
    (hq : q ≫ a = a' ≫ u) (hi : i' ≫ q = u ≫ i)
    (hs : i ≫ a = 𝟙 B) (hs' : i' ≫ a' = 𝟙 B')
    (K : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory (Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F' : DerivedCategory (Sheaf P'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (b : (Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.obj K ≅ F)
    (b' : (Etale.upperStar (ModuleCat.{u + 1} Λ) a').leftDerivedFunctor.obj K' ≅ F')
    (bp : (Etale.upperStar (ModuleCat.{u + 1} Λ) q).leftDerivedFunctor.obj F ≅ F')
    (e : (Etale.upperStar (ModuleCat.{u + 1} Λ) u).leftDerivedFunctor.obj K ≅ K')
    (heq : (Etale.upperStar (ModuleCat.{u + 1} Λ) q).leftDerivedFunctor.map b.hom ≫
      bp.hom = (diagonalCubePullbackIso Λ q a a' u hq).hom.app K ≫
        (Etale.upperStar (ModuleCat.{u + 1} Λ) a').leftDerivedFunctor.map e.hom ≫ b'.hom) :
    (diagonalCubePullbackIso Λ u i i' q hi.symm).hom.app F ≫
        (Etale.upperStar (ModuleCat.{u + 1} Λ) i').leftDerivedFunctor.map bp.hom ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) i').leftDerivedFunctor.mapIso b'.symm ≪≫
          (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) i' a' hs').app K').hom =
      (Etale.upperStar (ModuleCat.{u + 1} Λ) u).leftDerivedFunctor.map
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).leftDerivedFunctor.mapIso b.symm ≪≫
          (Etale.leftDerivedUpperStarCompSectionIso
            (ModuleCat.{u + 1} Λ) i a hs).app K).hom ≫ e.hom := by
  let U := (Etale.upperStar (ModuleCat.{u + 1} Λ) u).leftDerivedFunctor
  let I := (Etale.upperStar (ModuleCat.{u + 1} Λ) i).leftDerivedFunctor
  let I' := (Etale.upperStar (ModuleCat.{u + 1} Λ) i').leftDerivedFunctor
  let A := diagonalCubePullbackIso Λ u i i' q hi.symm
  let H := diagonalCubePullbackIso Λ q a a' u hq
  let S := Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) i a hs
  let S' := Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) i' a' hs'
  have hn := A.hom.naturality b.hom
  have he := S'.hom.naturality e.hom
  simp only [Functor.comp_map, Functor.id_map] at he
  have hsec := Etale.leftDerivedUpperStar_map_comp_compSectionIso
    (ModuleCat.{u + 1} Λ) u a a' q i i' hq hi hs hs' K
  have hA := cube_pullback_endpoint Λ i' q u i (i' ≫ q) (u ≫ i) rfl hi hi.symm rfl
  change A.hom.app F ≫ I'.map bp.hom ≫ (I'.mapIso b'.symm ≪≫ S'.app K').hom =
    U.map (I.mapIso b.symm ≪≫ S.app K).hom ≫ e.hom
  apply (cancel_epi (U.map (I.map b.hom))).mp
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  change U.map (I.map b.hom) ≫ A.hom.app F ≫ I'.map bp.hom ≫
      I'.map b'.inv ≫ S'.hom.app K' = _
  rw [reassoc_of% hn]
  rw [← I'.map_comp_assoc, heq, I'.map_comp, I'.map_comp]
  simp only [Category.assoc, ← I'.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [he]
  have hsec' : I'.map (H.hom.app K) ≫ S'.hom.app (U.obj K) =
      A.inv.app _ ≫ U.map (S.hom.app K) := by
    have hA' := congrArg (fun z ↦ z.hom.app
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.obj K)) hA
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom] at hA'
    rw [hA'] at hsec
    exact hsec
  rw [reassoc_of% hsec', Iso.hom_inv_id_app_assoc]
  simp only [← U.map_comp_assoc, ← I.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem cube_exponent (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (r : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of D.k)) :
    HasInvertibleExponent (ULift.{u + 1} (ZMod (C.l ^ r))) T := by
  let : Fintype D.k₀ := Fintype.ofFinite _
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hu : IsUnit (C.l : D.k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime _ (Fact.out : C.l.Prime) C.different.symm)
  refine ⟨C.l ^ r, pow_pos (Fact.out : C.l.Prime).pos _, ?_, ?_⟩
  · apply ULift.ext
    exact ZMod.natCast_self _
  · simpa only [← Nat.cast_pow, map_natCast] using
      (hu.pow r).map (((Scheme.ΓSpecIso (.of D.k)).inv ≫ aT.appTop).hom)

/-- The counit-defined diagonal comparison commutes with arbitrary change of base.
Source: latest blueprint, sk-prop-sp-purity-bc-factors.proof.md, Proof (1),
expanded in the DAG's six-step proof (blueprint: lem-sp-diagonal-exchange-cube).

Proof: (1) The fibre-product universal property identifies the primed self-product
with the base change of the original first projection; its canonical map is
pullback.map, and the diagonal and both projections are preserved.
(2) Smooth relative dimension is preserved under base change, so all projections
have dimension d. On standard-smooth charts the diagonal ideal is generated by the
d coordinate differences, a regular sequence; at d=0 use the empty regular sequence
near the clopen diagonal. Separatedness makes both diagonal sections closed.
(3) Finite-setting comparison hypotheses and Nagata provide compactifications.
Every bounded constructible finite-Tor input has an etale antecedent; the proper
counit mate and exact extension by zero identify the raw compact-support exchanges
with their witnessed transports, independently of witness and compactification.
Cohomological smoothness makes the four specified exceptional unit mates invertible.
(4) Paste compact-support exchanges, invert, and apply mate pasting to the specified
constructible adjunctions. This identifies each exceptional exchange with the
transpose of the pulled-back counit after inverse compact-support exchange.
(5) Apply pasting to the two decompositions f followed by u, and v followed by f'.
Their composites agree, giving the first equation with diagonalCubePullbackIso.
(6) Pull this equation along the primed diagonal. Insert the section compositors,
then cancel the two diagonal pullbacks of b and b'. Their inverses are exactly
the displayed diagonal pullbacks of the inverse mates followed by the section
compositors. This gives the second equation. Canonical site
comparison sends these equations to the displayed ordinary pro-etale categories.
Identity change of base, d=0, empty schemes and arbitrary nonflat v are included. -/
theorem diagonalExchangeCube (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (r : ℕ) (hr : 1 ≤ r) (d : ℕ) {X Y Y' : Scheme.{u}}
    (aY : Y ⟶ Spec (.of D.k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension d f]
    (v : Y' ⟶ Y) (aY' : Y' ⟶ Spec (.of D.k))
    [IsSeparated aY'] [LocallyOfFiniteType aY'] [QuasiCompact aY']
    (hv : v ≫ aY = aY') :
    diagonalExchangeCubeStatement D C r d aY f v := by
  have _ := hr
  have _ := hv
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := {}
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian aY'
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace aY'
  have : IsNoetherian Y' := {}
  have : IsLocallyNoetherian (pullback f v) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f v)
  have : CompactSpace (pullback f v : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f v)
  have : IsNoetherian (pullback f v) := {}
  have : IsLocallyNoetherian (pullback f f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f)
  have : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  have : IsNoetherian (pullback f f) := {}
  have : IsLocallyNoetherian (pullback (pullback.snd f v) (pullback.snd f v)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst (pullback.snd f v) (pullback.snd f v))
  have : CompactSpace (pullback (pullback.snd f v) (pullback.snd f v) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst (pullback.snd f v) (pullback.snd f v))
  have : IsNoetherian (pullback (pullback.snd f v) (pullback.snd f v)) := {}
  have : NeZero (C.l ^ r) := ⟨pow_ne_zero r (Fact.out : C.l.Prime).ne_zero⟩
  let Λ := ULift.{u + 1} (ZMod (C.l ^ r))
  have : HasInvertibleExponent Λ X := cube_exponent D C r X (f ≫ aY)
  have : HasInvertibleExponent Λ (pullback f v) :=
    cube_exponent D C r _ (pullback.snd f v ≫ aY')
  have : HasInvertibleExponent Λ (pullback f f) :=
    HasInvertibleExponent.of_hom (show pullback f f ⟶ X from pullback.fst f f)
  obtain ⟨sq₁, sq₂⟩ := cube_projection_squares f v
  have hΔ := cube_diagonal f v
  change diagonalCubeComparisons Λ f v d
  refine ⟨sq₁, sq₂, hΔ, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, cube_diagonal_regular f d,
    cube_diagonal_regular (pullback.snd f v) d,
    cube_witnessed Λ (IsPullback.of_hasPullback f f).flip,
    cube_witnessed Λ
      (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip,
    cube_witnessed Λ sq₁, cube_witnessed Λ (IsPullback.of_hasPullback f v), ?_⟩
  have hIso {A B A' B' : Scheme.{u}} {g : A ⟶ B} {g' : A' ⟶ B'}
      {a : A' ⟶ A} {b : B' ⟶ B}
      [QuasiSeparatedSpace B] [HasInvertibleExponent Λ A]
      [HasCompactification g] [HasCompactification g'] [QuasiCompact g']
      [SmoothOfRelativeDimension d g] (sq : IsPullback a g' g b) :
      IsIso (Etale.dualizingComplexBaseChangeMap Λ sq) := by
    have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
      Λ g d sq
    exact (Etale.isIso_dualizingComplexBaseChangeMap_iff Λ sq).mpr inferInstance
  have := hIso (IsPullback.of_hasPullback f f).flip
  have := hIso
    (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip
  have := hIso sq₁
  have := hIso (IsPullback.of_hasPullback f v)
  let b := asIso (Etale.dualizingComplexBaseChangeMap Λ
    (IsPullback.of_hasPullback f f).flip)
  let b' := asIso (Etale.dualizingComplexBaseChangeMap Λ
    (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip)
  let bp := asIso (Etale.dualizingComplexBaseChangeMap Λ sq₁)
  let e := asIso (Etale.dualizingComplexBaseChangeMap Λ (IsPullback.of_hasPullback f v))
  have hpaste := cube_dualizing_base_comp Λ (IsPullback.of_hasPullback f f).flip sq₁
  have hpaste' := cube_dualizing_base_comp_chosen Λ
    (IsPullback.of_hasPullback f v)
    (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip
    (diagonalCubeMap f v ≫ pullback.snd f f) (pullback.fst f v ≫ f)
    sq₂.w (pullback.condition (f := f) (g := v))
    (sq₁.paste_horiz (IsPullback.of_hasPullback f f).flip)
  have heq :
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (diagonalCubeMap f v)).leftDerivedFunctor.map
        b.hom ≫ bp.hom =
      (diagonalCubePullbackIso Λ (diagonalCubeMap f v) (pullback.snd f f)
        (pullback.snd (pullback.snd f v) (pullback.snd f v))
        (pullback.fst f v) sq₂.w).hom.app _ ≫
      (Etale.upperStar (ModuleCat.{u + 1} Λ)
        (pullback.snd (pullback.snd f v) (pullback.snd f v))).leftDerivedFunctor.map
        e.hom ≫ b'.hom := by
    have h := hpaste.symm.trans hpaste'
    apply (cancel_epi ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
      (diagonalCubeMap f v) (pullback.snd f f)).hom.app _)).mp
    simpa only [diagonalCubePullbackIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.hom_inv_id_app_assoc, b, b', bp, e, asIso_hom] using h
  refine ⟨b, b', bp, e, rfl, rfl, rfl, rfl,
    congrArg ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ)
      (pullback (pullback.snd f v) (pullback.snd f v))).mapDerivedCategory.map) heq, ?_⟩
  exact congrArg ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ)
    (pullback f v)).mapDerivedCategory.map) (cube_section_equation Λ
    (pullback.fst f v) (pullback.snd f f)
    (pullback.snd (pullback.snd f v) (pullback.snd f v)) (diagonalCubeMap f v)
    (pullback.diagonal f) (pullback.diagonal (pullback.snd f v)) sq₂.w hΔ
    (pullback.diagonal_snd f) (pullback.diagonal_snd (pullback.snd f v))
    _ _ _ _ b b' bp e heq)

end WeilConjectures
