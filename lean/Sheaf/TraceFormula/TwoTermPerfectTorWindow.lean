/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.TraceFormula.TwoTermPerfectDeterminantData
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.ResidueBettiZeroOfTensorVanishing
import all WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal
import all WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.PerfectOfOpenPullbacks
import all WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect

/-! # Two-term locally free models and Tor amplitude

Source: Stacks Project, Tags 0FJX, 08G7 and 068V.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
variable [d : ∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

omit d in
-- The old body and the adopted body are definitionally equal, including their
-- K-flat predicates. This proof also checks the independently parameterized universes.
set_option synthInstance.maxSize 256 in
private theorem adopted_vanishing_eq_original (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ) :
    schemeDerivedTensorCohomologyVanishes X E F i =
      (letI := SheafOfModules.monoidalCategory X.sheaf
       ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
         CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P ∧
           Nonempty (DerivedCategory.Q.obj P ≅ E) ∧
           IsZero ((CochainComplex.mapBifunctor P
             ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
             (curriedTensor _)).homology i)) := rfl


omit d in
private theorem complex_twoTerm_iso
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) :
    Nonempty (HomologicalComplex.double (K.d (-1) 0)
      (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide) ≅ K) := by
  let φ := HomologicalComplex.mkHomFromDouble
    (f := K.d (-1) 0) (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)
    (by decide) (𝟙 _) (𝟙 _) (by simp) (by
      intro i hi
      have hi' : i = 1 := by simpa using hi.symm
      subst i
      exact (hK 1 (by decide) (by decide)).eq_of_tgt _ _)
  have : ∀ i, IsIso (φ.f i) := by
    intro i
    by_cases hneg : i = -1
    · subst i
      dsimp [φ]
      rw [HomologicalComplex.mkHomFromDouble_f₀]
      infer_instance
    · by_cases hzero : i = 0
      · subst i
        dsimp [φ]
        rw [HomologicalComplex.mkHomFromDouble_f₁]
        infer_instance
      · exact ⟨⟨0, (HomologicalComplex.isZero_double_X _ _ i hneg hzero).eq_of_src _ _,
          (hK i hneg hzero).eq_of_src _ _⟩⟩
  have : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  exact ⟨asIso φ⟩

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable def moduleRestrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := restrictFunctor f

private local instance moduleRestrict_additive {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : (moduleRestrict f).Additive :=
  inferInstanceAs (restrictFunctor f).Additive

private local instance moduleRestrict_limits {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : PreservesFiniteLimits (moduleRestrict f) :=
  inferInstanceAs (PreservesFiniteLimits (restrictFunctor f))

private local instance moduleRestrict_colimits {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : PreservesFiniteColimits (moduleRestrict f) :=
  inferInstanceAs (PreservesFiniteColimits (restrictFunctor f))

private theorem exact_open_model {X : Scheme.{u}} (U : X.Opens)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := moduleRestrict U.ι
    Nonempty ((derivedPullback U.ι).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj K)) := by
  dsimp only
  let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := moduleRestrict U.ι
  have : R.Additive := moduleRestrict_additive U.ι
  have : PreservesFiniteLimits R := moduleRestrict_limits U.ι
  have : PreservesFiniteColimits R := moduleRestrict_colimits U.ι
  let : HasDerivedCategory.{w} U.toScheme.Modules := d U.toScheme
  obtain ⟨e⟩ := open_pullback_restriction_iso X U (DerivedCategory.Q.obj K)
  let θ : SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      (overEquiv U).functor ≅ R := overFunctorEquiv U
  let θD : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      (overEquiv U).functor).mapDerivedCategory.{w, w} ≅
        R.mapDerivedCategory.{w, w} :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      (_ ⋙ DerivedCategory.Q) (_ ⋙ DerivedCategory.Q) _ _
      (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex θ (ComplexShape.up ℤ))
        DerivedCategory.Q)
  exact ⟨e.symm ≪≫ θD.app _ ≪≫
    R.mapDerivedCategoryFactors.app K⟩

private theorem model_local_free {X : Scheme.{u}} (P : TwoTermDeterminantModel X)
    (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      ∃ K : CochainComplex
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ,
        (∀ i : ℤ, i < -1 ∨ 0 < i → IsZero (K.X i)) ∧
        (∀ i : ℤ, ∃ r : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
          (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin r)))) ∧
        Nonempty ((derivedPullback U.ι).obj (DerivedCategory.Q.obj P.complex) ≅
          DerivedCategory.Q.obj K) := by
  classical
  have := P.neg_free
  have := P.nonneg_free
  obtain ⟨I, U, hU, eU⟩ := IsFiniteLocallyFreeOfRank.exists_restrict_iso_free
    P.neg (r := P.negRank)
  obtain ⟨J, V, hV, eV⟩ := IsFiniteLocallyFreeOfRank.exists_restrict_iso_free
    P.nonneg (r := P.nonnegRank)
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by
    have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨j, hj⟩ : ∃ j, x ∈ V j := by
    have hx : x ∈ ⨆ j, V j := by rw [hV]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  let W := U i ⊓ V j
  let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) := moduleRestrict W.ι
  let K := (R.mapHomologicalComplex (.up ℤ)).obj P.complex
  have hzero (n : ℤ) (hn : n ≠ -1) (hn' : n ≠ 0) : IsZero (K.X n) :=
    R.map_isZero (HomologicalComplex.isZero_double_X _ _ n hn hn')
  refine ⟨W, ⟨hi, hj⟩, K, fun n hn ↦ hzero n (by omega) (by omega), ?_,
    exact_open_model W P.complex⟩
  intro n
  by_cases hneg : n = -1
  · subst n
    refine ⟨P.negRank, ⟨R.mapIso (HomologicalComplex.doubleXIso₀ _ _) ≪≫ ?_⟩⟩
    exact restrictCompIso P.neg (U i).ι (X.homOfLE (show W ≤ U i from inf_le_left))
      W.ι (X.homOfLE_ι inf_le_left) ≪≫
        (restrictFunctor _).mapIso (eU i).some ≪≫ restrictFreeIso _ _
  · by_cases hnonneg : n = 0
    · subst n
      refine ⟨P.nonnegRank,
        ⟨R.mapIso (HomologicalComplex.doubleXIso₁ _ _ (by decide)) ≪≫ ?_⟩⟩
      exact restrictCompIso P.nonneg (V j).ι
        (X.homOfLE (show W ≤ V j from inf_le_right)) W.ι
        (X.homOfLE_ι inf_le_right) ≪≫
          (restrictFunctor _).mapIso (eV j).some ≪≫ restrictFreeIso _ _
    · refine ⟨0, ⟨(hzero n hneg hnonneg).iso ?_⟩⟩
      rw [IsZero.iff_id_eq_zero]
      apply (SheafOfModules.freeHomEquiv _).injective
      ext z
      exact Fin.elim0 z.down

private theorem free_model_perfect_tor
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (X : Scheme.{u})
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hb : ∀ i : ℤ, i < -1 ∨ 0 < i → IsZero (K.X i))
    (hf : ∀ i : ℤ, ∃ r : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin r)))) :
    Scheme.IsPerfect X (DerivedCategory.Q.obj K) ∧
      ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ),
        i < -1 ∨ 0 < i → schemeDerivedTensorCohomologyVanishes X
          (DerivedCategory.Q.obj K) M i := by
  constructor
  · intro x
    let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) ⊤
    refine ⟨⊤, trivial, (R.mapHomologicalComplex (.up ℤ)).obj K,
      ⟨⟨-1, 0, fun i hi ↦ R.map_isZero (hb i hi)⟩, ?_⟩,
      ⟨R.mapDerivedCategoryFactors.app K⟩⟩
    intro i
    obtain ⟨r, ⟨e⟩⟩ := hf i
    let e' := R.mapIso e ≪≫
      (SheafOfModules.mapFreeIso R (ULift.{u} (Fin r)) (Iso.refl _)).symm
    exact ⟨r, e'.hom, e'.inv, e'.hom_inv_id⟩
  · have hflat (i : ℤ) : SheafOfModules.IsFlat (K.X i) := by
      obtain ⟨r, ⟨e⟩⟩ := hf i
      exact Scheme.flat_of_finiteFree X (K.X i) r e
    have hK := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
      X.toRingedSpace K ⟨0, fun i hi ↦ hb i (Or.inr hi)⟩ hflat
    intro M i hi
    exact ⟨K, hK, ⟨Iso.refl _⟩,
      Scheme.tensor_homology_isZero_of_term_isZero X K M i (hb i hi)⟩

private theorem perfect_transport
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {X : Scheme.{u}} {L M : schemeDerivedCategory X} (e : L ≅ M)
    (hM : Scheme.IsPerfect X M) : Scheme.IsPerfect X L := by
  intro x
  obtain ⟨U, hxU, K, hK, ⟨eK⟩⟩ := hM x
  exact ⟨U, hxU, K, hK, ⟨(SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso e ≪≫ eK⟩⟩

private theorem perfect_tor_local
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (X : Scheme.{u}) (L : schemeDerivedCategory X)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ M : schemeDerivedCategory U.toScheme,
        Nonempty ((derivedPullback U.ι).obj L ≅ M) ∧
        Scheme.IsPerfect U.toScheme M ∧
        ∀ (F : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (i : ℤ),
          i < -1 ∨ 0 < i → schemeDerivedTensorCohomologyVanishes U.toScheme M F i) :
    Scheme.IsPerfect X L ∧
      ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ),
        i < -1 ∨ 0 < i → schemeDerivedTensorCohomologyVanishes X L M i := by
  constructor
  · apply perfect_of_open_pullbacks L
    intro x
    obtain ⟨U, hxU, M, ⟨e⟩, hM, _⟩ := h x
    exact ⟨U, hxU, perfect_transport e hM⟩
  · apply torAmplitude_of_open_neighbourhoods X L (-1) 0 (by omega)
    intro x
    obtain ⟨U, hxU, M, ⟨e⟩, _, hM⟩ := h x
    refine ⟨U, hxU, fun F i hi ↦ ?_⟩
    apply (tensor_vanishes_iff U.toScheme _ F i).2
    exact ((tensor_vanishes_iff U.toScheme M F i).1 (hM F i hi)).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (tensorIso e (Iso.refl _)))

private theorem perfect_tor_of_twoTerm
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (X : Scheme.{u}) (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :
    Scheme.IsPerfect X L ∧
      ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ),
        i < -1 ∨ 0 < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (L ⊗ (DerivedCategory.singleFunctor _ 0).obj M)) := by
  have hmodel (Y : Scheme.{u}) (P : TwoTermDeterminantModel Y) :
      Scheme.IsPerfect Y (DerivedCategory.Q.obj P.complex) ∧
        ∀ (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (i : ℤ),
          i < -1 ∨ 0 < i → schemeDerivedTensorCohomologyVanishes Y
            (DerivedCategory.Q.obj P.complex) M i := by
    apply perfect_tor_local Y (DerivedCategory.Q.obj P.complex)
    intro y
    obtain ⟨U, hyU, K, hb, hf, eK⟩ := model_local_free P y
    have hK := free_model_perfect_tor U.toScheme K hb hf
    exact ⟨U, hyU, DerivedCategory.Q.obj K, eK, hK⟩
  have h := perfect_tor_local X L (fun x ↦ by
    obtain ⟨U, hxU, P, eP⟩ := hL x
    exact ⟨U, hxU, DerivedCategory.Q.obj P.complex, eP, hmodel U.toScheme P⟩)
  exact ⟨h.1, fun M i hi ↦ (tensor_vanishes_iff X L M i).1 (h.2 M i hi)⟩

private theorem twoTerm_of_perfect_tor
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (X : Scheme.{u}) (L : schemeDerivedCategory X) (hL : Scheme.IsPerfect X L)
    (hTor : ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ),
      i < -1 ∨ 0 < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (L ⊗ (DerivedCategory.singleFunctor _ 0).obj M))) :
    isTwoTermPerfect X L := by
  classical
  intro x
  obtain ⟨_, _, U, hxU, _, K, _, hrank, ⟨eK⟩⟩ :=
    Scheme.exists_finiteFreeResidueModel X L hL x
  let F : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv U).functor
  let P := (F.mapHomologicalComplex (.up ℤ)).obj K
  have hfree (i : ℤ) : Nonempty (P.X i ≅ SheafOfModules.free
      (R := moduleRings U.toScheme.toRingedSpace)
        (ULift.{u} (Fin (Scheme.derivedFiberBetti X L i x)))) :=
    ⟨F.mapIso (hrank i).some ≪≫
      (SheafOfModules.mapFreeIso F _ (Scheme.Modules.overEquivFunctorObjUnitIso U)).symm⟩
  have hzero (i : ℤ) (hi : i ≠ -1) (hi' : i ≠ 0) : IsZero (P.X i) := by
    have hbetti : Scheme.derivedFiberBetti X L i x = 0 :=
      Scheme.derivedFiberBetti_eq_zero_of_tensor_vanishes X L i x (fun M ↦
        (tensor_vanishes_iff X L M i).2 (hTor M i (by omega)))
    obtain ⟨ei⟩ := hfree i
    have hz : IsZero (SheafOfModules.free
        (R := moduleRings U.toScheme.toRingedSpace)
          (ULift.{u} (Fin (Scheme.derivedFiberBetti X L i x)))) := by
      rw [hbetti, IsZero.iff_id_eq_zero]
      apply (SheafOfModules.freeHomEquiv _).injective
      ext z
      exact Fin.elim0 z.down
    exact hz.of_iso ei
  let Q : TwoTermDeterminantModel U.toScheme :=
    { neg := P.X (-1)
      nonneg := P.X 0
      differential := P.d (-1) 0
      negRank := Scheme.derivedFiberBetti X L (-1) x
      nonnegRank := Scheme.derivedFiberBetti X L 0 x
      neg_free := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (hfree (-1)).some.symm
      nonneg_free := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (hfree 0).some.symm }
  obtain ⟨eP⟩ := Scheme.open_model_iso X U L K eK
  obtain ⟨eQ⟩ := complex_twoTerm_iso P hzero
  exact ⟨U, hxU, Q, ⟨eP ≪≫ DerivedCategory.Q.mapIso eQ.symm⟩⟩

/-- Every displayed model satisfies the local two-term condition.
Source: Stacks Project, Tag 0FJX
(blueprint: lem-trf-two-term-perfect-tor-window). -/
theorem twoTermPerfect_model {X : Scheme.{u}} (P : TwoTermDeterminantModel X) :
    isTwoTermPerfect X (DerivedCategory.Q.obj P.complex) := by
  classical
  intro x
  obtain ⟨U, hx, K, hzero, hfree, ⟨e⟩⟩ := model_local_free P x
  choose r hr using hfree
  let Q : TwoTermDeterminantModel U.toScheme :=
    { neg := K.X (-1)
      nonneg := K.X 0
      differential := K.d (-1) 0
      negRank := r (-1)
      nonnegRank := r 0
      neg_free := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (hr (-1)).some.symm
      nonneg_free := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (hr 0).some.symm }
  obtain ⟨eQ⟩ := complex_twoTerm_iso K (fun i hi hi' ↦ hzero i (by omega))
  exact ⟨U, hx, Q, ⟨e ≪≫ DerivedCategory.Q.mapIso eQ.symm⟩⟩

/-- The actual zero complex satisfies the local two-term condition on every scheme.
Source: Stacks Project, Tag 0FJX, rank-zero convention
(blueprint: lem-trf-two-term-perfect-tor-window). -/
theorem twoTermPerfect_zero
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (X : Scheme.{u}) : isTwoTermPerfect X (twoTermDeterminantZeroObject X) := by
  let K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ := 0
  have hb (i : ℤ) : IsZero (K.X i) :=
    (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)
  have hf (i : ℤ) : ∃ r : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin r))) := by
    refine ⟨0, ⟨(hb i).iso ?_⟩⟩
    rw [IsZero.iff_id_eq_zero]
    apply (SheafOfModules.freeHomEquiv _).injective
    ext z
    exact Fin.elim0 z.down
  have hK := free_model_perfect_tor X K (fun i _ ↦ hb i) hf
  apply twoTerm_of_perfect_tor X _ hK.1
  intro M i hi
  exact (tensor_vanishes_iff X (DerivedCategory.Q.obj K) M i).1 (hK.2 M i hi)

/-- Arbitrary derived pullback preserves the two-term locally free condition.
Source: Stacks Project, Tags 09UA and 0FJY
(blueprint: lem-trf-two-term-perfect-tor-window).

Proof: take a finite free residue model at the image of a point. The Tor-window
characterization makes every term outside degrees -1 and 0 free of rank zero.
The localized ordinary pullback preserves free modules and zero objects. Its comparison
with derived pullback gives the required two-term model on the inverse-image open. -/
theorem twoTermPerfect_pullback
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {X Y : Scheme.{u}} (g : Y ⟶ X) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L) : isTwoTermPerfect Y ((derivedPullback g).obj L) := by
  classical
  obtain ⟨hperfect, hTor⟩ := perfect_tor_of_twoTerm X L hL
  intro y
  obtain ⟨_, _, U, hyU, _, K, hKb, hrank, ⟨eK⟩⟩ :=
    Scheme.exists_finiteFreeResidueModel X L hperfect (g y)
  have hstrict : Scheme.IsStrictlyPerfect X U K := by
    refine ⟨hKb, ?_⟩
    intro i
    let e := (hrank i).some
    exact ⟨Scheme.derivedFiberBetti X L i (g y), e.hom, e.inv, e.hom_inv_id⟩
  have hKzero (i : ℤ) (hi : i ≠ -1) (hi' : i ≠ 0) : IsZero (K.X i) := by
    have hbetti : Scheme.derivedFiberBetti X L i (g y) = 0 :=
      Scheme.derivedFiberBetti_eq_zero_of_tensor_vanishes X L i (g y) (fun M ↦
        (tensor_vanishes_iff X L M i).2 (hTor M i (by omega)))
    have hz : IsZero (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U)
          (ULift.{u} (Fin (Scheme.derivedFiberBetti X L i (g y))))) := by
      rw [hbetti, IsZero.iff_id_eq_zero]
      apply (SheafOfModules.freeHomEquiv _).injective
      ext z
      exact Fin.elim0 z.down
    exact hz.of_iso (hrank i).some
  let V := g ⁻¹ᵁ U
  let F := Scheme.Modules.localizedPullback g U
  let A : SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv V).functor
  let P := (F.mapHomologicalComplex (.up ℤ)).obj K
  let R := (A.mapHomologicalComplex (.up ℤ)).obj P
  have hfree (i : ℤ) : Nonempty (R.X i ≅ SheafOfModules.free
      (R := moduleRings V.toScheme.toRingedSpace)
        (ULift.{u} (Fin (Scheme.derivedFiberBetti X L i (g y))))) := by
    obtain ⟨eF⟩ := localizedPullbackFree g U (Scheme.derivedFiberBetti X L i (g y))
    exact ⟨A.mapIso (F.mapIso (hrank i).some ≪≫ eF) ≪≫
      (SheafOfModules.mapFreeIso A _ (Scheme.Modules.overEquivFunctorObjUnitIso V)).symm⟩
  have hzero (i : ℤ) (hi : i ≠ -1) (hi' : i ≠ 0) : IsZero (R.X i) :=
    A.map_isZero (F.map_isZero (hKzero i hi hi'))
  let Q : TwoTermDeterminantModel V.toScheme :=
    { neg := R.X (-1)
      nonneg := R.X 0
      differential := R.d (-1) 0
      negRank := Scheme.derivedFiberBetti X L (-1) (g y)
      nonnegRank := Scheme.derivedFiberBetti X L 0 (g y)
      neg_free := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (hfree (-1)).some.symm
      nonneg_free := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (hfree 0).some.symm }
  obtain ⟨eP⟩ := localizedPullback_perfectModel_iso g U L K hstrict eK
  obtain ⟨eR⟩ := Scheme.open_model_iso Y V ((derivedPullback g).obj L) P eP
  obtain ⟨eQ⟩ := complex_twoTerm_iso R hzero
  exact ⟨V, hyU, Q, ⟨eR ≪≫ DerivedCategory.Q.mapIso eQ.symm⟩⟩

/-- Two-term finite locally free models are exactly perfect objects of Tor amplitude
`[-1,0]`. Source: Stacks Project, Tags 0FJX and 08G7
(blueprint: lem-trf-two-term-perfect-tor-window).

Proof: locally trivialize both terms of a two-term model on a common open refinement.
The resulting finite free complex is strictly perfect and K-flat; tensoring with a module
in degree zero has zero terms outside the two-term interval. Perfectness and the
cohomological vanishings descend from open neighbourhoods. Conversely, take a minimal
finite free residue model at a point. The Tor vanishings make every residue Betti number
outside the interval zero. Those terms are therefore free of rank zero and vanish.
The remaining differential gives the required two-term model. This includes rank zero
and the empty scheme, for which the local assertions are vacuous. -/
theorem isTwoTermPerfect_iff_perfect_tor
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (X : Scheme.{u}) (L : schemeDerivedCategory X) :
    isTwoTermPerfect X L ↔ Scheme.IsPerfect X L ∧
      ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ),
        i < -1 ∨ 0 < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (L ⊗ (DerivedCategory.singleFunctor _ 0).obj M)) := by
  exact ⟨perfect_tor_of_twoTerm X L, fun h ↦ twoTerm_of_perfect_tor X L h.1 h.2⟩

end AlgebraicGeometry
