/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MeromorphicModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Topology.GDelta.Basic
import WeilConjectures.AlgebraicGeometry.PrincipalOpenDenseOfNonZeroDivisor
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.StalkExact

/-!
# The denominator ideal of a regular meromorphic section

Source: Stacks Project, Divisors, Tag 02P0, Lemma 31.24.9
(blueprint: lem-sc-hilbert-denominator-ideal-nowhere-dense).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem denominator_regular (X : Scheme.{v}) (U : X.Opens)
    (b : meromorphicDenominators X U) : b.val ∈ nonZeroDivisors Γ(X, U) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro a ha
  apply TopCat.Presheaf.section_ext X.sheaf U a 0
  intro x hx
  rw [map_zero]
  have hb : X.presheaf.germ U x hx b.val ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    Submonoid.mem_iInf.mp b.property ⟨x, hx⟩
  apply (mem_nonZeroDivisors_iff_right.mp hb)
  change X.presheaf.germ U x hx a * X.presheaf.germ U x hx b.val = 0
  exact ((X.presheaf.germ U x hx).hom.map_mul a b.val).symm.trans
    ((congrArg (X.presheaf.germ U x hx) ha).trans ((X.presheaf.germ U x hx).hom.map_zero))

private theorem denominator_regular_on_invertible (X : Scheme.{v}) (M : X.Modules)
    [M.IsInvertible] (U : X.Opens) (b : meromorphicDenominators X U) :
    IsSMulRegular Γ(M, U) b.val := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro m hm
  apply M.isSheaf.section_ext
  intro x hx
  have := IsInvertible.sheafOfModules_isInvertible M
  obtain ⟨V, hxV, ⟨e⟩⟩ := exists_mem_over_iso_unit M x
  let W := U ⊓ V
  let hWU : W ≤ U := inf_le_left
  let hWV : W ≤ V := inf_le_right
  refine ⟨W, hWU, ⟨hx, hxV⟩, ?_⟩
  rw [map_zero]
  let c := restrictMeromorphicDenominator X (homOfLE hWU) b
  let ee := sectionsLinearEquivOfOverIsoUnit e hWV
  apply ee.injective
  rw [map_zero]
  apply mem_nonZeroDivisors_iff_left.mp (denominator_regular X W c)
  have h : c.val • M.presheaf.map (homOfLE hWU).op m = 0 := by
    change X.presheaf.map (homOfLE hWU).op b.val •
      M.presheaf.map (homOfLE hWU).op m = 0
    have hh := congrArg (M.presheaf.map (homOfLE hWU).op) hm
    simpa only [map_smul, map_zero] using hh
  have hh := congrArg ee h
  simpa only [ee.map_smul, map_zero, smul_eq_mul] using hh

private theorem meromorphic_injective (X : Scheme.{v}) (M : X.Modules) [M.IsInvertible] :
    Mono (toMeromorphicModule X M) := by
  let J := Opens.grothendieckTopology X
  let φ := (SheafOfModules.toSheaf X.ringCatSheaf).map (toMeromorphicModule X M)
  have hloc (U : X.Opensᵒᵖ) :
      Function.Injective (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (meromorphicLocalization X M)).app U) := by
    change Function.Injective
      (LocalizedModule.mkLinearMap (meromorphicDenominators X U.unop) Γ(M, U.unop))
    apply (IsLocalizedModule.injective_iff_isRegular (meromorphicDenominators X U.unop)
      (LocalizedModule.mkLinearMap _ _)).mpr
    exact denominator_regular_on_invertible X M U.unop
  have : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (meromorphicLocalization X M)) :=
    Presheaf.isLocallyInjective_of_injective J _ hloc
  have : Presheaf.IsLocallyInjective J
      (toSheafify J (meromorphicPresheaf X M).presheaf) := by
    dsimp [J]
    infer_instance
  have : Sheaf.IsLocallyInjective φ := by
    change Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (meromorphicLocalization X M) ≫ toSheafify J (meromorphicPresheaf X M).presheaf)
    infer_instance
  exact (SheafOfModules.toSheaf X.ringCatSheaf).mono_of_mono_map
    (Sheaf.mono_of_isLocallyInjective φ)

private theorem section_regular (X : Scheme.{v}) (M : X.Modules)
    (s : unit X ⟶ meromorphicModule X M)
    (hs : Mono (meromorphicSectionMap X M s)) : Mono s := by
  have : (unit X).IsInvertible := by
    change (CategoryTheory.MonoidalCategory.tensorUnit X.Modules).IsInvertible
    infer_instance
  have := meromorphic_injective X (unit X)
  have h : toMeromorphicModule X (unit X) ≫ meromorphicSectionMap X M s = s :=
    (exists_meromorphicSectionMap X M s).exists.choose_spec
  rw [← h]
  infer_instance

private theorem fraction_natural (X : Scheme.{v}) (M : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) (z : LocalizedModule (meromorphicDenominators X U) Γ(M, U)) :
    meromorphicFraction X M V (meromorphicRestriction X M i z) =
      (meromorphicModule X M).presheaf.map i.op (meromorphicFraction X M U z) := by
  exact PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (meromorphicPresheaf X M)) i.op z

private theorem fraction_restrict (X : Scheme.{v}) (M : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) (m : Γ(M, U)) (b : meromorphicDenominators X U) :
    meromorphicRestriction X M i (LocalizedModule.mk m b) =
      LocalizedModule.mk (M.presheaf.map i.op m) (restrictMeromorphicDenominator X i b) :=
  (exists_meromorphicRestriction X M i).choose_spec m b

private theorem ordinary_fraction (X : Scheme.{v}) (M : X.Modules)
    (U : X.Opens) (m : Γ(M, U)) :
    (toMeromorphicModule X M).app U m =
      meromorphicFraction X M U (LocalizedModule.mk m 1) := rfl

private theorem fraction_mul_denominator (X : Scheme.{v}) (M : X.Modules)
    (U : X.Opens) (m : Γ(M, U)) (b : meromorphicDenominators X U) :
    b.val • meromorphicFraction X M U (LocalizedModule.mk m b) =
      (toMeromorphicModule X M).app U m := by
  rw [← (meromorphicFraction X M U).map_smul, ordinary_fraction]
  congr 1
  change b.val • LocalizedModule.mk m b = LocalizedModule.mk m 1
  rw [LocalizedModule.smul'_mk]
  exact LocalizedModule.mk_cancel b m

private theorem fraction_membership (X : Scheme.{v}) (M : X.Modules) [M.IsInvertible]
    (s : unit X ⟶ meromorphicModule X M) (U : X.Opens)
    (m : Γ(M, U)) (b : meromorphicDenominators X U)
    (h : meromorphicFraction X M U (LocalizedModule.mk m b) =
      s.app U (1 : Γ(X, U))) (y : Γ(X, U)) (t : Γ(M, U)) :
    (toMeromorphicModule X M).app U t = s.app U y ↔ b.val • t = y • m := by
  have := meromorphic_injective X M
  have hinj : Function.Injective ((toMeromorphicModule X M).app U) := by
    exact (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map
        (toMeromorphicModule X M))).mp inferInstance
  have hs : s.app U y = y • s.app U (1 : Γ(X, U)) := by
    simpa only [smul_eq_mul, mul_one] using
      (Hom.app_smul s y (1 : Γ(X, U)))
  rw [hs, ← h]
  constructor
  · intro ht
    apply hinj
    rw [Hom.app_smul, Hom.app_smul, ht, smul_comm b.val y,
      fraction_mul_denominator]
  · intro ht
    rw [ordinary_fraction, ← (meromorphicFraction X M U).map_smul]
    congr 1
    rw [LocalizedModule.smul'_mk]
    apply LocalizedModule.mk_eq.mpr
    refine ⟨1, ?_⟩
    simpa only [one_smul, Submonoid.smul_def, OneMemClass.coe_one] using ht

private theorem unit_restrict_one (X : Scheme.{v}) {U V : X.Opens} (i : V ⟶ U) :
    (unit X).presheaf.map i.op (1 : Γ(X, U)) = (1 : Γ(X, V)) :=
  (X.presheaf.map i.op).hom.map_one

private theorem local_fraction (X : Scheme.{v}) (M : X.Modules) [M.IsInvertible]
    (s : unit X ⟶ meromorphicModule X M) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      ∃ (_e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
        (m : Γ(M, U)) (b : meromorphicDenominators X U),
        meromorphicFraction X M U (LocalizedModule.mk m b) = s.app U (1 : Γ(X, U)) := by
  have := IsInvertible.sheafOfModules_isInvertible M
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (meromorphicPresheaf X M)
  let q := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map η
  have hq : TopCat.Presheaf.IsLocallySurjective q := by
    change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (toSheafify _ (meromorphicPresheaf X M).presheaf)
    infer_instance
  obtain ⟨V, hV, ⟨z, hz⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff q).mp hq ⊤ (s.app ⊤ (1 : Γ(X, ⊤))) x trivial
  obtain ⟨m, b, hz⟩ : ∃ (m : Γ(M, V)) (b : meromorphicDenominators X V),
      meromorphicFraction X M V (LocalizedModule.mk m b) =
        (meromorphicModule X M).presheaf.map (homOfLE hV).op (s.app ⊤ (1 : Γ(X, ⊤))) := by
    induction z using LocalizedModule.induction_on with
    | _ m b => exact ⟨m, b, hz⟩
  obtain ⟨U, hxU, hUV, e₀, he₀⟩ := exists_isFreeGenerator M (x := x) hxV
  let e := he₀.overIso
  refine ⟨U.val, hxU, U.property, e, M.presheaf.map (homOfLE hUV).op m,
    restrictMeromorphicDenominator X (homOfLE hUV) b, ?_⟩
  rw [← fraction_restrict, fraction_natural]
  have hz' : meromorphicFraction X M V (LocalizedModule.mk m b) = s.app V (1 : Γ(X, V)) := by
    change meromorphicFraction X M V (LocalizedModule.mk m b) =
      (meromorphicModule X M).presheaf.map (homOfLE hV).op (s.app ⊤ (1 : Γ(X, ⊤))) at hz
    rw [← Hom.app_presheaf_map, unit_restrict_one] at hz
    exact hz
  rw [hz', ← Hom.app_presheaf_map, unit_restrict_one]

private theorem pullback_sections_iff {X : Scheme.{v}} {M N P : X.Modules}
    (f : M ⟶ P) (g : N ⟶ P) (U : X.Opens) (m : Γ(M, U)) :
    (∃ t : Γ(CategoryTheory.Limits.pullback f g, U), Hom.app (pullback.fst f g) U t = m) ↔
      ∃ n : Γ(N, U), Hom.app g U n = Hom.app f U m := by
  let E := (SheafOfModules.evaluation X.ringCatSheaf (op U)) ⋙
    CategoryTheory.forget (ModuleCat Γ(X, U))
  have h : IsPullback (E.map (pullback.fst f g)) (E.map (pullback.snd f g))
      (E.map f) (E.map g) := (IsPullback.of_hasPullback f g).map E
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Hom.app (pullback.snd f g) U t, (ConcreteCategory.congr_hom h.w t).symm⟩
  · rintro ⟨n, hn⟩
    obtain ⟨t, ht, _⟩ := Types.exists_of_isPullback h m n hn.symm
    exact ⟨t, ht⟩

private theorem numerator_regular (X : Scheme.{v}) (M : X.Modules) [M.IsInvertible]
    (s : unit X ⟶ meromorphicModule X M) (hs : Mono s) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (m : Γ(M, U)) (b : meromorphicDenominators X U)
    (h : meromorphicFraction X M U (LocalizedModule.mk m b) =
      s.app U (1 : Γ(X, U))) :
    sectionsLinearEquivOfOverIsoUnit e le_rfl m ∈ nonZeroDivisors Γ(X, U) := by
  let ee := sectionsLinearEquivOfOverIsoUnit e le_rfl
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  have hym : y • m = 0 := by
    apply ee.injective
    rw [map_zero, ee.map_smul]
    exact hy
  have hsy : s.app U y = 0 := by
    have hy' : (toMeromorphicModule X M).app U 0 = s.app U y :=
      (fraction_membership X M s U m b h y 0).mpr (by rw [smul_zero, hym])
    simpa only [map_zero] using hy'.symm
  have hinj : Function.Injective
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map s) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  exact hinj (hsy.trans (map_zero _).symm)

private theorem quotient_membership (A : Type v) [CommRing A] (a b y : A)
    (hb : b ∈ nonZeroDivisors A) :
    (∃ c : A, b * c = y * a) ↔
      ∃ c : A, algebraMap A (Localization (nonZeroDivisors A)) c =
        IsLocalization.mk' (Localization (nonZeroDivisors A)) a ⟨b, hb⟩ *
          algebraMap A (Localization (nonZeroDivisors A)) y := by
  let Q := Localization (nonZeroDivisors A)
  have hinj : Function.Injective (algebraMap A Q) :=
    IsLocalization.injective Q le_rfl
  have h (c : A) : algebraMap A Q c =
      IsLocalization.mk' Q a ⟨b, hb⟩ * algebraMap A Q y ↔ b * c = y * a := by
    rw [mul_comm _ (algebraMap A Q y), IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, hinj.eq_iff, mul_comm c b]
  exact exists_congr fun c ↦ (h c).symm

private theorem local_denominator_description (X : Scheme.{v}) (L : X.Modules)
    [L.IsInvertible] (s : unit X ⟶ meromorphicModule X L) (hs : Mono s) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      ∃ (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
        (a : Γ(X, U)) (b : meromorphicDenominators X U),
        a ∈ nonZeroDivisors Γ(X, U) ∧ ∃ hb : b.val ∈ nonZeroDivisors Γ(X, U),
        meromorphicFraction X L U
          (LocalizedModule.mk ((sectionsLinearEquivOfOverIsoUnit e le_rfl).symm a) b) =
          Hom.app s U (1 : Γ(X, U)) ∧
        ∀ y : Γ(X, U),
          (∃ t : Γ(CategoryTheory.Limits.pullback s (toMeromorphicModule X L), U),
            Hom.app (pullback.fst s (toMeromorphicModule X L)) U t = y) ↔
            ∃ c : Γ(X, U),
              algebraMap Γ(X, U) (Localization (nonZeroDivisors Γ(X, U))) c =
                IsLocalization.mk' (Localization (nonZeroDivisors Γ(X, U))) a
                    ⟨b.val, hb⟩ *
                  algebraMap Γ(X, U) (Localization (nonZeroDivisors Γ(X, U))) y := by
  obtain ⟨U, hx, hU, e, m, b, h⟩ := local_fraction X L s x
  let ee := sectionsLinearEquivOfOverIsoUnit e le_rfl
  refine ⟨U, hx, hU, e, ee m, b, numerator_regular X L s hs U e m b h,
    denominator_regular X U b, ?_, ?_⟩
  · change meromorphicFraction X L U (LocalizedModule.mk (ee.symm (ee m)) b) = _
    simpa only [LinearEquiv.symm_apply_apply] using h
  · intro y
    rw [pullback_sections_iff]
    rw [← quotient_membership]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨ee t, ?_⟩
      have ht' := congrArg ee ((fraction_membership X L s U m b h y t).mp ht)
      simpa only [ee.map_smul, smul_eq_mul] using ht'
    · rintro ⟨c, hc⟩
      refine ⟨ee.symm c, (fraction_membership X L s U m b h y _).mpr ?_⟩
      apply ee.injective
      simpa only [ee.map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul] using hc

private theorem app_injective {X : Scheme.{v}} {M N : X.Modules}
    (f : M ⟶ N) [Mono f] (U : X.Opens) : Function.Injective (f.app U) :=
  (ModuleCat.mono_iff_injective
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f)).mp inferInstance

private theorem pullback_sections_pair {X : Scheme.{v}} {M N P : X.Modules}
    (f : M ⟶ P) (g : N ⟶ P) (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U))
    (h : f.app U m = g.app U n) :
    ∃ t : Γ(CategoryTheory.Limits.pullback f g, U),
      (pullback.fst f g).app U t = m ∧ (pullback.snd f g).app U t = n := by
  let E := (SheafOfModules.evaluation X.ringCatSheaf (op U)) ⋙
    CategoryTheory.forget (ModuleCat Γ(X, U))
  exact Types.exists_of_isPullback ((IsPullback.of_hasPullback f g).map E) m n h

private theorem local_quasicoherent_criterion (X : Scheme.{v}) (L : X.Modules)
    [L.IsInvertible] (s : unit X ⟶ meromorphicModule X L)
    (U : X.Opens) (hU : IsAffineOpen U)
    (m : Γ(L, U)) (b : meromorphicDenominators X U)
    (h : meromorphicFraction X L U (LocalizedModule.mk m b) =
      s.app U (1 : Γ(X, U))) :
    IsLocalizing (modulesSpecToSheaf.obj
      ((CategoryTheory.Limits.pullback s (toMeromorphicModule X L)).restrict hU.fromSpec)) := by
  let I := CategoryTheory.Limits.pullback s (toMeromorphicModule X L)
  let i : I ⟶ unit X := pullback.fst s (toMeromorphicModule X L)
  let j : I ⟶ L := pullback.snd s (toMeromorphicModule X L)
  have := meromorphic_injective X L
  have : Mono i := inferInstance
  have : (unit X).IsQuasicoherent := by
    change (CategoryTheory.MonoidalCategory.tensorUnit X.Modules).IsQuasicoherent
    infer_instance
  apply isLocalizing_restrict_fromSpec_of_forall I hU
  · intro f z
    let D := X.basicOpen f
    let r := homOfLE (X.basicOpen_le f)
    let y : Γ(X, D) := i.app D z
    let t : Γ(L, D) := j.app D z
    have hD : meromorphicFraction X L D
        (LocalizedModule.mk (L.presheaf.map r.op m)
          (restrictMeromorphicDenominator X r b)) = s.app D (1 : Γ(X, D)) := by
      rw [← fraction_restrict, fraction_natural, h, ← Hom.app_presheaf_map,
        unit_restrict_one]
    have hpair : (toMeromorphicModule X L).app D t = s.app D y := by
      exact (ConcreteCategory.congr_hom
        ((SheafOfModules.evaluation X.ringCatSheaf (op D)).congr_map
          (pullback.condition (f := s) (g := toMeromorphicModule X L))) z).symm
    have heq := (fraction_membership X L s D _ _ hD y t).mp hpair
    change X.presheaf.map r.op b.val • t = y • L.presheaf.map r.op m at heq
    obtain ⟨n, y₀, hy₀⟩ := exists_map_eq_pow_smul_of_isAffineOpen (unit X) hU f y
    obtain ⟨k, t₀, ht₀⟩ := exists_map_eq_pow_smul_of_isAffineOpen L hU f t
    change Γ(X, U) at y₀
    change X.presheaf.map r.op y₀ = (X.presheaf.map r.op f) ^ n * y at hy₀
    let Y : Γ(X, U) := f ^ k * y₀
    let T : Γ(L, U) := f ^ n • t₀
    have hY : X.presheaf.map r.op Y = (X.presheaf.map r.op f) ^ (n + k) * y := by
      dsimp only [Y]
      rw [map_mul, hy₀, map_pow, ← mul_assoc, ← pow_add, Nat.add_comm k n]
    have hT : L.presheaf.map r.op T = (X.presheaf.map r.op f) ^ (n + k) • t := by
      rw [map_smul, ht₀, map_pow, smul_smul, ← pow_add]
    have hz : L.presheaf.map r.op (b.val • T - Y • m) = 0 := by
      rw [map_sub]
      simp only [map_smul]
      rw [hY, hT]
      change X.presheaf.map r.op b.val • ((X.presheaf.map r.op f) ^ (n + k) • t) -
        ((X.presheaf.map r.op f) ^ (n + k) • y) • L.presheaf.map r.op m = 0
      rw [smul_comm (X.presheaf.map r.op b.val), heq]
      simp only [smul_eq_mul, mul_smul, sub_self]
    obtain ⟨l, hl⟩ := exists_pow_smul_eq_zero_of_isAffineOpen L hU f
      (b.val • T - Y • m) hz
    have hclear : b.val • (f ^ l • T) = (f ^ l * Y) • m := by
      rw [smul_sub, sub_eq_zero] at hl
      calc
        b.val • (f ^ l • T) = f ^ l • (b.val • T) := smul_comm _ _ _
        _ = f ^ l • (Y • m) := hl
        _ = (f ^ l * Y) • m := (mul_smul _ _ _).symm
    obtain ⟨z₀, hi₀, _⟩ := pullback_sections_pair s (toMeromorphicModule X L) U
      (f ^ l * Y) (f ^ l • T) ((fraction_membership X L s U m b h _ _).mpr hclear).symm
    refine ⟨l + (n + k), z₀, (app_injective i D) ?_⟩
    rw [Hom.app_presheaf_map, hi₀, Hom.app_smul]
    change X.presheaf.map r.op (f ^ l * Y) =
      (X.presheaf.map r.op f) ^ (l + (n + k)) * y
    rw [map_mul, hY, map_pow, ← mul_assoc, ← pow_add]
  · intro f z hz
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen (unit X) hU f
      (i.app U z) (by
        rw [← Hom.app_presheaf_map, hz, map_zero])
    refine ⟨n, (app_injective i U) ?_⟩
    simpa only [Hom.app_smul, map_zero] using hn

private theorem denominator_quasicoherent (X : Scheme.{v}) (L : X.Modules)
    [L.IsInvertible] (s : unit X ⟶ meromorphicModule X L) :
    (CategoryTheory.Limits.pullback s (toMeromorphicModule X L)).IsQuasicoherent := by
  classical
  choose U hx hU e m b h using local_fraction X L s
  apply isQuasicoherent_of_iSup_opensRange_eq_top _ (fun x : X ↦ (hU x).fromSpec)
  · apply eq_top_iff.mpr
    intro x _
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨x, ?_⟩
    simpa only [IsAffineOpen.opensRange_fromSpec] using hx x
  · intro x
    have : IsIso ((CategoryTheory.Limits.pullback s (toMeromorphicModule X L)).restrict
        (hU x).fromSpec).fromTildeΓ :=
      (isIso_fromTildeΓ_iff_isLocalizing _).mpr
        (local_quasicoherent_criterion X L s (U x) (hU x) (m x) (b x) (h x))
    exact presentationOfIsIsoFromTildeΓ _

private theorem cokernel_stalk_zero_of_surjective {X : Scheme.{v}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens)
    (h : ∀ (V : X.Opens), V ≤ U → Function.Surjective (f.app V))
    (x : X) (hx : x ∈ U) : Subsingleton ((cokernel f : X.Modules).presheaf.stalk x) := by
  have hsurj : Function.Surjective ((stalkFunctor x).map f) := by
    intro z
    obtain ⟨V, hxV, n, rfl⟩ := N.presheaf.exists_germ_eq z
    let W := V ⊓ U
    have hxW : x ∈ W := ⟨hxV, hx⟩
    obtain ⟨m, hm⟩ := h W inf_le_right (N.presheaf.map (homOfLE inf_le_left).op n)
    refine ⟨M.presheaf.germ W x hxW m, ?_⟩
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.mapPresheaf
      (M.presheaf.germ W x hxW m) = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change N.presheaf.germ W x hxW (f.app W m) = _
    rw [hm, N.presheaf.germ_res_apply]
  have : Epi ((stalkFunctor x).map f) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr hsurj
  have hz : (stalkFunctor x).map (cokernel.π f) = 0 := by
    apply (cancel_epi ((stalkFunctor x).map f)).mp
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero]
  have hq : Function.Surjective ((stalkFunctor x).map (cokernel.π f)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hq a
  obtain ⟨b, rfl⟩ := hq b
  rw [hz]
  rfl

private theorem fraction_on_subopen (X : Scheme.{v}) (L : X.Modules)
    (s : unit X ⟶ meromorphicModule X L) {U V : X.Opens} (hVU : V ≤ U)
    (m : Γ(L, U)) (b : meromorphicDenominators X U)
    (h : meromorphicFraction X L U (LocalizedModule.mk m b) =
      s.app U (1 : Γ(X, U))) :
    meromorphicFraction X L V
      (LocalizedModule.mk (L.presheaf.map (homOfLE hVU).op m)
        (restrictMeromorphicDenominator X (homOfLE hVU) b)) =
      s.app V (1 : Γ(X, V)) := by
  rw [← fraction_restrict, fraction_natural, h, ← Hom.app_presheaf_map,
    unit_restrict_one]

private theorem denominator_projection_surjective (X : Scheme.{v}) (L : X.Modules)
    [L.IsInvertible] (s : unit X ⟶ meromorphicModule X L)
    (U : X.Opens) (m : Γ(L, U)) (b : meromorphicDenominators X U)
    (h : meromorphicFraction X L U (LocalizedModule.mk m b) =
      s.app U (1 : Γ(X, U))) (V : X.Opens) (hV : V ≤ X.basicOpen b.val) :
    Function.Surjective ((pullback.fst s (toMeromorphicModule X L)).app V) := by
  let hVU := hV.trans (X.basicOpen_le b.val)
  let bV := restrictMeromorphicDenominator X (homOfLE hVU) b
  let mV := L.presheaf.map (homOfLE hVU).op m
  have hb : IsUnit bV.val := by
    have hh := (X.toRingedSpace.isUnit_res_basicOpen b.val).map
      (X.presheaf.map (homOfLE hV).op).hom
    change IsUnit (X.presheaf.map (homOfLE hV).op
      (X.presheaf.map (homOfLE (X.basicOpen_le b.val)).op b.val)) at hh
    rw [← Functor.map_comp_apply] at hh
    exact hh
  intro y
  change Γ(X, V) at y
  rw [pullback_sections_iff]
  refine ⟨hb.unit⁻¹ • (y • mV), ?_⟩
  apply (fraction_membership X L s V mV bV
    (fraction_on_subopen X L s hVU m b h) y _).mpr
  change (hb.unit : Γ(X, V)) • (hb.unit⁻¹ • (y • mV)) = y • mV
  exact smul_inv_smul hb.unit _

private theorem sections_coordinates_natural (X : Scheme.{v}) (L : X.Modules)
    {U V : X.Opens} (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (hVU : V ≤ U) (m : Γ(L, U)) :
    sectionsLinearEquivOfOverIsoUnit e hVU
      (L.presheaf.map (homOfLE hVU).op m) =
      X.presheaf.map (homOfLE hVU).op
        (sectionsLinearEquivOfOverIsoUnit e le_rfl m) := by
  exact PresheafOfModules.naturality_apply e.hom.val
    (Over.homMk (homOfLE hVU) : Over.mk (homOfLE hVU) ⟶ Over.mk (𝟙 U)).op m

private theorem numerator_projection_surjective (X : Scheme.{v}) (L : X.Modules)
    [L.IsInvertible] (s : unit X ⟶ meromorphicModule X L)
    (U : X.Opens) (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (m : Γ(L, U)) (b : meromorphicDenominators X U)
    (h : meromorphicFraction X L U (LocalizedModule.mk m b) =
      s.app U (1 : Γ(X, U))) (V : X.Opens)
    (hV : V ≤ X.basicOpen (sectionsLinearEquivOfOverIsoUnit e le_rfl m)) :
    Function.Surjective ((pullback.snd s (toMeromorphicModule X L)).app V) := by
  let a := sectionsLinearEquivOfOverIsoUnit e le_rfl m
  let hVU := hV.trans (X.basicOpen_le a)
  let bV := restrictMeromorphicDenominator X (homOfLE hVU) b
  let mV := L.presheaf.map (homOfLE hVU).op m
  let ee := sectionsLinearEquivOfOverIsoUnit e hVU
  have ha : IsUnit (X.presheaf.map (homOfLE hVU).op a) := by
    have hh := (X.toRingedSpace.isUnit_res_basicOpen a).map
      (X.presheaf.map (homOfLE hV).op).hom
    change IsUnit (X.presheaf.map (homOfLE hV).op
      (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a)) at hh
    rw [← Functor.map_comp_apply] at hh
    exact hh
  intro t
  let y : Γ(X, V) := ha.unit⁻¹ * (bV.val * ee t)
  have heq : bV.val • t = y • mV := by
    apply ee.injective
    rw [ee.map_smul, ee.map_smul]
    change bV.val * ee t = y * ee mV
    rw [sections_coordinates_natural]
    change bV.val * ee t = ((ha.unit⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) * (bV.val * ee t) * ha.unit
    rw [mul_comm _ (ha.unit : Γ(X, V)), ← mul_assoc, Units.mul_inv, one_mul]
  obtain ⟨z, _, hz⟩ := pullback_sections_pair s (toMeromorphicModule X L) V y t
    ((fraction_membership X L s V mV bV
      (fraction_on_subopen X L s hVU m b h) y t).mpr heq).symm
  exact ⟨z, hz⟩

private theorem regular_basicOpen_dense (X : Scheme.{v}) (U : X.Opens)
    (hU : IsAffineOpen U) (a : Γ(X, U)) (ha : a ∈ nonZeroDivisors Γ(X, U)) :
    (U : Set X) ⊆ closure (X.basicOpen a : Set X) := by
  intro x hx
  let p := hU.primeIdealOf ⟨x, hx⟩
  have hp : p ∈ closure (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Γ(X, U))) :=
    PrimeSpectrum.dense_basicOpen_of_mem_nonZeroDivisors Γ(X, U) a ha p
  have hm := image_closure_subset_closure_image hU.fromSpec.continuous
    (Set.mem_image_of_mem hU.fromSpec hp)
  apply (closure_mono (show hU.fromSpec ''
    (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Γ(X, U))) ⊆
      (X.basicOpen a : Set X) from ?_))
    (by simpa only [p, hU.fromSpec_primeIdealOf] using hm)
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a := by
    rwa [hU.fromSpec_preimage_basicOpen]
  exact hz'

private theorem closed_nowhere_dense_of_local_basicOpen (X : Scheme.{v})
    (F : X.Modules) (U : X → X.Opens) (hx : ∀ x, x ∈ U x)
    (hU : ∀ x, IsAffineOpen (U x)) (a : ∀ x, Γ(X, U x))
    (ha : ∀ x, a x ∈ nonZeroDivisors Γ(X, U x))
    (hF : ∀ x y, y ∈ X.basicOpen (a x) → Subsingleton (F.presheaf.stalk y)) :
    ∃ Z : Set X, IsClosed Z ∧ IsNowhereDense Z ∧
      ∀ x : X, x ∉ Z → Subsingleton (F.presheaf.stalk x) := by
  let W : X.Opens := ⨆ x, X.basicOpen (a x)
  have hd : Dense (W : Set X) := by
    intro x
    exact closure_mono ((show (X.basicOpen (a x) : Set X) ⊆ (W : Set X) from
      le_iSup (fun x ↦ X.basicOpen (a x)) x))
        (regular_basicOpen_dense X (U x) (hU x) (a x) (ha x) (hx x))
  refine ⟨(W : Set X)ᶜ, ?_, ?_, ?_⟩
  · exact W.isOpen.isClosed_compl
  · exact (isClosed_isNowhereDense_iff_compl.mpr (by simpa only [compl_compl] using
      ⟨W.isOpen, hd⟩)).2
  · intro x hx
    have hx' : x ∈ (W : Set X) := not_not.mp hx
    obtain ⟨y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    exact hF y x hy

/-- Source: Stacks Project, Tag 02P0
(blueprint: lem-sc-hilbert-denominator-ideal-nowhere-dense).

1. Locally trivialize L on an affine open. Sheafification gives a local fraction a/b.
Regularity makes a a non-zero-divisor: a scalar annihilating a annihilates s, hence vanishes.
The injection O_X → K_X identifies the denominator ideal with {y | y(a/b) ∈ A}.
2. Localization of that ideal at f gives precisely the denominators of a/b over A_f:
clear a power of f for one inclusion; the reverse inclusion follows by localization.
This proves quasi-coherence.
3. Both maps out of the ideal are injective: the first is inclusion and the second is
multiplication by the regular section. Locally b lies in I and s(b) = a. Consequently the
cokernels are supported inside V(b) and V(a). Non-zero-divisors give dense principal opens
(lem-pc-principal-open-dense-of-nonzerodivisor), so these supports have nowhere-dense
closures. The local assertions glue.

The section s is represented by its O_X-linear map from O_X. The induced map from K_X
is `meromorphicSectionMap`; its monomorphism is exactly regularity. The ideal is the pullback
of L → K_X(L) along s; its projections are the maps denoted 1 and s in the source.
Membership y(a/b) ∈ A is stated in the total ring of fractions
`Localization (nonZeroDivisors A)`, as in lem-sc-hilbert-affine-denominator-module.
Support containment is expressed by vanishing cokernel stalks outside a closed
nowhere-dense set. -/
theorem meromorphic_denominator_ideal_nowhere_dense (X : Scheme.{v}) (L : X.Modules)
    [L.IsInvertible]
    (s : unit X ⟶ meromorphicModule X L)
    (hs : Mono (meromorphicSectionMap X L s)) :
    let I : X.Modules := CategoryTheory.Limits.pullback s (toMeromorphicModule X L)
    let i : I ⟶ unit X := CategoryTheory.Limits.pullback.fst s (toMeromorphicModule X L)
    let j : I ⟶ L := CategoryTheory.Limits.pullback.snd s (toMeromorphicModule X L)
    (∀ (V : X.Opens) (f : Γ(X, V)),
      (∃ t : Γ(I, V), Hom.app i V t = f) ↔
        ∃ t : Γ(L, V), Hom.app (toMeromorphicModule X L) V t = Hom.app s V f) ∧
    (∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      ∃ (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
        (a : Γ(X, U)) (b : meromorphicDenominators X U),
        a ∈ nonZeroDivisors Γ(X, U) ∧ ∃ hb : b.val ∈ nonZeroDivisors Γ(X, U),
        meromorphicFraction X L U
          (LocalizedModule.mk ((sectionsLinearEquivOfOverIsoUnit e le_rfl).symm a) b) =
          Hom.app s U (1 : Γ(X, U)) ∧
        ∀ y : Γ(X, U),
          (∃ t : Γ(I, U), Hom.app i U t = y) ↔
            ∃ c : Γ(X, U),
              algebraMap Γ(X, U) (Localization (nonZeroDivisors Γ(X, U))) c =
                IsLocalization.mk' (Localization (nonZeroDivisors Γ(X, U))) a
                    ⟨b.val, hb⟩ *
                  algebraMap Γ(X, U) (Localization (nonZeroDivisors Γ(X, U))) y) ∧
    SheafOfModules.IsQuasicoherent I ∧ Mono i ∧ Mono j ∧
    (∃ Z : Set X, IsClosed Z ∧ IsNowhereDense Z ∧
      ∀ x : X, x ∉ Z → Subsingleton ((presheaf (cokernel i : X.Modules)).stalk x)) ∧
    (∃ Z : Set X, IsClosed Z ∧ IsNowhereDense Z ∧
      ∀ x : X, x ∉ Z → Subsingleton ((presheaf (cokernel j : X.Modules)).stalk x)) := by
  classical
  have hs' := section_regular X L s hs
  have hg := meromorphic_injective X L
  refine ⟨fun V f ↦ pullback_sections_iff s (toMeromorphicModule X L) V f,
    local_denominator_description X L s hs', denominator_quasicoherent X L s,
    inferInstance, inferInstance, ?_, ?_⟩
  · choose U hx hU e m b h using local_fraction X L s
    apply closed_nowhere_dense_of_local_basicOpen X _ U hx hU
      (fun x ↦ (b x).val) (fun x ↦ denominator_regular X (U x) (b x))
    intro x y hy
    exact cokernel_stalk_zero_of_surjective _ (X.basicOpen (b x).val)
      (denominator_projection_surjective X L s (U x) (m x) (b x) (h x)) y hy
  · choose U hx hU e m b h using local_fraction X L s
    apply closed_nowhere_dense_of_local_basicOpen X _ U hx hU
      (fun x ↦ sectionsLinearEquivOfOverIsoUnit (e x) le_rfl (m x))
      (fun x ↦ numerator_regular X L s hs' (U x) (e x) (m x) (b x) (h x))
    intro x y hy
    exact cokernel_stalk_zero_of_surjective _
      (X.basicOpen (sectionsLinearEquivOfOverIsoUnit (e x) le_rfl (m x)))
      (numerator_projection_surjective X L s (U x) (e x) (m x) (b x) (h x)) y hy

end AlgebraicGeometry.Scheme.Modules
