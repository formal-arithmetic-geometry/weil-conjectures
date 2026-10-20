/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits
import WeilConjectures.CategoryTheory.Abelian.Filtration
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Enough injectives for strict finite filtered objects

Source: Stacks Project, `derived.tex`, Tags 05TR and 05TS
(blueprint: lem-trf-enough-strict-filtered-injectives).

The first clause is proved componentwise after splitting a finite filtered
injective into its injective graded pieces (the split description is the
statement of `lem-trf-injective-graded-filtration-splits`).  Strictness makes
the induced maps on the successive quotients monomorphisms, so the ordinary
injective extension property applies to each component.  Under
`EnoughInjectives`, the second clause embeds each quotient into an injective,
assembles the finite biproduct with the split filtration, and checks
monicity and strictness by the last nonzero coordinate and the lower-coordinate
projection.  The same construction gives the prescribed interval bounds,
including the zero and one-step cases.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem finite_bounds (X : FilteredObject C) (h : X.filtration.IsFinite) :
    ∃ a b : ℤ, a ≤ b ∧ X.filtration.step a = ⊤ ∧
      X.filtration.step (b + 1) = ⊥ := by
  obtain ⟨a, m, ha, hm⟩ := h
  refine ⟨a, max a m, le_max_left _ _, ha, le_antisymm ?_ bot_le⟩
  rw [← hm]
  exact X.filtration.antitone_step (by omega)

private theorem strict_factors {X Y : C} (u : X ⟶ Y) [Mono u]
    (S : Subobject X) (T : Subobject Y)
    (hs : imageSubobject (S.arrow ≫ u) = imageSubobject u ⊓ T)
    {Z : C} (z : Z ⟶ X) (hz : T.Factors (z ≫ u)) : S.Factors z := by
  have hf : (Subobject.mk (S.arrow ≫ u)).Factors (z ≫ u) := by
    rw [← imageSubobject_mono, hs, Subobject.inf_factors]
    exact ⟨imageSubobject_factors_comp_self u z, hz⟩
  obtain ⟨l, hl⟩ := (Subobject.mk_factors_iff _ _).mp hf
  have hl' : l ≫ S.arrow = z :=
    (cancel_mono u).mp (by simpa only [MonoOver.mk_arrow, Category.assoc] using hl)
  rw [← hl']
  exact Subobject.factors_comp_arrow l

private theorem strict_quotient_mono {X Y : C} (u : X ⟶ Y) [Mono u]
    (S : Subobject X) (T : Subobject Y)
    (hs : imageSubobject (S.arrow ≫ u) = imageSubobject u ⊓ T)
    (l : (S : C) ⟶ (T : C)) (hl : l ≫ T.arrow = S.arrow ≫ u) :
    Mono (cokernel.map S.arrow T.arrow l u hl.symm) := by
  have hp : IsPullback S.arrow l u T.arrow := by
    apply IsPullback.of_isLimit (c := PullbackCone.mk S.arrow l hl.symm)
    apply PullbackCone.IsLimit.mk _
      (fun s ↦ S.factorThru s.fst (strict_factors u S T hs s.fst
        ((Subobject.factors_iff _ _).mpr ⟨s.snd, s.condition.symm⟩)))
    · intro s
      exact Subobject.factorThru_arrow _ _ _
    · intro s
      apply (cancel_mono T.arrow).mp
      simp only [Category.assoc, hl, Subobject.factorThru_arrow_assoc]
      exact s.condition
    · intro s m hm hn
      apply (cancel_mono S.arrow).mp
      simpa only [Subobject.factorThru_arrow] using hm
  exact Abelian.mono_cokernel_map_of_isPullback hp

private theorem finiteBiproduct {K : Type} [Finite K] (J : K → C) : HasBiproduct J :=
  HasBiproduct.of_hasProduct J

attribute [local instance] finiteBiproduct

private theorem fromSubtype_mono {K : Type} (J : K → C) [Finite K] (P : K → Prop) :
    Mono (biproduct.fromSubtype J P) :=
  mono_of_mono_fac (biproduct.fromSubtype_toSubtype J P)

private noncomputable def tail {K : Type} [Finite K] (J : K → C) (d : K → ℤ)
    (p : ℤ) : Subobject (⨁ J) :=
  imageSubobject (biproduct.fromSubtype J (fun n ↦ p ≤ d n))

private theorem tail_factors {K : Type} [Finite K] (J : K → C) (d : K → ℤ)
    (p : ℤ) {Z : C} (z : Z ⟶ ⨁ J) :
    (tail J d p).Factors z ↔ ∀ n, d n < p → z ≫ biproduct.π J n = 0 := by
  classical
  have := fromSubtype_mono J (fun n ↦ p ≤ d n)
  rw [tail, imageSubobject_mono, Subobject.mk_factors_iff]
  constructor
  · rintro ⟨l, rfl⟩ n hn
    simp [biproduct.fromSubtype_π, not_le.mpr hn]
  · intro h
    refine ⟨z ≫ biproduct.toSubtype J (fun n ↦ p ≤ d n), ?_⟩
    apply biproduct.hom_ext
    intro n
    by_cases hn : p ≤ d n
    · simp [Category.assoc, hn]
    · simp [Category.assoc, hn, h n (lt_of_not_ge hn)]

private noncomputable def splitFiltration {K : Type} [Finite K] (J : K → C)
    (d : K → ℤ) : DecreasingFiltration (⨁ J) where
  F := tail J d
  F_succ_le p := by
    apply Subobject.le_of_factors
    apply (tail_factors J d p _).mpr
    intro n hn
    exact (tail_factors J d (p + 1) _).mp
      (Subobject.factors_self _) n (by omega)

private theorem tail_injective {K : Type} [Finite K] (J : K → C) (d : K → ℤ)
    (hJ : ∀ n, Injective (J n)) (p : ℤ) : Injective (tail J d p : C) := by
  have : ∀ n : {n // p ≤ d n}, Injective ((Subtype.restrict (fun n ↦ p ≤ d n) J) n) :=
    fun n ↦ hJ n.1
  have hm := fromSubtype_mono J (fun n ↦ p ≤ d n)
  exact Injective.of_iso
    ((imageSubobjectIso _ ≪≫ imageMonoIsoSource _).symm) inferInstance

private theorem splitFiltration_injective {K : Type} [Finite K] (J : K → C) (d : K → ℤ)
    (hJ : ∀ n, Injective (J n)) (p : ℤ) :
    Injective ((splitFiltration J d).gradedPiece p) := by
  let f := Subobject.ofLE ((splitFiltration J d).step (p + 1))
    ((splitFiltration J d).step p) ((splitFiltration J d).F_succ_le p)
  let S := ShortComplex.cokernelSequence f
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      mono_f := by dsimp [S, ShortComplex.cokernelSequence, f]; infer_instance }
  have : Injective S.X₁ := tail_injective J d hJ (p + 1)
  have : Injective S.X₂ := tail_injective J d hJ p
  exact (show Retract S.X₃ S.X₂ from
    { i := hS.splittingOfInjective.s
      r := S.g
      retract := hS.splittingOfInjective.s_g }).injective

private theorem subobject_factors_iff_cokernel {A Z : C} (S : Subobject A) (z : Z ⟶ A) :
    S.Factors z ↔ z ≫ cokernel.π S.arrow = 0 := by
  constructor
  · intro h
    rw [← S.factorThru_arrow z h, Category.assoc, cokernel.condition, comp_zero]
  · intro h
    rw [← Abelian.monoLift_comp S.arrow z h]
    exact Subobject.factors_comp_arrow _

private theorem strict_of_factors {A B : C} (v : A ⟶ B) [Mono v]
    (S : Subobject A) (T : Subobject B) (hv : T.Factors (S.arrow ≫ v))
    (hreflect : ∀ {Z : C} (z : Z ⟶ A), T.Factors (z ≫ v) → S.Factors z) :
    imageSubobject (S.arrow ≫ v) = imageSubobject v ⊓ T := by
  apply le_antisymm
  · exact le_inf (imageSubobject_comp_le _ _) (imageSubobject_le _
      (T.factorThru _ hv) (T.factorThru_arrow _ hv))
  · apply Subobject.le_of_factors
    have hleft : (Subobject.mk v).Factors (imageSubobject v ⊓ T).arrow := by
      rw [← imageSubobject_mono v]
      exact Subobject.inf_arrow_factors_left _ _
    obtain ⟨z, hz⟩ := (Subobject.mk_factors_iff _ _).mp hleft
    dsimp only [MonoOver.mk_arrow] at hz
    have hright : T.Factors (z ≫ v) := by
      rw [hz]
      exact Subobject.inf_arrow_factors_right _ _
    have hS := hreflect z hright
    have hf : (Subobject.mk (S.arrow ≫ v)).Factors (imageSubobject v ⊓ T).arrow := by
      apply (Subobject.mk_factors_iff _ _).mpr
      exact ⟨S.factorThru z hS, by
        dsimp only [MonoOver.mk_arrow]
        rw [← Category.assoc, S.factorThru_arrow, hz]⟩
    rwa [← imageSubobject_mono (S.arrow ≫ v)] at hf

private theorem tail_top {K : Type} [Finite K] (J : K → C) (d : K → ℤ)
    (p : ℤ) (h : ∀ n, p ≤ d n) : tail J d p = ⊤ := by
  apply top_unique
  apply Subobject.le_of_factors
  exact (tail_factors J d p _).mpr (fun n hn ↦ False.elim (by have := h n; omega))

private theorem tail_bot {K : Type} [Finite K] (J : K → C) (d : K → ℤ)
    (p : ℤ) (h : ∀ n, d n < p) : tail J d p = ⊥ := by
  apply le_antisymm _ bot_le
  apply Subobject.le_of_factors
  apply (Subobject.bot_factors_iff_zero _).mpr
  apply biproduct.hom_ext
  intro n
  simpa using (tail_factors J d p _).mp (Subobject.factors_self _) n (h n)

private theorem bounded_embedding [EnoughInjectives C] (X : FilteredObject C)
    (a b : ℤ) (hab : a ≤ b) (ha : X.filtration.step a = ⊤)
    (hb : X.filtration.step (b + 1) = ⊥) :
    ∃ (I : FilteredObject C) (v : X ⟶ I),
      Mono v.hom ∧
      (∀ p : ℤ, imageSubobject ((X.filtration.step p).arrow ≫ v.hom) =
        imageSubobject v.hom ⊓ I.filtration.step p) ∧
      (∀ p : ℤ, Injective (I.filtration.gradedPiece p)) ∧
      I.filtration.step a = ⊤ ∧ I.filtration.step (b + 1) = ⊥ := by
  classical
  let K := Set.Icc a b
  let J : K → C := fun n ↦ Injective.under (cokernel (X.filtration.step (n.1 + 1)).arrow)
  let I : FilteredObject C := ⟨⨁ J, splitFiltration J Subtype.val⟩
  let v₀ : X.obj ⟶ I.obj := biproduct.lift (fun n ↦
    cokernel.π (X.filtration.step (n.1 + 1)).arrow ≫ Injective.ι _)
  have hvπ (n : K) : v₀ ≫ biproduct.π J n =
      cokernel.π (X.filtration.step (n.1 + 1)).arrow ≫ Injective.ι _ :=
    biproduct.lift_π _ _
  have hfiltered (p : ℤ) : (I.filtration.step p).Factors
      ((X.filtration.step p).arrow ≫ v₀) := by
    apply (tail_factors J Subtype.val p _).mpr
    intro n hn
    rw [Category.assoc, hvπ, ← Category.assoc]
    have hle := X.filtration.antitone_step (show n.1 + 1 ≤ p by omega)
    rw [← Subobject.ofLE_arrow hle]
    simp only [Category.assoc, cokernel.condition_assoc, zero_comp, comp_zero]
  let v : X ⟶ I := ⟨v₀, fun p ↦ ⟨_, (I.filtration.step p).factorThru_arrow _
    (hfiltered p)⟩⟩
  have hmono : Mono v₀ := by
    let n : K := ⟨b, hab, le_rfl⟩
    have hzero : (X.filtration.step (n.1 + 1)).arrow = 0 := by
      dsimp [n]
      apply (Subobject.bot_factors_iff_zero _).mp
      rw [← hb]
      exact Subobject.factors_self _
    have := cokernel.π_of_zero hzero
    exact mono_of_mono_fac (hvπ n)
  refine ⟨I, v, hmono, ?_, ?_, ?_, ?_⟩
  · intro p
    apply strict_of_factors v₀ _ _ (hfiltered p)
    intro Z z hz
    by_cases hp : p ≤ a
    · have htop : X.filtration.step p = ⊤ := by
        apply top_unique
        rw [← ha]
        exact X.filtration.antitone_step hp
      rw [htop]
      exact Subobject.top_factors z
    · have htail := (tail_factors J Subtype.val p _).mp hz
      by_cases hpb : p ≤ b + 1
      · let n : K := ⟨p - 1, by omega, by omega⟩
        have hzπ := htail n (by dsimp [n]; omega)
        rw [Category.assoc, hvπ] at hzπ
        have hzq : z ≫ cokernel.π (X.filtration.step (n.1 + 1)).arrow = 0 :=
          (cancel_mono (Injective.ι _)).mp (by simpa [Category.assoc] using hzπ)
        have hn : n.1 + 1 = p := by dsimp [n]; omega
        rw [hn] at hzq
        exact (subobject_factors_iff_cokernel _ _).mpr hzq
      · let n : K := ⟨b, hab, le_rfl⟩
        have hzπ := htail n (by dsimp [n]; omega)
        rw [Category.assoc, hvπ] at hzπ
        have hzero : (X.filtration.step (n.1 + 1)).arrow = 0 := by
          dsimp [n]
          apply (Subobject.bot_factors_iff_zero _).mp
          rw [← hb]
          exact Subobject.factors_self _
        have := cokernel.π_of_zero hzero
        have hzq : z ≫ cokernel.π (X.filtration.step (n.1 + 1)).arrow = 0 :=
          (cancel_mono (Injective.ι _)).mp (by simpa [Category.assoc] using hzπ)
        have hz0 : z = 0 := (cancel_mono (cokernel.π (X.filtration.step (n.1 + 1)).arrow)).mp
          (by simpa only [zero_comp] using hzq)
        rw [hz0]
        exact Subobject.factors_zero
  · exact splitFiltration_injective J Subtype.val (fun _ ↦ inferInstance)
  · exact tail_top J Subtype.val a (fun n ↦ n.2.1)
  · exact tail_bot J Subtype.val (b + 1) (fun n ↦ by have := n.2.2; omega)

omit [Abelian C] in
private theorem iso_map_factors {A B Z : C} (e : A ≅ B) (S : Subobject A)
    (z : Z ⟶ A) : ((Subobject.map e.hom).obj S).Factors (z ≫ e.hom) ↔ S.Factors z := by
  have heq : (Subobject.map e.hom).obj S = Subobject.mk (S.arrow ≫ e.hom) := by
    rw [← Subobject.map_mk, Subobject.mk_arrow]
  rw [heq, Subobject.mk_factors_iff]
  constructor
  · rintro ⟨l, hl⟩
    have h : l ≫ S.arrow = z := (cancel_mono e.hom).mp (by
      simpa only [MonoOver.mk_arrow, Category.assoc] using hl)
    rw [← h]
    exact Subobject.factors_comp_arrow _
  · intro h
    refine ⟨S.factorThru z h, ?_⟩
    dsimp only [MonoOver.mk_arrow]
    rw [← Category.assoc, S.factorThru_arrow]

private theorem filtered_extension {X Y I : FilteredObject C}
    (hI : I.filtration.IsFinite) (u : X ⟶ Y) [Mono u.hom]
    (hu : ∀ p : ℤ, imageSubobject ((X.filtration.step p).arrow ≫ u.hom) =
      imageSubobject u.hom ⊓ Y.filtration.step p)
    (hinj : ∀ p : ℤ, Injective (I.filtration.gradedPiece p))
    (f : X ⟶ I) : ∃ g : Y ⟶ I, u ≫ g = f := by
  classical
  obtain ⟨a, b, hab, ha, hb⟩ := finite_bounds I hI
  obtain ⟨J, hJ, _, θ, hθ⟩ := injective_graded_filtration_splits I a b hab ha hb
    (fun n ↦ hinj n.1)
  have hθ' (p : ℤ) : (Subobject.map θ.hom).obj (I.filtration.step p) =
      tail J Subtype.val p := hθ p
  have hf (p : ℤ) : (tail J Subtype.val p).Factors
      (((X.filtration.step p).arrow ≫ f.hom) ≫ θ.hom) := by
    rw [← hθ']
    apply (iso_map_factors θ _ _).mpr
    obtain ⟨l, hl⟩ := f.preserves p
    rw [← hl]
    exact Subobject.factors_comp_arrow _
  have hzero (n : Set.Icc a b) : (X.filtration.step (n.1 + 1)).arrow ≫
      (f.hom ≫ θ.hom ≫ biproduct.π J n) = 0 := by
    simpa only [Category.assoc] using
      (tail_factors J Subtype.val (n.1 + 1) _).mp (hf (n.1 + 1)) n (by omega)
  have hext (n : Set.Icc a b) : ∃ g : Y.obj ⟶ J n,
      u.hom ≫ g = f.hom ≫ θ.hom ≫ biproduct.π J n ∧
      (Y.filtration.step (n.1 + 1)).arrow ≫ g = 0 := by
    obtain ⟨l, hl⟩ := u.preserves (n.1 + 1)
    let q := cokernel.map (X.filtration.step (n.1 + 1)).arrow
      (Y.filtration.step (n.1 + 1)).arrow l u.hom hl.symm
    have : Mono q := strict_quotient_mono u.hom _ _ (hu (n.1 + 1)) l hl
    have : Injective (J n) := hJ n
    let fbar := cokernel.desc (X.filtration.step (n.1 + 1)).arrow
      (f.hom ≫ θ.hom ≫ biproduct.π J n) (hzero n)
    obtain ⟨gbar, hgbar⟩ := Injective.factors fbar q
    refine ⟨cokernel.π (Y.filtration.step (n.1 + 1)).arrow ≫ gbar, ?_, by simp⟩
    have hq : u.hom ≫ cokernel.π (Y.filtration.step (n.1 + 1)).arrow =
        cokernel.π (X.filtration.step (n.1 + 1)).arrow ≫ q := by
      dsimp [q]
      simp
    rw [← Category.assoc, hq, Category.assoc, hgbar]
    exact cokernel.π_desc _ _ _
  choose gs hgs hzgs using hext
  let g₀ : Y.obj ⟶ ⨁ J := biproduct.lift gs
  have hgfiltered (p : ℤ) : (I.filtration.step p).Factors
      ((Y.filtration.step p).arrow ≫ g₀ ≫ θ.inv) := by
    apply (iso_map_factors θ _ _).mp
    rw [hθ']
    apply (tail_factors J Subtype.val p _).mpr
    intro n hn
    dsimp [g₀]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.lift_π]
    have hle := Y.filtration.antitone_step (show n.1 + 1 ≤ p by omega)
    rw [← Subobject.ofLE_arrow hle, Category.assoc, hzgs n, comp_zero]
  let g : Y ⟶ I := ⟨g₀ ≫ θ.inv, fun p ↦
    ⟨_, (I.filtration.step p).factorThru_arrow _ (hgfiltered p)⟩⟩
  refine ⟨g, ?_⟩
  have hcomp : u.hom ≫ g₀ = f.hom ≫ θ.hom := by
    apply biproduct.hom_ext
    intro n
    simpa only [g₀, Category.assoc, biproduct.lift_π] using hgs n
  have heq : u.hom ≫ (g₀ ≫ θ.inv) = f.hom := by
    rw [← Category.assoc, hcomp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (⟨u.hom ≫ (g₀ ≫ θ.inv), _⟩ : Hom X I) = f
  cases f
  congr 1

set_option linter.unusedVariables false in
/-- Finite filtered objects have enough filtered injectives for strict monomorphisms.
Source: Stacks Project, `derived.tex`, Tags 05TR and 05TS
(blueprint: lem-trf-enough-strict-filtered-injectives).

Proof plan:
1. Split a finite filtered injective into a finite biproduct of injective graded
   pieces using `lem-trf-injective-graded-filtration-splits`; the component of a
   filtered map to the `n`-th summand kills the next filtration step.
2. Strictness identifies the kernel of the map on each quotient
   `X/F^(n+1)X → Y/F^(n+1)Y` with zero, so the component factors through a
   monomorphism of quotients.
3. Extend each component by ordinary injectivity and assemble the finite
   biproduct map; the decreasing filtration makes all components below the
   filtration index vanish, so the result is filtered.
4. Assuming `EnoughInjectives`, embed every quotient of a finite filtered object
   into an injective, and use their finite biproduct with the split filtration.
5. The final coordinate proves monicity; the projection to coordinates below a
   given index has kernel exactly the corresponding filtration step, proving
   strictness and preserving the prescribed bounds. -/
theorem enough_strict_filtered_injectives :
    (∀ {X Y I : FilteredObject C}
      (hX : X.filtration.IsFinite) (hY : Y.filtration.IsFinite)
      (hI : I.filtration.IsFinite) (u : X ⟶ Y) [Mono u.hom],
      (∀ p : ℤ,
        imageSubobject ((X.filtration.step p).arrow ≫ u.hom) =
          imageSubobject u.hom ⊓ Y.filtration.step p) →
      (∀ p : ℤ, Injective (I.filtration.gradedPiece p)) →
      ∀ f : X ⟶ I, ∃ g : Y ⟶ I, u ≫ g = f) ∧
    (EnoughInjectives C →
      ∀ X : FilteredObject C,
        X.filtration.IsFinite →
        ∃ (I : FilteredObject C) (v : X ⟶ I),
          I.filtration.IsFinite ∧ Mono v.hom ∧
            (∀ p : ℤ,
              imageSubobject ((X.filtration.step p).arrow ≫ v.hom) =
                imageSubobject v.hom ⊓ I.filtration.step p) ∧
            (∀ p : ℤ, Injective (I.filtration.gradedPiece p))) ∧
    (EnoughInjectives C →
      ∀ (X : FilteredObject C) (a b : ℤ), a ≤ b →
        X.filtration.step a = ⊤ → X.filtration.step (b + 1) = ⊥ →
        ∃ (I : FilteredObject C) (v : X ⟶ I),
          Mono v.hom ∧
            (∀ p : ℤ,
              imageSubobject ((X.filtration.step p).arrow ≫ v.hom) =
                imageSubobject v.hom ⊓ I.filtration.step p) ∧
            (∀ p : ℤ, Injective (I.filtration.gradedPiece p)) ∧
            I.filtration.step a = ⊤ ∧ I.filtration.step (b + 1) = ⊥) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y I _ _ hI u _ hu hinj f
    exact filtered_extension hI u hu hinj f
  · intro h X hX
    obtain ⟨a, b, hab, ha, hb⟩ := finite_bounds X hX
    obtain ⟨I, v, hv, hs, hi, hIa, hIb⟩ := bounded_embedding X a b hab ha hb
    exact ⟨I, v, ⟨a, b + 1, hIa, hIb⟩, hv, hs, hi⟩
  · intro h X a b hab ha hb
    exact bounded_embedding X a b hab ha hb

end CategoryTheory.FilteredObject

end
