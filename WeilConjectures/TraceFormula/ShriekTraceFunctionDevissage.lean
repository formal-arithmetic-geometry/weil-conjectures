/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.TraceFormula.ShriekTraceFunction
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar

/-!

# Dévissage of the sheaf–function compatibility along an open–closed decomposition

Let `f : X ⟶ Y` be a morphism with automorphisms `e_X`, `e_Y`, and let `j : U ⟶ X` be an open
immersion with closed complement `i : Z ⟶ X`, both stable under `e_X`. The sheaf–function
compatibility (`ProEtale.CondensedRing.ShriekTraceFunctionAt`) along `j ≫ f` and along `i ≫ f`
gives it along `f` (`ProEtale.CondensedRing.shriekTraceFunctionAt_of_isCompl`).

The proof splits the points of `X` over `ȳ` into those of `U` and those of `Z`, and uses two
inputs, stated here as separate lemmas:

- `ProEtale.CondensedRing.weilStalkSupertrace_weilLowerShriek_eq_add`: the local trace of
  `Rf_!^Weil K` is the sum of those of `R(j ≫ f)_!^Weil j^* K` and `R(i ≫ f)_!^Weil i^* K`. It
  comes from the localization triangle `j_! j^* K ⟶ K ⟶ i_* i^* K ⟶` of Weil objects, the
  compatibility of the Frobenius with its connecting morphism (blueprint
  `prop-trf-trace-additivity-open-closed`, Step 2) and the additivity of the supertrace along the
  long exact sequence of stalks of homology sheaves. It is still `sorry`.
- `ProEtale.CondensedRing.weilStalkSupertrace_weilUpperStar`: the local trace of a pullback
  `g^* K` at `w̄` is the local trace of `K` at `w̄ ≫ g`. It is still `sorry`; its
  model-Frobenius analogue is
  `ProEtale.CondensedRing.WeilBoundedConstructible.trace_stalkFrobenius_weilUpperStar`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y W : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) (eW : W ≅ W)

/-- **Stalks of a pullback of Weil objects** (still `sorry`): for `g : W ⟶ X` with
`e_W ≫ g = g ≫ e_X` and a point `w̄` of `W` of degree `n + 1`,
`t_{n+1}(g^* K; w̄) = t_{n+1}(K; w̄ ≫ g)`. -/
theorem weilStalkSupertrace_weilUpperStar {g : W ⟶ X} (hg : eW.hom ≫ g = g ≫ eX.hom)
    (K : WeilBoundedConstructible ℓ eX.hom) (n : ℕ) (w : frobeniusFixedPoints eW n) :
    weilStalkSupertrace ℓ n w.1 w.2.2 ((weilUpperStar ℓ eW.hom eX.hom g hg).obj K) =
      weilStalkSupertrace ℓ n (frobeniusFixedPointsMap eW eX hg n w).1
        (frobeniusFixedPointsMap eW eX hg n w).2.2 K :=
  sorry

section Points

variable {V : Over (Spec (.of k))} {eV : V ≅ V} {m : V ⟶ X} [Mono m.left]
  (hm : eV.hom ≫ m = m ≫ eX.hom)

include hm in
omit [Finite k] [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- The restriction of an automorphism of finite order to a stable monomorphism has finite
order. -/
lemma exists_powSucc_eq_refl_of_mono (heX : ∃ m : ℕ, eX.powSucc m = Iso.refl X) :
    ∃ m : ℕ, eV.powSucc m = Iso.refl V := by
  obtain ⟨r, hr⟩ := heX
  refine ⟨r, Iso.ext (Over.OverMorphism.ext ?_)⟩
  rw [← cancel_mono m.left, ← Over.comp_left, Iso.powSucc_hom_comp_eq_comp_powSucc_hom eV eX hm r,
    hr]
  simp

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- A point of `X` of degree `n + 1` in the image of a monomorphism `m` stable under `e_X` lifts
to a point of `V` of degree `n + 1`. -/
lemma exists_frobeniusFixedPointsMap_eq {n : ℕ} (x : frobeniusFixedPoints eX n)
    (u : Spec (.of (AlgebraicClosure k)) ⟶ V.left) (hu : u ≫ m.left = x.1) :
    ∃ v : frobeniusFixedPoints eV n, frobeniusFixedPointsMap eV eX hm n v = x := by
  refine ⟨⟨u, ?_, ?_⟩, Subtype.ext hu⟩
  · rw [← Over.w m, ← Category.assoc, hu, x.2.1]
  · rw [← cancel_mono m.left, Category.assoc, ← Over.comp_left,
      Iso.powSucc_hom_comp_eq_comp_powSucc_hom eV eX hm n, Over.comp_left, ← Category.assoc, hu,
      x.2.2, Category.assoc, hu]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The points of `X` over `ȳ` in the image of a monomorphism `m` are the points of `V` over
`ȳ`. -/
lemma bijective_frobeniusFixedPointsMap_fiber {f : X ⟶ Y} (n : ℕ)
    (y : frobeniusFixedPoints eY n) (P : Set (frobeniusFixedPoints eX n))
    (hP : ∀ x, x ∈ P ↔ ∃ u : Spec (.of (AlgebraicClosure k)) ⟶ V.left, u ≫ m.left = x.1) :
    Function.Bijective (fun v : {v : frobeniusFixedPoints eV n // v.1 ≫ (m ≫ f).left = y.1} ↦
      (⟨⟨frobeniusFixedPointsMap eV eX hm n v.1, by
          simpa only [frobeniusFixedPointsMap, Over.comp_left, Category.assoc] using v.2⟩,
        (hP _).2 ⟨v.1.1, rfl⟩⟩ :
        {x : {x : frobeniusFixedPoints eX n // x.1 ≫ f.left = y.1} // x.1 ∈ P})) := by
  constructor
  · intro v₁ v₂ h
    refine Subtype.ext (Subtype.ext ?_)
    have := congrArg (fun x ↦ x.1.1.1) h
    exact (cancel_mono m.left).1 this
  · rintro ⟨⟨x, hx⟩, hxP⟩
    obtain ⟨u, hu⟩ := (hP x).1 hxP
    obtain ⟨v, rfl⟩ := exists_frobeniusFixedPointsMap_eq eX hm x u hu
    exact ⟨⟨v, by simpa only [frobeniusFixedPointsMap, Over.comp_left, Category.assoc] using hx⟩,
      rfl⟩

end Points

variable {U Z : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (eU : U ≅ U) (eZ : Z ≅ Z) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
  {j : U ⟶ X} {i : Z ⟶ X} [IsOpenImmersion j.left] [IsClosedImmersion i.left]
  (hj : eU.hom ≫ j = j ≫ eX.hom) (hi : eZ.hom ≫ i = i ≫ eX.hom)

/-- **Additivity of the local trace along an open–closed decomposition** (still `sorry`): for
an open immersion `j` with closed complement `i`, both stable under `e_X`,
`t(Rf_! K; ȳ) = t(R(j ≫ f)_! j^* K; ȳ) + t(R(i ≫ f)_! i^* K; ȳ)`. -/
theorem weilStalkSupertrace_weilLowerShriek_eq_add
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : WeilBoundedConstructible ℓ eX.hom) (n : ℕ) (y : frobeniusFixedPoints eY n) :
    weilStalkSupertrace ℓ n y.1 y.2.2 ((weilLowerShriek ℓ eX eY hf).obj K) =
      weilStalkSupertrace ℓ n y.1 y.2.2
          ((weilLowerShriek ℓ eU eY (comp_comm_of_comp_comm eU eY eX hj hf)).obj
            ((weilUpperStar ℓ eU.hom eX.hom j hj).obj K)) +
        weilStalkSupertrace ℓ n y.1 y.2.2
          ((weilLowerShriek ℓ eZ eY (comp_comm_of_comp_comm eZ eY eX hi hf)).obj
            ((weilUpperStar ℓ eZ.hom eX.hom i hi).obj K)) :=
  sorry

/-- **Dévissage along an open–closed decomposition**: the sheaf–function compatibility along
`j ≫ f` and along `i ≫ f` gives it along `f`, for an automorphism `e_X` of finite order. -/
theorem shriekTraceFunctionAt_of_isCompl
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (heX : ∃ m : ℕ, eX.powSucc m = Iso.refl X)
    (HU : ShriekTraceFunctionAt ℓ eU eY (comp_comm_of_comp_comm eU eY eX hj hf))
    (HZ : ShriekTraceFunctionAt ℓ eZ eY (comp_comm_of_comp_comm eZ eY eX hi hf)) :
    ShriekTraceFunctionAt ℓ eX eY hf := by
  intro K n y
  rw [weilStalkSupertrace_weilLowerShriek_eq_add ℓ eX eY eU eZ hf hj hi hcompl K n y, HU, HZ]
  simp only [weilStalkSupertrace_weilUpperStar]
  classical
  have := finite_frobeniusFixedPoints_of_powSucc_eq_refl eX heX n
  have := finite_frobeniusFixedPoints_of_powSucc_eq_refl eU
    (exists_powSucc_eq_refl_of_mono eX hj heX) n
  have := finite_frobeniusFixedPoints_of_powSucc_eq_refl eZ
    (exists_powSucc_eq_refl_of_mono eX hi heX) n
  let := Fintype.ofFinite (frobeniusFixedPoints eX n)
  let := Fintype.ofFinite (frobeniusFixedPoints eU n)
  let := Fintype.ofFinite (frobeniusFixedPoints eZ n)
  simp only [finsum_eq_sum_of_fintype]
  let P : Set (frobeniusFixedPoints eX n) := {x | x.1.base default ∈ Set.range j.left.base}
  have hPU : ∀ x, x ∈ P ↔ ∃ u : Spec (.of (AlgebraicClosure k)) ⟶ U.left, u ≫ j.left = x.1 := by
    intro x
    refine ⟨fun hx ↦ ⟨IsOpenImmersion.lift j.left x.1 ?_, IsOpenImmersion.lift_fac _ _ _⟩, ?_⟩
    · rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    · rintro ⟨u, hu⟩
      exact ⟨u.base default, by rw [← hu]; rfl⟩
  have hPZ : ∀ x, x ∈ Pᶜ ↔ ∃ z : Spec (.of (AlgebraicClosure k)) ⟶ Z.left, z ≫ i.left = x.1 := by
    intro x
    have hrange : x.1.base default ∈ Set.range i.left.base ↔ x ∈ Pᶜ := by
      rw [Set.mem_compl_iff, Set.mem_ofPred_eq, ← Set.mem_compl_iff, hcompl.compl_eq.symm]
    rw [← hrange]
    refine ⟨fun hx ↦ ⟨IsClosedImmersion.lift i.left x.1 ?_, IsClosedImmersion.lift_fac _ _ _⟩, ?_⟩
    · rw [Scheme.IdealSheafData.le_ker_iff_range_subset_support, Scheme.Hom.support_ker,
        i.left.isClosedMap.isClosed_range.closure_eq]
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    · rintro ⟨z, hz⟩
      exact ⟨z.base default, by rw [← hz]; rfl⟩
  rw [← Fintype.sum_subtype_add_sum_subtype
    (p := fun x : {x : frobeniusFixedPoints eX n // x.1 ≫ f.left = y.1} ↦ x.1 ∈ P)
    (f := fun x ↦ weilStalkSupertrace ℓ n x.1.1 x.1.2.2 K)]
  congr 1
  · exact Fintype.sum_bijective _ (bijective_frobeniusFixedPointsMap_fiber eX eY hj n y P hPU)
      (fun v ↦ weilStalkSupertrace ℓ n (frobeniusFixedPointsMap eU eX hj n v.1).1
        (frobeniusFixedPointsMap eU eX hj n v.1).2.2 K)
      (fun x ↦ weilStalkSupertrace ℓ n x.1.1.1 x.1.1.2.2 K) fun _ ↦ rfl
  · exact Fintype.sum_bijective _ (bijective_frobeniusFixedPointsMap_fiber eX eY hi n y Pᶜ hPZ)
      (fun v ↦ weilStalkSupertrace ℓ n (frobeniusFixedPointsMap eZ eX hi n v.1).1
        (frobeniusFixedPointsMap eZ eX hi n v.1).2.2 K)
      (fun x ↦ weilStalkSupertrace ℓ n x.1.1.1 x.1.1.2.2 K) fun _ ↦ rfl

end AlgebraicGeometry.ProEtale.CondensedRing
