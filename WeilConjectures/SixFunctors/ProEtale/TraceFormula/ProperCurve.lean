/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds

/-!
# The trace formula on proper smooth curves

The trace formula for a Weil complex whose model `X₀` is a proper smooth curve over `k`, such as
the projective line: the Lefschetz–Verdier formula
(`GeometricOperations.trace_globalOperator_eq_sum_localTerm`) on the proper `X` writes the trace
of the global operator as a sum of local terms over the components of the fixed scheme of `Φ_m`,
which are the points of `X₀(𝐅_{q^m})`, and the Frobenius local terms on a smooth curve
(`GeometricOperations.localTerm_traceClass_eq_trace`) are the stalk traces. This is the part of
Step 2 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula` that takes place
on `ℙ¹`.

## Main results

- `AlgebraicGeometry.specMap_comp_injective_of_field`,
  `AlgebraicGeometry.eq_of_comp_eq_id_of_base_eq`: morphisms out of the spectrum of a field
  are determined after a field extension, and sections over a field by their point.
- `WeilComplex.IsModelFrobenius.exists_fixedPoint_of_comp_frobeniusIterate_eq`:
  a field-valued point of `X` fixed by `Φ_m` factors through a fixed section.
- `AlgebraicGeometry.ProEtale.traceFormulaHolds_of_smoothOfRelativeDimension_one`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry

/-- Precomposition with `Spec L ⟶ Spec K`, for a field extension `ι : K ⟶ L`, is injective on
morphisms `Spec K ⟶ Z`. -/
lemma specMap_comp_injective_of_field {K L : Type u} [Field K] [Field L]
    (ι : CommRingCat.of K ⟶ CommRingCat.of L) {Z : Scheme.{u}} {a b : Spec (.of K) ⟶ Z}
    (h : Spec.map ι ≫ a = Spec.map ι ≫ b) : a = b := by
  obtain ⟨α, hα⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField a
    (Set.mem_range_self default)
  have hb : a.base default ∈ Set.range b.base := by
    refine ⟨(Spec.map ι).base default, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply,
      Subsingleton.elim ((Spec.map ι).base default) default]
  obtain ⟨β, hβ⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField b hb
  rw [hα, hβ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at h
  have hαβ := Scheme.specMap_comp_fromSpecResidueField_injective _ h
  obtain rfl : α = β := by
    ext r
    exact ι.hom.injective (congrArg (fun φ ↦ φ.hom r) hαβ)
  exact hα.trans hβ.symm

/-- Two sections of a morphism `X ⟶ Spec K` to the spectrum of a field with the same image point
are equal. -/
lemma eq_of_comp_eq_id_of_base_eq {K : Type u} [Field K] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) {x x' : Spec (.of K) ⟶ X} (hx : x ≫ a = 𝟙 _) (hx' : x' ≫ a = 𝟙 _)
    (h : x.base default = x'.base default) : x = x' := by
  obtain ⟨α, hα⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField x
    (Set.mem_range_self default)
  obtain ⟨β, hβ⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField x'
    (y := x.base default) ⟨default, h.symm⟩
  have hγ (φ : X.residueField (x.base default) ⟶ .of K)
      (hφ : (Spec.map φ ≫ X.fromSpecResidueField (x.base default)) ≫ a = 𝟙 _) :
      Spec.preimage (X.fromSpecResidueField (x.base default) ≫ a) ≫ φ = 𝟙 _ := by
    rw [Category.assoc, ← Spec.map_preimage (X.fromSpecResidueField (x.base default) ≫ a),
      ← Spec.map_comp, ← Spec.map_id] at hφ
    exact Spec.map_inj.1 hφ
  have hαγ := hγ α (hα ▸ hx)
  have hβγ := hγ β (hβ ▸ hx')
  have key (r : X.residueField (x.base default)) :
      (Spec.preimage (X.fromSpecResidueField (x.base default) ≫ a)).hom (α.hom r) = r :=
    α.hom.injective (congrArg (fun φ ↦ φ.hom (α.hom r)) hαγ)
  obtain rfl : α = β := by
    ext r
    conv_rhs => rw [← key r]
    exact (congrArg (fun φ ↦ φ.hom (α.hom r)) hβγ).symm
  exact hα.trans hβ.symm

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

namespace WeilComplex

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}} {k : Type u} [Field k]
  {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k)} {p : X ⟶ X₀}

/-- On `R`-points, for an algebra `R` over `k`, the iterate `Φ_m` of the model Frobenius followed
by `p` is the `q^m`-power map of `R`: `t ≫ Φ_m ≫ p = Spec (x ↦ x ^ (q ^ m)) ≫ t ≫ p`. -/
lemma IsModelFrobenius.comp_frobeniusIterate_comp_of_algebra [Fintype k] {s : Scheme.{u}}
    {aX : X ⟶ s} {W : WeilComplex (A := A) aX} {σ : s ⟶ Spec (.of k)}
    (hΦ : W.IsModelFrobenius f₀ σ p) (m : ℕ) {R : Type u} [CommRing R] [Algebra k R]
    (t : Spec (.of R) ⟶ X) :
    t ≫ W.frobeniusIterate m ≫ p = Spec.map (CommRingCat.ofHom
      ((FiniteField.frobeniusAlgHom k R ^ m : R →ₐ[k] R) : R →+* R)) ≫ t ≫ p := by
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  induction m generalizing t with
  | zero =>
    have h1 : CommRingCat.ofHom ((FiniteField.frobeniusAlgHom k R ^ 0 : R →ₐ[k] R) :
        R →+* R) = 𝟙 _ := by
      ext a
      simp
    rw [frobeniusIterate_zero, Category.id_comp, h1, Spec.map_id, Category.id_comp]
  | succ m ih =>
    have hφ := hF₀ (t ≫ p) (CommRingCat.ofHom
      ((FiniteField.frobeniusAlgHom k R : R →ₐ[k] R) : R →+* R))
      fun r ↦ by simp [Nat.card_eq_fintype_card]
    have hcomp : CommRingCat.ofHom ((FiniteField.frobeniusAlgHom k R : R →ₐ[k] R) :
        R →+* R) ≫ CommRingCat.ofHom ((FiniteField.frobeniusAlgHom k R ^ m : R →ₐ[k] R) :
        R →+* R) = CommRingCat.ofHom ((FiniteField.frobeniusAlgHom k R ^ (m + 1) :
        R →ₐ[k] R) : R →+* R) := by
      ext a
      simp [pow_succ]
    rw [frobeniusIterate_succ, Category.assoc, ← Category.assoc t, ih, Category.assoc, hp,
      ← Category.assoc t, hφ, ← hcomp, Spec.map_comp, Category.assoc]

/-- A point `t : Spec L ⟶ X` with values in a field `L` that is fixed by `Φ_m`, `m ≥ 1`, factors
through a section `x` of `a_X` fixed by `Φ_m`: the residue field of its image in `X₀` embeds into
the finite field of `q^m`-fixed elements of `L`, which lies in the algebraically closed `Ω`. -/
theorem IsModelFrobenius.exists_fixedPoint_of_comp_frobeniusIterate_eq [Finite k] {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] {aX : X ⟶ Spec (.of Ω)} {W : WeilComplex (A := A) aX}
    {σ : Spec (.of Ω) ⟶ Spec (.of k)} (hΦ : W.IsModelFrobenius f₀ σ p) {m : ℕ} (hm : m ≠ 0)
    {L : Type u} [Field L] (t : Spec (.of L) ⟶ X) (ht : t ≫ W.frobeniusIterate m = t) :
    ∃ x : Spec (.of Ω) ⟶ X, x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x ∧
      t = Spec.map (Spec.preimage (t ≫ aX)) ≫ x := by
  let := Fintype.ofFinite k
  have hι : Spec.map (Spec.preimage (t ≫ aX)) = t ≫ aX := Spec.map_preimage _
  let ι := Spec.preimage (t ≫ aX)
  let : Algebra k L := (ι.hom.comp (Spec.preimage σ).hom).toAlgebra
  have hfix : Spec.map (CommRingCat.ofHom
      ((FiniteField.frobeniusAlgHom k L ^ m : L →ₐ[k] L) : L →+* L)) ≫ t ≫ p = t ≫ p := by
    rw [← hΦ.comp_frobeniusIterate_comp_of_algebra, ← Category.assoc, ht]
  obtain ⟨φ, hφ⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField (t ≫ p)
    (Set.mem_range_self default)
  rw [hφ, Scheme.specMap_comp_specMap_comp_fromSpecResidueField_eq_iff] at hfix
  have hrange (a : X₀.residueField ((t ≫ p).base default)) : φ.hom a ∈ ι.hom.range := by
    refine (IsAlgClosed.splits (Polynomial.X ^ (Fintype.card k ^ m) - Polynomial.X :
      Polynomial Ω)).mem_range_of_isRoot (FiniteField.X_pow_card_sub_X_ne_zero Ω
        (Nat.one_lt_pow hm Fintype.one_lt_card)) ?_
    have := congrArg (fun χ ↦ χ.hom a) hfix
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      AlgHom.coe_toRingHom, FiniteField.coe_frobeniusAlgHom_pow] at this
    simpa [sub_eq_zero] using this
  let e : Ω ≃+* ι.hom.range := RingEquiv.ofBijective ι.hom.rangeRestrict
    ⟨fun a b h ↦ ι.hom.injective (congrArg Subtype.val h), ι.hom.rangeRestrict_surjective⟩
  let ε : X₀.residueField ((t ≫ p).base default) ⟶ .of Ω :=
    CommRingCat.ofHom (e.symm.toRingHom.comp (φ.hom.codRestrict ι.hom.range hrange))
  have hε : ε ≫ ι = φ := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hg : Spec.map ι ≫ Spec.map ε ≫ X₀.fromSpecResidueField ((t ≫ p).base default) =
      t ≫ p := by
    rw [← Category.assoc, ← Spec.map_comp, hε]
    exact hφ.symm
  have hgσ : (Spec.map ε ≫ X₀.fromSpecResidueField ((t ≫ p).base default)) ≫ f₀ =
      𝟙 _ ≫ σ := by
    refine specMap_comp_injective_of_field ι ?_
    rw [Category.assoc, reassoc_of% hg, hΦ.isPullback.w, ← Category.assoc, ← hι,
      Category.id_comp]
  let x := hΦ.isPullback.lift _ _ hgσ
  have htx : t = Spec.map ι ≫ x := by
    refine hΦ.isPullback.hom_ext ?_ ?_
    · rw [Category.assoc, hΦ.isPullback.lift_fst, hg]
    · rw [Category.assoc, hΦ.isPullback.lift_snd, Category.comp_id, hι]
  refine ⟨x, hΦ.isPullback.lift_snd _ _ _, specMap_comp_injective_of_field ι ?_, htx⟩
  rw [← Category.assoc, ← htx, ht]

end WeilComplex

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  {k : Type u} [Field k] [Finite k]

/-- The trace formula for a model `X₀` that is a proper smooth curve over `k`: by the
Lefschetz–Verdier formula on the proper `X = X₀ ×_k Ω`, the trace of `F_{c,m}(φ)` is the sum of
the local terms at the points of the fixed scheme of `Φ_m`, which are the fixed sections, and
on the smooth curve `X` these local terms are the traces of the stalk Frobenius maps. -/
theorem traceFormulaHolds_of_smoothOfRelativeDimension_one {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k)) [IsProper f₀] [SmoothOfRelativeDimension 1 f₀] :
    TraceFormulaHolds A f₀ := by
  intro Ω _ _ G X aX _ _ W σ p hΦ hctf m hm _ _ _ _
  have : IsProper aX := MorphismProperty.of_isPullback hΦ.isPullback ‹_›
  have : SmoothOfRelativeDimension 1 aX :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.of_isPullback hΦ.isPullback ‹_›
  have : IsProper (W.graph G hctf m).fixStr :=
    inferInstanceAs (IsProper ((W.graph G hctf m).fixι ≫ aX))
  have : Mono (W.graph G hctf m).fixι := inferInstanceAs (Mono (equalizer.ι _ _))
  let xFix (x : {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x}) :
      Spec (.of Ω) ⟶ (W.graph G hctf m).fix :=
    equalizer.lift x.1 ((Category.comp_id x.1).trans x.2.2.symm)
  have hxFix (x : {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x}) :
      xFix x ≫ (W.graph G hctf m).fixι = x.1 :=
    equalizer.lift_ι _ _
  -- distinct fixed sections give distinct points of the fixed scheme
  have hinj : Function.Injective fun x ↦ (xFix x).base default := fun x x' h ↦
    Subtype.ext (eq_of_comp_eq_id_of_base_eq aX x.2.1 x'.2.1 (by
      rw [← hxFix x, ← hxFix x', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact congrArg _ h))
  -- every point of the fixed scheme comes from a fixed section
  have hcover (z : (W.graph G hctf m).fix) : ∃ x, (xFix x).base default = z := by
    obtain ⟨x, hxs, hxm, htx⟩ := hΦ.exists_fixedPoint_of_comp_frobeniusIterate_eq
      (by omega : m ≠ 0)
      ((W.graph G hctf m).fix.fromSpecResidueField z ≫ (W.graph G hctf m).fixι) (by
        rw [Category.assoc]
        exact congrArg (_ ≫ ·) (((W.graph G hctf m).fixι_snd).trans (Category.comp_id _)))
    have h : (W.graph G hctf m).fix.fromSpecResidueField z = Spec.map (Spec.preimage
        (((W.graph G hctf m).fix.fromSpecResidueField z ≫ (W.graph G hctf m).fixι) ≫ aX)) ≫
          xFix ⟨x, hxs, hxm⟩ := by
      rw [← cancel_mono (W.graph G hctf m).fixι, Category.assoc, hxFix]
      exact htx
    have hz : ((W.graph G hctf m).fix.fromSpecResidueField z).base default = z := by
      have := Set.mem_range_self (f := ((W.graph G hctf m).fix.fromSpecResidueField z).base)
        default
      rwa [Scheme.range_fromSpecResidueField] at this
    refine ⟨⟨x, hxs, hxm⟩, ?_⟩
    rw [← hz, h, Scheme.Hom.comp_apply, Subsingleton.elim ((Spec.map _).base default) default]
  have hclosed (x : {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x}) :
      IsClosed (Set.range (xFix x).base) := by
    have : IsClosedImmersion (xFix x) :=
      isClosedImmersion_of_comp_eq_id (W.graph G hctf m).fixStr (xFix x) (by
        rw [Correspondence.fixStr, ← Category.assoc, hxFix]
        exact x.2.1)
    exact (xFix x).isClosedEmbedding.isClosed_range
  have : T1Space (W.graph G hctf m).fix := ⟨fun z ↦ by
    obtain ⟨x, rfl⟩ := hcover z
    simpa [Set.range_unique] using hclosed x⟩
  have : Finite (W.graph G hctf m).fix := Finite.of_surjective _ hcover
  let U (x : {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x}) :
      (W.graph G hctf m).fix.Opens :=
    ⟨Set.range (xFix x).base, isOpen_discrete _⟩
  have hrange (x : {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x}) :
      Set.range (U x).ι.base = Set.range (xFix x).base :=
    Scheme.Opens.range_ι _
  rw [GeometricOperations.trace_globalOperator_eq_sum_localTerm G hctf (W.graph G hctf m)
    (fun x ↦ (U x).ι) (fun x ↦ hrange x ▸ hclosed x) (fun x x' hne ↦ by
      dsimp only
      rw [hrange, hrange, Set.range_unique, Set.range_unique]
      exact Set.disjoint_singleton.2 (hinj.ne hne))
    (Set.eq_univ_of_forall fun z ↦ Set.mem_iUnion.2 (by
      obtain ⟨x, hx⟩ := hcover z
      exact ⟨x, hrange x ▸ ⟨default, hx⟩⟩))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  exact GeometricOperations.localTerm_traceClass_eq_trace G W f₀ σ p hΦ hctf m hm x.1 x.2.1
    x.2.2 (xFix x) (hxFix x) (U x).ι _ (hrange x)

end AlgebraicGeometry.ProEtale
