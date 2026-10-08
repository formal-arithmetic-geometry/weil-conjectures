/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.InternalHom

/-!
# Internal homs of lisse `ℓ`-adic sheaves

The internal hom `[ℚ̄_ℓ, ℚ̄_ℓ]` of the constant `ℓ`-adic sheaf `ℚ̄_ℓ = ℚ̄_ℓ,X` on the small
pro-étale site of a scheme `X` is `ℚ̄_ℓ` itself
(`AlgebraicGeometry.ProEtale.ihomAdicConstantSheafIso`): a `ℚ̄_ℓ`-linear endomorphism `φ` of the
restriction of `ℚ̄_ℓ` to `X.ProEt / U` is multiplication by the section `φ(1)`
(`AlgebraicGeometry.ProEtale.adicConstantSheaf_apply_eq_mul`).

Indeed, locally on `U` a section `s` of `ℚ̄_ℓ` is the pullback of the tautological function `τ`
on the constant profinite scheme `Spec B × K`, along the section `(id, s)` of `Spec B × K → Spec B`,
where `K` is a compact set of values of `s` (Bhatt–Scholze, §4.2). The function `τ` is constant
on the image of each of the sections `Spec B × {k}`, which cover `Spec B × K`, so by naturality and
`ℚ̄_ℓ`-linearity `φ(τ) = τ φ(1)` holds pointwise, and pulling back gives `φ(s) = s φ(1)`.

Since pullback along a weakly étale morphism commutes with internal homs
(`AlgebraicGeometry.ProEtale.upperStarIhomIsoOfWeaklyEtale`), and the internal hom is additive
in both variables, it follows that the internal hom of two lisse sheaves is lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.ihom`): pro-étale locally it is
`[ℚ̄_ℓⁿ, ℚ̄_ℓᵐ] ≅ ℚ̄_ℓⁿᵐ`.

## Main results

- `AlgebraicGeometry.ProEtale.adicConstantSheaf_apply_eq_mul`: a `ℚ̄_ℓ`-linear endomorphism of
  `ℚ̄_ℓ` over `U` is multiplication by a section.
- `AlgebraicGeometry.ProEtale.ihomAdicConstantSheafIso`: `[ℚ̄_ℓ, ℚ̄_ℓ] ≅ ℚ̄_ℓ`.
- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.ihom`: the internal hom of lisse sheaves is lisse.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed Enriched.FunctorCategory

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T : Type*} [TopologicalSpace T]

/-- The product of two locally finite functions is locally finite: locally its values lie in the
product of two finite-dimensional `ℚ_ℓ`-subspaces of `ℚ̄_ℓ`. -/
lemma mul_mem_locallyFiniteFunctions {f g : C(T, PadicAlgCl l)}
    (hf : f ∈ locallyFiniteFunctions l T) (hg : g ∈ locallyFiniteFunctions l T) :
    f * g ∈ locallyFiniteFunctions l T := by
  intro x
  obtain ⟨U, hU, hfU⟩ := hf x
  obtain ⟨V, hV, hgV⟩ := hg x
  have : FiniteDimensional ℚ_[l]
      ↥(Submodule.span ℚ_[l] (f '' U) * Submodule.span ℚ_[l] (g '' V)) :=
    Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hfU).mul (Module.Finite.iff_fg.1 hgV))
  refine ⟨U ∩ V, Filter.inter_mem hU hV, Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℚ_[l] (f '' U) * Submodule.span ℚ_[l] (g '' V)) ?_⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  exact Submodule.mul_mem_mul (Submodule.subset_span ⟨y, hy.1, rfl⟩)
    (Submodule.subset_span ⟨y, hy.2, rfl⟩)

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

section Sections

/-- The unit section `1` of `ℚ̄_ℓ` over `U`: the constant function `1`. -/
noncomputable def adicConstantSheafOne (U : X.ProEt) :
    (adicConstantSheaf l X).obj.obj (op U) :=
  ULift.up ⟨ContinuousMap.const _ 1, PadicAlgCl.const_mem_locallyFiniteFunctions 1⟩

@[simp]
lemma adicConstantSheafOne_apply (U : X.ProEt) (y : U.left) :
    (adicConstantSheafOne (l := l) U).down.1 y = 1 :=
  rfl

/-- The restriction of a section of `ℚ̄_ℓ` is the composite function. -/
@[simp]
lemma adicConstantSheaf_map_apply {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (s : (adicConstantSheaf l X).obj.obj U) (y : V.unop.left) :
    ((adicConstantSheaf l X).obj.map f s).down.1 y = s.down.1 (f.unop.left y) :=
  rfl

@[simp]
lemma adicConstantSheaf_smul_apply {U : X.ProEtᵒᵖ} (c : ULift.{u + 1} (PadicAlgCl l))
    (s : (adicConstantSheaf l X).obj.obj U) (y : U.unop.left) :
    (c • s).down.1 y = c.down * s.down.1 y :=
  rfl

/-- The unit section restricts to the unit section. -/
@[simp]
lemma adicConstantSheaf_map_one {U V : X.ProEt} (f : op U ⟶ op V) :
    (adicConstantSheaf l X).obj.map f (adicConstantSheafOne U) = adicConstantSheafOne V :=
  rfl

/-- The product of two sections of `ℚ̄_ℓ` over `U`. -/
noncomputable def adicConstantSheafMul {U : X.ProEtᵒᵖ}
    (f g : (adicConstantSheaf l X).obj.obj U) : (adicConstantSheaf l X).obj.obj U :=
  ULift.up ⟨f.down.1 * g.down.1, PadicAlgCl.mul_mem_locallyFiniteFunctions f.down.2 g.down.2⟩

@[simp]
lemma adicConstantSheafMul_apply {U : X.ProEtᵒᵖ} (f g : (adicConstantSheaf l X).obj.obj U)
    (y : U.unop.left) :
    (adicConstantSheafMul f g).down.1 y = f.down.1 y * g.down.1 y :=
  rfl

end Sections

section Tautological

/-- **Sections of `ℚ̄_ℓ` are locally pulled back from a tautological function.** Let `s` be a
section of `ℚ̄_ℓ` over `Y : X.ProEt` and `y` a point of `Y`. There are an open neighbourhood
`ι : Y₁ ⟶ Y` of `y`, a weakly étale `p : Y₂ ⟶ Y` with a section `σ : Y₁ ⟶ Y₂` over `Y`, and a
locally finite function `τ` on `Y₂` with `s ∘ ι = τ ∘ σ`, such that every point of `Y₂` lies on
a section `i : Y₁ ⟶ Y₂` over `Y` along which `τ` is constant.

Here `Y₁ = Spec B` is an affine open neighbourhood of `y` on which the values of `s` form a compact
subset `K` of a finite-dimensional `ℚ_ℓ`-subspace of `ℚ̄_ℓ`, `Y₂ = Spec B × K` is the spectrum of
`LocallyConstant K B`, `τ` is the projection to `K`, `σ = (id, s)`, and the sections `i` are the
`Spec B × {k}`. -/
lemma exists_tautological (Y : X.ProEt) (s : PadicAlgCl.locallyFiniteFunctions l Y.left)
    (y : Y.left) :
    ∃ (Y₁ Y₂ : X.ProEt) (ι : Y₁ ⟶ Y) (σ : Y₁ ⟶ Y₂) (p : Y₂ ⟶ Y)
      (τ : PadicAlgCl.locallyFiniteFunctions l Y₂.left) (z : Y₁.left),
      ι.left z = y ∧ σ ≫ p = ι ∧
      (∀ w, (s : C(Y.left, PadicAlgCl l)) (ι.left w) =
        (τ : C(Y₂.left, PadicAlgCl l)) (σ.left w)) ∧
      ∀ q : Y₂.left, ∃ (i : Y₁ ⟶ Y₂) (w : Y₁.left), i ≫ p = ι ∧ i.left w = q ∧
        ∀ w', (τ : C(Y₂.left, PadicAlgCl l)) (i.left w') = (τ : C(Y₂.left, PadicAlgCl l)) q := by
  obtain ⟨N, hN, hfin⟩ := s.2 y
  obtain ⟨B, j, hj, ⟨z, hz⟩, hjN⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := Y.left) (x := y) (U := ⟨interior N, isOpen_interior⟩) (mem_interior_iff_mem_nhds.2 hN)
  let K : Set (PadicAlgCl l) := Set.range fun w : Spec B ↦ (s : C(Y.left, PadicAlgCl l)) (j w)
  have hKc : IsCompact K := isCompact_range ((s : C(Y.left, PadicAlgCl l)).continuous.comp
    j.base.hom.continuous)
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hKN : K ⊆ (s : C(Y.left, PadicAlgCl l)) '' N := by
    rintro _ ⟨w, rfl⟩
    exact ⟨j w, interior_subset (hjN ⟨w, rfl⟩), rfl⟩
  let σK : C(PrimeSpectrum B, K) :=
    ⟨fun w ↦ ⟨(s : C(Y.left, PadicAlgCl l)) (j w), w, rfl⟩,
      ((s : C(Y.left, PadicAlgCl l)).continuous.comp j.base.hom.continuous).subtype_mk _⟩
  let L := LocallyConstant.liftPrimeSpectrum (RingHom.id B) σK
  let pB : Spec (CommRingCat.of (LocallyConstant K B)) ⟶ Spec B :=
    Spec.map (CommRingCat.ofHom (algebraMap B (LocallyConstant K B)))
  have hL : CommRingCat.ofHom (algebraMap B (LocallyConstant K B)) ≫ CommRingCat.ofHom L =
      𝟙 _ := by
    ext r
    exact LocallyConstant.liftPrimeSpectrum_algebraMap _ _ r
  have hev (k : K) : CommRingCat.ofHom (algebraMap B (LocallyConstant K B)) ≫
      CommRingCat.ofHom (LocallyConstant.evalRingHom k) = 𝟙 _ := by
    ext r
    rfl
  let Y₁ : X.ProEt := Scheme.ProEt.mk (j ≫ Y.hom)
  let Y₂ : X.ProEt := Scheme.ProEt.mk (pB ≫ j ≫ Y.hom)
  let ι : Y₁ ⟶ Y := MorphismProperty.Over.homMk j rfl
  let p : Y₂ ⟶ Y := MorphismProperty.Over.homMk (pB ≫ j) (by simp [Y₂])
  have hsec {g : CommRingCat.of (LocallyConstant K B) ⟶ B}
      (hg : CommRingCat.ofHom (algebraMap B (LocallyConstant K B)) ≫ g = 𝟙 _) :
      Spec.map g ≫ pB = 𝟙 _ := by
    rw [← Spec.map_comp, hg]
    exact Spec.map_id _
  let sec (g : CommRingCat.of (LocallyConstant K B) ⟶ B)
      (hg : CommRingCat.ofHom (algebraMap B (LocallyConstant K B)) ≫ g = 𝟙 _) : Y₁ ⟶ Y₂ :=
    MorphismProperty.Over.homMk (Spec.map g) (by
      change Spec.map g ≫ pB ≫ j ≫ Y.hom = j ≫ Y.hom
      rw [reassoc_of% (hsec hg)])
  have hsecp (g : CommRingCat.of (LocallyConstant K B) ⟶ B)
      (hg : CommRingCat.ofHom (algebraMap B (LocallyConstant K B)) ≫ g = 𝟙 _) :
      sec g hg ≫ p = ι := by
    apply MorphismProperty.Over.Hom.ext
    change Spec.map g ≫ pB ≫ j = j
    rw [reassoc_of% (hsec hg)]
  let τ : C(PrimeSpectrum (LocallyConstant K B), PadicAlgCl l) :=
    ⟨fun q ↦ ((LocallyConstant.homeomorphPrimeSpectrum.symm q).1 : PadicAlgCl l),
      continuous_subtype_val.comp (continuous_fst.comp
        LocallyConstant.homeomorphPrimeSpectrum.symm.continuous)⟩
  have hτ : τ ∈ PadicAlgCl.locallyFiniteFunctions l Y₂.left := by
    refine PadicAlgCl.mem_locallyFiniteFunctions_of_finiteDimensional
      (Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ_[l]
        ((s : C(Y.left, PadicAlgCl l)) '' N)) (Submodule.span_mono ?_))
    rintro _ ⟨q, rfl⟩
    exact hKN (LocallyConstant.homeomorphPrimeSpectrum.symm q).1.2
  have hτ' (k : K) (w : PrimeSpectrum B) :
      τ (PrimeSpectrum.comap (LocallyConstant.evalRingHom k) w) = k := by
    change ((LocallyConstant.homeomorphPrimeSpectrum.symm
      (LocallyConstant.toPrimeSpectrum (k, w))).1 : PadicAlgCl l) = k
    rw [← LocallyConstant.homeomorphPrimeSpectrum_apply, Homeomorph.symm_apply_apply]
  refine ⟨Y₁, Y₂, ι, sec _ hL, p, ⟨τ, hτ⟩, z, hz, hsecp _ hL, fun w ↦ ?_, fun q ↦ ?_⟩
  · change _ = ((LocallyConstant.homeomorphPrimeSpectrum.symm
      (PrimeSpectrum.comap L w)).1 : PadicAlgCl l)
    rw [LocallyConstant.comap_liftPrimeSpectrum, ← LocallyConstant.homeomorphPrimeSpectrum_apply,
      Homeomorph.symm_apply_apply]
    rfl
  · obtain ⟨⟨k, w⟩, rfl⟩ := LocallyConstant.homeomorphPrimeSpectrum.surjective q
    refine ⟨sec _ (hev k), w, hsecp _ (hev k), rfl, fun w' ↦ ?_⟩
    change τ (PrimeSpectrum.comap (LocallyConstant.evalRingHom k) w') = τ
      (LocallyConstant.toPrimeSpectrum (k, w))
    rw [hτ']
    exact (hτ' k w).symm

end Tautological

section Endomorphisms

variable {U : X.ProEt}
  (φ : Under.forget (op U) ⋙ (adicConstantSheaf l X).obj ⟶
    Under.forget (op U) ⋙ (adicConstantSheaf l X).obj)

/-- The pointwise form of the naturality of `φ` along a morphism `a : j ⟶ j'` of `Under (op U)`,
that is, a morphism `j'.right ⟶ j.right` over `U`. -/
lemma adicConstantSheaf_nat_apply {j j' : Under (op U)} (a : j ⟶ j')
    (s : (adicConstantSheaf l X).obj.obj j.right) (y : j'.right.unop.left) :
    (φ.app j' ((adicConstantSheaf l X).obj.map a.right s)).down.1 y =
      (φ.app j s).down.1 (a.right.unop.left y) := by
  have h := ConcreteCategory.congr_hom (φ.naturality a) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact congrArg (fun t : (adicConstantSheaf l X).obj.obj j'.right ↦ t.down.1 y) h

/-- The value of `φ` on the unit section over `j` is the restriction of its value on the unit
section over `U`. -/
lemma adicConstantSheaf_app_one_apply (j : Under (op U)) (y : j.right.unop.left) :
    (φ.app j (adicConstantSheafOne j.right.unop)).down.1 y =
      (φ.app (Under.mk (𝟙 (op U))) (adicConstantSheafOne U)).down.1 (j.hom.unop.left y) :=
  adicConstantSheaf_nat_apply φ (Under.homMk j.hom (by simp) : Under.mk (𝟙 (op U)) ⟶ j)
    (adicConstantSheafOne U) y

/-- If a section `t` over `j` becomes constant along `a : j ⟶ j'`, then at the points of the
image of `a`, `φ(t)` is `t` times the value of `φ` on the unit section over `U`. -/
lemma adicConstantSheaf_apply_eq_mul_of_const {j j' : Under (op U)} (a : j ⟶ j')
    (t : (adicConstantSheaf l X).obj.obj j.right) (y : j'.right.unop.left)
    (ht : ∀ y', t.down.1 (a.right.unop.left y') = t.down.1 (a.right.unop.left y)) :
    (φ.app j t).down.1 (a.right.unop.left y) =
      (φ.app (Under.mk (𝟙 (op U))) (adicConstantSheafOne U)).down.1
        (j.hom.unop.left (a.right.unop.left y)) * t.down.1 (a.right.unop.left y) := by
  have hc : (adicConstantSheaf l X).obj.map a.right t =
      ULift.up (t.down.1 (a.right.unop.left y)) • adicConstantSheafOne j'.right.unop :=
    adicConstantSheaf_ext fun y' ↦ (ht y').trans (mul_one _).symm
  have hy : j'.hom.unop.left y = j.hom.unop.left (a.right.unop.left y) := by
    rw [← Under.w a]
    rfl
  rw [← adicConstantSheaf_nat_apply φ a, hc, map_smul, adicConstantSheaf_smul_apply,
    adicConstantSheaf_app_one_apply, mul_comm, hy]

/-- **A `ℚ̄_ℓ`-linear endomorphism of `ℚ̄_ℓ` is multiplication by a section.** For a natural
`ℚ̄_ℓ`-linear endomorphism `φ` of the restriction of `ℚ̄_ℓ` to `X.ProEt / U`, `φ(s) = φ(1) s`.
Locally `s` is pulled back from a tautological function `τ`
(`AlgebraicGeometry.ProEtale.exists_tautological`), for which this holds pointwise since `τ` is
constant along sections through every point
(`AlgebraicGeometry.ProEtale.adicConstantSheaf_apply_eq_mul_of_const`). -/
theorem adicConstantSheaf_apply_eq_mul (j : Under (op U))
    (s : (adicConstantSheaf l X).obj.obj j.right) (y : j.right.unop.left) :
    (φ.app j s).down.1 y =
      (φ.app (Under.mk (𝟙 (op U))) (adicConstantSheafOne U)).down.1 (j.hom.unop.left y) *
        s.down.1 y := by
  obtain ⟨Y₁, Y₂, ι, σ, p, τ, z, rfl, hσ, hsτ, hsec⟩ := exists_tautological j.right.unop s.down y
  let j₁ : Under (op U) := Under.mk (j.hom ≫ ι.op)
  let j₂ : Under (op U) := Under.mk (j.hom ≫ p.op)
  let aι : j ⟶ j₁ := Under.homMk ι.op rfl
  let aσ : j₂ ⟶ j₁ := Under.homMk σ.op (by
    change j.hom ≫ p.op ≫ σ.op = j.hom ≫ ι.op
    rw [← op_comp, hσ])
  have h₁ : (adicConstantSheaf l X).obj.map aι.right s =
      (adicConstantSheaf l X).obj.map aσ.right (ULift.up τ) :=
    adicConstantSheaf_ext fun w ↦ hsτ w
  have := adicConstantSheaf_nat_apply φ aι s z
  rw [h₁, adicConstantSheaf_nat_apply φ aσ] at this
  change (φ.app j₂ (ULift.up τ)).down.1 (σ.left z) = (φ.app j s).down.1 (ι.left z) at this
  change (φ.app j s).down.1 (ι.left z) = _
  rw [← this]
  obtain ⟨i, w, hip, hiw, hτi⟩ := hsec (σ.left z)
  let ai : j₂ ⟶ j₁ := Under.homMk i.op (by
    change j.hom ≫ p.op ≫ i.op = j.hom ≫ ι.op
    rw [← op_comp, hip])
  have := adicConstantSheaf_apply_eq_mul_of_const φ ai (ULift.up τ) w (fun w' ↦ hτi w' |>.trans
    (by rw [← hiw]; rfl))
  change (φ.app j₂ (ULift.up τ)).down.1 (σ.left z) = _
  rw [← hiw]
  have e1 : j₂.hom.unop.left (i.left w) = j.hom.unop.left (ι.left z) := by
    change (p.left ≫ j.hom.unop.left) (i.left w) = _
    rw [Scheme.Hom.comp_apply, hiw, ← hσ]
    rfl
  refine this.trans ?_
  change (φ.app (Under.mk (𝟙 (op U))) (adicConstantSheafOne U)).down.1
    (j₂.hom.unop.left (i.left w)) *
    τ.1 (i.left w) = _
  rw [e1, hiw, ← hsτ z]
  rfl

end Endomorphisms

end AlgebraicGeometry.ProEtale
