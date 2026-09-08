/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Points of a group scheme trivial on a square-zero thickening

Let `G` be a group scheme over a field `K` and let `Spec (B ⧸ I) ⊆ Spec B` be a square-zero
thickening of affine `K`-schemes, i.e. `I ^ 2 = ⊥`. This file studies the group of those
`B`-points of `G` that become trivial on `Spec (B ⧸ I)`, and proves the two facts about it that
the étaleness of the multiplication by `n` isogeny of an abelian variety rests on: if `n` is
invertible in `K`, then this group has no `n`-torsion (*rigidity*) and it is `n`-divisible.

Classically this group is the group of `I`-valued tangent vectors of `G` at the identity, so it
is a `B ⧸ I`-module and both statements are immediate. Here no module structure is built.
Instead, the key computation is carried out directly on functions: a point `d` trivial on the
thickening has image the identity of `G`, hence factors through any affine open `U` around the
identity and induces a ring map `dᵈ : Γ(G, U) ⟶ B`, and the *product formula*
`(c * d)ᵈ f + 1ᵈ f = cᵈ f + dᵈ f`
holds for all `f : Γ(G, U)`. It is proved by comparing the four ring maps `Γ(U ×_K U) ⟶ B`
attached to the pairs `(c, d)`, `(c, 1)`, `(1, d)` and `(1, 1)` on a basic open neighbourhood of
the identity of `U ×_K U` on which the multiplication of `G` lands in `U`; on pure tensors the
identity to be proved is exactly `(cᵈ f - 1ᵈ f) * (dᵈ g - 1ᵈ g) = 0`, which holds because
`I ^ 2 = ⊥`. Since this needs no differentials, no tangent spaces and no smoothness, everything
below holds for an arbitrary group scheme over a field.

Mathlib has no file on the infinitesimal theory of group schemes, so this file is not a mirror
of any Mathlib file and lives outside `WeilConjectures/Mathlib/`.

## Main definitions

- `AlgebraicGeometry.Spec.overQuotientMk`: the closed immersion `Spec (B ⧸ I) ⟶ Spec B` attached
  to an ideal `I` of `B`, as a morphism of schemes over a base.
- `AlgebraicGeometry.IsAffineOpen.app`: the ring map on functions over an affine open `U`
  attached to a morphism `Spec S ⟶ X` whose image lies in `U`.

## Main statements

- `AlgebraicGeometry.GrpObj.eq_one_of_pow_eq_one`: **rigidity**. A `B`-point of `G` which is
  trivial on `Spec (B ⧸ I)` and whose `n`-th power is trivial is itself trivial, provided `n`
  is invertible in `K`.
- `AlgebraicGeometry.GrpObj.exists_pow_eq`: **divisibility**. If `n` is invertible in `K`, every
  `B`-point of `G` which is trivial on `Spec (B ⧸ I)` is the `n`-th power of a `B`-point of `G`
  which is trivial on `Spec (B ⧸ I)`.

## Blueprint

The declarations of this file are the infinitesimal input to Proposition 2.8 of §2.6 of
`blueprint/curve_estimates.pdf`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TensorProduct

open scoped MonObj

namespace AlgebraicGeometry.GrpObj

/-! ### The algebraic core

Two ring maps out of a localization that agree modulo a square-zero ideal on pure tensors
satisfy a four term additive identity. -/

section Algebra

variable {R S L : Type*} [CommRing R] [CommRing S] [CommRing L] [Algebra R L]

/-- An additive map on a localization satisfying the Leibniz rule with respect to a ring map
`β` and vanishing on the base ring vanishes. -/
private lemma eq_zero_of_leibniz (M : Submonoid R) [IsLocalization M L] (β : L →+* S)
    (D : L →+ S) (hD : ∀ x y : L, D (x * y) = β x * D y + β y * D x)
    (h : ∀ r : R, D (algebraMap R L r) = 0) (x : L) : D x = 0 := by
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  have hu : IsUnit (β (algebraMap R L (m : R))) := (IsLocalization.map_units L m).map β
  have h1 := hD (IsLocalization.mk' L r m) (algebraMap R L (m : R))
  rw [IsLocalization.mk'_spec, h r, h (m : R), mul_zero, zero_add] at h1
  exact hu.mul_left_cancel (by rw [← h1, mul_zero])

/-- Two ring maps out of a localization that agree modulo an ideal `I` on the base ring agree
modulo `I` everywhere. -/
private lemma sub_mem_of_localization (M : Submonoid R) [IsLocalization M L] (I : Ideal S)
    (α β : L →+* S) (h : ∀ r : R, α (algebraMap R L r) - β (algebraMap R L r) ∈ I) (x : L) :
    α x - β x ∈ I := by
  have : ((Ideal.Quotient.mk I).comp α) = (Ideal.Quotient.mk I).comp β :=
    IsLocalization.ringHom_ext M <| RingHom.ext fun r ↦ by
      simpa [Ideal.Quotient.eq] using h r
  exact (Ideal.Quotient.eq (I := I)).mp (RingHom.congr_fun this x)

variable {I : Ideal S}

private lemma le_nilradical_of_sq_eq_bot (hI : I ^ 2 = ⊥) : I ≤ nilradical S := fun x hx ↦
  ⟨2, by simpa [hI] using Ideal.pow_mem_pow hx 2⟩

private lemma mul_eq_zero_of_sq_eq_bot (hI : I ^ 2 = ⊥) {a b : S} (ha : a ∈ I) (hb : b ∈ I) :
    a * b = 0 := by
  have : a * b ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
  simpa [hI] using this

/-- Four ring maps out of a localization satisfying a four term additive identity modulo a
square-zero ideal on the base ring satisfy it everywhere. -/
private lemma add_eq_add_of_localization (M : Submonoid R) [IsLocalization M L] (hI : I ^ 2 = ⊥)
    (ψ₁ ψ₂ ψ₃ ψ₄ : L →+* S)
    (h₁ : ∀ r : R, ψ₁ (algebraMap R L r) - ψ₄ (algebraMap R L r) ∈ I)
    (h₂ : ∀ r : R, ψ₂ (algebraMap R L r) - ψ₄ (algebraMap R L r) ∈ I)
    (h₃ : ∀ r : R, ψ₃ (algebraMap R L r) - ψ₄ (algebraMap R L r) ∈ I)
    (h : ∀ r : R, ψ₁ (algebraMap R L r) + ψ₄ (algebraMap R L r)
      = ψ₂ (algebraMap R L r) + ψ₃ (algebraMap R L r)) (x : L) :
    ψ₁ x + ψ₄ x = ψ₂ x + ψ₃ x := by
  have hmul {a b : S} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 :=
    mul_eq_zero_of_sq_eq_bot hI ha hb
  have k₁ := sub_mem_of_localization M I ψ₁ ψ₄ h₁
  have k₂ := sub_mem_of_localization M I ψ₂ ψ₄ h₂
  have k₃ := sub_mem_of_localization M I ψ₃ ψ₄ h₃
  set D : L →+ S := AddMonoidHom.mk' (fun x ↦ ψ₁ x + ψ₄ x - ψ₂ x - ψ₃ x)
    (fun a b ↦ by simp only [map_add]; ring) with hDdef
  have hD : ∀ x y : L, D (x * y) = ψ₄ x * D y + ψ₄ y * D x := by
    intro x y
    have e₁ := hmul (k₁ x) (k₁ y)
    have e₂ := hmul (k₂ x) (k₂ y)
    have e₃ := hmul (k₃ x) (k₃ y)
    simp only [hDdef, AddMonoidHom.mk'_apply, map_mul] at *
    linear_combination e₁ - e₂ - e₃
  have := eq_zero_of_leibniz M ψ₄ D hD (fun r ↦ by
    simp only [hDdef, AddMonoidHom.mk'_apply]
    linear_combination h r) x
  simp only [hDdef, AddMonoidHom.mk'_apply] at this
  linear_combination this

variable {A : Type*} [CommRing A] [Algebra R A]

omit [Algebra R L] in
/-- **The four term identity for points of a group scheme, algebraically.**
Let `c`, `d` and `ε` be ring maps `A → S` with `c - ε` and `d - ε` valued in a square-zero
ideal `I`. If `ψ₁, ψ₂, ψ₃, ψ₄` are ring maps out of a localization `L` of `A ⊗[R] A` sending
`x ⊗ₜ y` to `c x * d y`, `c x * ε y`, `ε x * d y` and `ε x * ε y` respectively, then
`ψ₁ + ψ₄ = ψ₂ + ψ₃`. -/
private lemma localization_tmul_add_eq [Algebra (A ⊗[R] A) L] {s : A ⊗[R] A}
    [IsLocalization.Away s L] (hI : I ^ 2 = ⊥) (c d ε : A →+* S)
    (hc : ∀ x, c x - ε x ∈ I) (hd : ∀ x, d x - ε x ∈ I) (ψ₁ ψ₂ ψ₃ ψ₄ : L →+* S)
    (e₁ : ∀ x y, ψ₁ (algebraMap (A ⊗[R] A) L (x ⊗ₜ y)) = c x * d y)
    (e₂ : ∀ x y, ψ₂ (algebraMap (A ⊗[R] A) L (x ⊗ₜ y)) = c x * ε y)
    (e₃ : ∀ x y, ψ₃ (algebraMap (A ⊗[R] A) L (x ⊗ₜ y)) = ε x * d y)
    (e₄ : ∀ x y, ψ₄ (algebraMap (A ⊗[R] A) L (x ⊗ₜ y)) = ε x * ε y) (z : L) :
    ψ₁ z + ψ₄ z = ψ₂ z + ψ₃ z := by
  have hmul {a b : S} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 :=
    mul_eq_zero_of_sq_eq_bot hI ha hb
  refine add_eq_add_of_localization (Submonoid.powers s) hI ψ₁ ψ₂ ψ₃ ψ₄ ?_ ?_ ?_ ?_ z
  · refine fun w ↦ w.induction_on (by simp) (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [e₁, e₄]
      have : c x * d y - ε x * ε y = (c x - ε x) * d y + ε x * (d y - ε y) := by ring
      rw [this]
      exact I.add_mem (I.mul_mem_right _ (hc x)) (I.mul_mem_left _ (hd y))
    · simpa only [map_add, add_sub_add_comm] using I.add_mem hx hy
  · refine fun w ↦ w.induction_on (by simp) (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [e₂, e₄, ← sub_mul]
      exact I.mul_mem_right _ (hc x)
    · simpa only [map_add, add_sub_add_comm] using I.add_mem hx hy
  · refine fun w ↦ w.induction_on (by simp) (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [e₃, e₄, ← mul_sub]
      exact I.mul_mem_left _ (hd y)
    · simpa only [map_add, add_sub_add_comm] using I.add_mem hx hy
  · refine fun w ↦ w.induction_on (by simp) (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [e₁, e₂, e₃, e₄]
      have := hmul (hc x) (hd y)
      linear_combination this
    · simp only [map_add]
      linear_combination hx + hy
end Algebra

end AlgebraicGeometry.GrpObj

namespace AlgebraicGeometry

/-- The closed immersion `Spec (B ⧸ I) ⟶ Spec B` attached to an ideal `I` of `B`, as a morphism
of schemes over `Spec R`, where `Spec B` is seen as an `R`-scheme via `t`. -/
noncomputable def Spec.overQuotientMk {R B : CommRingCat.{u}} (I : Ideal B) (t : Spec B ⟶ Spec R) :
    Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ⟶ Over.mk t :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

@[simp]
lemma Spec.overQuotientMk_left {R B : CommRingCat.{u}} (I : Ideal B) (t : Spec B ⟶ Spec R) :
    (Spec.overQuotientMk I t).left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  rfl

/-! ### Morphisms landing in an affine chart

For a morphism `f : Spec S ⟶ X` whose image lies in an affine open `U` of `X`, the ring map
`hU.app f hf : Γ(X, U) ⟶ S` determines `f`, and every ring map arises this way. -/

section Chart

namespace IsAffineOpen

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

/-- The ring map on functions over the affine open `U` induced by a morphism `f : Spec S ⟶ X`
whose image is contained in `U`. It is the unique ring map `φ : Γ(X, U) ⟶ S` with
`Spec.map φ ≫ hU.fromSpec = f`; see `AlgebraicGeometry.IsAffineOpen.Spec_map_app` and
`AlgebraicGeometry.IsAffineOpen.app_eq`. -/
noncomputable def app {S : CommRingCat.{u}} (f : Spec S ⟶ X)
    (hf : Set.range f ⊆ (U : Set X)) : Γ(X, U) ⟶ S :=
  Spec.preimage (IsOpenImmersion.lift hU.fromSpec f (by rwa [hU.range_fromSpec]))

/-- A morphism `f : Spec S ⟶ X` landing in the affine open `U` is recovered from its ring map
on functions over `U`. -/
@[reassoc]
lemma Spec_map_app {S : CommRingCat.{u}} (f : Spec S ⟶ X)
    (hf : Set.range f ⊆ (U : Set X)) : Spec.map (app hU f hf) ≫ hU.fromSpec = f := by
  rw [app, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

/-- The ring map on functions attached to a morphism landing in the affine open `U` is the
unique one factoring it through `hU.fromSpec`. -/
lemma app_eq {S : CommRingCat.{u}} (f : Spec S ⟶ X)
    (hf : Set.range f ⊆ (U : Set X)) (φ : Γ(X, U) ⟶ S)
    (h : Spec.map φ ≫ hU.fromSpec = f) : app hU f hf = φ := by
  rw [app, ← IsOpenImmersion.lift_uniq hU.fromSpec f _ (Spec.map φ) h, Spec.preimage_map]

/-- Composing a morphism into `U` with a morphism of affine schemes on the source. -/
lemma app_Spec_map_comp {S S' : CommRingCat.{u}} (f : Spec S ⟶ X)
    (hf : Set.range f ⊆ (U : Set X)) (φ : S ⟶ S') :
    app hU (Spec.map φ ≫ f) (by
      refine .trans ?_ hf
      simpa using Set.range_comp_subset_range (Spec.map φ).base f.base) = app hU f hf ≫ φ := by
  refine app_eq hU _ _ _ ?_
  rw [Spec.map_comp, Category.assoc, Spec_map_app]

end IsAffineOpen

end Chart

/-- A natural number which is nonzero in a field `L` is a unit in `C` for every morphism
`Spec C ⟶ Spec L`. -/
private lemma isUnit_natCast {L : Type u} [Field L] {C : CommRingCat.{u}}
    (τ : Spec C ⟶ Spec (CommRingCat.of L)) {n : ℕ} (hn : (n : L) ≠ 0) : IsUnit ((n : C)) := by
  have h : ((n : C)) = (Spec.preimage τ).hom (n : L) := by rw [map_natCast]
  rw [h]
  exact (isUnit_iff_ne_zero.mpr hn).map (Spec.preimage τ).hom

namespace GrpObj

variable {K : Type u} [Field K] {G : Over (Spec (.of K))} [GrpObj G] {B : CommRingCat.{u}}
  {t : Spec B ⟶ Spec (.of K)} {I : Ideal B}

/-! ### Points trivial on the thickening

Being trivial on the thickening, i.e. `Spec.overQuotientMk I t ≫ d = 1`, is preserved by the
group operations, since precomposition is a group homomorphism. -/

private lemma one_triv : Spec.overQuotientMk I t ≫ (1 : Over.mk t ⟶ G) = 1 :=
  MonObj.comp_one _

private lemma mul_triv {c d : Over.mk t ⟶ G} (hc : Spec.overQuotientMk I t ≫ c = 1)
    (hd : Spec.overQuotientMk I t ≫ d = 1) : Spec.overQuotientMk I t ≫ (c * d) = 1 := by
  rw [MonObj.comp_mul, hc, hd, one_mul]

private lemma pow_triv {d : Over.mk t ⟶ G} (hd : Spec.overQuotientMk I t ≫ d = 1) (k : ℕ) :
    Spec.overQuotientMk I t ≫ d ^ k = 1 := by
  rw [MonObj.comp_pow, hd, one_pow]

private lemma one_left : (1 : Over.mk t ⟶ G).left = t ≫ (η[G]).left := by
  rw [Hom.one_def]; rfl

/-- A point of `G` trivial on the square-zero thickening agrees with the identity after
restricting to the thickening. -/
private lemma left_comp_quotientMk {d : Over.mk t ⟶ G}
    (hd : Spec.overQuotientMk I t ≫ d = 1) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ d.left
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (1 : Over.mk t ⟶ G).left := by
  have h := congr(($hd).left)
  rw [Over.comp_left, Spec.overQuotientMk_left] at h
  rw [h]
  simp only [one_left]
  exact Category.assoc _ _ _

private lemma triv_of_left_comp_quotientMk {c : Over.mk t ⟶ G}
    (h : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ c.left
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (1 : Over.mk t ⟶ G).left) :
    Spec.overQuotientMk I t ≫ c = 1 := by
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, Spec.overQuotientMk_left, h]
  simp only [one_left]
  exact (Category.assoc _ _ _).symm

/-- A point of `G` which is trivial on the square-zero thickening has the same image as the
identity section. -/
private lemma range_left_subset (hI : I ^ 2 = ⊥) {d : Over.mk t ⟶ G}
    (hd : Spec.overQuotientMk I t ≫ d = 1) :
    Set.range d.left ⊆ Set.range (η[G]).left := by
  have hsurj : Function.Surjective
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base :=
    (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
      (le_nilradical_of_sq_eq_bot hI)).surjective
  have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ d.left
      = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ≫ (η[G]).left := by
    rw [Category.assoc]
    exact (left_comp_quotientMk hd).trans (by rw [one_left])
  rintro _ ⟨y, rfl⟩
  obtain ⟨z, rfl⟩ := hsurj y
  refine ⟨(Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) z, ?_⟩
  exact (Scheme.Hom.comp_apply _ _ z).symm.trans
    ((congr(($h1) z)).symm.trans (Scheme.Hom.comp_apply _ _ z))

private lemma mul_left (c d : Over.mk t ⟶ G) :
    (c * d).left = pullback.lift c.left d.left (by rw [Over.w, Over.w]) ≫ (μ[G]).left := by
  rw [Hom.mul_def]; rfl

/-- The identity section is the unit of the group of points of `G`. -/
private lemma lift_unit_comp_mul :
    pullback.lift (η[G]).left (η[G]).left rfl ≫ (μ[G]).left = (η[G]).left := by
  have h : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ G) * 1 = 1 := one_mul 1
  rw [Hom.mul_def] at h
  have h2 := congr(($h).left)
  rw [Over.comp_left, Over.lift_left] at h2
  simpa only [← MonObj.one_eq_one] using h2

/-! ### The chart around the identity

Throughout, `U` is an affine open of `G` containing the image of the identity section, so that
every point trivial on the thickening factors through `U`. -/

section Chart

variable {U : G.left.Opens} (hU : IsAffineOpen U)
  (hUe : Set.range (η[G]).left ⊆ (U : Set G.left))

/-- The structure map `K ⟶ Γ(G, U)` of an affine open `U` of a `K`-scheme `G`. -/
private noncomputable def chartAlg : CommRingCat.of K ⟶ Γ(G.left, U) :=
  Spec.preimage (hU.fromSpec ≫ G.hom)

omit [GrpObj G] in
private lemma Spec_map_chartAlg : Spec.map (chartAlg hU) = hU.fromSpec ≫ G.hom :=
  Spec.map_preimage _

omit [GrpObj G] in
/-- A morphism `Spec S ⟶ G` landing in `U` is a `K`-algebra map on functions. -/
private lemma chartAlg_comp_app {S : CommRingCat.{u}} (f : Spec S ⟶ G.left)
    (hf : Set.range f ⊆ (U : Set G.left)) :
    chartAlg hU ≫ IsAffineOpen.app hU f hf = Spec.preimage (f ≫ G.hom) := by
  refine Spec.map_injective ?_
  rw [Spec.map_comp, Spec_map_chartAlg, Spec.map_preimage, ← Category.assoc,
    IsAffineOpen.Spec_map_app]

/-- The ring map on functions of the identity section of `G`. -/
private noncomputable def unitApp : Γ(G.left, U) ⟶ CommRingCat.of K :=
  IsAffineOpen.app hU (η[G]).left hUe

private lemma chartAlg_comp_unitApp : chartAlg hU ≫ unitApp hU hUe = 𝟙 _ := by
  rw [unitApp, chartAlg_comp_app]
  refine Spec.map_injective ?_
  rw [Spec.map_preimage, Spec.map_id]
  exact Over.w (η[G])

variable (hI : I ^ 2 = ⊥)

/-- The ring map on functions over `U` induced by a point of `G` trivial on the thickening. -/
private noncomputable def pt (d : Over.mk t ⟶ G) (hd : Spec.overQuotientMk I t ≫ d = 1) :
    Γ(G.left, U) ⟶ B :=
  IsAffineOpen.app hU d.left ((range_left_subset hI hd).trans hUe)

private lemma Spec_map_pt (d : Over.mk t ⟶ G) (hd : Spec.overQuotientMk I t ≫ d = 1) :
    Spec.map (pt hU hUe hI d hd) ≫ hU.fromSpec = d.left :=
  IsAffineOpen.Spec_map_app hU _ _

private lemma chartAlg_comp_pt (d : Over.mk t ⟶ G) (hd : Spec.overQuotientMk I t ≫ d = 1) :
    chartAlg hU ≫ pt hU hUe hI d hd = Spec.preimage t := by
  rw [pt, chartAlg_comp_app, Over.w d]
  rfl

private lemma pt_one :
    pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv = unitApp hU hUe ≫ Spec.preimage t := by
  refine IsAffineOpen.app_eq hU _ _ _ ?_
  rw [Spec.map_comp, Spec.map_preimage, unitApp, Category.assoc, IsAffineOpen.Spec_map_app,
    Hom.one_def]
  rfl


private lemma pt_congr {c d : Over.mk t ⟶ G} (hc : Spec.overQuotientMk I t ≫ c = 1)
    (hd : Spec.overQuotientMk I t ≫ d = 1) (h : c = d) :
    pt hU hUe hI c hc = pt hU hUe hI d hd := by
  subst h; rfl

/-- A point trivial on the thickening agrees with the identity modulo `I` on functions. -/
private lemma pt_sub_mem {d : Over.mk t ⟶ G} (hd : Spec.overQuotientMk I t ≫ d = 1)
    (x : Γ(G.left, U)) :
    (pt hU hUe hI d hd).hom x - (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom x ∈ I := by
  have key : pt hU hUe hI d hd ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)
      = pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv ≫
        CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    rw [pt, pt, ← IsAffineOpen.app_Spec_map_comp, ← IsAffineOpen.app_Spec_map_comp]
    exact IsAffineOpen.app_eq hU _ _ _
      (by rw [IsAffineOpen.Spec_map_app]; exact (left_comp_quotientMk hd).symm)
  refine (Ideal.Quotient.eq (I := I)).mp ?_
  simpa using congr(($key) x)

/-- The **tangent vector at the identity** attached to a `B`-point of `G` trivial on the
square-zero thickening: the difference between its ring map on functions over `U` and that of
the identity point. Classically this is an `I`-valued derivation on `Γ(G, U)`. -/
private noncomputable def delta (d : Over.mk t ⟶ G) (hd : Spec.overQuotientMk I t ≫ d = 1)
    (y : Γ(G.left, U)) : B :=
  (pt hU hUe hI d hd).hom y - (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y

private lemma delta_mem (d : Over.mk t ⟶ G) (hd : Spec.overQuotientMk I t ≫ d = 1)
    (y : Γ(G.left, U)) : delta hU hUe hI d hd y ∈ I :=
  pt_sub_mem hU hUe hI hd y

private lemma delta_one (y : Γ(G.left, U)) :
    delta hU hUe hI (1 : Over.mk t ⟶ G) one_triv y = 0 :=
  sub_self _

private lemma delta_congr {c d : Over.mk t ⟶ G} (hc : Spec.overQuotientMk I t ≫ c = 1)
    (hd : Spec.overQuotientMk I t ≫ d = 1) (h : c = d) (y : Γ(G.left, U)) :
    delta hU hUe hI c hc y = delta hU hUe hI d hd y := by
  subst h; rfl

/-- **The product formula.** If `c` and `d` are `B`-points of `G` which are trivial on the
square-zero thickening `Spec (B ⧸ I)`, then on functions on an affine neighbourhood of the
identity the ring map attached to `c * d` is the sum of those of `c` and `d`, minus that of the
identity. -/
private lemma pt_mul_add {c d : Over.mk t ⟶ G} (hc : Spec.overQuotientMk I t ≫ c = 1)
    (hd : Spec.overQuotientMk I t ≫ d = 1) (x : Γ(G.left, U)) :
    (pt hU hUe hI (c * d) (mul_triv hc hd)).hom x
        + (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom x
      = (pt hU hUe hI c hc).hom x + (pt hU hUe hI d hd).hom x := by
  let instA : Algebra K Γ(G.left, U) := (chartAlg hU).hom.toAlgebra
  let instB : Algebra K B := (Spec.preimage t).hom.toAlgebra
  have hA : (algebraMap K Γ(G.left, U) : K →+* Γ(G.left, U)) = (chartAlg hU).hom := rfl
  have hB : (algebraMap K B : K →+* B) = (Spec.preimage t).hom := rfl
  -- `B`-points of `G` landing in `U` are `K`-algebra maps on functions
  let mkA : ∀ (d' : Over.mk t ⟶ G), Spec.overQuotientMk I t ≫ d' = 1 →
      (Γ(G.left, U) →ₐ[K] B) := fun d' hd' ↦
    { (pt hU hUe hI d' hd').hom with
      commutes' := fun r ↦ by
        rw [hA, hB]
        exact congr(($(chartAlg_comp_pt hU hUe hI d' hd')).hom r) }
  -- the identity section as a `K`-algebra map on functions
  let eA : Γ(G.left, U) →ₐ[K] K :=
    { (unitApp hU hUe).hom with
      commutes' := fun r ↦ by
        rw [hA]
        simpa using congr(($(chartAlg_comp_unitApp hU hUe)).hom r) }
  -- the affine scheme `U ×_K U` and its two projections
  let T := (Γ(G.left, U) : Type u) ⊗[K] (Γ(G.left, U) : Type u)
  let i₁ : Γ(G.left, U) ⟶ CommRingCat.of T :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let i₂ : Γ(G.left, U) ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K)
      (A := (Γ(G.left, U) : Type u)) (B := (Γ(G.left, U) : Type u))).toRingHom
  have hcomm : (Spec.map i₁ ≫ hU.fromSpec) ≫ G.hom = (Spec.map i₂ ≫ hU.fromSpec) ≫ G.hom := by
    rw [Category.assoc, Category.assoc, ← Spec_map_chartAlg, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    change Algebra.TensorProduct.includeLeftRingHom ((chartAlg hU).hom r)
      = Algebra.TensorProduct.includeRight ((chartAlg hU).hom r)
    rw [← hA]
    exact RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := K) (A := (Γ(G.left, U) : Type u)) (B := (Γ(G.left, U) : Type u))) r
  let jT : Spec (CommRingCat.of T) ⟶ pullback G.hom G.hom :=
    pullback.lift (Spec.map i₁ ≫ hU.fromSpec) (Spec.map i₂ ≫ hU.fromSpec) hcomm
  have hjT₁ : jT ≫ pullback.fst G.hom G.hom = Spec.map i₁ ≫ hU.fromSpec :=
    pullback.lift_fst _ _ _
  have hjT₂ : jT ≫ pullback.snd G.hom G.hom = Spec.map i₂ ≫ hU.fromSpec :=
    pullback.lift_snd _ _ _
  let g : Spec (CommRingCat.of T) ⟶ G.left := jT ≫ (μ[G]).left
  have hg : g = jT ≫ (μ[G]).left := rfl
  -- the identity point of `U ×_K U`
  let θ : T →ₐ[K] K := Algebra.TensorProduct.lift eA eA fun _ _ ↦ .all _ _
  have hi₁ : i₁ ≫ CommRingCat.ofHom θ.toRingHom = unitApp hU hUe := by
    ext y; change eA y * eA 1 = _; simp; rfl
  have hi₂ : i₂ ≫ CommRingCat.ofHom θ.toRingHom = unitApp hU hUe := by
    ext y; change eA 1 * eA y = _; simp; rfl
  have hz : Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ g = (η[G]).left := by
    have h : Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ jT
        = pullback.lift (η[G]).left (η[G]).left rfl := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hjT₁, pullback.lift_fst, ← Category.assoc, ← Spec.map_comp, hi₁,
          unitApp, IsAffineOpen.Spec_map_app]
      · rw [Category.assoc, hjT₂, pullback.lift_snd, ← Category.assoc, ← Spec.map_comp, hi₂,
          unitApp, IsAffineOpen.Spec_map_app]
    rw [hg, ← Category.assoc, h, lift_unit_comp_mul]
  let pt0 : ↥(Spec (CommRingCat.of K)) := default
  have hp₀ : g ((Spec.map (CommRingCat.ofHom θ.toRingHom)) pt0) ∈ U := by
    have h : (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ g) pt0 = (η[G]).left pt0 :=
      congr(($hz) pt0)
    rw [Scheme.Hom.comp_apply] at h
    rw [h]
    exact hUe ⟨_, rfl⟩
  -- a basic open around it on which the multiplication lands in `U`
  obtain ⟨r, hrle, hrmem⟩ := (isAffineOpen_top (Spec (CommRingCat.of T))).exists_basicOpen_le
    (V := g ⁻¹ᵁ U) ⟨_, hp₀⟩ trivial
  let s : T := (Scheme.ΓSpecIso (CommRingCat.of T)).hom r
  have hbo : (Spec (CommRingCat.of T)).basicOpen r = PrimeSpectrum.basicOpen s :=
    basicOpen_eq_of_affine' r
  have hsne : θ s ≠ 0 := by
    rw [hbo] at hrmem
    have hmem : s ∉ (PrimeSpectrum.comap θ.toRingHom pt0).asIdeal :=
      (PrimeSpectrum.mem_basicOpen s (PrimeSpectrum.comap θ.toRingHom pt0)).mp hrmem
    intro h0
    refine hmem ?_
    change θ s ∈ pt0.asIdeal
    rw [h0]
    exact Submodule.zero_mem _
  -- the comultiplication into the localization of `Γ(U ×_K U)` at `s`
  let algTL : CommRingCat.of T ⟶ CommRingCat.of (Localization.Away s) :=
    CommRingCat.ofHom (algebraMap T (Localization.Away s))
  have hrangeL : ∀ y, (Spec.map algTL) y ∈ (Spec (CommRingCat.of T)).basicOpen r := by
    intro y
    rw [hbo]
    have h : ((Spec.map algTL) y : PrimeSpectrum T) ∈
        (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum T)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
      exact ⟨y, rfl⟩
    exact h
  have hjL : Set.range (Spec.map algTL ≫ g) ⊆ (U : Set G.left) := by
    rintro _ ⟨y, rfl⟩
    exact hrle (hrangeL y)
  let m : Γ(G.left, U) ⟶ CommRingCat.of (Localization.Away s) := IsAffineOpen.app hU _ hjL
  have hm : Spec.map m ≫ hU.fromSpec = Spec.map algTL ≫ g := IsAffineOpen.Spec_map_app hU _ hjL
  -- units and nilpotents
  have hunit_of : ∀ a b : B, IsUnit b → a - b ∈ I → IsUnit a := by
    intro a b hb hab
    have hn : IsNilpotent (a - b) := le_nilradical_of_sq_eq_bot hI hab
    have := hn.isUnit_add_left_of_commute hb (Commute.all _ _)
    simpa using this
  -- the point of `U ×_K U` attached to a pair of points of `G`
  let Ψ : ∀ (c' : Over.mk t ⟶ G), Spec.overQuotientMk I t ≫ c' = 1 →
      ∀ (d' : Over.mk t ⟶ G), Spec.overQuotientMk I t ≫ d' = 1 → (T →ₐ[K] B) :=
    fun c' hc' d' hd' ↦ Algebra.TensorProduct.lift (mkA c' hc') (mkA d' hd') fun _ _ ↦ .all _ _
  have hΨ0 : ∀ z : T, Ψ 1 one_triv 1 one_triv z = (Spec.preimage t).hom (θ z) := by
    intro z
    refine z.induction_on (by simp) (fun y y' ↦ ?_) (fun y y' hy hy' ↦ by simp [hy, hy'])
    change (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y
        * (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y' = _
    rw [pt_one]
    change (Spec.preimage t).hom ((unitApp hU hUe).hom y)
      * (Spec.preimage t).hom ((unitApp hU hUe).hom y') = _
    rw [← map_mul]
    rfl
  have hΨsub : ∀ (c' : Over.mk t ⟶ G) (hc' : Spec.overQuotientMk I t ≫ c' = 1)
      (d' : Over.mk t ⟶ G) (hd' : Spec.overQuotientMk I t ≫ d' = 1) (z : T),
      Ψ c' hc' d' hd' z - Ψ 1 one_triv 1 one_triv z ∈ I := by
    intro c' hc' d' hd' z
    refine z.induction_on (by simp) (fun y y' ↦ ?_) (fun y y' hy hy' ↦ ?_)
    · change (pt hU hUe hI c' hc').hom y * (pt hU hUe hI d' hd').hom y'
        - (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y
          * (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y' ∈ I
      have h1 := pt_sub_mem hU hUe hI hc' y
      have h2 := pt_sub_mem hU hUe hI hd' y'
      have h3 : (pt hU hUe hI c' hc').hom y * (pt hU hUe hI d' hd').hom y'
          - (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y
            * (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y'
          = ((pt hU hUe hI c' hc').hom y
              - (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y)
            * (pt hU hUe hI d' hd').hom y'
            + (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y
              * ((pt hU hUe hI d' hd').hom y'
                - (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y') := by ring
      rw [h3]
      exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2)
    · simpa only [map_add, add_sub_add_comm] using I.add_mem hy hy'
  -- the key factorisation of the multiplication through the localization
  have main : ∀ (c' : Over.mk t ⟶ G) (hc' : Spec.overQuotientMk I t ≫ c' = 1)
      (d' : Over.mk t ⟶ G) (hd' : Spec.overQuotientMk I t ≫ d' = 1),
      ∃ ψ : Localization.Away s →+* B,
        (∀ y y' : Γ(G.left, U), ψ (algebraMap T (Localization.Away s) (y ⊗ₜ y'))
          = (pt hU hUe hI c' hc').hom y * (pt hU hUe hI d' hd').hom y') ∧
        (∀ y, ψ (m.hom y) = (pt hU hUe hI (c' * d') (mul_triv hc' hd')).hom y) := by
    intro c' hc' d' hd'
    have hunit : IsUnit (Ψ c' hc' d' hd' s) := by
      refine hunit_of _ _ ?_ (hΨsub c' hc' d' hd' s)
      rw [hΨ0]
      exact (isUnit_iff_ne_zero.mpr hsne).map (Spec.preimage t).hom
    set ψ : Localization.Away s →+* B :=
      IsLocalization.Away.lift s (g := (Ψ c' hc' d' hd').toRingHom) hunit with hψdef
    have hψ : ∀ y y' : Γ(G.left, U), ψ (algebraMap T (Localization.Away s) (y ⊗ₜ y'))
        = (pt hU hUe hI c' hc').hom y * (pt hU hUe hI d' hd').hom y' := by
      intro y y'
      rw [hψdef, IsLocalization.Away.lift_eq]
      rfl
    refine ⟨ψ, hψ, fun y ↦ ?_⟩
    have hcomp₁ : i₁ ≫ algTL ≫ CommRingCat.ofHom ψ = pt hU hUe hI c' hc' := by
      ext y'
      change ψ (algebraMap T (Localization.Away s) (y' ⊗ₜ 1)) = _
      rw [hψ]
      simp
    have hcomp₂ : i₂ ≫ algTL ≫ CommRingCat.ofHom ψ = pt hU hUe hI d' hd' := by
      ext y'
      change ψ (algebraMap T (Localization.Away s) (1 ⊗ₜ y')) = _
      rw [hψ]
      simp
    have hfst : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map algTL ≫ jT
        ≫ pullback.fst G.hom G.hom = c'.left := by
      rw [hjT₁, ← Spec_map_pt hU hUe hI c' hc', ← hcomp₁]
      simp [Spec.map_comp]
    have hsnd : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map algTL ≫ jT
        ≫ pullback.snd G.hom G.hom = d'.left := by
      rw [hjT₂, ← Spec_map_pt hU hUe hI d' hd', ← hcomp₂]
      simp [Spec.map_comp]
    have hfac : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map algTL ≫ jT
        = pullback.lift c'.left d'.left (by rw [Over.w, Over.w]) := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, Category.assoc, Category.assoc]; exact hfst
      · rw [pullback.lift_snd, Category.assoc, Category.assoc]; exact hsnd
    have key : m ≫ CommRingCat.ofHom ψ = pt hU hUe hI (c' * d') (mul_triv hc' hd') := by
      rw [pt]
      refine (IsAffineOpen.app_eq hU _ _ _ ?_).symm
      rw [Spec.map_comp, Category.assoc, hm, hg, mul_left, ← hfac]
      simp
    simpa using congr(($key) y)
  obtain ⟨ψ₁, e₁, f₁⟩ := main c hc d hd
  obtain ⟨ψ₂, e₂, f₂⟩ := main c hc 1 one_triv
  obtain ⟨ψ₃, e₃, f₃⟩ := main 1 one_triv d hd
  obtain ⟨ψ₄, e₄, f₄⟩ := main 1 one_triv 1 one_triv
  have key := localization_tmul_add_eq (I := I) (s := s) hI (pt hU hUe hI c hc).hom
    (pt hU hUe hI d hd).hom (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom
    (pt_sub_mem hU hUe hI hc) (pt_sub_mem hU hUe hI hd) ψ₁ ψ₂ ψ₃ ψ₄ e₁ e₂ e₃ e₄ (m.hom x)
  rw [f₁, f₂, f₃, f₄] at key
  rw [pt_congr hU hUe hI _ _ (mul_one c), pt_congr hU hUe hI _ _ (one_mul d),
    pt_congr hU hUe hI _ _ (one_mul (1 : Over.mk t ⟶ G))] at key
  exact key

/-- A point trivial on the thickening is determined by its ring map on functions. -/
private lemma eq_of_pt_eq {c d : Over.mk t ⟶ G} (hc : Spec.overQuotientMk I t ≫ c = 1)
    (hd : Spec.overQuotientMk I t ≫ d = 1) (h : pt hU hUe hI c hc = pt hU hUe hI d hd) :
    c = d := by
  refine Over.OverMorphism.ext ?_
  rw [← Spec_map_pt hU hUe hI c hc, ← Spec_map_pt hU hUe hI d hd, h]


/-- The product formula, in terms of tangent vectors: the tangent vector of a product is the
sum of the tangent vectors. -/
private lemma delta_mul {c d : Over.mk t ⟶ G} (hc : Spec.overQuotientMk I t ≫ c = 1)
    (hd : Spec.overQuotientMk I t ≫ d = 1) (y : Γ(G.left, U)) :
    delta hU hUe hI (c * d) (mul_triv hc hd) y
      = delta hU hUe hI c hc y + delta hU hUe hI d hd y := by
  have h := pt_mul_add hU hUe hI hc hd y
  simp only [delta]
  linear_combination h

/-- The tangent vector of the `k`-th power of a point is `k` times its tangent vector. -/
private lemma delta_pow (d : Over.mk t ⟶ G) (hd : Spec.overQuotientMk I t ≫ d = 1) (k : ℕ)
    (y : Γ(G.left, U)) :
    delta hU hUe hI (d ^ k) (pow_triv hd k) y = k • delta hU hUe hI d hd y := by
  induction k with
  | zero =>
      rw [delta_congr hU hUe hI (pow_triv hd 0) one_triv (pow_zero d) y,
        delta_one hU hUe hI y, zero_nsmul]
  | succ k ih =>
      rw [delta_congr hU hUe hI (pow_triv hd (k + 1)) (mul_triv (pow_triv hd k) hd)
        (pow_succ d k) y, delta_mul hU hUe hI (pow_triv hd k) hd y, ih, succ_nsmul]

include hU hUe hI in
/-- **Rigidity, in a chart.** -/
private lemma eq_one_of_pow_eq_one_aux {n : ℕ} (hn : (n : K) ≠ 0) (d : Over.mk t ⟶ G)
    (hd : Spec.overQuotientMk I t ≫ d = 1) (hdn : d ^ n = 1) : d = 1 := by
  refine eq_of_pt_eq hU hUe hI hd one_triv (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
  have h := delta_pow hU hUe hI d hd n x
  rw [delta_congr hU hUe hI (pow_triv hd n) one_triv hdn x, delta_one hU hUe hI x,
    nsmul_eq_mul] at h
  have h0 := ((isUnit_natCast t hn).mul_right_eq_zero).mp h.symm
  rw [delta, sub_eq_zero] at h0
  exact h0

include hU hUe hI in
/-- **Divisibility, in a chart.** -/
private lemma exists_pow_eq_aux {n : ℕ} (hn : (n : K) ≠ 0) (d : Over.mk t ⟶ G)
    (hd : Spec.overQuotientMk I t ≫ d = 1) :
    ∃ c : Over.mk t ⟶ G, Spec.overQuotientMk I t ≫ c = 1 ∧ c ^ n = d := by
  obtain ⟨u, hu⟩ := (isUnit_natCast t hn).exists_right_inv
  -- the `n`-th root of `d`, on functions: the identity point plus `1 / n` times the tangent
  -- vector of `d`; this is a ring map because the tangent vector is `I`-valued and `I ^ 2 = ⊥`
  let φ : Γ(G.left, U) →+* B :=
    { toFun := fun y ↦ (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y
        + u * delta hU hUe hI d hd y
      map_one' := by simp [delta]
      map_zero' := by simp [delta]
      map_add' := fun a b ↦ by simp only [delta, map_add]; ring
      map_mul' := fun a b ↦ by
        have h0 := mul_eq_zero_of_sq_eq_bot hI (delta_mem hU hUe hI d hd a)
          (delta_mem hU hUe hI d hd b)
        simp only [delta, map_mul] at h0 ⊢
        linear_combination (u - u * u) * h0 }
  -- it is a `K`-algebra map, since the tangent vector kills constants
  have hφ : chartAlg hU ≫ CommRingCat.ofHom φ = Spec.preimage t := by
    refine CommRingCat.hom_ext (RingHom.ext fun y ↦ ?_)
    have h1 : (pt hU hUe hI d hd).hom ((chartAlg hU).hom y) = (Spec.preimage t).hom y :=
      congr(($(chartAlg_comp_pt hU hUe hI d hd)).hom y)
    have h2 : (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom ((chartAlg hU).hom y)
        = (Spec.preimage t).hom y :=
      congr(($(chartAlg_comp_pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv)).hom y)
    change (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom ((chartAlg hU).hom y)
      + u * delta hU hUe hI d hd ((chartAlg hU).hom y) = _
    rw [delta, h1, h2]
    ring
  -- hence it defines a `B`-point of `G`
  have hw : (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ≫ G.hom = (Over.mk t).hom := by
    rw [Category.assoc, ← Spec_map_chartAlg, ← Spec.map_comp, hφ, Spec.map_preimage]
    rfl
  have hc : Spec.overQuotientMk I t
      ≫ Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) hw = 1 := by
    refine triv_of_left_comp_quotientMk ?_
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec = _
    rw [← Spec_map_pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv, ← Category.assoc, ← Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    refine CommRingCat.hom_ext (RingHom.ext fun y ↦ ?_)
    refine (Ideal.Quotient.eq (I := I)).mpr ?_
    change (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y + u * delta hU hUe hI d hd y
        - (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom y ∈ I
    simpa using I.mul_mem_left u (delta_mem hU hUe hI d hd y)
  refine ⟨_, hc, ?_⟩
  have hptc : pt hU hUe hI _ hc = CommRingCat.ofHom φ := IsAffineOpen.app_eq hU _ _ _ rfl
  refine eq_of_pt_eq hU hUe hI (pow_triv hc n) hd
    (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
  have h2 : delta hU hUe hI _ hc x = u * delta hU hUe hI d hd x := by
    rw [delta, hptc]
    change (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom x + u * delta hU hUe hI d hd x
      - (pt hU hUe hI (1 : Over.mk t ⟶ G) one_triv).hom x = _
    ring
  have h := delta_pow hU hUe hI _ hc n x
  rw [h2, nsmul_eq_mul, ← mul_assoc, hu, one_mul, delta, delta, sub_left_inj] at h
  exact h

end Chart

/-! ### Rigidity and divisibility -/

/-- There is an affine open neighbourhood of the image of the identity section. -/
private lemma exists_chart : ∃ (U : G.left.Opens) (_ : IsAffineOpen U),
    Set.range (η[G]).left ⊆ (U : Set G.left) := by
  have hss : Subsingleton ↥(𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of K)))
  obtain ⟨y₀⟩ : Nonempty ↥(𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (Nonempty ↥(Spec (CommRingCat.of K)))
  obtain ⟨_, ⟨V, hV, rfl⟩, hmem, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((η[G]).left y₀)) isOpen_univ
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨y, rfl⟩
  rw [@Subsingleton.elim _ hss y y₀]
  exact hmem

/-- **Rigidity for points trivial on a square-zero thickening.** If `n` is invertible in `K`,
a `B`-point of a group scheme `G` over `K` which is trivial on the square-zero thickening
`Spec (B ⧸ I)` and whose `n`-th power is trivial is itself trivial. -/
theorem eq_one_of_pow_eq_one (hI : I ^ 2 = ⊥) {n : ℕ} (hn : (n : K) ≠ 0) (d : Over.mk t ⟶ G)
    (hd : Spec.overQuotientMk I t ≫ d = 1) (hdn : d ^ n = 1) : d = 1 := by
  obtain ⟨U, hU, hUe⟩ := exists_chart (G := G)
  exact eq_one_of_pow_eq_one_aux hU hUe hI hn d hd hdn

/-- **Divisibility for points trivial on a square-zero thickening.** If `n` is invertible in `K`,
every `B`-point of a group scheme `G` over `K` which is trivial on the square-zero thickening
`Spec (B ⧸ I)` is the `n`-th power of such a point. -/
theorem exists_pow_eq (hI : I ^ 2 = ⊥) {n : ℕ} (hn : (n : K) ≠ 0) (d : Over.mk t ⟶ G)
    (hd : Spec.overQuotientMk I t ≫ d = 1) :
    ∃ c : Over.mk t ⟶ G, Spec.overQuotientMk I t ≫ c = 1 ∧ c ^ n = d := by
  obtain ⟨U, hU, hUe⟩ := exists_chart (G := G)
  exact exists_pow_eq_aux hU hUe hI hn d hd

end GrpObj


end AlgebraicGeometry
