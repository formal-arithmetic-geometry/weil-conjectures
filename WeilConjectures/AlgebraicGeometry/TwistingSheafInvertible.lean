/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Picard
public import WeilConjectures.AlgebraicGeometry.Modules.Sheafification
public import WeilConjectures.AlgebraicGeometry.TwistingSheaf

/-!
# The twisting sheaves `𝒪(d)` on `Proj` are invertible

Let `𝒜 : ℕ → σ` be a graded ring with underlying ring `A`, and let `𝒪(d)`, `d : ℤ`, be the
twisting sheaves on `Proj 𝒜` constructed in `WeilConjectures/AlgebraicGeometry/TwistingSheaf.lean`.
Multiplying fractions gives a morphism of presheaves of `𝒪`-modules
`𝒪(d) ⊗ 𝒪(e) ⟶ 𝒪(d + e)` from the *sectionwise* tensor product, and we show that it is locally
bijective, hence that it identifies the tensor product of sheaves of modules
`𝒪(d) ⊗ 𝒪(e)` with `𝒪(d + e)`.

Local bijectivity holds over a basic open set `D₊(f)` with `f` homogeneous of degree `m` dividing
both `d` and `e`: there `𝒪(d)`, `𝒪(e)` and `𝒪(d + e)` are free of rank one on `f ^ (d / m)`,
`f ^ (e / m)` and `f ^ (d / m + e / m)`, and multiplication is the obvious bijection. The
hypothesis that such basic open sets cover `Proj 𝒜` is `Proj.IsCoveredByDvdDegree`; it holds for
all `d` and `e` when the irrelevant ideal of `𝒜` is generated in degree one, for instance for a
polynomial ring.

Taking `e = -d` and using `𝒪(0) ≅ 𝒪` then shows that `𝒪(d)` is an invertible sheaf.

## Main definitions

- `AlgebraicGeometry.Proj.IsCoveredByDvdDegree`: the condition that `Proj 𝒜` is covered by the
  basic open sets `D₊(f)` for `f` homogeneous of a degree dividing both `d` and `e`.
- `AlgebraicGeometry.Proj.twistingSheafTensorIso`: the isomorphism
  `𝒪(d) ⊗ 𝒪(e) ≅ 𝒪(d + e)`.

## Main results

- `AlgebraicGeometry.Proj.invertible_twistingSheaf`: `𝒪(d)` is an invertible sheaf of modules.
- `AlgebraicGeometry.Proj.invertible_twistingSheaf_of_irrelevant_le_span`: on `Proj` of a graded
  ring whose irrelevant ideal is generated in degree one, `𝒪(d)` is invertible for every `d : ℤ`.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace TopCat

namespace AlgebraicGeometry

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveSpectrum.TwistingSheaf

/-- The ring of sections of the structure sheaf of `Proj 𝒜` over `U`, spelled as the value at `U`
of the presheaf of rings over which the twisting presheaves are presheaves of modules, so that
scalar multiplication on their sections is found by instance resolution. -/
abbrev sectionRing (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) : RingCat :=
  ((Proj 𝒜).sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U

/-- The `d`-th twisting presheaf as a presheaf of `𝒪`-modules on `Proj 𝒜`, spelled over the
presheaf of rings `𝒪 ⋙ forget₂ CommRingCat RingCat` so that the monoidal structure on presheaves
of modules is found by instance resolution. -/
abbrev twistingPresheaf (d : ℤ) :
    PresheafOfModules ((Proj 𝒜).sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  presheafOfModules 𝒜 d

/-- The sections of the `d`-th twisting presheaf over `U`. -/
abbrev sectionModule (d : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    ModuleCat (sectionRing 𝒜 U) :=
  (twistingPresheaf 𝒜 d).obj U

variable {𝒜}

/-- The product of a local fraction of degree `d` and a local fraction of degree `e` is a local
fraction of degree `d + e`. -/
theorem mul_mem'' {d e c : ℤ} (hc : d + e = c) {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    {a b : ∀ x : U.unop, atPoint 𝒜 x.1}
    (ha : (isLocallyFraction 𝒜 d).pred a) (hb : (isLocallyFraction 𝒜 e).pred b) :
    (isLocallyFraction 𝒜 c).pred (fun x ↦ a x * b x) := by
  subst hc
  intro x
  obtain ⟨V₁, m₁, e₁, i₁, j₁, h₁, ⟨r₁, hr₁⟩, ⟨s₁, hs₁⟩, hw₁, w₁⟩ := ha x
  obtain ⟨V₂, m₂, e₂, i₂, j₂, h₂, ⟨r₂, hr₂⟩, ⟨s₂, hs₂⟩, hw₂, w₂⟩ := hb x
  refine ⟨V₁ ⊓ V₂, ⟨m₁, m₂⟩, Opens.infLELeft _ _ ≫ e₁, i₁ + i₂, j₁ + j₂, by push_cast; omega,
    ⟨r₁ * r₂, SetLike.mul_mem_graded hr₁ hr₂⟩, ⟨s₁ * s₂, SetLike.mul_mem_graded hs₁ hs₂⟩,
    fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hw₁ ⟨y.1, y.2.1⟩)
      (hw₂ ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at w₁ w₂
  simp [w₁ y hy.1, w₂ y hy.2, Localization.mk_mul]
  rfl

section Apply

variable {d : ℤ} {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}

@[simp]
theorem sectionModule_smul_apply (c : sectionRing 𝒜 U) (a : sectionModule 𝒜 d U) (x : U.unop) :
    (c • a).1 x = (c.1 x).val * a.1 x := rfl

@[simp]
theorem sectionModule_add_apply (a b : sectionModule 𝒜 d U) (x : U.unop) :
    (a + b).1 x = a.1 x + b.1 x := rfl

@[simp]
theorem sectionModule_zero_apply (x : U.unop) : (0 : sectionModule 𝒜 d U).1 x = 0 := rfl

@[simp]
theorem val_mul_apply (g h : sectionRing 𝒜 U) (x : U.unop) :
    ((g * h).1 x).val = (g.1 x).val * (h.1 x).val :=
  HomogeneousLocalization.val_mul _ _

@[simp]
theorem val_add_apply (g h : sectionRing 𝒜 U) (x : U.unop) :
    ((g + h).1 x).val = (g.1 x).val + (h.1 x).val :=
  HomogeneousLocalization.val_add _ _

@[simp]
theorem val_zero_apply (x : U.unop) : ((0 : sectionRing 𝒜 U).1 x).val = 0 :=
  HomogeneousLocalization.val_zero

end Apply

section Generator

variable {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
  (hU : ∀ x : U.unop, f ∉ x.1.asHomogeneousIdeal.toIdeal)

/-- If a homogeneous element `f` does not belong to a point `x` of `Proj 𝒜`, then the fraction
`f / 1` is a unit of the localization `A_x`. -/
def unitAtPoint {x : ProjectiveSpectrum 𝒜} (hx : f ∉ x.asHomogeneousIdeal.toIdeal) :
    (atPoint 𝒜 x)ˣ where
  val := Localization.mk f 1
  inv := Localization.mk 1 ⟨f, hx⟩
  val_inv := by rw [mul_comm]; exact Localization.mk_one_mul_mk_one ⟨f, hx⟩
  inv_val := Localization.mk_one_mul_mk_one ⟨f, hx⟩

/-- The integral power `f ^ k` of an element `f` which is invertible at every point of the open
set `U`, as a dependent function on `U`. When `f` is homogeneous of degree `m`, this is a section
of `𝒪(m * k)`, see `AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.powFun_mem`. -/
def powFun (k : ℤ) (x : U.unop) : atPoint 𝒜 x.1 :=
  ((unitAtPoint (hU x)) ^ k : (atPoint 𝒜 x.1)ˣ)

theorem powFun_add (k l : ℤ) (x : U.unop) :
    powFun hU (k + l) x = powFun hU k x * powFun hU l x := by
  simp [powFun, zpow_add]

@[simp]
theorem powFun_zero (x : U.unop) : powFun hU 0 x = 1 := by simp [powFun]

theorem powFun_natCast (n : ℕ) (x : U.unop) :
    powFun hU (n : ℤ) x = Localization.mk (f ^ n) 1 := by
  simp [powFun, unitAtPoint, Localization.mk_pow]

theorem powFun_neg_natCast (n : ℕ) (x : U.unop)
    (hx : f ^ n ∉ x.1.asHomogeneousIdeal.toIdeal) :
    powFun hU (-(n : ℤ)) x = Localization.mk 1 ⟨f ^ n, hx⟩ := by
  rw [powFun, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  simp only [unitAtPoint, Units.inv_mk, Localization.mk_pow, one_pow]
  rfl

include hU in
theorem pow_notMem (n : ℕ) (x : U.unop) : f ^ n ∉ x.1.asHomogeneousIdeal.toIdeal := by
  induction n with
  | zero => simpa using (Ideal.ne_top_iff_one _).mp x.1.isPrime.ne_top
  | succ n ih =>
    rw [pow_succ]
    exact fun h ↦ (x.1.isPrime.mem_or_mem h).elim ih (hU x)

include hf in
theorem powFun_mem (k : ℤ) {c : ℤ} (hc : c = m * k) :
    (isLocallyFraction 𝒜 c).pred (powFun hU k) := by
  apply PrelocalPredicate.sheafifyOf
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact ⟨0, n * m, by subst hc; push_cast; ring, ⟨f ^ n, by
      simpa [smul_eq_mul] using SetLike.pow_mem_graded n hf⟩, ⟨1, SetLike.one_mem_graded 𝒜⟩,
      fun y ↦ (Ideal.ne_top_iff_one _).mp y.1.isPrime.ne_top,
      fun y ↦ (powFun_natCast hU n y).trans rfl⟩
  · exact ⟨n * m, 0, by subst hc; push_cast; ring, ⟨1, SetLike.one_mem_graded 𝒜⟩, ⟨f ^ n, by
      simpa [smul_eq_mul] using SetLike.pow_mem_graded n hf⟩,
      fun y ↦ pow_notMem hU n y, fun y ↦ powFun_neg_natCast hU n y _⟩

include hf

/-- The generator `f ^ k` of the sections of `𝒪(m * k)` over an open set on which the
homogeneous element `f` of degree `m` is invertible. -/
def sectionPow (k : ℤ) {c : ℤ} (hc : c = m * k) : sectionModule 𝒜 c U :=
  ⟨powFun hU k, powFun_mem hf hU k hc⟩

@[simp]
theorem sectionPow_apply (k : ℤ) {c : ℤ} (hc : c = m * k) (x : U.unop) :
    (sectionPow hf hU k hc).1 x = powFun hU k x := rfl

/-- The coefficient of a section of `𝒪(m * k)` with respect to the generator `f ^ k`, over an
open set on which the homogeneous element `f` of degree `m` is invertible. -/
def powCoeff (k : ℤ) {c : ℤ} (hc : c = m * k) (s : sectionModule 𝒜 c U) : sectionRing 𝒜 U :=
  sectionsZeroInv ⟨fun x ↦ s.1 x * powFun hU (-k) x,
    mul_mem'' (by rw [hc]; ring) s.2 (powFun_mem hf hU (-k) rfl)⟩

@[simp]
theorem val_powCoeff (k : ℤ) {c : ℤ} (hc : c = m * k) (s : sectionModule 𝒜 c U) (x : U.unop) :
    ((powCoeff hf hU k hc s).1 x).val = s.1 x * powFun hU (-k) x :=
  val_sectionsZeroInv _ x

theorem powCoeff_smul (k : ℤ) {c : ℤ} (hc : c = m * k) (s : sectionModule 𝒜 c U) :
    powCoeff hf hU k hc s • sectionPow hf hU k hc = s := by
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [sectionModule_smul_apply, sectionPow_apply, val_powCoeff, mul_assoc, ← powFun_add]
  simp

theorem powCoeff_smul_gen (k : ℤ) {c : ℤ} (hc : c = m * k) (g : sectionRing 𝒜 U) :
    powCoeff hf hU k hc (g • sectionPow hf hU k hc) = g := by
  refine Subtype.ext (funext fun x ↦ HomogeneousLocalization.val_injective _ ?_)
  rw [val_powCoeff, sectionModule_smul_apply, sectionPow_apply, mul_assoc, ← powFun_add]
  simp

theorem powCoeff_add (k : ℤ) {c : ℤ} (hc : c = m * k) (s t : sectionModule 𝒜 c U) :
    powCoeff hf hU k hc (s + t) = powCoeff hf hU k hc s + powCoeff hf hU k hc t := by
  refine Subtype.ext (funext fun x ↦ HomogeneousLocalization.val_injective _ ?_)
  rw [val_powCoeff, val_add_apply, val_powCoeff, val_powCoeff, sectionModule_add_apply]
  exact add_mul _ _ _

theorem powCoeff_zero (k : ℤ) {c : ℤ} (hc : c = m * k) : powCoeff hf hU k hc 0 = 0 := by
  refine Subtype.ext (funext fun x ↦ HomogeneousLocalization.val_injective _ ?_)
  rw [val_powCoeff, val_zero_apply, sectionModule_zero_apply]
  exact zero_mul _

theorem powCoeff_mul {c d e a b : ℤ} (hd : d = m * a) (he : e = m * b) (hc : c = m * (a + b))
    (hde : d + e = c) (s : sectionModule 𝒜 d U) (t : sectionModule 𝒜 e U) :
    powCoeff hf hU (a + b) hc ⟨fun x ↦ s.1 x * t.1 x, mul_mem'' hde s.2 t.2⟩ =
      powCoeff hf hU a hd s * powCoeff hf hU b he t := by
  refine Subtype.ext (funext fun x ↦ HomogeneousLocalization.val_injective _ ?_)
  rw [val_powCoeff, val_mul_apply, val_powCoeff, val_powCoeff, neg_add, powFun_add]
  ring

end Generator

variable (𝒜)

/-- Sectionwise multiplication, as a morphism of presheaves of `𝒪`-modules on `Proj 𝒜` from the
sectionwise tensor product of `𝒪(d)` and `𝒪(e)` to `𝒪(d + e)`. -/
def tensorMulHom (d e : ℤ) :
    twistingPresheaf 𝒜 d ⊗ twistingPresheaf 𝒜 e ⟶ twistingPresheaf 𝒜 (d + e) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun s t ↦ (⟨fun x ↦ s.1 x * t.1 x, mul_mem'' rfl s.2 t.2⟩ : sectionModule 𝒜 (d + e) U))
    (fun _ _ _ ↦ Subtype.ext (funext fun _ ↦ add_mul _ _ _))
    (fun _ _ _ ↦ Subtype.ext (funext fun _ ↦ mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (funext fun _ ↦ mul_add _ _ _))
    (fun _ _ _ ↦ Subtype.ext (funext fun _ ↦ mul_left_comm _ _ _))
  naturality _ := ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl)

variable {𝒜}

theorem tensorMulHom_app_tmul {d e : ℤ} {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : sectionModule 𝒜 d U) (t : sectionModule 𝒜 e U) :
    ((tensorMulHom 𝒜 d e).app U).hom (s ⊗ₜ t) =
      ⟨fun x ↦ s.1 x * t.1 x, mul_mem'' rfl s.2 t.2⟩ := rfl

section Bijective

variable {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
  (hU : ∀ x : U.unop, f ∉ x.1.asHomogeneousIdeal.toIdeal)

include hf hU in
/-- **Local triviality of the multiplication map**: over an open set on which a homogeneous
element `f` of degree `m` is invertible, and when `m` divides both `d` and `e`, sectionwise
multiplication is a bijection from the tensor product of the sections of `𝒪(d)` and `𝒪(e)` onto
the sections of `𝒪(d + e)`. Indeed both are free of rank one, generated by `f ^ a ⊗ f ^ b` and
`f ^ (a + b)` respectively. -/
theorem bijective_tensorMulHom_app {d e a b : ℤ} (hd : d = m * a) (he : e = m * b) :
    Function.Bijective ((tensorMulHom 𝒜 d e).app U).hom := by
  have hde : d + e = (m : ℤ) * (a + b) := by rw [hd, he]; ring
  have hgen : ((tensorMulHom 𝒜 d e).app U).hom
      (sectionPow hf hU a hd ⊗ₜ sectionPow hf hU b he) = sectionPow hf hU (a + b) hde := by
    rw [tensorMulHom_app_tmul]
    exact Subtype.ext (funext fun x ↦ (powFun_add hU a b x).symm)
  have key : ∀ t : ((twistingPresheaf 𝒜 d ⊗ twistingPresheaf 𝒜 e).obj U : Type _),
      powCoeff hf hU (a + b) hde (((tensorMulHom 𝒜 d e).app U).hom t) •
        (sectionPow hf hU a hd ⊗ₜ sectionPow hf hU b he) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, powCoeff_zero, zero_smul]
    | tmul p q =>
      rw [tensorMulHom_app_tmul, powCoeff_mul hf hU hd he hde rfl,
        ← TensorProduct.smul_tmul_smul, powCoeff_smul, powCoeff_smul]
    | add p q hp hq => rw [map_add, powCoeff_add, add_smul, hp, hq]
  exact ⟨fun p q hpq ↦ by rw [← key p, ← key q, hpq], fun s ↦
    ⟨powCoeff hf hU (a + b) hde s • (sectionPow hf hU a hd ⊗ₜ sectionPow hf hU b he), by
      rw [map_smul, hgen, powCoeff_smul]⟩⟩

include hf hU in
theorem bijective_toPresheaf_map_tensorMulHom_app {d e a b : ℤ} (hd : d = m * a)
    (he : e = m * b) :
    Function.Bijective
      (((PresheafOfModules.toPresheaf _).map (tensorMulHom 𝒜 d e)).app U) :=
  bijective_tensorMulHom_app hf hU hd he

end Bijective

end ProjectiveSpectrum.TwistingSheaf

namespace Proj

open ProjectiveSpectrum.TwistingSheaf

variable {𝒜}

/-- The condition that every point of `Proj 𝒜` lies in a basic open set `D₊(f)` attached to a
homogeneous element `f` of some degree `m` dividing both `d` and `e`.

Over such a `D₊(f)` the twisting sheaves `𝒪(d)`, `𝒪(e)` and `𝒪(d + e)` are free of rank one,
generated by the integral powers `f ^ (d / m)`, `f ^ (e / m)` and `f ^ (d / m + e / m)`, and
sectionwise multiplication `𝒪(d) ⊗ 𝒪(e) ⟶ 𝒪(d + e)` is bijective. The condition holds for all
`d` and `e` as soon as the irrelevant ideal of `𝒜` is generated in degree one, see
`AlgebraicGeometry.Proj.isCoveredByDvdDegree_of_irrelevant_le_span`. -/
def IsCoveredByDvdDegree (𝒜 : ℕ → σ) [GradedRing 𝒜] (d e : ℤ) : Prop :=
  ∀ x : ProjectiveSpectrum 𝒜, ∃ (m : ℕ) (f : A), f ∈ 𝒜 m ∧ f ∉ x.asHomogeneousIdeal ∧
    (m : ℤ) ∣ d ∧ (m : ℤ) ∣ e

theorem IsCoveredByDvdDegree.neg_right {d e : ℤ} (H : IsCoveredByDvdDegree 𝒜 d e) :
    IsCoveredByDvdDegree 𝒜 d (-e) := fun x ↦
  (H x).imp fun _ h ↦ h.imp fun _ h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.neg_right⟩

variable {d e : ℤ}

theorem isLocallyInjective_tensorMulHom (H : IsCoveredByDvdDegree 𝒜 d e) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥(Proj 𝒜))
      ((PresheafOfModules.toPresheaf _).map (tensorMulHom 𝒜 d e)) where
  equalizerSieve_mem {U} s t h x hx := by
    obtain ⟨m, f, hf, hfx, ⟨a, ha⟩, ⟨b, hb⟩⟩ := H x
    refine ⟨U.unop ⊓ ProjectiveSpectrum.basicOpen 𝒜 f, homOfLE inf_le_left, ?_, hx, hfx⟩
    refine (bijective_toPresheaf_map_tensorMulHom_app
      (U := op (U.unop ⊓ ProjectiveSpectrum.basicOpen 𝒜 f)) hf (fun y ↦ y.2.2) ha hb).injective ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]

theorem isLocallySurjective_tensorMulHom (H : IsCoveredByDvdDegree 𝒜 d e) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥(Proj 𝒜))
      ((PresheafOfModules.toPresheaf _).map (tensorMulHom 𝒜 d e)) where
  imageSieve_mem {U} s x hx := by
    obtain ⟨m, f, hf, hfx, ⟨a, ha⟩, ⟨b, hb⟩⟩ := H x
    refine ⟨U ⊓ ProjectiveSpectrum.basicOpen 𝒜 f, homOfLE inf_le_left, ?_, hx, hfx⟩
    exact (bijective_toPresheaf_map_tensorMulHom_app
      (U := op (U ⊓ ProjectiveSpectrum.basicOpen 𝒜 f)) hf (fun y ↦ y.2.2) ha hb).surjective _

/-- **`𝒪(d) ⊗ 𝒪(e) ≅ 𝒪(d + e)`**: under the covering hypothesis
`AlgebraicGeometry.Proj.IsCoveredByDvdDegree`, multiplication of fractions identifies the tensor
product of the twisting sheaves `𝒪(d)` and `𝒪(e)` with `𝒪(d + e)`. -/
def twistingSheafTensorIso (H : IsCoveredByDvdDegree 𝒜 d e) :
    twistingSheaf 𝒜 d ⊗ twistingSheaf 𝒜 e ≅ twistingSheaf 𝒜 (d + e) :=
  SheafOfModules.tensorIsoOfW (R := (Proj 𝒜).sheaf) (F := twistingSheaf 𝒜 d)
    (G := twistingSheaf 𝒜 e) (H := twistingSheaf 𝒜 (d + e))
    (SheafOfModules.sheafificationObjIso (Proj 𝒜).sheaf (twistingSheaf 𝒜 d))
    (SheafOfModules.sheafificationObjIso (Proj 𝒜).sheaf (twistingSheaf 𝒜 e))
    (SheafOfModules.sheafificationObjIso (Proj 𝒜).sheaf (twistingSheaf 𝒜 (d + e)))
    (tensorMulHom 𝒜 d e)
    (by
      have := isLocallyInjective_tensorMulHom H
      have := isLocallySurjective_tensorMulHom H
      exact GrothendieckTopology.W_of_isLocallyBijective _ _)

/-- **The twisting sheaf `𝒪(d)` is invertible**, i.e. is a line bundle, as soon as `Proj 𝒜` is
covered by basic open sets `D₊(f)` with `f` homogeneous of a degree dividing `d`: its inverse is
`𝒪(-d)`. -/
theorem invertible_twistingSheaf (d : ℤ) (H : IsCoveredByDvdDegree 𝒜 d d) :
    (twistingSheaf 𝒜 d).Invertible :=
  SheafOfModules.Invertible.left (R := (Proj 𝒜).sheaf) (M := twistingSheaf 𝒜 d)
    (N := twistingSheaf 𝒜 (-d))
    (twistingSheafTensorIso H.neg_right ≪≫
      eqToIso (congrArg (twistingSheaf 𝒜) (add_neg_cancel d)) ≪≫ twistingSheafZeroIso ≪≫
      (SheafOfModules.tensorUnitIso (Proj 𝒜).sheaf).symm)

section DegreeOne

variable (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span {a : A | a ∈ 𝒜 1})

include hspan

/-- If the irrelevant ideal of `𝒜` is generated by elements of degree one, then no point of
`Proj 𝒜` contains all of `𝒜 1`. -/
theorem exists_degreeOne_notMem (x : ProjectiveSpectrum 𝒜) :
    ∃ f ∈ 𝒜 1, f ∉ x.asHomogeneousIdeal := by
  by_contra! hx
  exact x.not_irrelevant_le fun a ha ↦ Ideal.span_le.2 (fun b hb ↦ hx b hb) (hspan ha)

/-- If the irrelevant ideal of `𝒜` is generated by elements of degree one, then `Proj 𝒜` is
covered by the basic open sets of the elements of degree one, so that the covering hypothesis
`AlgebraicGeometry.Proj.IsCoveredByDvdDegree` holds for every pair of degrees. -/
theorem isCoveredByDvdDegree_of_irrelevant_le_span (d e : ℤ) : IsCoveredByDvdDegree 𝒜 d e :=
  fun x ↦ by
    obtain ⟨f, hf, hfx⟩ := exists_degreeOne_notMem hspan x
    exact ⟨1, f, hf, hfx, by simp, by simp⟩

/-- **On `Proj` of a graded ring whose irrelevant ideal is generated in degree one — for instance
a polynomial ring — every twisting sheaf `𝒪(d)`, `d : ℤ`, is invertible.** -/
theorem invertible_twistingSheaf_of_irrelevant_le_span (d : ℤ) :
    (twistingSheaf 𝒜 d).Invertible :=
  invertible_twistingSheaf d (isCoveredByDvdDegree_of_irrelevant_le_span hspan d d)

end DegreeOne

end Proj

end AlgebraicGeometry
