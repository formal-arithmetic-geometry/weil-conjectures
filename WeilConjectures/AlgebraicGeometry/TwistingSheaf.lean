/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.Mathlib.RingTheory.Localization.Defs

/-!
# The twisting sheaves `𝒪(d)` on `Proj` of a graded ring

Let `𝒜 : ℕ → σ` be a graded ring with underlying ring `A`. For `d : ℤ` we construct the `d`-th
twisting sheaf `𝒪(d)` on `Proj 𝒜`, as a sheaf of modules over the structure sheaf.

Mathlib constructs the structure sheaf of `Proj 𝒜` as the sheaf of dependent functions
`x ↦ (A_x)₀` which are locally a quotient `r / s` of two homogeneous elements *of the same
degree*; see `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean`. The sheaf
`𝒪(d)` is constructed here in exactly the same way, with sections the dependent functions
`x ↦ A_x` which are locally a quotient `r / s` of homogeneous elements with
`deg r - deg s = d`; this is Hartshorne's `(S(d))~`. Because the degree shift is by an
*integer*, all the twists `𝒪(d)`, `d : ℤ`, of an `ℕ`-graded ring are available at once.

The construction is pointwise, so that local triviality is immediate: if `f` is homogeneous of
degree `m`, then multiplication by `f` is an isomorphism `𝒪(d) ≅ 𝒪(d + m)` over the basic open
set `D₊(f)`, with inverse the division by `f`. In particular, on
`ℙᴺ_A = Proj A[T₀, …, T_N]` the sheaf `𝒪(1)` is trivial on each of the standard affine charts
`D₊(Tᵢ)`, the transition functions being the units `Tᵢ / Tⱼ`.

Because the construction is pointwise, the locus where a global section does not vanish is
described pointwise as well: for `a ∈ 𝒜 j`, the value of `homogeneousSection ha` at a point `x`
is a **unit** of the local ring `A_x = Localization.AtPrime x.asHomogeneousIdeal.toIdeal` — the
localization of the whole graded ring `A` at `x`, not the local ring `𝒪_{Proj 𝒜, x}` of the
scheme `Proj 𝒜` — exactly when `a ∉ x`, that is, exactly on the basic open set `D₊(a)`. Being a
unit, rather than being nonzero, is the right test: the value `a / 1` can be nonzero in `A_x`
while lying in the maximal ideal, which is what "`a` vanishes at `x`" means.

If moreover some `f ∈ 𝒜 j` avoids `x`, then `f` trivialises `𝒪(j)` near `x` (this is
`Proj.isIso_app_twistingSheafMul`) and `Proj.homogeneousSection_apply_eq_mul` identifies the
value of `homogeneousSection ha` at `x` with `a / f` times the local generator attached to `f`,
where now `a / f` does lie in `𝒪_{Proj 𝒜, x}`. The two non-vanishing criteria agree
(`Proj.isUnit_homogeneousSection_apply_iff_isUnit_mk`), but only conditionally: for a general
graded ring no element of `𝒜 j` need avoid a given `x`, whereas
`Proj.isUnit_homogeneousSection_apply_iff` is unconditional.

## Main definitions

- `AlgebraicGeometry.Proj.twistingSheaf`: the twisting sheaf `𝒪(d)` on `Proj 𝒜`, for `d : ℤ`.
- `AlgebraicGeometry.Proj.homogeneousSection`: the global section of `𝒪(j)` attached to a
  homogeneous element of degree `j`. On `ℙᴺ` these are the homogeneous coordinates
  `T₀, …, T_N ∈ Γ(ℙᴺ, 𝒪(1))`. `AlgebraicGeometry.Proj.homogeneousSectionHom` bundles this
  construction as an additive monoid homomorphism `↥(𝒜 j) →+ Γ(𝒪(j), ⊤)`.
- `AlgebraicGeometry.Proj.twistingSheafMul`: multiplication by a homogeneous element `f` of
  degree `m`, as a morphism `𝒪(d) ⟶ 𝒪(d + m)`.

## Main results

- `AlgebraicGeometry.Proj.twistingSheafRestrictIso`: **local triviality**, multiplication by a
  homogeneous element `f` of degree `m` is an isomorphism `𝒪(d) ≅ 𝒪(d + m)` over `D₊(f)`.
- `AlgebraicGeometry.Proj.twistingSheafZeroIso`: `𝒪(0)` is the structure sheaf.
- `AlgebraicGeometry.Proj.isUnit_homogeneousSection_apply_iff`: the section of `𝒪(j)` attached
  to `a ∈ 𝒜 j` does not vanish at a point `x` if and only if `x ∈ D₊(a)`. Dually,
  `AlgebraicGeometry.Proj.homogeneousSection_apply_mem_maximalIdeal_iff` says that it vanishes
  at `x` if and only if `a` lies in the homogeneous prime ideal of `x`.
- `AlgebraicGeometry.Proj.homogeneousSection_apply_eq_mul`: near a point `x` avoided by some
  `f ∈ 𝒜 j`, the section attached to `a` is `a / f` times the local generator attached to `f`.
- `AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.sectionPowEquiv`: **local freeness**, over
  an open set on which a homogeneous element `f` of degree `m` is invertible, the sections of
  `𝒪(m * k)`, `k : ℤ`, form a free module of rank one over the sections of the structure sheaf,
  on the generator `f ^ k`.

## TODO

- The compatibility of `AlgebraicGeometry.Proj.twistingSheafTensorIso` with global sections: the
  image of `homogeneousSection a ⊗ homogeneousSection b` under `𝒪(i) ⊗ 𝒪(j) ≅ 𝒪(i + j)` should
  be `homogeneousSection (a * b)`. This is what associativity of the tensor isomorphisms and the
  computation of the induced map `ℤ → Pic (Proj 𝒜)` will need.
- The *fibrewise* description of a global section, in the sense of
  `AlgebraicGeometry.Scheme.Modules.fiber`: for `a ∈ 𝒜 j`, the image of
  `homogeneousSection ha` under
  `Scheme.Modules.sectionsPullback ((Proj 𝒜).fromSpecResidueField x) (twistingSheaf 𝒜 j)`
  vanishes if and only if `a ∈ x`. Unlike the pointwise criterion proved here, this form
  survives pulling `𝒪(j)` back along a morphism, which is what the blueprint consumes; it needs
  a description of the pullback of `𝒪(j)` along `Spec κ(x) ⟶ Proj 𝒜`, which is not available
  yet. `Proj.isUnit_homogeneousSection_apply_iff` is the proof ingredient for it.
- The transfer of `𝒪(1)` to the relative projective space `ℙ(n; S)` of
  `WeilConjectures/AlgebraicGeometry/ProjectiveSpace.lean`, by pulling back along the map to
  the integral model, and the compatibility with base change.

## Blueprint

`Proj.isUnit_homogeneousSection_apply_iff` and `Proj.homogeneousSection_apply_mem_maximalIdeal_iff`
are inputs to `lem:deg-general-hyperplane`, the existence of a hyperplane section avoiding the
associated points of a coherent sheaf. They are the `Proj`-level half of the statement used
there, that on `ℙᴺ` the hyperplane `V(∑ⱼ aⱼ Tⱼ)` contains a point with homogeneous coordinates
`ξ` exactly when `∑ⱼ aⱼ ξⱼ` vanishes in its residue field. The lemma itself is not proved here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace TopCat

namespace AlgebraicGeometry

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveSpectrum.TwistingSheaf

/-- The localization of `A` at the homogeneous prime ideal corresponding to a point of
`Proj 𝒜`. -/
abbrev atPoint (x : ProjectiveSpectrum 𝒜) : Type _ :=
  Localization.AtPrime x.asHomogeneousIdeal.toIdeal

variable {𝒜}

/-- The predicate saying that a dependent function on an open `U` is, on all of `U`, the
fraction `r / s` with `r` homogeneous of degree `j`, `s` homogeneous of degree `i`, and
`j = i + d`. -/
def IsFraction (d : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, atPoint 𝒜 x.1) : Prop :=
  ∃ (i j : ℕ) (_ : (j : ℤ) = i + d) (r : 𝒜 j) (s : 𝒜 i)
    (s_nin : ∀ x : U, (s : A) ∉ x.1.asHomogeneousIdeal.toIdeal),
    ∀ x : U, f x = Localization.mk (r : A) ⟨(s : A), s_nin x⟩

variable (𝒜)

/-- `IsFraction d` is a prelocal predicate. -/
def isFractionPrelocal (d : ℤ) :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => atPoint 𝒜 x where
  pred f := IsFraction d f
  res := by
    rintro V U i f ⟨j, k, hjk, r, s, h, w⟩
    exact ⟨j, k, hjk, r, s, (h <| i ·), (w <| i ·)⟩

/-- The sections of the `d`-th twisting sheaf are the dependent functions which locally are
fractions `r / s` with `deg r - deg s = d`. -/
def isLocallyFraction (d : ℤ) :
    LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => atPoint 𝒜 x :=
  (isFractionPrelocal 𝒜 d).sheafify

section Sections

variable {𝒜}

open ProjectiveSpectrum.StructureSheaf in
/-- The `A`-valued dependent functions on `U` form a module over the sections of the structure
sheaf of `Proj 𝒜` on `U`, by pointwise multiplication. -/
instance modulePi (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj 𝒜).ringCatSheaf.obj.obj U) (∀ x : U.unop, atPoint 𝒜 x.1) :=
  inferInstanceAs (Module ↥(sectionsSubring (𝒜 := 𝒜) U) _)

theorem zero_mem' (d : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜 d).pred (0 : ∀ x : U.unop, atPoint 𝒜 x.1) := by
  intro x
  obtain ⟨f, m, hfm, hm, hfx⟩ := x.1.exists_homogeneous_notMem
  have hkm : 0 ≤ ((d.natAbs * m : ℕ) : ℤ) + d := by
    have h2 : d.natAbs ≤ d.natAbs * m := Nat.le_mul_of_pos_right _ hm
    omega
  have hfk : f ^ d.natAbs ∉ x.1.asHomogeneousIdeal := fun h ↦
    hfx (x.1.isPrime.mem_of_pow_mem _ h)
  refine ⟨U.unop ⊓ ProjectiveSpectrum.basicOpen 𝒜 (f ^ d.natAbs), ⟨x.2, hfk⟩,
    Opens.infLELeft _ _, d.natAbs * m, (((d.natAbs * m : ℕ) : ℤ) + d).toNat,
    (Int.toNat_of_nonneg hkm).symm ▸ rfl, ⟨0, zero_mem _⟩,
    ⟨f ^ d.natAbs, by simpa [smul_eq_mul] using SetLike.pow_mem_graded d.natAbs hfm⟩,
    fun y ↦ y.2.2, fun _ ↦ ?_⟩
  simpa using (Localization.mk_zero _).symm

theorem add_mem' (d : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a b : ∀ x : U.unop, atPoint 𝒜 x.1)
    (ha : (isLocallyFraction 𝒜 d).pred a) (hb : (isLocallyFraction 𝒜 d).pred b) :
    (isLocallyFraction 𝒜 d).pred (a + b) := by
  intro x
  obtain ⟨Va, ma, ia, i₁, j₁, h₁, ⟨r₁, hr₁⟩, ⟨s₁, hs₁⟩, hw₁, w₁⟩ := ha x
  obtain ⟨Vb, mb, ib, i₂, j₂, h₂, ⟨r₂, hr₂⟩, ⟨s₂, hs₂⟩, hw₂, w₂⟩ := hb x
  have key : i₁ + j₂ = i₂ + j₁ := by omega
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, i₁ + i₂, i₂ + j₁, by push_cast; omega,
    ⟨s₂ * r₁ + s₁ * r₂, add_mem (SetLike.mul_mem_graded hs₂ hr₁)
      (key ▸ SetLike.mul_mem_graded hs₁ hr₂)⟩, ⟨s₁ * s₂, SetLike.mul_mem_graded hs₁ hs₂⟩,
    fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hw₁ ⟨y.1, y.2.1⟩) (hw₂ ⟨y.1, y.2.2⟩),
    ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at w₁ w₂
  simp [w₁ y hy.1, w₂ y hy.2, Localization.add_mk, add_comm (s₁ * r₂)]
  rfl

theorem smul_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (c : (Proj 𝒜).ringCatSheaf.obj.obj U) (a : ∀ x : U.unop, atPoint 𝒜 x.1) (x : U.unop) :
    (c • a) x = (c.1 x).val * a x := rfl

theorem smul_mem' (d : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (c : (Proj 𝒜).ringCatSheaf.obj.obj U) (a : ∀ x : U.unop, atPoint 𝒜 x.1)
    (ha : (isLocallyFraction 𝒜 d).pred a) :
    (isLocallyFraction 𝒜 d).pred (c • a) := by
  intro x
  obtain ⟨V₁, m₁, e₁, i₀, ⟨r₀, hr₀⟩, ⟨s₀, hs₀⟩, hw₀, w₀⟩ := c.2 x
  obtain ⟨V₂, m₂, e₂, i, j, hij, ⟨r, hr⟩, ⟨s, hs⟩, hw, w⟩ := ha x
  refine ⟨V₁ ⊓ V₂, ⟨m₁, m₂⟩, Opens.infLELeft _ _ ≫ e₁, i₀ + i, i₀ + j, by push_cast; omega,
    ⟨r₀ * r, SetLike.mul_mem_graded hr₀ hr⟩, ⟨s₀ * s, SetLike.mul_mem_graded hs₀ hs⟩,
    fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hw₀ ⟨y.1, y.2.1⟩) (hw ⟨y.1, y.2.2⟩),
    ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at w₀ w
  simp [smul_apply, w y hy.2, w₀ y hy.1, Localization.mk_mul]

/-- A dependent function which on all of `U` is the quotient of a homogeneous element of degree
`j` by a homogeneous element of degree `i` invertible on `U` is a local fraction of degree
`j - i`. -/
theorem mk_mem {i j : ℕ} {r s : A} (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i) {c : ℤ} (hc : (j : ℤ) - i = c)
    {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (hs' : ∀ x : U.unop, s ∉ x.1.asHomogeneousIdeal.toIdeal)
    {a : ∀ x : U.unop, atPoint 𝒜 x.1} (ha : ∀ x, a x = Localization.mk r ⟨s, hs' x⟩) :
    (isLocallyFraction 𝒜 c).pred a :=
  PrelocalPredicate.sheafifyOf ⟨i, j, by omega, ⟨r, hr⟩, ⟨s, hs⟩, hs', ha⟩

/-- The product of a local fraction of degree `d` and a local fraction of degree `e` is a local
fraction of degree `d + e`. -/
theorem mul_mem {d e c : ℤ} (hc : d + e = c) {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
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
  change a ⟨y, _⟩ * b ⟨y, _⟩ = _
  rw [w₁ y hy.1, w₂ y hy.2, Localization.mk_mul]
  rfl

end Sections

variable (d : ℤ)

/-- The sections of the `d`-th twisting sheaf on an open set `U`: the dependent functions
`U → ⨆ x, Aₓ` that are locally fractions of degree `d`. -/
def sections (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Submodule ((Proj 𝒜).ringCatSheaf.obj.obj U) (∀ x : U.unop, atPoint 𝒜 x.1) where
  carrier := {f | (isLocallyFraction 𝒜 d).pred f}
  zero_mem' := zero_mem' d U
  add_mem' := add_mem' d U _ _
  smul_mem' c _ h := smul_mem' d U c _ h

/-- The `d`-th twisting sheaf, valued in `Type`: the subsheaf of the sheaf of dependent
functions consisting of those which are locally fractions of degree `d`. -/
def sheafInType : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 d)

instance addCommGroupSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddCommGroup ((sheafInType 𝒜 d).1.obj U) :=
  inferInstanceAs (AddCommGroup (sections 𝒜 d U))

instance moduleSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj 𝒜).ringCatSheaf.obj.obj U) ((sheafInType 𝒜 d).1.obj U) :=
  inferInstanceAs (Module _ (sections 𝒜 d U))

/-- The `d`-th twisting presheaf, valued in abelian groups. -/
def presheafInAb : Presheaf Ab (ProjectiveSpectrum.top 𝒜) where
  obj U := AddCommGrpCat.of ((sheafInType 𝒜 d).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (sheafInType 𝒜 d).1.map i
      map_zero' := rfl
      map_add' _ _ := Subtype.ext rfl }

instance modulePresheafInAbObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj 𝒜).ringCatSheaf.obj.obj U) ((presheafInAb 𝒜 d).obj U) :=
  inferInstanceAs (Module _ (sections 𝒜 d U))

/-- The `Ab`-valued twisting presheaf agrees with the `Type`-valued one. -/
def presheafInAbCompForget : presheafInAb 𝒜 d ⋙ forget Ab ≅ (sheafInType 𝒜 d).1 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

theorem isSheaf_presheafInAb : (presheafInAb 𝒜 d).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr
    (TopCat.Presheaf.isSheaf_of_iso (presheafInAbCompForget 𝒜 d).symm (sheafInType 𝒜 d).property)

variable {𝒜} in
theorem mul_mem' {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : ∀ x : U.unop, atPoint 𝒜 x.1) (ha : (isLocallyFraction 𝒜 d).pred a) :
    (isLocallyFraction 𝒜 (d + m)).pred (fun x ↦ Localization.mk f 1 * a x) :=
  mul_mem (d := (m : ℤ)) (e := d) (by omega)
    (mk_mem hf (SetLike.one_mem_graded 𝒜) (by simp)
      (fun y ↦ (Ideal.ne_top_iff_one _).mp y.1.isPrime.ne_top) (fun _ ↦ rfl)) ha

variable {𝒜} in
theorem div_mem' {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : ∀ x : U.unop, f ∉ x.1.asHomogeneousIdeal.toIdeal)
    (a : ∀ x : U.unop, atPoint 𝒜 x.1) (ha : (isLocallyFraction 𝒜 (d + m)).pred a) :
    (isLocallyFraction 𝒜 d).pred (fun x ↦ Localization.mk 1 ⟨f, hU x⟩ * a x) :=
  mul_mem (d := -(m : ℤ)) (e := d + m) (by omega)
    (mk_mem (SetLike.one_mem_graded 𝒜) hf (by simp) hU (fun _ ↦ rfl)) ha

/-- The `d`-th twisting presheaf as a presheaf of `𝒪`-modules on `Proj 𝒜`. -/
def presheafOfModules : (Proj 𝒜).PresheafOfModules :=
  PresheafOfModules.ofPresheaf (presheafInAb 𝒜 d) (by intros; rfl)

/-- The ring of sections of the structure sheaf of `Proj 𝒜` over `U`, spelled as the value at
`U` of the presheaf of rings over which the twisting presheaves are presheaves of modules, so
that scalar multiplication on their sections is found by instance resolution. -/
abbrev sectionRing (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) : RingCat :=
  ((Proj 𝒜).sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U

/-- The `d`-th twisting presheaf as a presheaf of `𝒪`-modules on `Proj 𝒜`, spelled over the
presheaf of rings `𝒪 ⋙ forget₂ CommRingCat RingCat` so that the monoidal structure on presheaves
of modules is found by instance resolution. -/
abbrev twistingPresheaf :
    PresheafOfModules ((Proj 𝒜).sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  presheafOfModules 𝒜 d

/-- The sections of the `d`-th twisting presheaf over `U`. -/
abbrev sectionModule (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    ModuleCat (sectionRing 𝒜 U) :=
  (twistingPresheaf 𝒜 d).obj U

section Apply

variable {𝒜} {d : ℤ} {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}

@[simp]
theorem sectionModule_smul_apply (c : sectionRing 𝒜 U) (a : sectionModule 𝒜 d U) (x : U.unop) :
    (c • a).1 x = (c.1 x).val * a.1 x := rfl

@[simp]
theorem sectionModule_add_apply (a b : sectionModule 𝒜 d U) (x : U.unop) :
    (a + b).1 x = a.1 x + b.1 x := rfl

@[simp]
theorem sectionModule_zero_apply (x : U.unop) : (0 : sectionModule 𝒜 d U).1 x = 0 := rfl

@[simp]
theorem sectionRing_val_mul_apply (g h : sectionRing 𝒜 U) (x : U.unop) :
    ((g * h).1 x).val = (g.1 x).val * (h.1 x).val :=
  HomogeneousLocalization.val_mul _ _

@[simp]
theorem sectionRing_val_add_apply (g h : sectionRing 𝒜 U) (x : U.unop) :
    ((g + h).1 x).val = (g.1 x).val + (h.1 x).val :=
  HomogeneousLocalization.val_add _ _

@[simp]
theorem sectionRing_val_zero_apply (x : U.unop) : ((0 : sectionRing 𝒜 U).1 x).val = 0 :=
  HomogeneousLocalization.val_zero

end Apply

variable {𝒜}

/-- Multiplication by a homogeneous element `f` of degree `m`, as a morphism of presheaves of
abelian groups from `𝒪(d)` to `𝒪(d + m)`. -/
def mulPresheafHom {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (d : ℤ) :
    presheafInAb 𝒜 d ⟶ presheafInAb 𝒜 (d + m) where
  app U := AddCommGrpCat.ofHom
    { toFun s := ⟨fun x ↦ Localization.mk f 1 * s.1 x, mul_mem' (d := d) hf U s.1 s.2⟩
      map_zero' := Subtype.ext (funext fun _ ↦ mul_zero _)
      map_add' _ _ := Subtype.ext (funext fun _ ↦ mul_add _ _ _) }
  naturality _ _ _ := rfl

section Zero

open ProjectiveSpectrum.StructureSheaf HomogeneousLocalization in
/-- A section of `𝒪(0)` takes values in the degree-zero homogeneous localizations. -/
theorem exists_val_eq {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (t : ∀ x : U.unop, atPoint 𝒜 x.1) (ht : (isLocallyFraction 𝒜 0).pred t) (x : U.unop) :
    ∃ y : AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal, y.val = t x := by
  obtain ⟨V, hxV, e, i, j, hij, ⟨r, hr⟩, ⟨s, hs⟩, hw, w⟩ := ht x
  have hji : j = i := by omega
  subst hji
  refine ⟨.mk ⟨j, ⟨r, hr⟩, ⟨s, hs⟩, hw ⟨x.1, hxV⟩⟩, ?_⟩
  rw [val_mk]
  exact (w ⟨x.1, hxV⟩).symm

open ProjectiveSpectrum.StructureSheaf HomogeneousLocalization in
/-- The degree-zero homogeneous localizations sit inside the localizations, compatibly with the
local fraction conditions. -/
theorem val_mem' {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : (Proj 𝒜).ringCatSheaf.obj.obj U) :
    (isLocallyFraction 𝒜 0).pred (fun x ↦ (s.1 x).val) := by
  intro x
  obtain ⟨V, hxV, e, i, ⟨r, hr⟩, ⟨t, ht⟩, hw, w⟩ := s.2 x
  refine ⟨V, hxV, e, i, i, by simp, ⟨r, hr⟩, ⟨t, ht⟩, hw, fun y ↦ ?_⟩
  simp only [Subtype.forall] at w
  simp [w y.1 y.2, val_mk]

open ProjectiveSpectrum.StructureSheaf HomogeneousLocalization in
/-- The inverse of the canonical map from the sections of the structure sheaf to those of
`𝒪(0)`. -/
def sectionsZeroInv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (t : sections 𝒜 0 U) :
    (Proj 𝒜).ringCatSheaf.obj.obj U :=
  ⟨fun x ↦ (exists_val_eq t.1 t.2 x).choose, by
    intro x
    obtain ⟨V, hxV, e, i, j, hij, ⟨r, hr⟩, ⟨s, hs⟩, hw, w⟩ := t.2 x
    have hji : j = i := by omega
    subst hji
    refine ⟨V, hxV, e, j, ⟨r, hr⟩, ⟨s, hs⟩, hw, fun y ↦ ?_⟩
    refine HomogeneousLocalization.val_injective _ ?_
    rw [(exists_val_eq t.1 t.2 (e y)).choose_spec, val_mk]
    exact w y⟩

@[simp]
theorem val_sectionsZeroInv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (t : sections 𝒜 0 U)
    (x : U.unop) : ((sectionsZeroInv t).1 x).val = t.1 x :=
  (exists_val_eq t.1 t.2 x).choose_spec

open HomogeneousLocalization in
/-- The canonical morphism of presheaves of abelian groups from the structure sheaf of `Proj 𝒜`
to the degree-zero twisting presheaf. -/
def unitToPresheafInAbZero :
    (PresheafOfModules.unit (Proj 𝒜).ringCatSheaf.obj).presheaf ⟶ presheafInAb 𝒜 0 where
  app _ := AddCommGrpCat.ofHom
    { toFun s := ⟨fun x ↦ (s.1 x).val, val_mem' s⟩
      map_zero' := Subtype.ext (funext fun _ ↦ val_zero)
      map_add' _ _ := Subtype.ext (funext fun _ ↦ val_add _ _) }
  naturality _ _ _ := rfl

end Zero

section Generator

variable {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
  (hU : ∀ x : U.unop, f ∉ x.1.asHomogeneousIdeal.toIdeal)

/-- If an element `f` does not belong to a point `x` of `Proj 𝒜`, then the fraction `f / 1` is a
unit of the localization `A_x`. This is `IsLocalization.map_units`, spelled so that both the
unit `f / 1` and its inverse `1 / f` are explicit fractions. -/
def unitAtPoint {x : ProjectiveSpectrum 𝒜} (hx : f ∉ x.asHomogeneousIdeal.toIdeal) :
    (atPoint 𝒜 x)ˣ where
  val := Localization.mk f 1
  inv := Localization.mk 1 ⟨f, hx⟩
  val_inv := by
    rw [mul_comm]
    exact Localization.mk_one_mul_mk_one ⟨f, hx⟩
  inv_val := Localization.mk_one_mul_mk_one ⟨f, hx⟩

/-- The integral power `f ^ k` of an element `f` which is invertible at every point of the open
set `U`, as a dependent function on `U`. When `f` is homogeneous of degree `m`, this is a section
of `𝒪(m * k)`, see `AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.powFun_mem`. -/
def powFun (k : ℤ) (x : U.unop) : atPoint 𝒜 x.1 :=
  (unitAtPoint (hU x) ^ k).val

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

include hf in
/-- The integral power `f ^ k` of a homogeneous element `f` of degree `m` which is invertible on
`U` is a section of `𝒪(m * k)` over `U`. -/
theorem powFun_mem (k : ℤ) {c : ℤ} (hc : c = m * k) :
    (isLocallyFraction 𝒜 c).pred (powFun hU k) := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact mk_mem (by simpa [smul_eq_mul] using SetLike.pow_mem_graded n hf)
      (SetLike.one_mem_graded 𝒜) (by subst hc; push_cast; ring)
      (fun y ↦ (Ideal.ne_top_iff_one _).mp y.1.isPrime.ne_top) (powFun_natCast hU n)
  · exact mk_mem (SetLike.one_mem_graded 𝒜)
      (by simpa [smul_eq_mul] using SetLike.pow_mem_graded n hf)
      (by subst hc; push_cast; ring)
      (fun y h ↦ hU y (y.1.isPrime.mem_of_pow_mem n h))
      (fun y ↦ powFun_neg_natCast hU n y _)

include hf in
/-- The generator `f ^ k` of the sections of `𝒪(m * k)` over an open set on which the
homogeneous element `f` of degree `m` is invertible. -/
def sectionPow (k : ℤ) {c : ℤ} (hc : c = m * k) : sectionModule 𝒜 c U :=
  ⟨powFun hU k, powFun_mem hf hU k hc⟩

@[simp]
theorem sectionPow_apply (k : ℤ) {c : ℤ} (hc : c = m * k) (x : U.unop) :
    (sectionPow hf hU k hc).1 x = powFun hU k x := rfl

include hf in
/-- The coefficient of a section of `𝒪(m * k)` with respect to the generator `f ^ k`, over an
open set on which the homogeneous element `f` of degree `m` is invertible. -/
def powCoeff (k : ℤ) {c : ℤ} (hc : c = m * k) (s : sectionModule 𝒜 c U) : sectionRing 𝒜 U :=
  sectionsZeroInv ⟨fun x ↦ s.1 x * powFun hU (-k) x,
    mul_mem (by rw [hc]; ring) s.2 (powFun_mem hf hU (-k) rfl)⟩

@[simp]
theorem val_powCoeff (k : ℤ) {c : ℤ} (hc : c = m * k) (s : sectionModule 𝒜 c U) (x : U.unop) :
    ((powCoeff hf hU k hc s).1 x).val = s.1 x * powFun hU (-k) x :=
  val_sectionsZeroInv _ x

theorem powCoeff_smul_sectionPow (k : ℤ) {c : ℤ} (hc : c = m * k) (s : sectionModule 𝒜 c U) :
    powCoeff hf hU k hc s • sectionPow hf hU k hc = s := by
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [sectionModule_smul_apply, sectionPow_apply, val_powCoeff, mul_assoc, ← powFun_add]
  simp

theorem powCoeff_smul_sectionPow_self (k : ℤ) {c : ℤ} (hc : c = m * k) (g : sectionRing 𝒜 U) :
    powCoeff hf hU k hc (g • sectionPow hf hU k hc) = g := by
  refine Subtype.ext (funext fun x ↦ HomogeneousLocalization.val_injective _ ?_)
  rw [val_powCoeff, sectionModule_smul_apply, sectionPow_apply, mul_assoc, ← powFun_add]
  simp

include hf in
/-- **Local freeness of the twisting sheaves.** Over an open set `U` on which a homogeneous
element `f` of degree `m` is invertible, the sections of `𝒪(m * k)`, `k : ℤ`, form a free module
of rank one over the sections of the structure sheaf, on the generator `f ^ k`. -/
def sectionPowEquiv (k : ℤ) {c : ℤ} (hc : c = m * k) :
    sectionRing 𝒜 U ≃ₗ[sectionRing 𝒜 U] sectionModule 𝒜 c U where
  toFun g := g • sectionPow hf hU k hc
  map_add' g g' := add_smul g g' _
  map_smul' g g' := mul_smul g g' _
  invFun := powCoeff hf hU k hc
  left_inv := powCoeff_smul_sectionPow_self hf hU k hc
  right_inv := powCoeff_smul_sectionPow hf hU k hc

@[simp]
theorem sectionPowEquiv_apply (k : ℤ) {c : ℤ} (hc : c = m * k) (g : sectionRing 𝒜 U) :
    sectionPowEquiv hf hU k hc g = g • sectionPow hf hU k hc := rfl

@[simp]
theorem sectionPowEquiv_symm_apply (k : ℤ) {c : ℤ} (hc : c = m * k) (s : sectionModule 𝒜 c U) :
    (sectionPowEquiv hf hU k hc).symm s = powCoeff hf hU k hc s := rfl

theorem powCoeff_add (k : ℤ) {c : ℤ} (hc : c = m * k) (s t : sectionModule 𝒜 c U) :
    powCoeff hf hU k hc (s + t) = powCoeff hf hU k hc s + powCoeff hf hU k hc t :=
  map_add (sectionPowEquiv hf hU k hc).symm s t

theorem powCoeff_zero (k : ℤ) {c : ℤ} (hc : c = m * k) : powCoeff hf hU k hc 0 = 0 :=
  map_zero (sectionPowEquiv hf hU k hc).symm

/-- The coefficient with respect to the generator `f ^ (a + b)` of a product of sections is the
product of the coefficients with respect to `f ^ a` and `f ^ b`. -/
theorem powCoeff_mul {c d e a b : ℤ} (hd : d = m * a) (he : e = m * b) (hc : c = m * (a + b))
    (hde : d + e = c) (s : sectionModule 𝒜 d U) (t : sectionModule 𝒜 e U) :
    powCoeff hf hU (a + b) hc ⟨fun x ↦ s.1 x * t.1 x, mul_mem hde s.2 t.2⟩ =
      powCoeff hf hU a hd s * powCoeff hf hU b he t := by
  refine Subtype.ext (funext fun x ↦ HomogeneousLocalization.val_injective _ ?_)
  rw [val_powCoeff, sectionRing_val_mul_apply, val_powCoeff, val_powCoeff, neg_add, powFun_add]
  ring

end Generator

end ProjectiveSpectrum.TwistingSheaf

open ProjectiveSpectrum.TwistingSheaf in
/-- **The twisting sheaf `𝒪(d)` on `Proj 𝒜`**. -/
def Proj.twistingSheaf (d : ℤ) : (Proj 𝒜).Modules :=
  ⟨presheafOfModules 𝒜 d, isSheaf_presheafInAb 𝒜 d⟩

namespace Proj

variable {𝒜}

open ProjectiveSpectrum.TwistingSheaf

/-- The canonical morphism `𝒪 ⟶ 𝒪(0)` from the structure sheaf to the zeroth twisting sheaf. -/
def unitToTwistingSheafZero :
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules) ⟶ twistingSheaf 𝒜 0 :=
  ⟨PresheafOfModules.homMk unitToPresheafInAbZero
    (fun _ _ _ ↦ Subtype.ext (funext fun _ ↦ HomogeneousLocalization.val_mul _ _))⟩

@[simp]
theorem unitToTwistingSheafZero_app_apply (U : (Proj 𝒜).Opens)
    (s : Γ((SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules), U)) (x : U) :
    ((Scheme.Modules.Hom.app unitToTwistingSheafZero U) s).1 x = (s.1 x).val := rfl

instance : IsIso (unitToTwistingSheafZero (𝒜 := 𝒜)) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U ↦ by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun s t h ↦ Subtype.ext (funext fun x ↦ HomogeneousLocalization.val_injective _ ?_),
      fun t ↦ ⟨sectionsZeroInv t, Subtype.ext (funext fun x ↦ val_sectionsZeroInv t x)⟩⟩
    exact congrFun (congrArg Subtype.val h) x

/-- **`𝒪(0)` is the structure sheaf**: the zeroth twisting sheaf of `Proj 𝒜` is isomorphic to
the structure sheaf `𝒪`. -/
noncomputable def twistingSheafZeroIso :
    twistingSheaf 𝒜 0 ≅ (SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules) :=
  (asIso unitToTwistingSheafZero).symm

/-- A homogeneous element `a` of degree `j` defines a global section of `𝒪(j)` on `Proj 𝒜`,
namely `x ↦ a / 1`. On `ℙᴺ_A = Proj A[T₀, …, T_N]` these are the homogeneous coordinates
`T₀, …, T_N ∈ Γ(ℙᴺ, 𝒪(1))`. -/
def homogeneousSection {j : ℕ} {a : A} (ha : a ∈ 𝒜 j) : Γ(twistingSheaf 𝒜 j, ⊤) :=
  ⟨fun _ ↦ Localization.mk a 1, fun x ↦ ⟨⊤, x.2, 𝟙 _, 0, j, by simp, ⟨a, ha⟩,
    ⟨1, SetLike.one_mem_graded 𝒜⟩,
    fun y ↦ (Ideal.ne_top_iff_one _).mp y.1.isPrime.ne_top, fun _ ↦ rfl⟩⟩

@[simp]
theorem homogeneousSection_add {j : ℕ} {a b : A} (ha : a ∈ 𝒜 j) (hb : b ∈ 𝒜 j) :
    homogeneousSection (add_mem ha hb) = homogeneousSection ha + homogeneousSection hb :=
  Subtype.ext (funext fun _ ↦ (Localization.add_mk_self a 1 b).symm)

@[simp]
theorem homogeneousSection_zero (j : ℕ) :
    homogeneousSection (𝒜 := 𝒜) (zero_mem (𝒜 j)) = 0 :=
  Subtype.ext (funext fun _ ↦ Localization.mk_zero _)

@[simp]
theorem homogeneousSection_apply {j : ℕ} {a : A} (ha : a ∈ 𝒜 j) (x : (⊤ : (Proj 𝒜).Opens)) :
    (homogeneousSection ha).1 x = Localization.mk a 1 := rfl

variable (𝒜) in
/-- The homogeneous elements of degree `j` map additively to the global sections of `𝒪(j)`;
this is `AlgebraicGeometry.Proj.homogeneousSection` as an additive monoid homomorphism. -/
def homogeneousSectionHom (j : ℕ) : ↥(𝒜 j) →+ Γ(twistingSheaf 𝒜 j, ⊤) where
  toFun a := homogeneousSection a.2
  map_zero' := homogeneousSection_zero j
  map_add' a b := homogeneousSection_add a.2 b.2

@[simp]
theorem homogeneousSectionHom_apply {j : ℕ} (a : ↥(𝒜 j)) :
    homogeneousSectionHom 𝒜 j a = homogeneousSection a.2 :=
  rfl

/-- A finite sum of homogeneous elements of degree `j` gives the sum of the corresponding
sections of `𝒪(j)`: on `ℙᴺ` this expresses the section `∑ⱼ cⱼ Tⱼ` in terms of the homogeneous
coordinates. -/
theorem homogeneousSection_sum {j : ℕ} {ι : Type*} (a : ι → ↥(𝒜 j)) (s : Finset ι) :
    homogeneousSection (𝒜 := 𝒜) (∑ i ∈ s, a i).2 =
      ∑ i ∈ s, homogeneousSection (a i).2 :=
  map_sum (homogeneousSectionHom 𝒜 j) a s

/-- Multiplication by a homogeneous element `f` of degree `m` is a morphism of `𝒪`-modules
`𝒪(d) ⟶ 𝒪(d + m)` on `Proj 𝒜`. -/
def twistingSheafMul {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (d : ℤ) :
    twistingSheaf 𝒜 d ⟶ twistingSheaf 𝒜 (d + m) :=
  ⟨PresheafOfModules.homMk (mulPresheafHom hf d)
    (fun _ _ _ ↦ Subtype.ext (funext fun _ ↦ mul_left_comm _ _ _))⟩

/-- Over a basic open `D₊(f)`, division by the homogeneous element `f` of degree `m` maps the
sections of `𝒪(d + m)` to the sections of `𝒪(d)`. -/
def twistingSheafDivApp {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (d : ℤ) {U : (Proj 𝒜).Opens}
    (hU : U ≤ Proj.basicOpen 𝒜 f) :
    Γ(twistingSheaf 𝒜 (d + m), U) ⟶ Γ(twistingSheaf 𝒜 d, U) :=
  AddCommGrpCat.ofHom
    { toFun s := ⟨fun x ↦ Localization.mk 1
        (⟨f, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) * s.1 x,
        div_mem' (d := d) hf _ (fun x ↦ hU x.2) s.1 s.2⟩
      map_zero' := Subtype.ext (funext fun _ ↦ mul_zero _)
      map_add' _ _ := Subtype.ext (funext fun _ ↦ mul_add _ _ _) }

@[simp]
theorem twistingSheafMul_app_apply {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (d : ℤ) (U : (Proj 𝒜).Opens)
    (s : Γ(twistingSheaf 𝒜 d, U)) (x : U) :
    (((twistingSheafMul hf d).app U) s).1 x = Localization.mk f 1 * s.1 x := rfl

@[simp]
theorem twistingSheafDivApp_apply {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (d : ℤ) {U : (Proj 𝒜).Opens}
    (hU : U ≤ Proj.basicOpen 𝒜 f) (s : Γ(twistingSheaf 𝒜 (d + m), U)) (x : U) :
    ((twistingSheafDivApp hf d hU) s).1 x =
      Localization.mk 1 (⟨f, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) * s.1 x := rfl

/-- **Local triviality of `𝒪(d)`**: over a basic open set `D₊(f)` with `f` homogeneous of
degree `m`, multiplication by `f` is an isomorphism from the sections of `𝒪(d)` to those of
`𝒪(d + m)`. -/
theorem isIso_app_twistingSheafMul {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (d : ℤ) {U : (Proj 𝒜).Opens}
    (hU : U ≤ Proj.basicOpen 𝒜 f) : IsIso ((twistingSheafMul hf d).app U) :=
  ⟨twistingSheafDivApp hf d hU, by
    ext s
    refine Subtype.ext (funext fun x ↦ ?_)
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
      twistingSheafDivApp_apply, twistingSheafMul_app_apply, AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply]
    rw [← mul_assoc, Localization.mk_one_mul_mk_one, one_mul], by
    ext s
    refine Subtype.ext (funext fun x ↦ ?_)
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
      twistingSheafMul_app_apply, twistingSheafDivApp_apply, AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply]
    rw [← mul_assoc, mul_comm (Localization.mk f 1), Localization.mk_one_mul_mk_one, one_mul]⟩


/-- **Local triviality of `𝒪(d)`**: for `f` homogeneous of degree `m`, multiplication by `f` is
an isomorphism of `𝒪`-modules `𝒪(d) ≅ 𝒪(d + m)` over the basic open set `D₊(f)`. -/
instance isIso_restrict_twistingSheafMul {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (d : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι).map (twistingSheafMul hf d)) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun V ↦
    isIso_app_twistingSheafMul hf d ((Proj.basicOpen 𝒜 f).ι_image_le V)

/-- **`𝒪(d)` is trivial over the basic open set `D₊(f)`** for `f` homogeneous of degree `m`:
multiplication by `f` is an isomorphism `𝒪(d)|_{D₊(f)} ≅ 𝒪(d + m)|_{D₊(f)}`. -/
noncomputable def twistingSheafRestrictIso {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (d : ℤ) :
    (twistingSheaf 𝒜 d).restrict (Proj.basicOpen 𝒜 f).ι ≅
      (twistingSheaf 𝒜 (d + m)).restrict (Proj.basicOpen 𝒜 f).ι :=
  asIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι).map (twistingSheafMul hf d))

section Vanishing

variable {j : ℕ} {a : A} (ha : a ∈ 𝒜 j) (x : Proj 𝒜)

/-- The value of `homogeneousSection ha` at a point `x` is the image of `a` in the local ring
`A_x`. -/
theorem homogeneousSection_apply_eq_algebraMap :
    (homogeneousSection ha).1 ⟨x, trivial⟩ = algebraMap A (atPoint 𝒜 x) a :=
  Localization.mk_one_eq_algebraMap a

/-- **Pointwise non-vanishing.** The global section of `𝒪(j)` attached to a homogeneous element
`a` of degree `j` does not vanish at a point `x` of `Proj 𝒜` — that is, its value at `x` is a
unit of the local ring `A_x` — if and only if `x` lies in the basic open set `D₊(a)`. -/
theorem isUnit_homogeneousSection_apply_iff :
    IsUnit ((homogeneousSection ha).1 ⟨x, trivial⟩) ↔ x ∈ Proj.basicOpen 𝒜 a := by
  rw [homogeneousSection_apply_eq_algebraMap ha x,
    IsLocalization.AtPrime.isUnit_to_map_iff (atPoint 𝒜 x) x.asHomogeneousIdeal.toIdeal a]
  exact Ideal.mem_primeCompl_iff.trans (Proj.mem_basicOpen 𝒜 a x).symm

/-- **Pointwise vanishing.** The global section of `𝒪(j)` attached to a homogeneous element `a`
of degree `j` vanishes at a point `x` of `Proj 𝒜` — that is, its value at `x` lies in the
maximal ideal of the local ring `A_x` — if and only if `a` lies in the homogeneous prime ideal
of `x`. -/
theorem homogeneousSection_apply_mem_maximalIdeal_iff :
    (homogeneousSection ha).1 ⟨x, trivial⟩ ∈ IsLocalRing.maximalIdeal (atPoint 𝒜 x) ↔
      a ∈ x.asHomogeneousIdeal := by
  rw [homogeneousSection_apply_eq_algebraMap ha x]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff (atPoint 𝒜 x)
    x.asHomogeneousIdeal.toIdeal a

/-- The non-vanishing locus of the global section of `𝒪(j)` attached to a homogeneous element
`a` of degree `j` is the basic open set `D₊(a)`. -/
theorem setOf_isUnit_homogeneousSection_apply :
    {y : Proj 𝒜 | IsUnit ((homogeneousSection ha).1 ⟨y, trivial⟩)} =
      (Proj.basicOpen 𝒜 a : Set (Proj 𝒜)) :=
  Set.ext fun y ↦ isUnit_homogeneousSection_apply_iff ha y

section LocalGenerator

variable {f : A} (hf : f ∈ 𝒜 j) (hfx : f ∉ x.asHomogeneousIdeal)

/-- Near a point `x` avoided by a homogeneous element `f` of degree `j`, the section of `𝒪(j)`
attached to `f` is a local generator, and the section attached to `a ∈ 𝒜 j` is `a / f` times it.
Here `a / f` is an element of the local ring `𝒪_{Proj 𝒜, x}` of `Proj 𝒜` at `x`, acting on the
value at `x` through `HomogeneousLocalization.val`. -/
theorem homogeneousSection_apply_eq_mul :
    (homogeneousSection ha).1 ⟨x, trivial⟩ =
      (HomogeneousLocalization.mk ⟨j, ⟨a, ha⟩, ⟨f, hf⟩, hfx⟩ :
        HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal).val *
        (homogeneousSection hf).1 ⟨x, trivial⟩ := by
  simp only [homogeneousSection_apply, HomogeneousLocalization.val_mk, Localization.mk_mul,
    mul_one]
  exact (Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [mul_comm]))).symm

/-- The element `a / f` of the local ring `𝒪_{Proj 𝒜, x}` is a unit if and only if `x` lies in
the basic open set `D₊(a)`, i.e. if and only if `a` avoids the homogeneous prime ideal of `x`. -/
theorem isUnit_mk_iff_mem_basicOpen :
    IsUnit (HomogeneousLocalization.mk ⟨j, ⟨a, ha⟩, ⟨f, hf⟩, hfx⟩ :
        HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) ↔
      x ∈ Proj.basicOpen 𝒜 a :=
  (HomogeneousLocalization.isUnit_mk_iff 𝒜 _ _).trans (Proj.mem_basicOpen 𝒜 a x).symm

/-- **The two readings of non-vanishing at `x` agree**: the value of `homogeneousSection ha` at
`x` is a unit of `A_x` if and only if the coefficient `a / f` of that value with respect to the
local generator attached to `f` is a unit of `𝒪_{Proj 𝒜, x}`. -/
theorem isUnit_homogeneousSection_apply_iff_isUnit_mk :
    IsUnit ((homogeneousSection ha).1 ⟨x, trivial⟩) ↔
      IsUnit (HomogeneousLocalization.mk ⟨j, ⟨a, ha⟩, ⟨f, hf⟩, hfx⟩ :
        HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
  (isUnit_homogeneousSection_apply_iff ha x).trans (isUnit_mk_iff_mem_basicOpen ha x hf hfx).symm

end LocalGenerator

end Vanishing

end Proj

end AlgebraicGeometry
