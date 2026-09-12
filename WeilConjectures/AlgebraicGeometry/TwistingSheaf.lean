/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
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

## Main definitions

- `AlgebraicGeometry.Proj.twistingSheaf`: the twisting sheaf `𝒪(d)` on `Proj 𝒜`, for `d : ℤ`.
- `AlgebraicGeometry.Proj.homogeneousSection`: the global section of `𝒪(j)` attached to a
  homogeneous element of degree `j`. On `ℙᴺ` these are the homogeneous coordinates
  `T₀, …, T_N ∈ Γ(ℙᴺ, 𝒪(1))`.
- `AlgebraicGeometry.Proj.twistingSheafMul`: multiplication by a homogeneous element `f` of
  degree `m`, as a morphism `𝒪(d) ⟶ 𝒪(d + m)`.

## Main results

- `AlgebraicGeometry.Proj.twistingSheafRestrictIso`: **local triviality**, multiplication by a
  homogeneous element `f` of degree `m` is an isomorphism `𝒪(d) ≅ 𝒪(d + m)` over `D₊(f)`.
- `AlgebraicGeometry.Proj.twistingSheafZeroIso`: `𝒪(0)` is the structure sheaf.

## TODO

- `𝒪(d)` is an invertible sheaf, i.e. `SheafOfModules.Invertible (Proj.twistingSheaf 𝒜 d)`.
  This needs the isomorphism `𝒪(d) ⊗ 𝒪(e) ≅ 𝒪(d + e)`, hence the comparison between the tensor
  product of sheaves of modules and the sectionwise tensor product.
- The fibrewise description of a global section: for `a` homogeneous of degree `j`, the section
  `homogeneousSection a` of `𝒪(j)` vanishes at a point `x` if and only if `a ∈ x`.

The transfer of `𝒪(d)` to the relative projective space `ℙ(n; S)`, by pulling back along the
map to the integral model, and its compatibility with base change, are in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistingSheaf`.
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
    (isLocallyFraction 𝒜 (d + m)).pred (fun x ↦ Localization.mk f 1 * a x) := by
  intro x
  obtain ⟨V, hxV, e, i, j, hij, ⟨r, hr⟩, ⟨t, ht⟩, hw, w⟩ := ha x
  refine ⟨V, hxV, e, i, m + j, by push_cast; omega, ⟨f * r, SetLike.mul_mem_graded hf hr⟩,
    ⟨t, ht⟩, hw, fun y ↦ ?_⟩
  simp only [Subtype.forall] at w
  simp [w y.1 y.2, Localization.mk_mul]

variable {𝒜} in
theorem div_mem' {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : ∀ x : U.unop, f ∉ x.1.asHomogeneousIdeal.toIdeal)
    (a : ∀ x : U.unop, atPoint 𝒜 x.1) (ha : (isLocallyFraction 𝒜 (d + m)).pred a) :
    (isLocallyFraction 𝒜 d).pred (fun x ↦ Localization.mk 1 ⟨f, hU x⟩ * a x) := by
  intro x
  obtain ⟨V, hxV, e, i, j, hij, ⟨r, hr⟩, ⟨t, ht⟩, hw, w⟩ := ha x
  refine ⟨V, hxV, e, m + i, j, by push_cast; omega, ⟨r, hr⟩,
    ⟨f * t, SetLike.mul_mem_graded hf ht⟩,
    fun y ↦ (y.1 : ProjectiveSpectrum 𝒜).asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hU (e y)) (hw y), fun y ↦ ?_⟩
  simp only [Subtype.forall] at w
  simp [w y.1 y.2, Localization.mk_mul]
  rfl

/-- The `d`-th twisting presheaf as a presheaf of `𝒪`-modules on `Proj 𝒜`. -/
def presheafOfModules : (Proj 𝒜).PresheafOfModules :=
  PresheafOfModules.ofPresheaf (presheafInAb 𝒜 d) (by intros; rfl)

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
theorem homogeneousSection_apply {j : ℕ} {a : A} (ha : a ∈ 𝒜 j) (x : (⊤ : (Proj 𝒜).Opens)) :
    (homogeneousSection ha).1 x = Localization.mk a 1 := rfl

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

end Proj

end AlgebraicGeometry
