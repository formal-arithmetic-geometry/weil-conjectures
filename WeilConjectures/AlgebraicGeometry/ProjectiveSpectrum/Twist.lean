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

/-!
# The twisting sheaves `𝒪(m)` on `Proj` of a graded ring

Let `𝒜 : ℕ → σ` be a graded ring with underlying ring `A`, and let `m : ℤ`. We construct the
twisting sheaf `𝒪(m)` on `Proj 𝒜` as a sheaf of modules over the structure sheaf.

The construction mirrors the one of the structure sheaf in
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean`. The fibre at a point `x` is
the degree-`m` part `HomogeneousLocalization.degreePart 𝒜 x m` of the localization `A_x`: the
fractions `a / b` with `a ∈ 𝒜 i`, `b ∈ 𝒜 j`, `b ∉ x` and `i = j + m`. A section of `𝒪(m)` over
an open set `U` is a dependent function `x ↦ s x` into these fibres which is locally a fixed
fraction `a / b` of this kind. This is Hartshorne's `(S(m))~`. Sections of the structure sheaf
are dependent functions into the degree-`0` parts `(A_x)₀`, and they act on sections of `𝒪(m)`
by pointwise multiplication.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpectrum.Twist.isLocallyFraction`: the local predicate cutting
  out the sections of `𝒪(m)`.
- `AlgebraicGeometry.ProjectiveSpectrum.Twist.sections`: the sections of `𝒪(m)` over `U`, as a
  submodule of the dependent functions over the sections of the structure sheaf.
- `AlgebraicGeometry.Proj.twist`: the twisting sheaf `𝒪(m)` on `Proj 𝒜`.

## Main results

- `AlgebraicGeometry.ProjectiveSpectrum.Twist.isSheaf_presheafInAb`: the sheaf condition.
- `AlgebraicGeometry.Proj.twistZeroIso`: `𝒪(0)` is the structure sheaf.

## TODO

- On `D₊(f)` with `f ∈ 𝒜 d`, `d > 0`, the sheaf `𝒪(m)` restricts to a free module of rank one
  when `d ∣ m`; this is the sheaf-level form of
  `HomogeneousLocalization.degreePart.powDivPowEquiv`.
- For a polynomial ring, the global sections of `𝒪(m)` are the homogeneous polynomials of
  degree `m`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace TopCat HomogeneousLocalization

namespace AlgebraicGeometry

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveSpectrum.Twist

/-- The fibre of the twisting sheaf `𝒪(m)` at a point `x` of `Proj 𝒜`: the degree-`m` part of
the localization of `A` at `x`. -/
abbrev fiber (m : ℤ) (x : ProjectiveSpectrum 𝒜) : Type _ :=
  degreePart 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl m

variable {𝒜}

/-- The predicate saying that a dependent function on an open `U` is, on all of `U`, the fixed
fraction `a / b` with `a ∈ 𝒜 i`, `b ∈ 𝒜 j`, `i = j + m` and `b` avoiding every point of `U`. -/
def IsFraction (m : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, fiber 𝒜 m x.1) :
    Prop :=
  ∃ (i j : ℕ) (_ : (i : ℤ) = j + m) (a : 𝒜 i) (b : 𝒜 j)
    (hb : ∀ x : U, (b : A) ∉ x.1.asHomogeneousIdeal.toIdeal),
    ∀ x : U, (f x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      Localization.mk (a : A) ⟨b, hb x⟩

variable (𝒜)

/-- The predicate `IsFraction m` is prelocal: if it holds on `U`, it holds on every open subset
of `U`. -/
def isFractionPrelocal (m : ℤ) :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => fiber 𝒜 m x where
  pred f := IsFraction m f
  res := by
    rintro V U i f ⟨k, l, hkl, a, b, h, w⟩
    exact ⟨k, l, hkl, a, b, (h <| i ·), (w <| i ·)⟩

/-- The sections of the twisting sheaf `𝒪(m)` are the dependent functions which are locally
fractions `a / b` with `deg a = deg b + m`. -/
def isLocallyFraction (m : ℤ) :
    LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => fiber 𝒜 m x :=
  (isFractionPrelocal 𝒜 m).sheafify

section Sections

variable {𝒜}

open ProjectiveSpectrum.StructureSheaf in
/-- The dependent functions into the fibres of `𝒪(m)` on `U` form a module over the sections of
the structure sheaf of `Proj 𝒜` on `U`, by pointwise multiplication. -/
instance modulePi (m : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj 𝒜).ringCatSheaf.obj.obj U) (∀ x : U.unop, fiber 𝒜 m x.1) :=
  inferInstanceAs (Module ↥(sectionsSubring (𝒜 := 𝒜) U) _)

theorem coe_smul_apply {m : ℤ} {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (c : (Proj 𝒜).ringCatSheaf.obj.obj U) (s : ∀ x : U.unop, fiber 𝒜 m x.1) (x : U.unop) :
    ((c • s) x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = (c.1 x).val * s x :=
  rfl

theorem zero_mem' (m : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜 m).pred (0 : ∀ x : U.unop, fiber 𝒜 m x.1) := by
  intro x
  obtain ⟨f, d, hfd, hd, hfx⟩ := x.1.exists_homogeneous_notMem
  have hkd : 0 ≤ ((m.natAbs * d : ℕ) : ℤ) + m := by
    have := Nat.le_mul_of_pos_right m.natAbs hd
    omega
  have hfk : f ^ m.natAbs ∉ x.1.asHomogeneousIdeal := fun h ↦
    hfx (x.1.isPrime.mem_of_pow_mem _ h)
  refine ⟨U.unop ⊓ ProjectiveSpectrum.basicOpen 𝒜 (f ^ m.natAbs), ⟨x.2, hfk⟩,
    Opens.infLELeft _ _, (((m.natAbs * d : ℕ) : ℤ) + m).toNat, m.natAbs * d,
    Int.toNat_of_nonneg hkd, ⟨0, zero_mem _⟩,
    ⟨f ^ m.natAbs, by simpa [smul_eq_mul, mul_comm] using SetLike.pow_mem_graded m.natAbs hfd⟩,
    fun y ↦ y.2.2, fun _ ↦ ?_⟩
  simp [Localization.mk_zero]

theorem add_mem' (m : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (s t : ∀ x : U.unop, fiber 𝒜 m x.1)
    (hs : (isLocallyFraction 𝒜 m).pred s) (ht : (isLocallyFraction 𝒜 m).pred t) :
    (isLocallyFraction 𝒜 m).pred (s + t) := by
  intro x
  obtain ⟨V₁, m₁, e₁, i₁, j₁, h₁, ⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩, hw₁, w₁⟩ := hs x
  obtain ⟨V₂, m₂, e₂, i₂, j₂, h₂, ⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩, hw₂, w₂⟩ := ht x
  have key : j₁ + i₂ = j₂ + i₁ := by omega
  refine ⟨V₁ ⊓ V₂, ⟨m₁, m₂⟩, Opens.infLELeft _ _ ≫ e₁, j₁ + i₂, j₁ + j₂, by push_cast; omega,
    ⟨b₁ * a₂ + b₂ * a₁, add_mem (SetLike.mul_mem_graded hb₁ ha₂)
      (key ▸ SetLike.mul_mem_graded hb₂ ha₁)⟩, ⟨b₁ * b₂, SetLike.mul_mem_graded hb₁ hb₂⟩,
    fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hw₁ ⟨y.1, y.2.1⟩)
      (hw₂ ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at w₁ w₂
  exact (congrArg₂ (· + ·) (w₁ y hy.1) (w₂ y hy.2)).trans (Localization.add_mk _ _ _ _)

theorem smul_mem' (m : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (c : (Proj 𝒜).ringCatSheaf.obj.obj U) (s : ∀ x : U.unop, fiber 𝒜 m x.1)
    (hs : (isLocallyFraction 𝒜 m).pred s) :
    (isLocallyFraction 𝒜 m).pred (c • s) := by
  intro x
  obtain ⟨V₁, m₁, e₁, k, ⟨r, hr⟩, ⟨q, hq⟩, hw₀, w₀⟩ := c.2 x
  obtain ⟨V₂, m₂, e₂, i, j, hij, ⟨a, ha⟩, ⟨b, hb⟩, hw, w⟩ := hs x
  refine ⟨V₁ ⊓ V₂, ⟨m₁, m₂⟩, Opens.infLELeft _ _ ≫ e₁, k + i, k + j, by push_cast; omega,
    ⟨r * a, SetLike.mul_mem_graded hr ha⟩, ⟨q * b, SetLike.mul_mem_graded hq hb⟩,
    fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hw₀ ⟨y.1, y.2.1⟩)
      (hw ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at w₀ w
  rw [coe_smul_apply]
  change (c.1 ⟨y, _⟩).val * (s ⟨y, _⟩ : Localization.AtPrime _) = _
  rw [w y hy.2, w₀ y hy.1, val_mk, Localization.mk_mul]
  rfl

end Sections

variable (m : ℤ)

/-- The sections of the twisting sheaf `𝒪(m)` on an open set `U`: the dependent functions into
the fibres of `𝒪(m)` that are locally fractions, as a module over the sections of the structure
sheaf. -/
def sections (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Submodule ((Proj 𝒜).ringCatSheaf.obj.obj U) (∀ x : U.unop, fiber 𝒜 m x.1) where
  carrier := {s | (isLocallyFraction 𝒜 m).pred s}
  zero_mem' := zero_mem' m U
  add_mem' := add_mem' m U _ _
  smul_mem' c _ h := smul_mem' m U c _ h

/-- The twisting sheaf `𝒪(m)`, valued in `Type`: the subsheaf of the sheaf of dependent
functions consisting of the local fractions. -/
def sheafInType : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 m)

instance addCommGroupSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddCommGroup ((sheafInType 𝒜 m).1.obj U) :=
  inferInstanceAs (AddCommGroup (sections 𝒜 m U))

/-- The twisting presheaf `𝒪(m)`, valued in abelian groups. -/
def presheafInAb : Presheaf Ab (ProjectiveSpectrum.top 𝒜) where
  obj U := AddCommGrpCat.of ((sheafInType 𝒜 m).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (sheafInType 𝒜 m).1.map i
      map_zero' := rfl
      map_add' _ _ := rfl }

instance modulePresheafInAbObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj 𝒜).ringCatSheaf.obj.obj U) ((presheafInAb 𝒜 m).obj U) :=
  inferInstanceAs (Module _ (sections 𝒜 m U))

/-- The `Ab`-valued twisting presheaf agrees with the `Type`-valued one after forgetting. -/
def presheafInAbCompForget : presheafInAb 𝒜 m ⋙ forget Ab ≅ (sheafInType 𝒜 m).1 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

theorem isSheaf_presheafInAb : (presheafInAb 𝒜 m).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr
    (TopCat.Presheaf.isSheaf_of_iso (presheafInAbCompForget 𝒜 m).symm (sheafInType 𝒜 m).property)

/-- The twisting presheaf `𝒪(m)` as a presheaf of modules over the structure sheaf of
`Proj 𝒜`. -/
def presheafOfModules : (Proj 𝒜).PresheafOfModules :=
  PresheafOfModules.ofPresheaf (presheafInAb 𝒜 m) (by intros; rfl)

section Zero

variable {𝒜}

/-- A section of `𝒪(0)` takes values in the degree-zero homogeneous localizations, compatibly
with the local fraction data. -/
theorem exists_val_eq {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (t : sections 𝒜 0 U)
    (x : U.unop) :
    ∃ p : AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal, p.val = t.1 x := by
  obtain ⟨V, hxV, e, i, j, hij, ⟨a, ha⟩, ⟨b, hb⟩, hw, w⟩ := t.2 x
  obtain rfl : i = j := by omega
  exact ⟨.mk ⟨i, ⟨a, ha⟩, ⟨b, hb⟩, hw ⟨x.1, hxV⟩⟩, by rw [val_mk]; exact (w ⟨x.1, hxV⟩).symm⟩

/-- The values of a section of the structure sheaf form a section of `𝒪(0)`. -/
theorem val_mem_sections {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : (Proj 𝒜).ringCatSheaf.obj.obj U) :
    (isLocallyFraction 𝒜 0).pred
      (fun x ↦ ⟨(s.1 x).val, val_mem_degreePart_zero _⟩ : ∀ x : U.unop, fiber 𝒜 0 x.1) := by
  intro x
  obtain ⟨V, hxV, e, i, ⟨r, hr⟩, ⟨q, hq⟩, hw, w⟩ := s.2 x
  refine ⟨V, hxV, e, i, i, by simp, ⟨r, hr⟩, ⟨q, hq⟩, hw, fun y ↦ ?_⟩
  simp only [Subtype.forall] at w
  simp [w y.1 y.2, val_mk]

/-- The inverse of the canonical map from the sections of the structure sheaf to those
of `𝒪(0)`. -/
def sectionsZeroInv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (t : sections 𝒜 0 U) :
    (Proj 𝒜).ringCatSheaf.obj.obj U :=
  ⟨fun x ↦ (exists_val_eq t x).choose, by
    intro x
    obtain ⟨V, hxV, e, i, j, hij, ⟨a, ha⟩, ⟨b, hb⟩, hw, w⟩ := t.2 x
    obtain rfl : i = j := by omega
    refine ⟨V, hxV, e, i, ⟨a, ha⟩, ⟨b, hb⟩, hw, fun y ↦ val_injective _ ?_⟩
    rw [(exists_val_eq t (e y)).choose_spec, val_mk]
    exact w y⟩

@[simp]
theorem val_sectionsZeroInv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (t : sections 𝒜 0 U)
    (x : U.unop) : ((sectionsZeroInv t).1 x).val = t.1 x :=
  (exists_val_eq t x).choose_spec

/-- The canonical morphism of presheaves of abelian groups from the structure sheaf of `Proj 𝒜`
to the twisting presheaf `𝒪(0)`. -/
def unitToPresheafInAbZero :
    (PresheafOfModules.unit (Proj 𝒜).ringCatSheaf.obj).presheaf ⟶ presheafInAb 𝒜 0 where
  app _ := AddCommGrpCat.ofHom
    { toFun s := ⟨_, val_mem_sections s⟩
      map_zero' := Subtype.ext (funext fun _ ↦ Subtype.ext val_zero)
      map_add' _ _ := Subtype.ext (funext fun _ ↦ Subtype.ext (val_add _ _)) }
  naturality _ _ _ := rfl

end Zero

end ProjectiveSpectrum.Twist

open ProjectiveSpectrum.Twist in
/-- **The twisting sheaf `𝒪(m)` on `Proj 𝒜`**, for `m : ℤ`: its sections over `U` are the
dependent functions `x ↦ s x ∈ (A_x)ₘ` which are locally fractions `a / b` of homogeneous
elements with `deg a = deg b + m`. -/
def Proj.twist (m : ℤ) : (Proj 𝒜).Modules :=
  ⟨presheafOfModules 𝒜 m, isSheaf_presheafInAb 𝒜 m⟩

namespace Proj

variable {𝒜}

open ProjectiveSpectrum.Twist

/-- The canonical morphism `𝒪 ⟶ 𝒪(0)` from the structure sheaf of `Proj 𝒜` to its zeroth
twisting sheaf. -/
def unitToTwistZero :
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules) ⟶ twist 𝒜 0 :=
  ⟨PresheafOfModules.homMk unitToPresheafInAbZero
    (fun _ _ _ ↦ Subtype.ext (funext fun _ ↦ Subtype.ext (val_mul _ _)))⟩

@[simp]
theorem coe_unitToTwistZero_app_apply (U : (Proj 𝒜).Opens)
    (s : Γ((SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules), U)) (x : U) :
    (((Scheme.Modules.Hom.app unitToTwistZero U) s).1 x :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = (s.1 x).val :=
  rfl

instance : IsIso (unitToTwistZero (𝒜 := 𝒜)) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U ↦ by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun s t h ↦ Subtype.ext (funext fun x ↦ val_injective _ ?_),
      fun t ↦ ⟨sectionsZeroInv t, Subtype.ext (funext fun x ↦
        Subtype.ext (val_sectionsZeroInv t x))⟩⟩
    exact congrArg Subtype.val (congrFun (congrArg Subtype.val h) x)

/-- **`𝒪(0)` is the structure sheaf**: the zeroth twisting sheaf of `Proj 𝒜` is isomorphic to
the structure sheaf. -/
def twistZeroIso :
    twist 𝒜 0 ≅ (SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules) :=
  (asIso unitToTwistZero).symm

end Proj

end AlgebraicGeometry
