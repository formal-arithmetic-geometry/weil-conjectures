/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
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

The fibre is the submodule `degreePart 𝒜 x m` rather than all of `A_x`, so that the
`HomogeneousLocalization`-module structure of the fibres can be used directly: `𝒪(0) ≅ 𝒪` is
`HomogeneousLocalization.degreePart.zeroEquiv` applied pointwise, and multiplication by a
homogeneous element is `HomogeneousLocalization.mul_mem_degreePart` applied pointwise.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpectrum.Twist.isLocallyFraction`: the local predicate cutting
  out the sections of `𝒪(m)`.
- `AlgebraicGeometry.Proj.twist`: the twisting sheaf `𝒪(m)` on `Proj 𝒜`.
- `AlgebraicGeometry.Proj.twistMul`: multiplication by a homogeneous element `f` of degree `d`,
  as a morphism `𝒪(m) ⟶ 𝒪(m + d)`.

## Main results

- `AlgebraicGeometry.Proj.unitIsoTwistZero`: `𝒪(0)` is the structure sheaf.
- `AlgebraicGeometry.Proj.twistRestrictIso`: on the basic open set `D₊(f)`, multiplication by
  `f` is an isomorphism `𝒪(m) ≅ 𝒪(m + d)`. Together with `unitIsoTwistZero`, this says that
  `𝒪(k * d)` is trivial on `D₊(f)`.
- `AlgebraicGeometry.Proj.nonempty_restrict_twist_iso_unit`: `𝒪(m)` is trivial on `D₊(f)` for
  every `m` when `f` has degree `1`.
- `AlgebraicGeometry.Proj.isInvertible_twist`: `𝒪(m)` is invertible when the `D₊(f)` with `f`
  of degree `1` cover `Proj 𝒜`.

## TODO

- Construct `M~` for an arbitrary graded `A`-module `M` and recover `𝒪(m)` as `(A(m))~`. All
  the proofs in this file go through with `a ∈ 𝒜 i` replaced by `a ∈ M i`.
- The multiplication `𝒪(m) ⊗ 𝒪(n) ≅ 𝒪(m + n)`.
- The global sections `𝒜 m → Γ(𝒪(m))` of homogeneous elements; for a polynomial ring, they are
  all the global sections.
- Relate `Proj.twist` to `Proj.twistingSheaf` on the `Abelian-variety` branch, whose fibres are
  all of `A_x`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace TopCat HomogeneousLocalization

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ)

namespace ProjectiveSpectrum.Twist

/-- The fibre of the twisting sheaf `𝒪(m)` at a point `x` of `Proj 𝒜`: the degree-`m` part of
the localization of `A` at `x`. -/
abbrev fiber (x : ProjectiveSpectrum 𝒜) :=
  degreePart 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl m

variable {𝒜 m}

/-- The predicate saying that a dependent function on an open `U` is, on all of `U`, the fixed
fraction `a / b` with `a ∈ 𝒜 i`, `b ∈ 𝒜 j`, `i = j + m` and `b` avoiding every point of `U`. -/
def IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, fiber 𝒜 m x.1) : Prop :=
  ∃ (i j : ℕ) (h : (i : ℤ) = j + m) (a : 𝒜 i) (b : 𝒜 j)
    (hb : ∀ x : U, (b : A) ∉ x.1.asHomogeneousIdeal.toIdeal),
    ∀ x : U, f x = degreePart.mk a b (hb x) h

variable (𝒜 m)

/-- The predicate `IsFraction` is prelocal: if it holds on `U`, it holds on every open subset
of `U`. -/
def isFractionPrelocal :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ fiber 𝒜 m x where
  pred f := IsFraction f
  res := by
    rintro V U i f ⟨k, l, hkl, a, b, h, w⟩
    exact ⟨k, l, hkl, a, b, (h <| i ·), (w <| i ·)⟩

/-- The sections of the twisting sheaf `𝒪(m)` are the dependent functions which are locally
fractions `a / b` with `deg a = deg b + m`. -/
def isLocallyFraction : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ fiber 𝒜 m x :=
  (isFractionPrelocal 𝒜 m).sheafify

variable {𝒜 m}

/-- A fixed fraction `a / b` of degree `m` is a section of `𝒪(m)` wherever `b` does not
vanish. -/
theorem isLocallyFraction_mk {i j : ℕ} (h : (i : ℤ) = j + m) (a : 𝒜 i) (b : 𝒜 j)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hb : ∀ x : U, (b : A) ∉ x.1.asHomogeneousIdeal.toIdeal) :
    (isLocallyFraction 𝒜 m).pred fun x : U ↦ degreePart.mk a b (hb x) h :=
  fun x ↦ ⟨U, x.2, 𝟙 _, i, j, h, a, b, hb, fun _ ↦ rfl⟩

/-- The pointwise product of a section of `𝒪(m)` and a section of `𝒪(n)` is a section of
`𝒪(k)`, for `m + n = k`. -/
theorem isLocallyFraction_mul {n k : ℤ} (h : m + n = k) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {s : ∀ x : U, fiber 𝒜 m x.1} {t : ∀ x : U, fiber 𝒜 n x.1}
    (hs : (isLocallyFraction 𝒜 m).pred s) (ht : (isLocallyFraction 𝒜 n).pred t) :
    (isLocallyFraction 𝒜 k).pred fun x ↦
      ⟨s x * t x, h ▸ mul_mem_degreePart (s x).2 (t x).2⟩ := by
  intro x
  obtain ⟨V₁, m₁, e₁, i₁, j₁, h₁, ⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩, hw₁, w₁⟩ := hs x
  obtain ⟨V₂, m₂, e₂, i₂, j₂, h₂, ⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩, hw₂, w₂⟩ := ht x
  refine ⟨V₁ ⊓ V₂, ⟨m₁, m₂⟩, Opens.infLELeft _ _ ≫ e₁, i₁ + i₂, j₁ + j₂, by omega,
    ⟨a₁ * a₂, SetLike.mul_mem_graded ha₁ ha₂⟩, ⟨b₁ * b₂, SetLike.mul_mem_graded hb₁ hb₂⟩,
    fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hw₁ ⟨y.1, y.2.1⟩)
      (hw₂ ⟨y.1, y.2.2⟩), fun y ↦ ?_⟩
  ext
  exact congr($(w₁ ⟨y.1, y.2.1⟩).1 * $(w₂ ⟨y.1, y.2.2⟩).1).trans (Localization.mk_mul _ _ _ _)

/-- The values of a section of the structure sheaf form a section of `𝒪(0)`. -/
theorem isLocallyFraction_zeroEquiv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : (Proj 𝒜).ringCatSheaf.obj.obj U) :
    (isLocallyFraction 𝒜 0).pred fun x : U.unop ↦ degreePart.zeroEquiv (s.1 x) := by
  intro x
  obtain ⟨V, hxV, e, i, ⟨r, hr⟩, ⟨q, hq⟩, hw, w⟩ := s.2 x
  refine ⟨V, hxV, e, i, i, by simp, ⟨r, hr⟩, ⟨q, hq⟩, hw, fun y ↦ ?_⟩
  ext
  simp [w y, val_mk]

open ProjectiveSpectrum.StructureSheaf in
/-- The dependent functions into the fibres of `𝒪(m)` on `U` form a module over the sections of
the structure sheaf of `Proj 𝒜` on `U`, by pointwise multiplication. -/
instance modulePi (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj 𝒜).ringCatSheaf.obj.obj U) (∀ x : U.unop, fiber 𝒜 m x.1) :=
  inferInstanceAs (Module ↥(sectionsSubring (𝒜 := 𝒜) U) _)

/-- Sections of the structure sheaf act on dependent functions into the fibres of `𝒪(m)`
pointwise. -/
@[simp]
theorem smul_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (c : (Proj 𝒜).ringCatSheaf.obj.obj U) (s : ∀ x : U.unop, fiber 𝒜 m x.1) (x : U.unop) :
    (c • s) x = c.1 x • s x :=
  rfl

namespace Sections

variable (m) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)

/-- The zero function is a section of `𝒪(m)`. -/
theorem zero_mem' : (isLocallyFraction 𝒜 m).pred (0 : ∀ x : U.unop, fiber 𝒜 m x.1) := by
  intro x
  obtain ⟨j, hj, b, hb, hbx⟩ := x.1.exists_homogeneous_notMem_of_le (-m).toNat
  refine ⟨U.unop ⊓ ProjectiveSpectrum.basicOpen 𝒜 b, ⟨x.2, hbx⟩, Opens.infLELeft _ _,
    (j + m).toNat, j, by omega, 0, ⟨b, hb⟩, fun y ↦ y.2.2, fun _ ↦ ?_⟩
  ext
  simp [Localization.mk_zero]

variable {m U}

/-- The sum of two sections of `𝒪(m)` is a section of `𝒪(m)`. -/
theorem add_mem' {s t : ∀ x : U.unop, fiber 𝒜 m x.1} (hs : (isLocallyFraction 𝒜 m).pred s)
    (ht : (isLocallyFraction 𝒜 m).pred t) : (isLocallyFraction 𝒜 m).pred (s + t) := by
  intro x
  obtain ⟨V₁, m₁, e₁, i₁, j₁, h₁, ⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩, hw₁, w₁⟩ := hs x
  obtain ⟨V₂, m₂, e₂, i₂, j₂, h₂, ⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩, hw₂, w₂⟩ := ht x
  refine ⟨V₁ ⊓ V₂, ⟨m₁, m₂⟩, Opens.infLELeft _ _ ≫ e₁, j₁ + i₂, j₁ + j₂, by omega,
    ⟨b₁ * a₂ + b₂ * a₁, add_mem (SetLike.mul_mem_graded hb₁ ha₂) ?_⟩,
    ⟨b₁ * b₂, SetLike.mul_mem_graded hb₁ hb₂⟩,
    fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hw₁ ⟨y.1, y.2.1⟩)
      (hw₂ ⟨y.1, y.2.2⟩), fun y ↦ ?_⟩
  · rw [show j₁ + i₂ = j₂ + i₁ by omega]
    exact SetLike.mul_mem_graded hb₂ ha₁
  · ext
    exact congr($(w₁ ⟨y.1, y.2.1⟩).1 + $(w₂ ⟨y.1, y.2.2⟩).1).trans (Localization.add_mk _ _ _ _)

/-- A section of `𝒪(m)` multiplied by a section of the structure sheaf is a section of
`𝒪(m)`. -/
theorem smul_mem' (c : (Proj 𝒜).ringCatSheaf.obj.obj U) {s : ∀ x : U.unop, fiber 𝒜 m x.1}
    (hs : (isLocallyFraction 𝒜 m).pred s) : (isLocallyFraction 𝒜 m).pred (c • s) :=
  isLocallyFraction_mul (zero_add m) (isLocallyFraction_zeroEquiv c) hs

end Sections

variable (𝒜 m)

/-- The sections of the twisting sheaf `𝒪(m)` on an open set `U`: the dependent functions into
the fibres of `𝒪(m)` that are locally fractions, as a module over the sections of the structure
sheaf. -/
def sections (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Submodule ((Proj 𝒜).ringCatSheaf.obj.obj U) (∀ x : U.unop, fiber 𝒜 m x.1) where
  carrier := {s | (isLocallyFraction 𝒜 m).pred s}
  zero_mem' := Sections.zero_mem' m U
  add_mem' := Sections.add_mem'
  smul_mem' := Sections.smul_mem'

/-- The twisting sheaf `𝒪(m)`, valued in `Type`: the subsheaf of the sheaf of dependent
functions consisting of the local fractions. -/
def sheafInType : Sheaf (Type u) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 m)

/-- The sections of `𝒪(m)` form an abelian group. -/
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

/-- The sections of `𝒪(m)` over `U` form a module over the sections of the structure sheaf
over `U`. -/
instance modulePresheafInAbObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj 𝒜).ringCatSheaf.obj.obj U) ((presheafInAb 𝒜 m).obj U) :=
  inferInstanceAs (Module _ (sections 𝒜 m U))

/-- The `Ab`-valued twisting presheaf agrees with the `Type`-valued one after forgetting. -/
def presheafInAbCompForget : presheafInAb 𝒜 m ⋙ forget Ab ≅ (sheafInType 𝒜 m).1 :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by cat_disch)

/-- The presheaf `𝒪(m)` is a sheaf. -/
theorem isSheaf_presheafInAb : (presheafInAb 𝒜 m).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr
    (TopCat.Presheaf.isSheaf_of_iso (presheafInAbCompForget 𝒜 m).symm (sheafInType 𝒜 m).property)

/-- The twisting presheaf `𝒪(m)` as a presheaf of modules over the structure sheaf of
`Proj 𝒜`. -/
def presheafOfModules : (Proj 𝒜).PresheafOfModules :=
  PresheafOfModules.ofPresheaf (presheafInAb 𝒜 m) fun _ _ _ _ _ ↦ rfl

variable {𝒜}

section Zero

/-- The canonical morphism of presheaves of abelian groups from the structure sheaf of `Proj 𝒜`
to the twisting presheaf `𝒪(0)`, given by `HomogeneousLocalization.degreePart.zeroEquiv` at
every point. -/
def unitToPresheafInAbZero :
    (PresheafOfModules.unit (Proj 𝒜).ringCatSheaf.obj).presheaf ⟶ presheafInAb 𝒜 0 where
  app _ := AddCommGrpCat.ofHom
    { toFun s := ⟨_, isLocallyFraction_zeroEquiv s⟩
      map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
      map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _) }
  naturality _ _ _ := rfl

/-- The map `𝒪 ⟶ 𝒪(0)` is `HomogeneousLocalization.degreePart.zeroEquiv` at every point. -/
@[simp]
theorem unitToPresheafInAbZero_app_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : (Proj 𝒜).ringCatSheaf.obj.obj U) (x : U.unop) :
    (unitToPresheafInAbZero.app U s).1 x = degreePart.zeroEquiv (s.1 x) :=
  rfl

/-- The inverse of the canonical map from the sections of the structure sheaf to those
of `𝒪(0)`, given by the inverse of `HomogeneousLocalization.degreePart.zeroEquiv` at every
point. -/
def sectionsZeroInv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (t : sections 𝒜 0 U) :
    (Proj 𝒜).ringCatSheaf.obj.obj U :=
  ⟨fun x ↦ degreePart.zeroEquiv.symm (t.1 x), by
    intro x
    obtain ⟨V, hxV, e, i, j, hij, ⟨a, ha⟩, ⟨b, hb⟩, hw, w⟩ := t.2 x
    obtain rfl : i = j := by omega
    refine ⟨V, hxV, e, i, ⟨a, ha⟩, ⟨b, hb⟩, hw, fun y ↦ ?_⟩
    refine (LinearEquiv.symm_apply_eq _).mpr ((w y).trans ?_)
    ext
    simp [val_mk]⟩

/-- `sectionsZeroInv` is a right inverse of `HomogeneousLocalization.degreePart.zeroEquiv`
at every point. -/
@[simp]
theorem zeroEquiv_sectionsZeroInv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (t : sections 𝒜 0 U) (x : U.unop) :
    degreePart.zeroEquiv ((sectionsZeroInv t).1 x) = t.1 x :=
  LinearEquiv.apply_symm_apply _ _

end Zero

section Mul

variable {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)

include hf

/-- Multiplication by a homogeneous element `f` of degree `d`, as a morphism of presheaves of
abelian groups from `𝒪(m)` to `𝒪(m + d)`. -/
def mulPresheafHom : presheafInAb 𝒜 m ⟶ presheafInAb 𝒜 (m + d) where
  app U := AddCommGrpCat.ofHom
    { toFun s := ⟨_, isLocallyFraction_mul rfl s.2
        (isLocallyFraction_mk (by simp) ⟨f, hf⟩ ⟨1, SetLike.one_mem_graded 𝒜⟩
          fun x ↦ (Ideal.ne_top_iff_one _).mp x.1.isPrime.ne_top)⟩
      map_zero' := Subtype.ext (funext fun _ ↦ Subtype.ext (zero_mul _))
      map_add' _ _ := Subtype.ext (funext fun _ ↦ Subtype.ext (add_mul _ _ _)) }
  naturality _ _ _ := rfl

/-- The map `𝒪(m) ⟶ 𝒪(m + d)` multiplies every value by `f`. -/
@[simp]
theorem val_mulPresheafHom_app_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : (presheafInAb 𝒜 m).obj U) (x : U.unop) :
    (((mulPresheafHom m hf).app U s).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * Localization.mk f 1 :=
  rfl

/-- On an open set `U` contained in `D₊(f)`, division by the homogeneous element `f` of
degree `d` maps the sections of `𝒪(m + d)` to those of `𝒪(m)`. -/
def divPresheafHomApp {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (presheafInAb 𝒜 (m + d)).obj U ⟶ (presheafInAb 𝒜 m).obj U :=
  AddCommGrpCat.ofHom
    { toFun s := ⟨_, isLocallyFraction_mul (add_neg_cancel_right m d) s.2
        (isLocallyFraction_mk (by simp) ⟨1, SetLike.one_mem_graded 𝒜⟩ ⟨f, hf⟩
          fun x ↦ hU x.2)⟩
      map_zero' := Subtype.ext (funext fun _ ↦ Subtype.ext (zero_mul _))
      map_add' _ _ := Subtype.ext (funext fun _ ↦ Subtype.ext (add_mul _ _ _)) }

/-- The map `𝒪(m + d) ⟶ 𝒪(m)` on `U ≤ D₊(f)` divides every value by `f`. -/
@[simp]
theorem val_divPresheafHomApp_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (s : (presheafInAb 𝒜 (m + d)).obj U)
    (x : U.unop) :
    ((divPresheafHomApp m hf hU s).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk 1 (⟨f, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
  rfl

/-- On an open set `U` contained in `D₊(f)`, multiplication by `f` is a bijection from the
sections of `𝒪(m)` to those of `𝒪(m + d)`. -/
theorem isIso_mulPresheafHom_app {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) : IsIso ((mulPresheafHom m hf).app U) := by
  have key (x : U.unop) :
      Localization.mk f 1 *
          Localization.mk 1 (⟨f, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) =
        (1 : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) := by
    rw [Localization.mk_mul, one_mul, mul_one]
    exact Localization.mk_self (⟨f, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  have key' (x : U.unop) := (mul_comm _ _).trans (key x)
  refine ⟨divPresheafHomApp m hf hU, ?_, ?_⟩ <;>
  · ext s : 2
    refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
    simp [mul_assoc, key, key']

end Mul

end ProjectiveSpectrum.Twist

namespace Proj

open ProjectiveSpectrum.Twist

/-- **The twisting sheaf `𝒪(m)` on `Proj 𝒜`**, for `m : ℤ`: its sections over `U` are the
dependent functions `x ↦ s x ∈ (A_x)ₘ` which are locally fractions `a / b` of homogeneous
elements with `deg a = deg b + m`. -/
def twist : (Proj 𝒜).Modules :=
  ⟨presheafOfModules 𝒜 m, isSheaf_presheafInAb 𝒜 m⟩

variable {𝒜}

/-- The canonical morphism `𝒪 ⟶ 𝒪(0)` from the structure sheaf of `Proj 𝒜` to its zeroth
twisting sheaf. -/
def unitToTwistZero :
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules) ⟶ twist 𝒜 0 :=
  ⟨PresheafOfModules.homMk unitToPresheafInAbZero fun _ _ _ ↦
    Subtype.ext (funext fun _ ↦ Subtype.ext (val_mul _ _))⟩

/-- The morphism `𝒪 ⟶ 𝒪(0)` sends a section `s` of the structure sheaf to the section
`x ↦ s x` of `𝒪(0)`. -/
@[simp]
theorem val_unitToTwistZero_app_apply (U : (Proj 𝒜).Opens)
    (s : Γ((SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules), U)) (x : U) :
    ((Scheme.Modules.Hom.app unitToTwistZero U) s).1 x = degreePart.zeroEquiv (s.1 x) :=
  rfl

/-- The morphism `𝒪 ⟶ 𝒪(0)` is an isomorphism. -/
instance : IsIso (unitToTwistZero (𝒜 := 𝒜)) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U ↦ by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun s t h ↦ ?_, fun t ↦ ⟨sectionsZeroInv t, ?_⟩⟩
    · refine Subtype.ext (funext fun x ↦ degreePart.zeroEquiv.injective ?_)
      simpa using congr($(h).1 x)
    · exact Subtype.ext (funext fun x ↦ (val_unitToTwistZero_app_apply _ _ _).trans
        (zeroEquiv_sectionsZeroInv t x))

/-- **`𝒪(0)` is the structure sheaf**: the zeroth twisting sheaf of `Proj 𝒜` is isomorphic to
the structure sheaf. -/
def unitIsoTwistZero :
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules) ≅ twist 𝒜 0 :=
  asIso unitToTwistZero

variable {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)

/-- Multiplication by a homogeneous element `f` of degree `d` is a morphism of `𝒪`-modules
`𝒪(m) ⟶ 𝒪(m + d)` on `Proj 𝒜`. -/
def twistMul : twist 𝒜 m ⟶ twist 𝒜 (m + d) :=
  ⟨PresheafOfModules.homMk (mulPresheafHom m hf) fun _ _ _ ↦
    Subtype.ext (funext fun _ ↦ Subtype.ext (mul_assoc _ _ _))⟩

/-- On the basic open set `D₊(f)`, multiplication by `f` is an isomorphism `𝒪(m) ≅ 𝒪(m + d)`. -/
instance isIso_restrict_twistMul :
    IsIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι).map (twistMul m hf)) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun V ↦
    isIso_mulPresheafHom_app m hf ((Proj.basicOpen 𝒜 f).ι_image_le V)

/-- **`𝒪(m)` is locally trivial**: on the basic open set `D₊(f)` of a homogeneous element `f`
of degree `d`, multiplication by `f` is an isomorphism `𝒪(m)|_{D₊(f)} ≅ 𝒪(m + d)|_{D₊(f)}`. -/
def twistRestrictIso :
    (twist 𝒜 m).restrict (Proj.basicOpen 𝒜 f).ι ≅
      (twist 𝒜 (m + d)).restrict (Proj.basicOpen 𝒜 f).ι :=
  asIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι).map (twistMul m hf))

/-- **`𝒪(m)` is trivial on `D₊(f)`** for a homogeneous element `f` of degree `1`: composing
`twistRestrictIso` `|m|` times gives `𝒪(m)|_{D₊(f)} ≅ 𝒪(0)|_{D₊(f)}`, and `𝒪(0) ≅ 𝒪`. -/
lemma nonempty_restrict_twist_iso_unit (hf : f ∈ 𝒜 1) :
    Nonempty ((twist 𝒜 m).restrict (Proj.basicOpen 𝒜 f).ι ≅ SheafOfModules.unit _) := by
  have key (m : ℤ) : Nonempty ((twist 𝒜 m).restrict (Proj.basicOpen 𝒜 f).ι ≅
      (twist 𝒜 0).restrict (Proj.basicOpen 𝒜 f).ι) := by
    induction m using Int.induction_on with
    | zero => exact ⟨Iso.refl _⟩
    | succ k ih => exact ⟨(twistRestrictIso k hf).symm ≪≫ ih.some⟩
    | pred k ih =>
      have e := twistRestrictIso (-(k : ℤ) - 1) hf
      rw [show -(k : ℤ) - 1 + ((1 : ℕ) : ℤ) = -k by omega] at e
      exact ⟨e ≪≫ ih.some⟩
  exact ⟨(key m).some ≪≫ (Scheme.Modules.restrictFunctor _).mapIso unitIsoTwistZero.symm ≪≫
    Scheme.Modules.restrictUnitIso _⟩

variable (𝒜) in
/-- **`𝒪(m)` is invertible** on `Proj 𝒜` when the basic open sets `D₊(f)` of the homogeneous
elements `f` of degree `1` cover `Proj 𝒜`, e.g. when `𝒜` is generated in degree `1`. -/
lemma isInvertible_twist (h : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ Proj.basicOpen 𝒜 f) :
    (twist 𝒜 m).IsInvertible where
  exists_isoUnit x := by
    obtain ⟨f, hf, hx⟩ := h x
    obtain ⟨e⟩ := nonempty_restrict_twist_iso_unit m hf
    exact ⟨_, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback _).symm.app _ ≪≫ e⟩⟩

end Proj

end AlgebraicGeometry
