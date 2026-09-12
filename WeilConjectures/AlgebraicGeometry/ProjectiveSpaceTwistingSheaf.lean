/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.TwistingSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The twisting sheaves `𝒪(d)` on the relative projective space `ℙ(n; S)`

The projective `n`-space `ℙ(n; S)` over a base scheme `S` is defined in
`WeilConjectures/AlgebraicGeometry/ProjectiveSpace.lean` as the base change
`S ×_{Spec ℤ} ℙⁿ_ℤ` of the integral model `ℙⁿ_ℤ = Proj ℤ[T]`. Its twisting sheaves are
defined here by pulling back the twisting sheaves of the integral model, constructed in
`WeilConjectures/AlgebraicGeometry/TwistingSheaf.lean`, along the canonical map
`ProjectiveSpace.toProjInt n S : ℙ(n; S) ⟶ ℙⁿ_ℤ`.

This is the cheap and canonical definition: there is as yet no comparison
`ℙ(n; Spec A) ≅ Proj.projectiveSpaceOverAffine n A` (it needs `Proj` to commute with base
change, which Mathlib does not have), so `𝒪(d)` on `ℙ(n; S)` cannot be read off from a `Proj`
presentation of `ℙ(n; S)` itself. Pulling back along `toProjInt` costs nothing and makes base
change compatibility formal: `toProjInt` is compatible with the functoriality
`ProjectiveSpace.map n f` of `ℙ(n; -)` in the base, so `(map n f)^* 𝒪(d) ≅ 𝒪(d)` follows from
the pseudofunctoriality of pullback.

The homogeneous coordinates `T₀, …, T_N ∈ Γ(ℙ(n; S), 𝒪(1))` are likewise obtained from the
homogeneous coordinates on the integral model, by the pullback map on global sections
`AlgebraicGeometry.Scheme.Modules.sectionsPullback`.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.twistingSheaf`: the twisting sheaf `𝒪(d)` on `ℙ(n; S)`,
  for `d : ℤ`.
- `AlgebraicGeometry.ProjectiveSpace.homogeneousSection`: the global section of `𝒪(j)` on
  `ℙ(n; S)` attached to a homogeneous polynomial of degree `j` in `ℤ[T]`.
- `AlgebraicGeometry.ProjectiveSpace.homogeneousCoord`: the homogeneous coordinates
  `T₀, …, T_N ∈ Γ(ℙ(n; S), 𝒪(1))`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.pullbackTwistingSheafIso`: **compatibility with base
  change**, `(map n f)^* 𝒪(d) ≅ 𝒪(d)` for a morphism `f : S ⟶ T` of base schemes.
- `AlgebraicGeometry.ProjectiveSpace.sectionsPullback_homogeneousSection`: the global sections
  attached to homogeneous polynomials are compatible with base change.

## Implementation notes

Two general lemmas about `AlgebraicGeometry.Scheme.Modules.sectionsPullback`, the pullback of
global sections — its compatibility with `pullbackComp` and with `pullbackCongr` — are proved
here rather than in `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`, where they
belong, because that file is being extended concurrently; they should be moved there.

## TODO

- `𝒪(d)` is an invertible sheaf on `ℙ(n; S)`. Since the pullback of sheaves of modules is
  monoidal (`AlgebraicGeometry.Scheme.Modules.pullback f` is `Functor.Monoidal`), hence
  preserves invertible objects by `SheafOfModules.Invertible.pullback`, this is immediate from
  the invertibility of `Proj.twistingSheaf`, which is not yet available.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

/-! ### Global sections and the pseudofunctoriality of the pullback

The two lemmas in this section say that `Scheme.Modules.sectionsPullback`, the pullback of
global sections, is compatible with the identifications `a^* b^* M ≅ (a ≫ b)^* M` and
`c^* M ≅ d^* M` for `c = d`. They are general facts about sheaves of modules on schemes and
belong next to `Scheme.Modules.sectionsPullback` itself, in
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`.
-/

variable {X Y Z : Scheme.{u}}

/-- The restriction map `Γ(M, c ⁻¹ᵁ ⊤) ⟶ Γ(M, ⊤)` of a sheaf of modules is the identity. -/
lemma presheaf_map_homOfLE_preimage_top (c : X ⟶ Y) (M : X.Modules) :
    M.presheaf.map (homOfLE (by simp : (⊤ : X.Opens) ≤ c ⁻¹ᵁ ⊤)).op = 𝟙 Γ(M, ⊤) :=
  (congrArg (fun i : (op (c ⁻¹ᵁ ⊤) : X.Opensᵒᵖ) ⟶ op ⊤ ↦ M.presheaf.map i)
    (Subsingleton.elim _ (𝟙 (op (⊤ : X.Opens))))).trans (M.presheaf.map_id _)

/-- Pulling back a global section in two steps along `a` and `b` agrees, under the
identification `a^* b^* M ≅ (a ≫ b)^* M`, with pulling it back in one step along `a ≫ b`. -/
lemma pullbackComp_hom_sectionsPullback (a : X ⟶ Y) (b : Y ⟶ Z) (M : Z.Modules) (s : Γ(M, ⊤)) :
    Hom.app ((pullbackComp a b).hom.app M) ⊤
        (sectionsPullback a ((pullback b).obj M) (sectionsPullback b M s)) =
      sectionsPullback (a ≫ b) M s := by
  have key := congrArg (fun ψ ↦ Hom.app ψ ⊤ s) (unit_pushforwardPullbackComp a b M)
  simp only [Hom.comp_app, pushforwardPullbackComp_app] at key
  simp only [sectionsPullback, ConcreteCategory.comp_apply, presheaf_map_homOfLE_preimage_top]
  exact key

/-- Pulling back a global section along equal morphisms gives the same section, under the
identification `c^* M ≅ d^* M`. -/
lemma pullbackCongr_hom_sectionsPullback {c d : X ⟶ Y} (h : c = d) (M : Y.Modules)
    (s : Γ(M, ⊤)) :
    Hom.app ((pullbackCongr h).hom.app M) ⊤ (sectionsPullback c M s) = sectionsPullback d M s := by
  subst h
  rfl

end Scheme.Modules

namespace ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u)

/-- The graded ring `ℤ[T]` of the integral model `ℙⁿ_ℤ` of `ℙ(n; S)`, with its total-degree
grading. -/
abbrev gradingInt : ℕ → Submodule (ULift.{u} ℤ) (MvPolynomial n (ULift.{u} ℤ)) :=
  MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)

/-- The twisting sheaf `𝒪(d)` of the integral model `ℙⁿ_ℤ` of `ℙ(n; S)`. This is
`Proj.twistingSheaf`, with its type spelled in terms of `Proj.projectiveSpaceOverAffine`. -/
def twistingSheafInt (d : ℤ) : (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)).Modules :=
  Proj.twistingSheaf (gradingInt n) d

variable (S : Scheme.{u})

/-- **The twisting sheaf `𝒪(d)` on `ℙ(n; S)`**, defined as the pullback along
`toProjInt n S : ℙ(n; S) ⟶ ℙⁿ_ℤ` of the twisting sheaf `𝒪(d)` of the integral model. -/
def twistingSheaf (d : ℤ) : ℙ(n; S).Modules :=
  (Scheme.Modules.pullback (toProjInt n S)).obj (twistingSheafInt n d)

variable {n}

/-- A homogeneous polynomial `a` of degree `j` in `ℤ[T]` defines a global section of `𝒪(j)` on
`ℙ(n; S)`, the pullback of the corresponding global section of `𝒪(j)` on the integral model
`ℙⁿ_ℤ`. -/
def homogeneousSection {j : ℕ} {a : MvPolynomial n (ULift.{u} ℤ)} (ha : a ∈ gradingInt n j)
    (S : Scheme.{u}) : Γ(twistingSheaf n S j, ⊤) :=
  Scheme.Modules.sectionsPullback (toProjInt n S) (twistingSheafInt n j)
    (Proj.homogeneousSection ha)

/-- **The homogeneous coordinates** `T₀, …, T_N ∈ Γ(ℙ(n; S), 𝒪(1))`, the global sections of
`𝒪(1)` attached to the variables of `ℤ[T]`. -/
def homogeneousCoord (i : n) (S : Scheme.{u}) : Γ(twistingSheaf n S 1, ⊤) :=
  homogeneousSection ((MvPolynomial.mem_homogeneousSubmodule _ _).2
    (MvPolynomial.isHomogeneous_X _ i)) S

variable (n) in
/-- **The twisting sheaves are compatible with base change**: for a morphism `f : S ⟶ T` of
base schemes, the pullback of `𝒪(d)` on `ℙ(n; T)` along `map n f : ℙ(n; S) ⟶ ℙ(n; T)` is
`𝒪(d)` on `ℙ(n; S)`. This holds because both are pullbacks of the twisting sheaf of the
integral model, along the two sides of the commuting triangle
`map n f ≫ toProjInt n T = toProjInt n S`. -/
def pullbackTwistingSheafIso {S T : Scheme.{u}} (f : S ⟶ T) (d : ℤ) :
    (Scheme.Modules.pullback (map n f)).obj (twistingSheaf n T d) ≅ twistingSheaf n S d :=
  (Scheme.Modules.pullbackComp (map n f) (toProjInt n T)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (map_toProjInt n f)).app _

/-- **The homogeneous sections are compatible with base change**: the global section of
`𝒪(j)` on `ℙ(n; S)` attached to a homogeneous polynomial `a` is the pullback along
`map n f` of the corresponding section on `ℙ(n; T)`. -/
lemma sectionsPullback_homogeneousSection {j : ℕ} {a : MvPolynomial n (ULift.{u} ℤ)}
    (ha : a ∈ gradingInt n j) {S T : Scheme.{u}} (f : S ⟶ T) :
    Scheme.Modules.Hom.app (pullbackTwistingSheafIso n f j).hom ⊤
        (Scheme.Modules.sectionsPullback (map n f) (twistingSheaf n T j)
          (homogeneousSection ha T)) =
      homogeneousSection ha S := by
  simp only [pullbackTwistingSheafIso, homogeneousSection, twistingSheaf, Iso.trans_hom,
    Iso.app_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  refine Eq.trans (congrArg (fun x ↦ Scheme.Modules.Hom.app
    ((Scheme.Modules.pullbackCongr (map_toProjInt n f)).hom.app (twistingSheafInt n j)) ⊤ x)
      (Scheme.Modules.pullbackComp_hom_sectionsPullback (map n f) (toProjInt n T)
        (twistingSheafInt n j) (Proj.homogeneousSection ha))) ?_
  exact Scheme.Modules.pullbackCongr_hom_sectionsPullback (map_toProjInt n f)
    (twistingSheafInt n j) (Proj.homogeneousSection ha)

end ProjectiveSpace

end AlgebraicGeometry
