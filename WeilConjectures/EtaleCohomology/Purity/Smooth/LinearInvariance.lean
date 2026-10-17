/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence

/-!
# Linear changes of coordinates preserve the class of the zero section of affine space

For a matrix `g ∈ GL_d(Γ(S, 𝒪_S))`, the linear automorphism `φ_g : 𝔸^d_S ⟶ 𝔸^d_S`,
`t ↦ g t` (`AlgebraicGeometry.AffineSpace.linearMap`), preserves the zero section, and it
preserves the class `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_d) ∈ H^{2d}_{0}(𝔸^d_S, Λ(d))` of the zero section, the
class whose adjoint is the purity isomorphism of affine space and whose transpose under
`Rp_! ⊣ Rp^!` is the integration of `𝔸^d_S` (`lem-amb-linear-trace-invariance`). In
particular the class is symmetric under permutations of the coordinates, and it commutes with
base change (`prop-pur-affine-space-purity-compatibilities`).

## Main definitions

- `AlgebraicGeometry.AffineSpace.linearMap`: the linear endomorphism `t ↦ g t` of `𝔸^d_S`.

## Main statements

- `AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_linearMap`
- `AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_permutation`
- `AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_baseChange`
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace AffineSpace

variable {S : Scheme.{u}} {d : ℕ}

/-- The coordinates `t₁, …, t_d` of `𝔸^d_S`. -/
noncomputable abbrev coordFin (S : Scheme.{u}) (d : ℕ) : Fin d → Γ(𝔸(ULift.{u} (Fin d); S), ⊤) :=
  fun a ↦ coord S (ULift.up a)

/-- The linear endomorphism `t ↦ g t` of `𝔸^d_S` given by a matrix `g` of functions on `S`: the
`a`-th coordinate of the image of `t` is `∑_b g_{ab} t_b`. -/
noncomputable def linearMap (g : Matrix (Fin d) (Fin d) Γ(S, ⊤)) :
    𝔸(ULift.{u} (Fin d); S) ⟶ 𝔸(ULift.{u} (Fin d); S) :=
  homOfVector (𝔸(ULift.{u} (Fin d); S) ↘ S) fun a ↦
    (g.map (𝔸(ULift.{u} (Fin d); S) ↘ S).appTop.hom).mulVec (coordFin S d) a.down

@[reassoc (attr := simp)]
lemma linearMap_over (g : Matrix (Fin d) (Fin d) Γ(S, ⊤)) :
    linearMap g ≫ 𝔸(ULift.{u} (Fin d); S) ↘ S = 𝔸(ULift.{u} (Fin d); S) ↘ S :=
  homOfVector_over _ _

lemma linearMap_appTop_coordFin (g : Matrix (Fin d) (Fin d) Γ(S, ⊤)) (a : Fin d) :
    (linearMap g).appTop (coordFin S d a) =
      (g.map (𝔸(ULift.{u} (Fin d); S) ↘ S).appTop.hom).mulVec (coordFin S d) a :=
  homOfVector_appTop_coord _ _ _

end AffineSpace

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] {S : Scheme.{u}}
  [HasInvertibleExponent Λ S] {d : ℕ}

local instance (S : Scheme.{u}) [HasInvertibleExponent Λ S] (n : Type u) :
    HasInvertibleExponent Λ 𝔸(n; S) :=
  .of_hom (𝔸(n; S) ↘ S)

/-- Blueprint `lem-amb-linear-trace-invariance`: Linear changes of coordinates preserve
integration

For `g ∈ GL_d(Γ(S, 𝒪_S))`, the linear automorphism `φ_g : t ↦ g t` of `𝔸^d_S` preserves the
class `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_d) ∈ H^{2d}_0(𝔸^d_S, Λ(d))` of the zero section: the restriction of
supports along `φ_g`, which maps the zero section to itself, carries the class to itself. The
coordinates pull back to `g t`, and the class of the frame `g t` is that of `t`
(`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec`, which is the
blueprint's argument through the universal matrix over `GL_{d,S}`, whose geometric fibres are
connected).

The class is the one whose adjoint is the affine-space purity isomorphism and whose transpose is
the affine-space integration `t_{p_d}`; the integration map itself is not constructed in this
repository (see `AlgebraicGeometry.VectorBundle.integration`), so the invariance is stated for the
class. -/
theorem restrictSupportedClass_kummerBoundaryProduct_linearMap
    (g : Matrix (Fin d) (Fin d) Γ(S, ⊤)) (hg : IsUnit g.det)
    (g' : 𝔸(ULift.{u} (Fin d); S).zeroLocusSubscheme (Set.range (AffineSpace.coordFin S d)) ⟶
      𝔸(ULift.{u} (Fin d); S).zeroLocusSubscheme (Set.range (AffineSpace.coordFin S d)))
    (hg' : IsPullback g' (𝔸(ULift.{u} (Fin d); S).zeroLocusSubschemeι
      (Set.range (AffineSpace.coordFin S d)))
      (𝔸(ULift.{u} (Fin d); S).zeroLocusSubschemeι (Set.range (AffineSpace.coordFin S d)))
      (AffineSpace.linearMap g)) :
    restrictSupportedClass (ModuleCat.{u + 1} Λ) (AffineSpace.linearMap g) _ _ g' hg'
        (leftDerivedUpperStarConstantComplexIso Λ _).inv
        (leftDerivedUpperStarTateShiftIso Λ _ d)
        (kummerBoundaryProduct Λ (AffineSpace.coordFin S d)) =
      kummerBoundaryProduct Λ (AffineSpace.coordFin S d) := by
  set t := AffineSpace.coordFin S d
  set M := g.map (𝔸(ULift.{u} (Fin d); S) ↘ S).appTop.hom
  have hM : IsUnit M.det := by
    rw [← RingHom.map_det]
    exact hg.map _
  obtain ⟨gφ, hgφ⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι (AffineSpace.linearMap g) (Set.range t)
      (Set.range (M.mulVec t)) (by
        rw [← Set.range_comp]
        exact congrArg Set.range (funext (AffineSpace.linearMap_appTop_coordFin g)))⟩
  obtain ⟨g₀, hg₀⟩ := Scheme.exists_isPullback_zeroLocusSubschemeι_of_span_eq
    (U := 𝔸(ULift.{u} (Fin d); S)) (s := Set.range (M.mulVec t)) (s' := Set.range t)
    (Ideal.span_range_mulVec_of_isUnit_det _ hM)
  rw [restrictSupportedClass_comp_tateShift Λ (𝟙 _) (AffineSpace.linearMap g) _
      (Category.id_comp _).symm _ _ _ gφ hgφ g₀ hg₀ g' hg',
    restrictSupportedClass_kummerBoundaryProduct Λ (AffineSpace.linearMap g) t (M.mulVec t)
      (AffineSpace.linearMap_appTop_coordFin g) gφ hgφ]
  exact restrictSupportedClass_kummerBoundaryProduct_mulVec Λ t M hM g₀ hg₀

/-- Blueprint `prop-pur-affine-space-purity-compatibilities`: Symmetry and compatibilities of
affine-space purity

*Symmetry.* The class `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_d)` of the zero section of `𝔸^d_S`, which generates the
affine-space purity comparison `γ_{p_d}`, is symmetric under permutations `σ` of the coordinates:
the restriction of supports along the permutation of coordinates `t ↦ (t_{σ a})_a` carries it to
itself. This is the case of a permutation matrix of
`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_linearMap`; the Koszul sign
is `+1`, all classes being of even degree. -/
theorem restrictSupportedClass_kummerBoundaryProduct_permutation (σ : Equiv.Perm (Fin d))
    (g' : 𝔸(ULift.{u} (Fin d); S).zeroLocusSubscheme (Set.range (AffineSpace.coordFin S d)) ⟶
      𝔸(ULift.{u} (Fin d); S).zeroLocusSubscheme (Set.range (AffineSpace.coordFin S d)))
    (hg' : IsPullback g' (𝔸(ULift.{u} (Fin d); S).zeroLocusSubschemeι
      (Set.range (AffineSpace.coordFin S d)))
      (𝔸(ULift.{u} (Fin d); S).zeroLocusSubschemeι (Set.range (AffineSpace.coordFin S d)))
      (AffineSpace.linearMap (σ.permMatrix Γ(S, ⊤)))) :
    restrictSupportedClass (ModuleCat.{u + 1} Λ) (AffineSpace.linearMap (σ.permMatrix Γ(S, ⊤)))
        _ _ g' hg' (leftDerivedUpperStarConstantComplexIso Λ _).inv
        (leftDerivedUpperStarTateShiftIso Λ _ d)
        (kummerBoundaryProduct Λ (AffineSpace.coordFin S d)) =
      kummerBoundaryProduct Λ (AffineSpace.coordFin S d) :=
  restrictSupportedClass_kummerBoundaryProduct_linearMap Λ _
    (by rw [Matrix.det_permutation]; exact (Units.isUnit _).map (Int.castRingHom _)) g' hg'

/-- Blueprint `prop-pur-affine-space-purity-compatibilities`: Symmetry and compatibilities of
affine-space purity

*Base change.* For `f : S' ⟶ S`, the restriction of supports along the base change
`𝔸^d_{S'} ⟶ 𝔸^d_S` carries the class of the zero section of `𝔸^d_S` to that of `𝔸^d_{S'}`: the
coordinates pull back to the coordinates. -/
theorem restrictSupportedClass_kummerBoundaryProduct_baseChange {S' : Scheme.{u}}
    [HasInvertibleExponent Λ S'] (f : S' ⟶ S)
    (g' : 𝔸(ULift.{u} (Fin d); S').zeroLocusSubscheme (Set.range (AffineSpace.coordFin S' d)) ⟶
      𝔸(ULift.{u} (Fin d); S).zeroLocusSubscheme (Set.range (AffineSpace.coordFin S d)))
    (hg' : IsPullback g' (𝔸(ULift.{u} (Fin d); S').zeroLocusSubschemeι
      (Set.range (AffineSpace.coordFin S' d)))
      (𝔸(ULift.{u} (Fin d); S).zeroLocusSubschemeι (Set.range (AffineSpace.coordFin S d)))
      (AffineSpace.map (ULift.{u} (Fin d)) f)) :
    restrictSupportedClass (ModuleCat.{u + 1} Λ) (AffineSpace.map (ULift.{u} (Fin d)) f) _ _ g' hg'
        (leftDerivedUpperStarConstantComplexIso Λ _).inv
        (leftDerivedUpperStarTateShiftIso Λ _ d)
        (kummerBoundaryProduct Λ (AffineSpace.coordFin S d)) =
      kummerBoundaryProduct Λ (AffineSpace.coordFin S' d) :=
  restrictSupportedClass_kummerBoundaryProduct Λ _ _ _
    (fun a ↦ AffineSpace.map_appTop_coord (n := ULift.{u} (Fin d)) f (ULift.up a)) g' hg'

end Etale

end AlgebraicGeometry
