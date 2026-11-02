/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleQuotientEpi
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Mathlib.RingTheory.OrzechProperty
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank

/-! # The normalized tautological quotient in rank one

Source: Stacks Project, Tag 01OB, and Tag 0FI5, invertible case.
(blueprint: lem-pur-projective-line-quotient-isomorphism).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

private theorem toSkyscraper_zero {X : Scheme.{u}} (x : X) (M : X.Modules)
    (I : Type u) [AddCommGroup I] [Module (X.presheaf.stalk x) I] :
    toSkyscraper (0 : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] I) = 0 := by
  apply hom_ext
  intro U
  ext s
  apply SkyscraperSections.ext
  intro hx
  rfl

private theorem stalk_surjective {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) [Epi φ] (x : X) : Function.Surjective (φ.stalkLinearMap x) := by
  let q := (LinearMap.range (φ.stalkLinearMap x)).mkQ
  have hz : φ ≫ toSkyscraper q = 0 := by
    rw [comp_toSkyscraper, LinearMap.range_mkQ_comp]
    exact toSkyscraper_zero x M _
  have hz' : toSkyscraper q = 0 := (cancel_epi φ).mp (hz.trans (by simp))
  have hq : q = 0 := (skyscraperHomEquiv x _ N).injective
    (hz'.trans (toSkyscraper_zero x N _).symm)
  rw [← LinearMap.range_eq_top]
  rw [← Submodule.ker_mkQ (LinearMap.range (φ.stalkLinearMap x))]
  change LinearMap.ker q = ⊤
  rw [hq, LinearMap.ker_zero]

private theorem stalk_basis {X : Scheme.{u}} (M : X.Modules) (r : ℕ)
    [M.IsFiniteLocallyFreeOfRank r] (x : X) :
    Nonempty (Module.Basis (ULift.{u} (Fin r)) (X.presheaf.stalk x) (M.presheaf.stalk x)) := by
  obtain ⟨I, U, hU, he⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.mp
      (inferInstance : M.IsFiniteLocallyFreeOfRank r)
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ _).mp hU).exists_mem x
  exact ⟨(exists_basis_stalk_of_over_iso_free (he i).some hi).choose⟩

private theorem same_rank_epi_iso {X : Scheme.{u}} {M N : X.Modules} (r : ℕ)
    [M.IsFiniteLocallyFreeOfRank r] [N.IsFiniteLocallyFreeOfRank r]
    (φ : M ⟶ N) [Epi φ] : IsIso φ := by
  apply isIso_of_bijective_stalkLinearMap
  intro x
  let bM := (stalk_basis M r x).some
  let bN := (stalk_basis N r x).some
  let e := bM.equiv bN (Equiv.refl _)
  have := Module.Finite.of_basis bN
  exact OrzechProperty.bijective_of_surjective_of_injective e.toLinearMap
    (φ.stalkLinearMap x) e.injective (stalk_surjective φ x)

/-- The tautological quotient of any normalized realization of a rank-one bundle is an iso.

Source: Stacks Project, Tags 01OB, 0FI5.
(blueprint: lem-pur-projective-line-quotient-isomorphism).

Proof: the normalized generators make the quotient epic. Its source and target
are locally free of rank one. An epimorphism of sheaves of modules is surjective
on stalks: if the quotient of a target stalk by the image were nonzero, its quotient
map would give, by the stalk-skyscraper adjunction, a nonzero map annihilating the
epimorphism. On each stalk the source and target have finite bases of the same
size. Conjugate by their basis equivalence and use the Hopfian property of finite
modules over a commutative ring to get bijectivity. Stalks detect isomorphisms.
This needs neither a frame chosen for D nor a nonempty-base hypothesis. -/
theorem projectiveLineQuotient_isIso {S : Scheme.{u}} {F : S.Modules}
    [F.IsFiniteLocallyFreeOfRank 1] (D : ProjectiveBundleRealization S F)
    (hD : D.L.IsInvertible) : IsIso D.quotient := by
  have hF : ((tensorPullback D.A.data.relProjHom).obj F).IsFiniteLocallyFreeOfRank 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      ((projectiveBundleTensorPullbackIso _).app F).symm
  let := hD
  have := IsInvertible.sheafOfModules_isInvertible D.L
  have hL : D.L.IsFiniteLocallyFreeOfRank 1 :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one D.L).mp this
  have := projectiveBundleQuotient_epi D
  exact same_rank_epi_iso 1 D.quotient

end AlgebraicGeometry.Scheme.Modules
