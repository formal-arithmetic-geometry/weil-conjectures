/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful

/-! The open-immersion counit step for the condensed open-image argument: the actual
derived counit `j^* Rj_* K → K` is invertible.

Source: latest blueprint, p-dl-a1-exact, Steps 5--6; Stacks Project, Tag 09BN
(blueprint: new-dl-a1-underived-counit).

Proof: base change preserves the given open immersion, so the geometric open is an
open immersion. The published open-localization instance then makes the derived
upper-star/lower-star counit invertible on every bounded constructible object.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem geometricOpen_eq_pullback_map
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {U₀ C₀ : Over (Spec (.of D.k₀))} (j₀ : U₀ ⟶ C₀) :
    dlGeometricOpen D j₀ =
      pullback.map U₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) C₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀.left
        (𝟙 _) (𝟙 _) (by simp) (by simp) := by
  apply pullback.hom_ext <;> simp [dlGeometricOpen, Over.pullback_map_left]

set_option linter.style.haveILetI false in
/-- The derived upper-star/lower-star counit is invertible on every bounded
constructible object for the geometric open immersion. -/
theorem condensedOpenImage_underivedCounit
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (_iota : PadicAlgCl ell →+* ℂ)
    (U₀ C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    [IsDominant j₀.left] :
    ∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ell)
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left,
      IsIso ((derivedUpperStarLowerStarAdjunction
        (Profinite.padicAlgClRingObj ell) (dlGeometricOpen D j₀)).counit.app K.obj) := by
  letI : IsOpenImmersion (dlGeometricOpen D j₀) := by
    rw [geometricOpen_eq_pullback_map]
    infer_instance
  intro K
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
