/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs

/-! The Frobenius square for the geometric open.

Source: latest blueprint, p-dl-a1-exact, Step 8
(blueprint: new-dl-a1-frobenius-square).

Proof: both composites are morphisms into the fibre product
`C₀ ×_{k₀} Spec k`, so it suffices to compare their two projections. The geometric
open is `j₀ × id`, and the model Frobenius is `id × Spec(φ)` for the geometric
Frobenius `φ` of `k` over `k₀` (`galoisMap_projections`). On the first projection both
composites are `pr₁ ≫ j₀`; on the second both are `pr₂ ≫ Spec(φ)`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- There is a commutative square between the model Frobenius maps and the
base-changed geometric open immersion. -/
theorem condensedOpenImage_frobeniusSquare
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (_iota : PadicAlgCl ell →+* ℂ)
    (U₀ C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    [IsDominant j₀.left] :
    Nonempty (CommSq (StrictWeil.modelFrobenius D U₀).hom (dlGeometricOpen D j₀)
        (dlGeometricOpen D j₀) (StrictWeil.modelFrobenius D C₀).hom) := by
  let := Fintype.ofFinite D.k₀
  refine ⟨⟨?_⟩⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, dlGeometricOpen, Over.pullback_map_left, pullback.lift_fst]
    simp only [← Category.assoc, StrictWeil.modelFrobenius]
    rw [(D.galoisMap_projections _ _).1]
    rw [Category.assoc, (D.galoisMap_projections _ _).1]
    simp only [pullback.lift_fst]
  · simp only [Category.assoc, dlGeometricOpen, Over.pullback_map_left, pullback.lift_snd]
    simp only [StrictWeil.modelFrobenius]
    rw [(D.galoisMap_projections _ _).2]
    rw [(D.galoisMap_projections _ _).2]
    rw [← Category.assoc, pullback.lift_snd]

end AlgebraicGeometry.ProEtale.CondensedRing
