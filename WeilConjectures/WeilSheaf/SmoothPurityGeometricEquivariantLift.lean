/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityReductionWeilStep
public import WeilConjectures.WeilSheaf.SmoothPurityEquivariantIsoLift
public import WeilConjectures.WeilSheaf.SmoothPurityReductionHomShift

/-! # Reconstructing the geometric integral Weil orientation

For the actual Tate and exceptional complexes, geometric pullback automatically supplies
the reduction coherence, and Tate-line finiteness supplies the inverse-limit hypotheses.
The remaining input is existence of the finite equivariant orientations for the specified
integral Weil data.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

set_option hygiene false in
local notation "𝐓" => (shiftFunctor _ (2 * d : ℤ)).obj
  (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)
set_option hygiene false in
local notation "𝐖" => (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)

/-- Finite equivariant orientations for the actual reduction comparisons lift to an
integral equivariant orientation. All coherence and finiteness obligations are discharged. -/
theorem exists_geometric_equivariant_integralOrientation_iso (g : X.left ⟶ X.left)
    (φT : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj 𝐓.obj ≅ 𝐓.obj)
    (φW : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj 𝐖.obj ⟶ 𝐖.obj)
    (hne : ∀ n : ℕ, ∃ e : (purityIntegralReduction X.left ℓ E.1 (n + 1)).obj 𝐓.obj ≅
        (purityIntegralReduction X.left ℓ E.1 (n + 1)).obj 𝐖.obj,
      IsWeilEquivariant L((g)^*⟦Profinite.integersModPowRingObj ℓ E.1 (n + 1)⟧)
        (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E.1 (n + 1) g) φT.hom)
        (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E.1 (n + 1) g) φW) e.hom) :
    ∃ e : 𝐓 ≅ 𝐖,
      IsWeilEquivariant L((g)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧) φT.hom φW e.hom.hom := by
  let G := L((g)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
  have hshift (n : ℕ) : Finite ((G.obj 𝐓.obj) ⟦(1 : ℤ)⟧ ⟶
      (Mod.comap (integersModPowReduction X.left ℓ E.1 (n + 1))).mapDerivedCategory.obj
        ((purityIntegralReduction X.left ℓ E.1 (n + 1)).obj 𝐖.obj)) := by
    have := finite_shift_hom_integralOrientation_reduction (ℓ := ℓ) (E := E.1) f d (n + 1)
    exact Finite.of_equiv _
      (((shiftFunctor _ (1 : ℤ)).mapIso φT).homCongr (Iso.refl _)).symm
  exact exists_equivariant_iso_of_finite_reductions ℓ E G
    (fun n ↦ L((g)^*⟦Profinite.integersModPowRingObj ℓ E.1 (n + 1)⟧))
    (fun n ↦ integersModPowReductionUpperStarIso ℓ E.1 (n + 1) g)
    𝐓 𝐖 φT.hom φW
    (fun n ↦ finite_hom_derivedReduction_integralOrientation (ℓ := ℓ) (E := E.1) f d (n + 1))
    hne (fun n s hs ↦ isWeilEquivariant_derivedReductionStep g (n + 1) φT.hom φW s hs)

end AlgebraicGeometry.ProEtale.CondensedRing
