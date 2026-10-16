/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups A4, C4 and B3
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Sheaf.CategoryTheory.HomColimitExtension
public import Mathlib.CategoryTheory.Category.ULift
import Sheaf.CategoryTheory.HomColimitTruncation
import Sheaf.Paper.CondensedLocallyClosedExtensionTower
import all Sheaf.Paper.CondensedLocalPieceHomContinuity
import Sheaf.Paper.IntegralLfpHomContinuity

/-! # Sequential Hom continuity for a constructible integral sheaf -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

/-- Shifted Hom from a constructible integral sheaf commutes with uniformly bounded-below
sequential colimits. The lifted indexing category is equivalent to the ordinary natural numbers.
Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3),
Lemma 6.8.12 and the proof of Lemma 6.3.14.
(blueprint: lem-weil-pbc-integral-constructible-sheaf-hom)

Proof. Apply the good-truncation comparison theorem at the common cohomological
lower bound. Exact filtered colimits preserve the truncation quasi-isomorphisms,
so it suffices to use canonical cocones of termwise bounded-below diagrams.
Resolve a locally finitely presented integral module by two locally finite free
modules. Their Hom continuity and the rotated short exact single-sheaf triangle
prove continuity for the resolved module in every integer shift. Integral torsion
is retained in this resolution. For a locally closed piece, use the coefficient-
generic costalk-model theorem: it identifies the Hom diagram and cocone with a
strictly bounded-below model on the stratum, compatibly with every leg. Invertible
stage and vertex comparisons then identify the canonical colimit.desc maps.
Finally, finite stratification and noetherian open/closed induction express a
constructible sheaf as a finite distinguished extension of these pieces. Induct
on that tower using distinguished extension closure of homColimitProperty. The
good-truncation comparison returns the result for the supplied cocone c. Empty
schemes and zero ranks are covered by the same categorical argument. -/
theorem integralConstructible_sheaf_hom_colimit (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))
    (hM : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) M)
    (D : AsSmall.{u + 1} ℕ ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) ℤ)
    (c : Cocone D) (hc : Nonempty (IsColimit c))
    (hD : ∃ a : ℤ, ∀ n, (DerivedCategory.Q.obj (D.obj n)).IsGE a) :
    homColimitProperty (D ⋙ DerivedCategory.Q) (DerivedCategory.Q.mapCocone c)
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨hc⟩ := hc
  apply homColimitProperty_of_strictly_bounded _ _ D c hc hD
  intro N hN
  obtain ⟨r, hr⟩ := exists_condensedLocallyClosed_extension_tower X (integralCoeff ℓ E) M hM
  let D' := N ⋙ DerivedCategory.Q
  let c' := DerivedCategory.Q.mapCocone (colimit.cocone N)
  have hP : condensedLocallyClosedPiece (integralCoeff ℓ E) X ≤ homColimitProperty D' c' :=
    locally_closed_generators_continuity X (integralCoeff ℓ E) N hN
      (fun U _ P hP L hL n ↦ integral_lfp_hom_continuity U ℓ E P hP L hL n)
  have h : ∀ r : ℕ, (condensedLocallyClosedPiece (integralCoeff ℓ E) X).extensionProductIter r ≤
      homColimitProperty D' c' := by
    intro r
    induction r with
    | zero => exact hP
    | succ r ih =>
      rw [ObjectProperty.extensionProductIter_succ]
      rintro K ⟨A, B, f, g, k, hdist, hA, hB⟩
      exact homColimitProperty_extensions D' c' _ hdist (hP _ hA) (ih _ hB)
  exact h r _ hr

end AlgebraicGeometry.ProEtale.CondensedRing
