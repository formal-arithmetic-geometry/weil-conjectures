/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBound
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.Proper.ProperIndConstructibleUnbounded
import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedWindowIso

/-!
# Proper direct image of unbounded ind-constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-unbounded-window,
statement and three proof paragraphs (blueprint: sk-lem-proper-unbounded-window).
The schemes have the standing setting of sk-def-sfb-dc-setting, inherited through
sk-lem-proper-heart-bound. All filtered diagrams are small in the coefficient universe.
The window assertion records the actual two cohomology arrows of the truncation zigzag.
Their composite, the inverse of the first followed by the second, is the required
isomorphism in the full subcategory IndCons.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma dimensionBound_of_nat_tests (δ : WithBot ℕ∞) (d : ℤ)
    (hδ : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ δ → (n : ℤ) ≤ d) :
    δ ≤ if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥ := by
  by_cases hd : 0 ≤ d
  · rw [ite_eq_left hd]
    by_contra hle
    have hsucc : ((d.toNat + 1 : ℕ) : WithBot ℕ∞) ≤ δ := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ENat.WithBot.add_one_le_iff).2 (lt_of_not_ge hle)
    have := hδ (d.toNat + 1) hsucc
    omega
  · rw [ite_eq_right hd]
    apply le_of_eq
    by_contra hne
    have hzero : (0 : WithBot ℕ∞) ≤ δ := by
      cases δ with
      | bot => exact False.elim (hne rfl)
      | coe a => exact WithBot.coe_le_coe.mpr (by simp)
    have := hδ 0 hzero
    omega

/-- Preservation of Dic, its upper and lower bounds, and the canonical finite window.
Dic is expanded as membership of every cohomology sheaf in the ambient filtered-colimit
closure of constructible sheaves. The two window maps are the images of truncLEι and
truncGEπ, not an arbitrary isomorphism between the endpoint sheaves. The first endpoint
is ind-constructible by the first clause; the last endpoint is included explicitly.
Invertibility of the two arrows puts the middle sheaf in IndCons too, and fullness makes
their inverses and their composite morphisms of IndCons.
Source: blueprint sk-lem-proper-unbounded-window, displayed assertions and final paragraph
(blueprint: sk-lem-proper-unbounded-window). -/
def ProperUnboundedWindowAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (d : ℤ) : Prop :=
  ∀ K : DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) →
    (∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj K))) ∧
    (∀ b : ℤ, K.IsLE b →
      ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj K).IsLE (b + 2 * d + 1)) ∧
    (∀ a : ℤ, K.IsGE a →
      ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj K).IsGE a) ∧
    (∀ q : ℤ,
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
        ((DerivedCategory.homologyFunctor _ q).obj
          ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj
            ((DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)).obj
              ((DerivedCategory.TStructure.t.truncLE q).obj K)))) ∧
      IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.map
          ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
      IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.map
          ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app
            ((DerivedCategory.TStructure.t.truncLE q).obj K)))))

/-- Proper pushforward of unbounded complexes with ind-constructible finite-extension
cohomology preserves that property, has amplitude [0,2d+1], and has the stated finite window.
Source: blueprint main-20261015, sk-lem-proper-unbounded-window, all three paragraphs
(blueprint: sk-lem-proper-unbounded-window).

Proof for stage 3, following the five steps of the DAG:
1. det-ambient-ind-derived-sums(2) and def-kun-truncations keep both canonical
   truncations in Dic. Their cohomology agrees with that of the input in the retained
   range and vanishes outside it. In particular tau_ge(-n) K is bounded below.
2. det-proper-unbounded-window-bounded-below applies the bounded-below spectral sequence,
   with sk-lem-proper-heart-bound, to give IndCons membership and both amplitude bounds.
3. For arbitrary K and each degree q, det-proper-unbounded-window-arbitrary identifies
   H^q(Rp_*K) with H^q(Rp_*tau_ge(-n) K) for sufficiently large n. Step 2 gives
   ind-constructibility of the latter, hence of the former by repleteness. If K is at most
   b, its truncations are too; step 2 and the same identification give the upper bound.
4. If K is at least a, it is already bounded below. Apply step 2 directly for the lower
   bound, with no bounded-above restriction.
5. Set A = tau_le(q) K and B = tau_ge(q-2d-1) A. Step 1 keeps A and B in Dic.
   det-proper-unbounded-window-iso makes the two canonical cohomology arrows alpha and
   beta invertible. Step 3 puts their objects in IndCons. The required isomorphism is
   alpha inverse followed by beta; its inverse is beta inverse followed by alpha.
   Fullness of IndCons makes all these maps morphisms of that subcategory. -/
theorem properUnboundedWindow
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperUnboundedWindowAssertions (Profinite.continuousMapRingObj.{u} E) p d := by
  intro K hK
  have hdim := fun y ↦ dimensionBound_of_nat_tests _ d (hd y)
  have h := proper_indConstructible_unbounded ℓ E k p₀ hp₀ hpℓ X Y p d hdim
  have hK' := h K hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hK'.2.1
  · exact hK'.2.2.2
  · exact hK'.2.2.1
  · intro q
    exact (proper_unbounded_window_iso ℓ E k p₀ hp₀ hpℓ X Y p d hd K hK q).2.2

/-- The same unbounded proper-window theorem for the condensed algebraic closure.
Its sections take values in a finite subextension, as in sk-def-sfb-qlbar-condensed.
Source: blueprint main-20261015, sk-lem-proper-unbounded-window, all three paragraphs
(blueprint: sk-lem-proper-unbounded-window).

Proof for stage 3: det-ambient-ind-derived-sums(2) and def-kun-truncations give stability
of Dic under the two good truncations. Apply det-proper-unbounded-window-bounded-below
first to bounded-below inputs. For arbitrary inputs, in each degree use the eventual
cohomology isomorphism of det-proper-unbounded-window-arbitrary, then the bounded-below
case and closure of IndCons under isomorphism. This also gives the upper bound b+2d+1.
The lower-bound case is already bounded below, so the bounded-below node applies directly.
Finally apply det-proper-unbounded-window-iso to A = tau_le(q) K and its truncation
B = tau_ge(q-2d-1) A. Both cohomology arrows are invertible and all three sheaves are
ind-constructible. Their composite alpha inverse followed by beta is the window
isomorphism, with inverse beta inverse followed by alpha, in the full category IndCons. -/
theorem properUnboundedWindow_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperUnboundedWindowAssertions (Profinite.padicAlgClRingObj.{u} ℓ) p d := by
  intro K hK
  have hdim := fun y ↦ dimensionBound_of_nat_tests _ d (hd y)
  have h := proper_indConstructible_unbounded_padicAlgCl ℓ k p₀ hp₀ hpℓ X Y p d hdim
  have hK' := h K hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hK'.2.1
  · exact hK'.2.2.2
  · exact hK'.2.2.1
  · intro q
    exact (proper_unbounded_window_iso_padicAlgCl ℓ k p₀ hp₀ hpℓ X Y p d hd K hK q).2.2

end AlgebraicGeometry.ProEtale
