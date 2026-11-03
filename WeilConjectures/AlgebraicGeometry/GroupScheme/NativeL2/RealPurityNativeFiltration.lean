/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealPurityNativeComposition

/-! # Mixedness from the actual finite composition filtration

Source: sk-p-real-purity, final paragraph: finitely many pure quotients have a
common upper weight bound (blueprint: lem-rp-native-mixed-of-composition-filtration).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- An actual finite constructible filtration whose successive quotients are simple
subquotients gives mixedness as soon as those subquotients are pure.
Source: sk-p-real-purity, final paragraph
(blueprint: lem-rp-native-mixed-of-composition-filtration).

Proof: choose a purity weight for each of the finitely many successive quotients.
The finite range of this function is bounded above, also when the filtration has
length zero. Use any such bound and the given filtration in the definition of Mixed.
Every sheaf and arrow is retained; only the finite bound is chosen. -/
theorem mixed_of_composition_filtration
    (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ)
    (n : ℕ) (G : Fin (n + 1) → WeilModule D l X₀)
    (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ)
    (hcon : ∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left (G i).carrier)
    (hzero : IsZero (G 0)) (hend : Nonempty (G (Fin.last n) ≅ M))
    (hmono : ∀ i, Mono (φ i))
    (hsimple : ∀ i, IsNonzeroSimpleSubquotient D l X₀ M (cokernel (φ i)))
    (hpure : ∀ Q, IsNonzeroSimpleSubquotient D l X₀ M Q →
      ∃ w : ℝ, Pure D l X₀ Q iota w) :
    ∃ w : ℝ, Mixed D l X₀ M iota w := by
  classical
  choose v hv using fun i : Fin n ↦ hpure _ (hsimple i)
  obtain ⟨w, hw⟩ := (Set.finite_range v).bddAbove
  refine ⟨w, n, G, φ, hcon, hzero, hend, hmono, ?_⟩
  intro i
  exact ⟨v i, hw (Set.mem_range_self i), hv i⟩

/-- Purity of all actual simple subquotients implies mixedness of a lisse native
Weil module. Source: sk-p-real-purity, final paragraph
(blueprint: lem-rp-native-mixed-of-composition-filtration).

Proof: take the actual finite constructible composition filtration. Its quotients are
simple subquotients of the original module, so choose their given purity weights and
bound this finite family above. The same filtration then witnesses mixedness. -/
theorem mixed_of_simple_subquotients_pure
    [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom]
    (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (hpure : ∀ Q, IsNonzeroSimpleSubquotient D l X₀ M Q →
      ∃ w : ℝ, Pure D l X₀ Q iota w) :
    ∃ w : ℝ, Mixed D l X₀ M iota w := by
  obtain ⟨n, G, φ, hcon, h0, hend, hmono, hsimple⟩ :=
    native_exists_composition_filtration D l X₀ M hM
  exact mixed_of_composition_filtration D l X₀ M iota
    n G φ hcon h0 hend hmono hsimple hpure

end WeilConjectures.NativeL2
