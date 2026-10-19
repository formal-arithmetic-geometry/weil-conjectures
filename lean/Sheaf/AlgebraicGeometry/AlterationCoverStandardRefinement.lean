/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.QuasiExcellentFiniteTypeStability

/-!
# Standard refinement of a prime-to-ell alteration cover

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, Theorem 3.2.3,
printed pp. 30--31, Corollary 2.2.4, printed p. 27, and Exposé XIII 3.2.1,
printed p. 199 (blueprint: lem-per-alteration-cover-standard-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.PrimeToEllAlteration

/-- A finite alteration cover has a standard refinement with integral sources and positive
prime-to-ell finite locally free ranks. The existential `base` in `hcover` represents the
identity object of `alt/S`: its underlying object of `Over S` is exactly `Over.mk (𝟙 S)`.
The original maps `q_b` are `(T b).obj.hom`.

Source: ILO Exposé II, Theorem 3.2.3, pp. 30--31, with Corollary 2.2.4, p. 27;
finite form in Exposé XIII 3.2.1, p. 199
(blueprint: lem-per-alteration-cover-standard-refinement).

Proof:
1. Apply `lem-per-alteration-cover-proper-normal-form` to obtain an integral Noetherian
   proper surjective `Y → S` of positive generic degree `d` coprime to `ell` and a finite
   completely decomposed separated étale family over `Y` mapping to the original cover.
2. Apply `lem-per-integral-etale-chart-flatification` to the identity chart of `S` and
   `Y → S`. It gives a normal integral modification `S₀ → S` and an integral finite locally
   free surjection `Y₀ → S₀` of rank `d` mapping to `Y`. Pull back the étale family to `Y₀`.
   Étaleness, separatedness and finite type survive base change by
   `lem-weil-pbc-etale-covering-base-change` and `lem-pod-separated-finite-type-base-change`.
   Complete decomposition survives because a residue-field rational point remains rational
   after tensoring with the residue field of a point of `Y₀`.
3. Apply `lem-per-finite-flat-cd-etale-exchange` to obtain finite locally free surjections
   of positive coprime ranks over a finite completely decomposed étale family on `S₀`.
   `lem-weil-pbc-finite-type-over-noetherian` gives Noetherianity. Partition the étale charts
   into finitely many normal integral clopen components by `lem-fin-etale-normal-components`,
   restrict the finite covers, and discard empty charts.
4. Over each chart's function field, a composition series of the finite generic algebra
   expresses its dimension as a sum of residue-field degrees. Since the total rank is
   coprime to `ell`, some summand has positive degree prime to `ell`. Its reduced closure
   is integral by `lem-weil-pbc-reduced-induced-closed-subscheme`. It is finite over the
   chart by `lem-weil-pbc-closed-immersion-finite` and `lem-weil-pbc-finite-composition`,
   proper by `lem-weil-pbc-finite-proper`, and surjective because its closed image contains
   the generic point. It retains the map to a member of the original cover.
5. `lem-per-quasi-excellent-finite-type-stability` gives quasi-excellence of `S₀`.
   Apply `lem-per-integral-etale-chart-flatification` simultaneously to these integral
   covers of the étale charts. It supplies `S'`, integral `E_i,W_i`, and finite locally
   free surjections of the selected ranks. Compose the modifications using
   `lem-weil-pbc-proper-composition`; intersect their dense isomorphism opens. Base change
   preserves the separated étale family and its residue-field lifts as in step 2. Compose
   the maps to the original members to obtain `h_i` and the displayed equations.
   `lem-sfb-finite-type-composition-base-change` and
   `lem-weil-pbc-finite-type-over-noetherian` give all finite type and Noetherian clauses. -/
theorem alteration_cover_standard_refinement
    (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S]
    (hS : ∀ V : S.affineOpens, IsQuasiExcellent Γ(S, V.1))
    (ell : ℕ) [Fact ell.Prime]
    (hinv : ∀ s : S, IsUnit (ell : S.presheaf.stalk s))
    {B : Type w} [Finite B] (T : B → Alt S)
    (hcover : ∃ (base : Alt S) (_ : base.obj = Over.mk (𝟙 S))
      (q : ∀ b : B, T b ⟶ base), IsCoveringFamily ell T q) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (n : ℕ) (E W : Fin n → Scheme.{u})
      (e : ∀ i, E i ⟶ S') (a : ∀ i, W i ⟶ E i) (r : Fin n → ℕ)
      (b : Fin n → B) (h : ∀ i, W i ⟶ (T (b i)).obj.left),
      IsIntegral S' ∧ IsNoetherian S' ∧ IsProper p ∧
      (∃ U : S.Opens, Dense (U : Set S) ∧ IsIso (p ∣_ U)) ∧
      (LocallyOfFiniteType p ∧ QuasiCompact p) ∧
      (∀ i, IsIntegral (E i) ∧ IsNoetherian (E i) ∧
        IsIntegral (W i) ∧ IsNoetherian (W i)) ∧
      (∀ i, IsSeparated (e i) ∧ Etale (e i) ∧
        LocallyOfFiniteType (e i) ∧ QuasiCompact (e i)) ∧
      (∀ i, (a i).IsFiniteLocallyFreeOfDegree (r i) ∧
        Surjective (a i) ∧ 0 < r i ∧ Nat.Coprime (r i) ell) ∧
      (∀ i, LocallyOfFiniteType (e i ≫ p) ∧ QuasiCompact (e i ≫ p)) ∧
      (∀ i, LocallyOfFiniteType (a i ≫ e i ≫ p) ∧ QuasiCompact (a i ≫ e i ≫ p)) ∧
      (∀ s' : S', ∃ (i : Fin n) (z : E i),
        e i z = s' ∧ IsIso ((e i).residueFieldMap z)) ∧
      (∀ i, h i ≫ (T (b i)).obj.hom = a i ≫ e i ≫ p) := by
  sorry

end AlgebraicGeometry.PrimeToEllAlteration
