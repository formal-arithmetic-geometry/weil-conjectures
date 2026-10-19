/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import Sheaf.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import Sheaf.AlgebraicGeometry.QuasiFiniteAtPointIsolated

/-!
# Affine criterion and Zariski locality for local quasi-finiteness

Source: Stacks Project, Morphisms of Schemes, Tag 01TK, conditions (1), (2), (3)
(blueprint: lem-a1-scheme-lqf-affine-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The Stacks local quasi-finiteness predicate is equivalent both to finite type and
quasi-finiteness at every prime on every affine pair, and to local quasi-finiteness on
an open covering of the target and open coverings of its inverse images.
Source: Stacks Project, Morphisms of Schemes, Tag 01TK, conditions (1), (2), (3)
(blueprint: lem-a1-scheme-lqf-affine-criterion).

Proof:
1. Assume local quasi-finiteness. By `lem-weil-pbc-lqf-locally-finite-type` and
   `lem-weil-pbc-lft-affine-pairs`, every affine-pair section map is of finite type.
   For each prime of the source coordinate ring, take its corresponding point.
   `pqf-def-quasifinite` and `lem-weil-pbc-quasi-finite-at-point-isolated` show that its
   fibre point is isolated. Apply
   `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs` to the given affine pair
   to obtain quasi-finiteness at that prime. This proves (1) implies (2).
2. Given (2), choose an affine target neighbourhood of the image of each source point
   and an affine source neighbourhood inside its inverse image, using
   `lem-weil-pbc-affine-opens-basis`. Apply (2) at the prime corresponding to the point.
   These witnesses give `IsQuasiFiniteAtPoint` by `pqf-def-quasifinite`; hence (1).
3. Given (1), choose an affine open cover of the target and affine open covers of its
   inverse images using `lem-weil-pbc-affine-opens-basis`. Every restriction is locally
   quasi-finite by `lem-weil-pbc-lqf-restriction-to-opens`, proving (3).
4. Given (3), any source point lies in a covering piece over a target covering open.
   Unpack local quasi-finiteness of that restriction using `pqf-def-quasifinite`.
   Its affine neighbourhood witnesses are also open subschemes of the original source
   and target and give quasi-finiteness of the original map at the point, proving (1).

No finiteness, separation, or Noetherian hypotheses are imposed. The finite-type
witness is passed explicitly to the ring predicate, using the algebra of `appLE`.
The covering indices may be empty; containment witnesses specify the canonical `resLE`.
-/
theorem isLocallyQuasiFinite_affine_criterion {X S : Scheme.{u}} (f : X ⟶ S) :
    (f.IsLocallyQuasiFinite ↔
      ∀ (A : X.Opens) (B : S.Opens), IsAffineOpen A → IsAffineOpen B →
        ∀ e : A ≤ f ⁻¹ᵁ B,
          ∃ hft : (f.appLE B A e).hom.FiniteType,
            ∀ q : PrimeSpectrum Γ(X, A),
              @Algebra.IsQuasiFiniteAtPrime Γ(S, B) Γ(X, A) _ _
                (f.appLE B A e).hom.toAlgebra hft q) ∧
    (f.IsLocallyQuasiFinite ↔
      ∃ (J : Type u) (B : J → S.Opens) (I : J → Type u)
        (A : ∀ j : J, I j → X.Opens) (e : ∀ (j : J) (i : I j), A j i ≤ f ⁻¹ᵁ B j),
        (⨆ j : J, B j) = ⊤ ∧
        (∀ j : J, (⨆ i : I j, A j i) = f ⁻¹ᵁ B j) ∧
        ∀ (j : J) (i : I j), (f.resLE (B j) (A j i) (e j i)).IsLocallyQuasiFinite) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
