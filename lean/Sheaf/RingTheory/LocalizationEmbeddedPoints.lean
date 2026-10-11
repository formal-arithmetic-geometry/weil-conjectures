/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.Localization.Module
public import Sheaf.RingTheory.RemoveEmbeddedPrimes

/-!
# Localization and removal of embedded associated points

Source: Stacks Project, Tag 02M7
(blueprint: lem-sc-hilbert-embedded-points-affine-localization).
-/

@[expose] public section

universe u v

namespace Module

/-- Source: Stacks Project, Tag 02M7
(blueprint: lem-sc-hilbert-embedded-points-affine-localization).
The quotients removing embedded associated points commute with localization.
The two maximality hypotheses specify the quotients constructed in
`exists_maximal_nowhereDense_support_quotient`. The equality on the images of
`m : M` specifies the canonical isomorphism induced by the quotient maps.

Proof for stage 3, following the three steps of the DAG node:
1. Localize the exact sequence `0 → K → M → M ⧸ K → 0`. Exactness identifies
   the localized quotient with the quotient of the localized module by the
   image of localized K, compatibly with the quotient maps.
2. By `lem-sc-hilbert-embedded-points-affine-removal`, K is maximal with
   nowhere dense support. Every submodule is finite and has closed support;
   the support of M has finitely many irreducible components (Stacks Tag 0052).
   Nowhere density is equivalent to vanishing at their generic points q_i.
   Thus K is the kernel of `M → ∏ i, M_{q_i}`: this kernel itself has nowhere
   dense support, so maximality gives equality. After inverting f, the generic
   points are precisely the q_i avoiding f. For q_i containing f, the finite
   module M_{q_i} is supported only at the closed point and is killed by a
   power of its maximal ideal, hence by a power of f. Localizing this kernel
   and its finite product therefore gives the analogous kernel for M_f.
3. Apply `lem-sc-hilbert-embedded-points-affine-removal` over the Noetherian
   ring R_f to the finite module M_f. The kernel in step 2 is its maximal
   nowhere-dense-support submodule Kf. Step 1 now gives the desired linear
   equivalence and its compatibility with both quotient maps.
-/
theorem localization_commutes_with_embedded_point_removal
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (f : R)
    (K : Submodule R M)
    (Kf : Submodule (Localization (Submonoid.powers f))
      (LocalizedModule (Submonoid.powers f) M))
    (hK : Maximal (fun L : Submodule R M =>
      IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R L}) K)
    (hKf : Maximal (fun L : Submodule (Localization (Submonoid.powers f))
      (LocalizedModule (Submonoid.powers f) M) =>
      IsNowhereDense {p : Module.support (Localization (Submonoid.powers f))
        (LocalizedModule (Submonoid.powers f) M) |
        p.val ∈ Module.support (Localization (Submonoid.powers f)) L}) Kf) :
    ∃ e : LocalizedModule (Submonoid.powers f) (M ⧸ K) ≃ₗ[
      Localization (Submonoid.powers f)]
      ((LocalizedModule (Submonoid.powers f) M) ⧸ Kf),
      ∀ m : M,
        e (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ K) (K.mkQ m)) =
          Kf.mkQ (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) := by
  sorry

end Module
