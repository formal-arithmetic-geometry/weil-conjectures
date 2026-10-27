/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.StableFiberCurve
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar

/-! # Faithfulness of stable-curve automorphisms on Picard torsion

Source: Deligne, Le lemme de Gabber, Lemma 3.5.1, printed pp.139--140
(blueprint: lem-sfb-stable-picard-torsion-faithfulness).

Picard classes and their pullbacks are the existing scheme Picard construction.
The multidegree condition is evaluated on the canonical normalization of each
reduced irreducible component, with its inherited structural map to the field.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.StablePointedModuli

/-- An automorphism of a stable unpointed curve acting trivially on all multidegree-zero
Picard classes killed by an invertible integer at least three is the identity.
Singular and reducible curves and automorphisms of wild order are included.

Source: Deligne, Le lemme de Gabber, Lemma 3.5.1, printed pp.139--140
(blueprint: lem-sfb-stable-picard-torsion-faithfulness).

Proof:
1. By `lem-sfb-stable-relative-picard-kummer`, the multidegree-zero Picard space N
   is semiabelian and its k-points are exactly the classes in the statement. Pullback
   by a induces u on N, acting identically on N[n](k) by the hypothesis.
2. `lem-sfb-stable-isom-finite-unramified` makes Aut(C) finite: distinct k-points of
   its finite coordinate algebra give distinct maximal ideals, and the Chinese remainder
   theorem bounds their number by its dimension. Thus a, and hence u, has finite order r.
   No invertibility of r is needed.
3. By `lem-sfb-semiabelian-hom-finite-free`, R = End(N) has a finite integral basis.
   The endomorphism u - 1 vanishes on N[n](k).
4. `lem-sfb-semiabelian-torsion-kernel-divisibility` gives u - 1 = n b in R.
5. Apply `lem-sfb-finite-free-ring-congruence-torsion` to u^r = 1 and u = 1 + n b
   to obtain u = 1. Thus a fixes every multidegree-zero Picard class.
6. `lem-sfb-stable-picard-action-faithful` now gives a = 1. -/
theorem picard_torsion_faithfulness (k : Type u) [Field k] [IsAlgClosed k]
    (g : ℕ) (hg : 2 ≤ g)
    (C : Fiber (Spec (.of k)) g 0 (Over.mk (𝟙 (Spec (.of k)))))
    (n : ℕ) (hn : 3 ≤ n) (hinv : IsUnit (n : k))
    (a : Aut (fiberCurve C))
    (hfix : ∀ L : (fiberCurve C).left.Pic,
      (∀ Z : irreducibleComponents (fiberCurve C).left,
        @Scheme.Modules.degree k _
          (((fiberCurve C).left).reducedNormalizationComponent Z).normalization
          ⟨((fiberCurve C).left).normalizedComponentMap Z ≫ (fiberCurve C).hom⟩
          ((Scheme.Modules.pullback (((fiberCurve C).left).normalizedComponentMap Z)).obj
            ((fromSkeleton (fiberCurve C).left.Modules).obj L.val)) = 0) →
      L ^ n = 1 → Scheme.Pic.map a.hom.left L = L) :
    a = 1 := by
  sorry

end AlgebraicGeometry.StablePointedModuli
