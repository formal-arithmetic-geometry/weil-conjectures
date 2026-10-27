/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.AlgebraicGeometry.FineFanBlowup

/-!
# Local rigidity of morphisms to an affine fan

Source: ILO, Exposé VIII, proof of Theorem 3.3.15, printed p.109, and
Lemma 3.1.8(ii), printed p.99 (blueprint: lem-trf-affine-fan-germ-rigidity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.FineFan

/-- Local morphisms to the sharp spectrum of a fine sharp monoid agree near a point
when all canonical sections have equal germs there. The neighbourhood `U` is an open
of the open subspace `V`, hence is also an open of `T` contained in `V`. The first
conjunct equates the restricted canonical-section homomorphisms; the second equates
the whole sheafed-space morphisms, including continuous maps and all sheaf maps.
We use multiplicative notation for monoids, so the source's additive zero is `1`.
No nontriviality or nonempty generating-set assumption excludes the trivial monoid.

Source: ILO VIII, proof of Theorem 3.3.15, p.109, shrinking for fine monoids and
Lemma 3.1.8(ii), p.99 (blueprint: lem-trf-affine-fan-germ-rigidity).

Proof:
1. For the trivial monoid take the whole of `V`; both section homomorphisms send its
only element to `1`, without choosing generators. Otherwise fineness supplies a finite
generating set. Equality of the germs of each generator supplies a neighbourhood
where its two sections agree. Intersect these finitely many neighbourhoods in `V`.
2. Every monoid element is a product of generators, allowing the empty product.
Induction on such a product extends the equality to every element, because the
section maps and restrictions are monoid homomorphisms. This proves the first conjunct.
3. Restriction to an open preserves stalks, their sharpness, and locality of the two
morphisms. Canonical pullback commutes with restriction. Apply the uniqueness assertion
of lem-trf-affine-fan-canonical-section-rigidity (equivalently the injectivity clause
of lem-trf-affine-fan-hom-universal) to these restricted morphisms and the equality
from step 2. This identifies their point maps and their sheaf maps simultaneously. -/
theorem affine_fan_germ_rigidity
    (T : SheafedSpace CommMonCat.{u})
    (hT : ∀ x : T, IsSharp (stalk T.presheaf x))
    (P : Type u) [CommMonoid P] (hP : IsFine P) (sP : IsSharp P)
    (V : Opens T) (t : V)
    (h k : T.restrict V.isOpenEmbedding ⟶ affine P)
    (hh : IsLocalMorphism h) (hk : IsLocalMorphism k)
    (heq : ∀ p : P,
      germ (T.restrict V.isOpenEmbedding).presheaf ⊤ t (by trivial)
          (((SheafedSpace.Γ.map h.op).hom.comp (affineSection P)) p) =
        germ (T.restrict V.isOpenEmbedding).presheaf ⊤ t (by trivial)
          (((SheafedSpace.Γ.map k.op).hom.comp (affineSection P)) p)) :
    ∃ U : Opens V, t ∈ U ∧
      (SheafedSpace.Γ.map
        ((T.restrict V.isOpenEmbedding).ofRestrict U.isOpenEmbedding).op).hom.comp
          ((SheafedSpace.Γ.map h.op).hom.comp (affineSection P)) =
        (SheafedSpace.Γ.map
          ((T.restrict V.isOpenEmbedding).ofRestrict U.isOpenEmbedding).op).hom.comp
            ((SheafedSpace.Γ.map k.op).hom.comp (affineSection P)) ∧
      (T.restrict V.isOpenEmbedding).ofRestrict U.isOpenEmbedding ≫ h =
        (T.restrict V.isOpenEmbedding).ofRestrict U.isOpenEmbedding ≫ k := by
  sorry

end AlgebraicGeometry.FineFan
