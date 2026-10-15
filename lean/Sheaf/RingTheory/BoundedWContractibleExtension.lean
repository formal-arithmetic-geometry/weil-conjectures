/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.SetTheory.Cardinal.Arithmetic
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.RingTheory.ProfiniteComponentRingPullback
import Sheaf.RingTheory.StrictWCover
import Sheaf.RingTheory.StrictWCoverProperties
import Sheaf.RingTheory.StrictWCoverSize
import Sheaf.RingTheory.WContractibleGeometricCriterion
import Sheaf.Topology.BoundedExtremallyDisconnectedCover

/-! # Bounded w-contractible extensions

Source: Stacks Project, Tags 0981, 0983, 0984 and 0989
(blueprint: lem-weil-pbc-wcontractible-ring-extension).
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

namespace RingHom

/-- Every ring has a bounded faithfully flat ind-etale extension splitting all faithfully
flat weakly etale extensions, and its spectrum is a singleton pro-etale cover.
Source: Stacks Project, Tags 0981, 0983, 0984 and 0989
(blueprint: lem-weil-pbc-wcontractible-ring-extension).

Proof plan:
1. Form the strict w-local cover C_A. The strict-w-cover theorem gives faithful flatness,
ind-etaleness, w-locality and strictly henselian maximal local rings. Its size theorem gives
|C_A| ≤ κ.
2. The profinite component-ring-pullback theorem identifies its component space with its
closed points, hence bounds that space by 2^κ. The bounded-extremally-disconnected-cover
lemma gives a profinite extremally disconnected surjection T onto it, of size ≤ 2^(2^(2^κ)).
3. Apply profinite-component-ring-pullback to construct C_A → D, ind-Zariski and ind-etale,
identifying local rings and preserving w-locality. Surjectivity on spectra and flatness,
using ind-etale-stability and flat-surjective-spectrum-faithfully-flat, make A → D faithfully
flat and ind-etale. The maximal local rings of D remain strictly henselian.
4. The wcontractible-geometric-criterion supplies the retraction of every faithfully flat
weakly etale D → B from these conditions and the extremal disconnectedness of T.
5. Each maximal local ring of D has size ≤ κ, since fractions in the corresponding local
ring of C_A are represented by pairs of elements of C_A. The diagonal map into the product
of maximal local rings is injective: a nonzero element has its annihilator contained in a
maximal ideal and cannot vanish in that localization. There are ≤ |T| such ideals, giving
|D| ≤ κ^(2^(2^(2^κ))). For the zero ring the product is empty and the bound still holds.
6. For every affine open U of Spec A, its inverse image V is affine by
morphism-affine-schemes-affine. The fibre-product-affine-spectra lemma identifies it with
the spectrum of the base-changed algebra. Faithfully-flat-base-change and
faithfully-flat-surjective-spectrum show V maps onto U. The sole affine open V verifies
the finite-affine-open covering condition of Tag 0989. Weak etaleness follows from
ind-etale-stability, so this singleton is a pro-etale covering. -/
theorem exists_bounded_wContractible_extension (A : Type u) [CommRing A]
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hA : Cardinal.mk A ≤ κ) :
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧
      Cardinal.mk D ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) ∧
      (∀ (B : Type (max u v)) [CommRing B] (g : D →+* B),
        g.FaithfullyFlat → g.WeaklyEtale →
          ∃ r : B →+* D, r.comp g = RingHom.id D) ∧
      Presieve.singleton (Spec.map (CommRingCat.ofHom f)) ∈
        Scheme.proetalePrecoverage (Spec (CommRingCat.of A)) := by
  sorry

end RingHom
