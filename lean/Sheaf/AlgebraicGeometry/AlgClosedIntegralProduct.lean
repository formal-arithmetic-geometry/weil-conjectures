/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.Irreducible
import WeilConjectures.FieldTheory.AlgClosedFiniteTypeTensorDomain

/-!
# Products of integral varieties over an algebraically closed field

Source: Stacks Project, Varieties, Tag 05P3, lemma-product-varieties, integrality clause
(blueprint: lem-sfb-algclosed-integral-product).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The fibre product of two integral separated finite type schemes over an algebraically
closed field is integral. Source: Stacks Project, Varieties, Tag 05P3,
lemma-product-varieties, integrality clause (blueprint: lem-sfb-algclosed-integral-product).

Proof:
1. Choose finite affine open covers of both factors using def-weil-finite-type-morphism,
   and discard empty charts. The index sets remain nonempty. The coordinate algebras
   are finite type domains by def-pc-integral-scheme.
2. Products of these charts are open in the fibre product, by def-pc-fibre-product and
   lem-weil-pbc-open-immersion-base-change. They are precisely the intersections of the
   inverse images of the two affine opens under the projections, and cover the product.
   By lem-weil-pbc-fibre-product-affine-spectra their coordinate rings are tensor products.
   These are domains by lem-weil-pbc-algclosed-finite-type-tensor-domain.
3. Any two product charts meet. The corresponding intersections in both factors are
   nonempty by irreducibility (def-pc-integral-scheme, def-weil-irreducible-components).
   The map from the first intersection to Spec k is surjective since Spec k has one point
   (def-weil-affine-spectrum). Its base change to the second intersection is surjective
   by lem-weil-pbc-surjective-base-change. Hence their fibre product is nonempty, and the
   universal property identifies it with the intersection of the two product charts.
4. Apply lem-per-integral-affine-cover-criterion to this nonempty affine cover with domain
   coordinate rings and pairwise nonempty intersections. -/
theorem isIntegral_pullback_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (A B : Scheme.{u})
    [A.Over (Spec (CommRingCat.of k))] [B.Over (Spec (CommRingCat.of k))]
    [IsIntegral A] [IsIntegral B]
    [IsSeparated (A ↘ Spec (CommRingCat.of k))]
    [IsSeparated (B ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (A ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (A ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (B ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (B ↘ Spec (CommRingCat.of k))] :
    IsIntegral (pullback (A ↘ Spec (CommRingCat.of k)) (B ↘ Spec (CommRingCat.of k))) := by
  sorry

end AlgebraicGeometry
