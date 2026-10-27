/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Grp

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Topology.Sheaves.Stalks

/-!
# A flat subgroup containing an identity neighbourhood is open

Source: the translation argument motivated by Conrad, *Reductive group schemes*,
Theorem B.3.2(2), final proof, printed p. 289; the general lemma and its proof are
recorded in the DAG (blueprint: lem-sfb-flat-subgroup-identity-neighbourhood-open).
The supporting scheme results are Stacks Tags 01JY, 01U9, 01TS, 02GP, 01U7,
01TR, 01UA, 00HR, 05CK, 01QO and 007T.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- A closed subgroup, flat and locally of finite presentation over the base, is open
if an open neighbourhood of the identity section factors through it.
Source: the general translation lemma motivated by Conrad, *Reductive group schemes*,
Theorem B.3.2(2), final proof, printed p. 289
(blueprint: lem-sfb-flat-subgroup-identity-neighbourhood-open).

Proof plan, following the five steps of the DAG:
1. On `P = H ×[S] G`, the shear `(h,g) ↦ (h,i(h)g)` is an automorphism, with inverse
   `(h,g) ↦ (h,i(h)⁻¹g)`. The base change `H ×[S] V → P` of `v` is an open immersion
   by `lem-weil-pbc-open-immersion-base-change` (Stacks 01JY), as is its composite
   with the shear. Composing with the projection to `G` gives `q(h,t) = i(h)v(t)`.
2. The projection `P → G` is flat and locally of finite presentation by base change
   of `H → S` (`lem-weil-pbc-flat-morphism-base-change` and clause (3) of
   `lem-weil-pbc-qcqs-morphism-permanence`, Stacks 01U9 and 01TS). The open immersion
   into `P` is étale, hence flat and locally of finite presentation
   (`lem-weil-pbc-open-immersion-etale`, `def-weil-etale-morphism`, Stacks 02GP).
   Composition (`lem-pc-flat-compose`, `lem-sbc-locally-finite-presentation-composition`,
   Stacks 01U7 and 01TR) gives both properties for `q`.
3. By `lem-weil-pbc-flat-lfp-open` (Stacks 01UA), the image of `q` is open.
   The factorization `b ≫ i = v` factors `q` through `H` by `(h,t) ↦ h b(t)`.
   The map `h ↦ (h,eV(p_H(h)))` gives the converse image inclusion, because
   `eV ≫ v` is the identity section. Thus the image of `q` equals the image of `i`.
   Since `i` is closed, it is a homeomorphism onto this open image.
4. At each `h : H`, take the point `z = (h,eV(p_H(h)))` above `i(h)`.
   The flat local stalk map of `q` is faithfully flat by
   `lem-weil-pbc-flat-local-hom-faithfully-flat` (Stacks 00HR), hence injective by
   `lem-weil-pbc-faithfully-flat-universally-injective` (Stacks 05CK), applied to
   the base ring as module. It factors through the stalk map of `i`, which is
   therefore injective and is also surjective by the closed immersion property
   (Stacks 01QO). Every stalk map of `i` is consequently an isomorphism.
5. Transport the sheaf map to the open image. The stalk criterion
   `lem-weil-pbc-sets-sheaf-iso-on-stalks` (Stacks 007T) makes its underlying sheaf
   map an isomorphism. The inverse section maps preserve the ring operations and
   commute with restrictions by bijectivity and naturality. The open embedding
   and this structure sheaf isomorphism give `IsOpenImmersion i.left`.
-/
theorem isOpenImmersion_of_flat_subgroup_identity_neighbourhood
    {S : Scheme.{u}} (H G : Over S) [GrpObj H] [GrpObj G]
    (i : H ⟶ G) [IsMonHom i] [IsClosedImmersion i.left]
    [Flat H.hom] [LocallyOfFinitePresentation H.hom]
    (V : Over S) (v : V ⟶ G) [IsOpenImmersion v.left]
    (eV : 𝟙_ (Over S) ⟶ V) (b : V ⟶ H)
    (heV : eV ≫ v = MonObj.one (X := G)) (hb : b ≫ i = v) :
    IsOpenImmersion i.left := by
  sorry

end AlgebraicGeometry
