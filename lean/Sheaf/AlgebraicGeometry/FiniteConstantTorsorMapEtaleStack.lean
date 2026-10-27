/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSchemeActionTorsorGroupoid
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescent
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty

/-! # Étale descent for finite constant-group torsors with equivariant maps

Source: Stacks Project, examples-stacks.tex, Tags 0370 and 0BLZ
(blueprint: lem-sfb-finite-constant-torsor-map-etale-stack).

The coproduct cocone and its unit and multiplication equations present `G = H_S`.
The existing étale torsor category retains actual schemes, equivariant maps and
cartesian arrows. The conclusion uses the existing total-category stack convention.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.SchemeAction

/-- Torsors under a finite constant group, together with equivariant maps to an
arbitrary action scheme, form an étale stack. The cocone presents the constant
scheme, and its displayed equations specify the group structure induced by `H`.
No freeness of the action on `V`, finite-type assumption or invertibility of the
order of `H` is imposed.

Source: Stacks Project, examples-stacks.tex, Tag 0370
(lemma-group-quotient-stack-in-groupoids), with scheme-torsor effectivity from
Tag 0BLZ (lemma-finite-etale-stack)
(blueprint: lem-sfb-finite-constant-torsor-map-etale-stack).

Proof:
1. Pull back trivializing étale covers and their equivariant trivializations along
any base map. The fibre-product universal property supplies the pullback comparisons
and their coherence. Equivariant cartesian arrows are thus fibred in groupoids.
2. An étale covering is fpqc (lem-weil-pbc-fpqc-finer-than-etale), and remains so
under arbitrary base change (lem-weil-pbc-etale-covering-base-change). Representable
fpqc descent (lem-weil-pbc-fpqc-representable-descent) glues compatible scheme maps
uniquely, including their equations over a base.
3. A trivial torsor is the finite coproduct of its base: it is étale by
lem-sc-etale-coproduct-etale and finite by the affine product-ring description
lem-weil-pbc-finite-affine-coproduct-spectrum and finiteness local on the target
(lem-weil-pbc-finite-local-on-target). Descend these properties using
lem-weil-pbc-fpqc-descend-finite and lem-galois-fpqc-descend-etale.
4. Glue local isomorphisms and their inverses by step 2. Their inverse, equivariance
and map-to-V equations hold globally by uniqueness. Apply the same argument after
every base change to obtain the entire isomorphism sheaf assertion.
5. For object descent, take disjoint unions of the local finite étale torsors and
of the covering schemes (lem-weil-pbc-scheme-coproduct-family). Finite étaleness is
local on the open-and-closed summands (lem-weil-pbc-closed-finite-etale-zariski-local).
Apply lem-galois-descent to the resulting surjective étale map. The overlap cocycle
provides a global finite étale scheme with the specified local identifications.
6. Glue each h-action using step 2. Its unit, multiplication and inverse equations
hold by uniqueness on the cover. The coproduct property assembles these maps into
the constant group action. Compose local trivializing covers with the original
cover (lem-weil-pbc-etale-covering-composition), proving that the descended scheme
is an étale locally trivial torsor.
7. Glue the local maps to V by step 2. Their being over S and equivariance hold by
uniqueness on the cover. The local identifications preserve these maps and induce
exactly the prescribed cocycle. Together with steps 1 and 4 this gives the stack
property in def-sfb-stable-pointed-moduli-groupoids, also over the empty scheme. -/
theorem finite_constant_torsor_map_isModuliStack
    {S : Scheme.{u}} (H : Type v) [Group H] [Finite H]
    (G V : Over S) [GrpObj G] [ModObj G V]
    (incl : H → (Over.mk (𝟙 S) ⟶ G))
    (hincl : IsColimit (Cofan.mk G incl))
    (hincl_one : incl 1 = 1)
    (hincl_mul : ∀ g h : H, incl (g * h) = incl g * incl h) :
    IsModuliStack (etaleTorsorGroupoid G V) := by
  sorry

end AlgebraicGeometry.SchemeAction
