/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Gluing

/-! # Affine closed pinching pushouts

Source: Stacks Project, Tag 0ET0, `lemma-basic-example-pushout`
(blueprint: lem-sfb-affine-closed-pinching-pushout).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The spectrum of the explicit matching-pairs ring is the scheme pushout when the
first map to the common quotient is surjective. Here `CommRingCat.pullbackCone α β`
is Mathlib's concrete cone: its ring is the subring of `A × T` on which the two maps
agree, and its two projections are the component projections. Zero rings are allowed.

Source: Stacks Project, Tag 0ET0, `lemma-basic-example-pushout`
(blueprint: lem-sfb-affine-closed-pinching-pushout).

Proof plan:
1. The matching-pairs ring P is the kernel of the difference map A ⊕ T → D.
   This is an elementary calculation; functoriality of Spec gives commutativity.
2. Localize this exact sequence at p = (a,t). Exact module localization
   (`lem-weil-pbc-localization-module-exact`, Stacks 01Z8) identifies P_p with
   A_a ×_{D_d} T_t, where d = α(a) = β(t). The component map is injective,
   including for nilpotent p.
3. For compatible maps Spec A → Z and Spec T → Z, the topological pushout
   (`lem-sfb-fibre-product-spectrum-topology`, Stacks 0B7J) gives a unique
   continuous map h from Spec P. Use the affine-open basis
   (`lem-weil-pbc-affine-opens-basis`) and the principal-open basis
   (`lem-weil-pbc-spec-localization-away-basic-open`) to cover Spec P by D(p)
   whose images under h lie in affine opens V of Z.
4. The inverse images of D(p) are D(a), D(t), D(d). Their localization open
   immersions (`lem-weil-pbc-principal-localization-open-immersion` and
   `def-weil-open-immersion`) identify their coordinate rings. The affine Spec
   correspondence (`def-weil-affine-spectrum`) and step 2 give a ring map
   Γ(V) → P_p and hence a scheme map D(p) → V → Z. Joint surjectivity in the
   topological lemma identifies its continuous map with h on D(p).
5. Two maps from D(r) to an affine V agreeing on the two inverse images coincide:
   their coordinate maps into P_r have the same two components, so step 2 and
   the affine Spec correspondence give equality.
6. Near a point of an overlap, choose a smaller affine target open inside the
   intersection of the two affine target opens, using the affine-open basis,
   and a principal source neighbourhood mapping into it. Step 5 proves the
   local maps agree there. Scheme-morphism gluing
   (`lem-weil-pbc-scheme-morphism-gluing`, Stacks 01JA and 04TN) constructs the
   global scheme map and identifies its restrictions with the original maps.
7. Any other compatible map has continuous map h by step 3. Step 5 gives equality
   on the principal cover, and gluing gives global equality. For empty Spec P,
   the same argument uses the empty cover. This is exactly the colimit universal
   property (`def-weil-pbc-category-colimit`); no finiteness or Noetherianity
   is used.
-/
theorem isPushout_spec_pullbackCone_of_surjective
    {A D T : CommRingCat.{u}} (α : A ⟶ D) (β : T ⟶ D)
    (hα : Function.Surjective α.hom) :
    IsPushout (Spec.map α) (Spec.map β)
      (Spec.map (CommRingCat.pullbackCone α β).fst)
      (Spec.map (CommRingCat.pullbackCone α β).snd) := by
  sorry

end AlgebraicGeometry
