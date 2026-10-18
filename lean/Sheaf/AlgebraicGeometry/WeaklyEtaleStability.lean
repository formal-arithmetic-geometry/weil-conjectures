/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.IndEtaleStability

/-!
# Stability of weakly étale and affine pro-étale morphisms

Source: blueprint node `sk-lem-pe-weakly-etale-stability`, order 702, and Stacks
Project, Tag 092A (blueprint: sk-lem-pe-weakly-etale-stability).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

/-- Weakly étale morphisms are stable under base change and composition, are Zariski-local on
source and target, and satisfy the over-base morphism property. Affine pro-étale morphisms are
stable under affine base change and composition.

Source: blueprint node `sk-lem-pe-weakly-etale-stability`, order 702, proof steps 1--5,
and Stacks Project, Tag 092A (blueprint: sk-lem-pe-weakly-etale-stability).

Proof (current reviewed DAG, steps 1--5):

1. A base change of `f` is flat. Its diagonal is the base change of the flat diagonal of
`f`, using the canonical identification of the iterated fibre products. This uses
`def-pc-fibre-product` and `lem-weil-pbc-flat-morphism-base-change`.

2. For `V ⟶ U ⟶ X`, flatness composes. The composite diagonal factors as
`V ⟶ V ×_U V ⟶ V ×_X V`. The first map is the flat diagonal of `V ⟶ U`; the second
is the base change of the flat diagonal of `U ⟶ X` along `V ×_X V ⟶ U ×_X U`.
Flatness of their composite uses `lem-pc-flat-compose`.

3. Restricting source and target to open subschemes preserves the local rings and the
induced local homomorphisms. The restricted self-fibre product is open in the original
self-fibre product, and the restricted diagonal is the restriction of the original diagonal.
Thus flatness of the morphism and of its diagonal can be checked on either Zariski cover.
This uses `def-weil-flat-morphism`, `def-weil-open-immersion`, and `def-pc-fibre-product`.

4. Factor an `X`-morphism `h : U ⟶ V` as its graph `U ⟶ U ×_X V` followed by the
second projection. The graph is the base change of the flat diagonal of `V ⟶ X`, and
the projection is the base change of the flat map `U ⟶ X`; hence `h` is flat. The square
from `Δ_h : U ⟶ U ×_V U` to `Δ_(U/X) : U ⟶ U ×_X U`, with identity on the left,
is cartesian: a pair whose image is `(u,u)` is uniquely determined by `u`.
Consequently `Δ_h` is flat by base change. This uses `def-pc-fibre-product`,
`lem-weil-pbc-flat-morphism-base-change`, and `lem-pc-flat-compose`.

5. On affine spectra, `lem-weil-pbc-fibre-product-affine-spectra` identifies base change
with the spectrum of tensor base change of rings. Apply the base-change and composition
clauses of `lem-weil-pbc-ind-etale-stability`, and use `proAffineEtale_Spec_iff`.
For these ring clauses, tensor products commute with filtered colimits and finite
presentation descends each étale algebra to a finite stage. No global ind-étale
presentation of an arbitrary weakly étale morphism is assumed.
-/
theorem weaklyEtale_stability :
    MorphismProperty.IsStableUnderBaseChange @WeaklyEtale.{u} ∧
      MorphismProperty.IsStableUnderComposition @WeaklyEtale.{u} ∧
      IsZariskiLocalAtSource @WeaklyEtale.{u} ∧
      IsZariskiLocalAtTarget @WeaklyEtale.{u} ∧
      (∀ {S U V : Scheme.{u}} (u : U ⟶ S) (v : V ⟶ S) (f : U ⟶ V),
        WeaklyEtale u → WeaklyEtale v → f ≫ v = u → WeaklyEtale f) ∧
      (∀ {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
        (f : X ⟶ Y) (g : Y ⟶ Z),
        proAffineEtale f → proAffineEtale g → proAffineEtale (f ≫ g)) ∧
      (∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y),
        proAffineEtale.{u}.IsStableUnderBaseChangeAlong f) := by
  sorry

end AlgebraicGeometry
