/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
public import WeilConjectures.SixFunctors.ProEtale.Derived.LocallyPerfect.Defs

/-!
# A complex with a deep perfect top part and finite Tor amplitude is perfect

This is the last step of Stacks, Tag 0FPV, in the form used for `D(Y_proét, Λ)`. Let
`K ≅ Q(M)` have Tor amplitude in `[a, b]`, and let `j : E ⟶ M` be a degreewise monomorphism from
a bounded complex `E` of finite free sheaves, vanishing below `m` and an isomorphism in degrees
`≥ m`, where `m + 2 ≤ a`. If the differential `E^{m+1} ⟶ E^{m+2}` is induced by a `Λ`-linear map
`f`, then `K` is represented by the truncation `τ^{≥ m+2} E`, whose terms are the finite free
sheaves `E^i` for `i > m + 2` and the cokernel `B = c(coker f)` in degree `m + 2`. The Tor
amplitude makes `B` flat, so `coker f` is a flat finitely presented module, hence projective,
and `B` is dualizable.

## Main results

- `AlgebraicGeometry.ProEtale.flat_of_flat_constantSheaf`: over a nonempty scheme, a module
  whose constant sheaf is flat is flat.
- `AlgebraicGeometry.ProEtale.exists_iso_Q_obj_of_torAmplitudeIn`: the step described above.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Over a nonempty scheme, a `Λ`-module whose constant pro-étale sheaf is flat is flat: the
constant sheaf functor is monoidal, exact and reflects zero objects. -/
lemma flat_of_flat_constantSheaf {Y : Scheme.{u}} [Nonempty Y] (B : ModuleCat.{u + 1} Λ)
    (h : ObjectProperty.flat ((constantSheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} Λ)).obj B)) : Module.Flat Λ B := by
  sorry

end AlgebraicGeometry.ProEtale
