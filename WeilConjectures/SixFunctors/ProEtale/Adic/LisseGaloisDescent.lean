/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGerm
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint

/-!
# Galois descent for sections of lisse sheaves over fields

Let `k : Spec K' ⟶ Y` be a weakly étale morphism from the spectrum of a field and `Ω / K'` a
separable normal (Galois, possibly infinite) extension. Then `Spec Ω ⟶ Spec K' ⟶ Y` is an
object of `Y_proét` on which `Gal(Ω / K')` acts by the automorphisms `Spec σ`
(`AlgebraicGeometry.ProEtale.fieldExtAut`), and `Spec Ω ⟶ Spec K'` is a pro-étale cover. For a
lisse `ℓ`-adic sheaf `F` on `Y`, restriction identifies the sections of `F` over `Spec K'` with
the `Gal(Ω / K')`-invariant sections over `Spec Ω`:

* restriction is injective
  (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.injective_map_fieldExtHom`): every geometric point
  of `Spec K'` lifts to `Spec Ω`, and sections of lisse sheaves are detected by their germs;
* an invariant section descends
  (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_map_fieldExtHom_eq`): by the sheaf
  condition for the cover `Spec Ω ⟶ Spec K'` it suffices that its pullbacks along any two
  `p₁ p₂ : Z ⟶ Spec Ω` over `Spec K'` agree, which is checked on germs, since any two
  `K'`-embeddings of the normal extension `Ω` into an algebraically closed field differ by an
  element of `Gal(Ω / K')` (`AlgebraicGeometry.ProEtale.exists_algEquiv_comp_specMap_eq`).

For `K'` the fraction field of the strict henselization of a curve at a boundary point and `Ω` a
separable closure, `Gal(Ω / K')` is the inertia group at the point: this is the second step of
blueprint `lem-wf-boundary-stalk-invariants`, which identifies the boundary stalk of `j_* F`
with the inertia invariants of the geometric generic stalk.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {K' Ω : Type u} [Field K'] [Field Ω] [Algebra K' Ω]

variable [Algebra.IsSeparable K' Ω] {Y : Scheme.{u}} (k : Spec (.of K') ⟶ Y) [WeaklyEtale k]

variable {l : ℕ} [Fact l.Prime] {F : AdicSheaf l Y}

end AlgebraicGeometry.ProEtale
