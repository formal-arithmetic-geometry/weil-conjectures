/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite etale descent along the punctured root cover

Source: Stacks Project, Tags 02LA and 02VN, finite and etale fpqc descent applied to the punctured
root cover in Tag 0EYG.
(blueprint: lem-sbc-root-split-factor-finite-etale)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Finiteness and etaleness descend from a splitting over a punctured root cover.

Source: Stacks Project, Tags 02LA and 02VN, applied to the punctured cover in
Tag 0EYG. (blueprint: lem-sbc-root-split-factor-finite-etale)

Proof: On U=D(g), the algebra U[T]/(T^n-g) is finite free of positive rank n.
Its root t is a unit since t^n=g, and n is a unit, so the derivative n*t^(n-1)
is a unit. Thus the punctured root map V to U is finite etale and faithfully
flat. The equation hj identifies the supplied pullback over Spec R with the
pullback of j over U. The equation for delta identifies its structural map
with the projection from d copies of V. That projection is finite etale,
including d=0. Finiteness and etaleness descend along V to U by Tags 02LA
and 02VN. Neither regularity nor a point on the divisor is needed.
Edge cases: n=0 is excluded; d=0 gives the empty finite etale cover; when
D(g) is empty, j has empty source and the conclusion still holds. -/
theorem root_split_factor_finite_etale
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g))
    (hj : j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    (d : ℕ) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    IsFinite j ∧ Etale j := by sorry

end AlgebraicGeometry.Scheme
