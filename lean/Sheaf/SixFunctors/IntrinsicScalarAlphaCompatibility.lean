/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.SixFunctors.SemilinearProperOpenScalarSupport

/-! # Scalar compatibility of the intrinsic inverse-image clopen word

Source: Stacks Project, Tag 0F7B, open case; Zheng, Construction 4.1 and Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 64
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
variable (B : Type (u + 1)) [CommRing B]
  (φ : ∀ n : ℕ, B →+* C n)
  (hφ : ∀ n : ℕ, (τ n).hom.comp (φ (n + 1)) = φ n)

/-- Scalar preserves the specified inverse-image alpha word, before taking proper mates.
Source: Stacks Project, Tags 03DI and 0F7B; Zheng, Construction 4.1 and Lemma 4.10.
Proof: obtain the ordinary scalar comparison package D. Its level identifications
and transition equations give a section-normalized isomorphism from D.rho to the
chosen rhoOrdinary. Conjugating D.d by these isomorphisms gives the chosen ordinary
direct-image comparison: both are identity on every section. Transpose this identity
and localize it to identify scalarB D with the conjugate of rhoP. Transpose again
under the open adjunction to identify scalarA D with the conjugate of rhoJ; the
open units fix this identification uniquely. Apply the alpha preservation clause
of derivedScalarComparison, and the pre-mate alpha normalization from the intrinsic/
varying-ring comparison. Substitute these conjugation formulas. Naturality moves
the boundary identifications past alpha and its strict-tower counterpart, and the
inverse pairs cancel. This proves the stated equation on whole derived systems.
The clopen projection used by the ordinary package is (1,0), so empty components,
zero coefficient rings and nonflat coefficient maps require no extra hypothesis.
No proper-adjunction mate of alpha is taken in this argument.
(blueprint: lem-sf-intrinsic-scalar-alpha-compatibility). -/
theorem intrinsicScalarAlphaCompatibility
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived C τ S) :
    (rho C τ B φ hφ W).map ((alpha C τ k r p i h).app M) ≫
        (rhoJ C τ B φ hφ k).hom.app ((P C τ r).obj M) ≫
        (StrictTower.J B k).map ((rhoP C τ B φ hφ r).hom.app M) =
      (rhoP C τ B φ hφ p).hom.app ((J C τ i).obj M) ≫
        (StrictTower.G B p).map ((rhoJ C τ B φ hφ i).hom.app M) ≫
        (StrictTower.alpha B k r p i h).app ((rho C τ B φ hφ S).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
