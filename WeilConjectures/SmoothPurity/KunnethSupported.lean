/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.SupportedExteriorProduct
public import WeilConjectures.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness

/-!
# Künneth for cohomology with closed support

Source: literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/sk-prop-an/
lem-pur-kunneth-supported.md, node lem-pur-kunneth-supported, order 3256
(blueprint: lem-pur-kunneth-supported).

The coefficient ring is the actual ring `A_{E,n} = 𝒪_E/ϖ_E^n`, that is
`Padic.coefficientExtensionRing ell E n` with its quotient ring structure, as in the
ordinary finite-ring Künneth theorem `isIso_ordinaryGlobalKunnethMap_finiteCoefficientRing`
(blueprint: lem-pur-ordinary-kunneth-finite-ring); `E` lives in `Type (u + 1)` so that
this ring is directly a coefficient ring for `ModuleCat.{u + 1}`.

## Main statements

* `kunnethSupported`: the supported exterior product is an isomorphism for bounded
  etale complexes when the second factor has finite Tor amplitude, together with
  the corresponding statement for specified pro-etale realizations.
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/--
The supported Künneth map is an isomorphism for bounded etale complexes with
coefficients in `A_{E,n}` and finite Tor amplitude in the second variable; the same holds
for specified pro-etale realizations coming from the etale complexes.

Source: literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/sk-prop-an/
lem-pur-kunneth-supported.md, node lem-pur-kunneth-supported, order 3256
(blueprint: lem-pur-kunneth-supported).

Proof:
1. Put `U = X \ Z`, `V = Y \ W`, `F = K ⊠ L`. Pullback preserves the cohomology interval of
   `K` and (lem-sf-etale-stalk-tor-test) the Tor interval of `L`, so `F` and its open
   restrictions are bounded below (lem-sf-source-tensor-cohomology-interval). The
   second-variable clause of lem-pur-supported-product-localization (with `D' = X`,
   `B' = Y`, `C' = W`) gives a morphism of support-restriction triangles
   (lem-pur-support-restriction-triangle, def-pur-supported-localization-comparisons)
   with components `κ^{X,W}`, `κ^{X,Y}`, `κ^{X,V}`. The last two are ordinary exterior
   products (def-pur-supported-exterior-product), isomorphisms by
   lem-pur-ordinary-kunneth-finite-ring; the five lemma makes `κ^{X,W}` invertible.
2. The same argument on `U × Y` with `K|_U, L` makes `κ^{U,W}` invertible.
3. The first-variable clause of lem-pur-supported-product-localization (with `B = X`,
   `C = Z`, `D = W`) gives a morphism of triangles with components `κ^{Z,W}`, `κ^{X,W}`,
   `κ^{U,W}` and commuting boundary square; the five lemma in each degree makes
   `κ^{Z,W}` invertible.
4. For pro-etale realizations, lem-pur-support-site-comparison gives the equality
   `RΓ_{Z×W}(θ) c κ_et = κ_proet (c ⊗ c)` with all other factors invertible, so the
   pro-etale pairing (def-pur-proetale-supported-exterior-product) of `ν^*K, ν^*L` is
   invertible; lem-pur-proetale-supported-product-naturality transports this along the
   retained etale-origin witnesses.
-/
theorem kunnethSupported
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of D.k))
    (g : Y ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
    (L : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
    (hK : ∃ a b : ℤ, K.obj.IsGE a ∧ K.obj.IsLE b)
    (hL : ∃ a b : ℤ, L.obj.IsGE a ∧ L.obj.IsLE b)
    (hTor : ∃ a b : ℤ,
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing ell E n) Y a b L.obj) :
    IsIso (supportedExteriorProduct (Padic.coefficientExtensionRing ell E n) f g i j
        K.obj L.obj) ∧
      (∀ (Kp : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
        (Lp : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y)
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
        (wK : Scheme.FixedEtaleOriginWitness X (Padic.coefficientExtensionRing ell E n) Kp)
        (wL : Scheme.FixedEtaleOriginWitness Y (Padic.coefficientExtensionRing ell E n) Lp)
        (_eK : wK.complex ≅ K) (_eL : wL.complex ≅ L),
        haveI : Finite (Padic.coefficientExtensionRing ell E n) :=
          Padic.finite_coefficientExtensionRing ell E n hn
        IsIso (ProEtale.supportedExteriorProductOverField
          (Padic.coefficientExtensionRing ell E n) D.k f g i j Kp.obj Lp.obj)) := by
  sorry

end AlgebraicGeometry.Etale
