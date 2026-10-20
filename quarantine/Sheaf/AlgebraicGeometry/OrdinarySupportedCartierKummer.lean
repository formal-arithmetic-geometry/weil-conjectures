/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem
import Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence

/-!
# Existence of an ordinary supported Cartier Kummer map

Source: Stacks Project, Tags 03PL and 0A45; blueprint
sec-smooth-purity/sk-prop-sf-cbc/lem-amb-cartier-kummer-map.md
(blueprint: lem-asd-ordinary-supported-kummer).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The supported Cartier Kummer morphism, with its defining relative boundary,
unit/Chern equation, Cartier-preserving pullback square, and derived scalar square.
The derived arrow is displayed explicitly; Ext is only its canonical degree-two
representative. The boundary determines that representative uniquely. Pullback and
scalar-extension representatives are themselves normalized by the same boundary.

Source: Stacks 03PL and 0A45; blueprint lem-amb-cartier-kummer-map
(blueprint: lem-asd-ordinary-supported-kummer).

Proof:

1. By `def-pc-divisor-line-bundle`, the line is the dual of the Cartier ideal.
On an affine chart with regular generator f, its dual basis is e = f⁻¹ and the
canonical divisor section is f e. On the complement f is a unit, so this is a
specified frame τ. If f changes to u f, the dual basis changes to u⁻¹ e and the
section stays the same. `lem-sc-line-bundle-torsor` identifies these frames with
the actual G_m-torsor of the line.

2. Apply `lem-amb-relative-torsor-cohomology` to this torsor with its specified
section on the complement. This gives the relative H¹ class, independent of charts
and refinements. Equivalently, form the integral torsor extension and quotient by
the splitting over the open complement. The result is an extension of i_* Z_D by
G_m; its fibre over the supported section one is the frame torsor, and τ maps to
zero. This is exactly the extension model in SupportedKummerBoundary.

3. `lem-amb-kummer-any-base` supplies the actual short exact Kummer sequence.
Its relative connecting map is the Yoneda product with that extension. Naturality
of the relative connecting map from `lem-amb-relative-torsor-cohomology` identifies
its forgotten-support class with the Kummer Chern class of the line. G_m is used
only as an abelian sheaf; it is never treated as a ZMod N-module.

4. `lem-weil-pbc-etale-module-cohomology-forget` identifies module and abelian
derived sections of roots of unity, and these comparisons commute with restriction.
Their relative cones therefore agree. `lem-amb-closed-support-hom` identifies the
relative class with an Ext class from i_* (ZMod N)_D. The forget-support map is
precomposition with the constant unit. Concretely,
`lem-weil-pbc-open-closed-short-exact` and
`lem-weil-pbc-extension-by-zero-adjunction` identify derived Hom from the open-closed
triangle with the relative fibre of the restriction of sections. Thus the map out
of the relative fibre is the specified unit, giving the Chern equality.

5. A closed immersion is finite, so `lemma-weil-pbc-finite-direct-image-exact`
identifies its derived direct image of a sheaf with its degree-zero direct image.
Apply `lem-pur-derived-change-of-rings` along ZMod N → A. By
`lemma-weil-pbc-finite-stalk-formula`, the supported constant has stalk ZMod N on D
and zero elsewhere. `lem-kun-stalk-as-pullback`,
`lem-kun-inverse-image-monoidal`, and `lem-kun-pullback-constant` compute the
extended stalks as A and zero, and the canonical comparison is the identity there.
`prop-weil-pbc-geometric-stalks-exact` and
`lemma-weil-pbc-geometric-stalk-conservative` show that its cone is acyclic.
`lem-asd-finite-etale-twist-line` makes the roots sheaf a flat rank-one ZMod N-line,
so the extended target is the actual finite twist in degree zero. The same
calculation extends the constant unit to the A-unit. This proves the Chern and
scalar clauses, with the scalar maps fixed on constants and pure root tensors.
The supported constant and the root line are flat over ZMod N, so their
normalized scalar units have SupportedDerivedScalarUnit's unbounded derived
universal property. Functoriality of derived scalar extension gives the Ext square.

6. For Cartier-preserving pullback, the pulled-back chart equation f' is again
regular: if (f') = (g) with g regular, write f' = a g and g = b f'; cancellation
gives b a = 1. Thus the pulled-back line and its specified divisor section are
those of D'. Naturality in `lem-amb-relative-torsor-cohomology` pulls back the
relative torsor and Kummer boundaries. The roots comparison is an isomorphism:
on a root-trivializing etale cover from `lem-asd-finite-etale-twist-line`, a
primitive root and its pullback give the same rank-one generator (for N = 1 both
root modules are zero). The canonical closed exchange is an isomorphism by the
stalk formula and conservative geometric stalks. The support-Hom comparison of
step 4 is natural: all comparisons send the constant generator one to one, on
both the base and its open complement. Exact inverse image
`prop-weil-pbc-inverse-image-modules-exact` preserves the open-closed triangle.
Finally `lem-kun-inverse-image-monoidal` and `lem-kun-pullback-constant` commute
pullback with derived scalar extension. Substitution gives the base-change Ext
square with the specified roots-and-line transport.

The relative support-Hom comparison and the coefficient-forgetting comparison
are isomorphisms, so the specified relative boundary determines the Ext class
uniquely. Apply the construction also to each Cartier pullback and to ZMod N.
No regularity of T, flatness of A over ZMod N, or flatness of the Cartier-preserving
base morphism is used.
-/
theorem ordinary_supported_kummer (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    ∃ (κ : Ext
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
        (Scheme.finiteEtaleTateLine T N A hA) 2)
      (c : (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A D) ⟶
        (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)
      (c₁ : Ext (ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2)
      (t : OrdinaryFiniteTwistTransport A N hA),
      c = supportedExactDerivedMap (lowerStar (ModuleCat.{u + 1} A) i)
        (ordinaryFiniteConstant A D) (Scheme.finiteEtaleTateLine T N A hA) κ ∧
      SupportedKummerBoundary A N hA i hI hT κ ∧
      (∀ κ' : Ext
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
        (Scheme.finiteEtaleTateLine T N A hA) 2,
        SupportedKummerBoundary A N hA i hI hT κ' → κ' = κ) ∧
      (Ext.mk₀ (ordinaryFiniteIntegralGenerator A T)).comp
        (c₁.mapExactFunctor (RawModuleScalarComparison.forget A T)) (zero_add 2) =
          supportedKummerChern A N hA i hI hT ∧
      supportedDerivedUnit A i ≫ c = c₁.hom ∧
      (∀ {D' T' : Scheme.{u}} (i' : D' ⟶ T') [IsClosedImmersion i']
        (v : T' ⟶ T) (w : D' ⟶ D) (sq : IsPullback w i' i v)
        (hI' : i'.ker.IsInvertible),
        ∃ κ' : Ext
          ((lowerStar (ModuleCat.{u + 1} A) i').obj (ordinaryFiniteConstant A D'))
          (Scheme.finiteEtaleTateLine T' N A hA) 2,
          SupportedKummerBoundary A N hA i' hI'
            (by simpa using hT.map v.appTop.hom) κ' ∧
          IsIso (supportedConstantExchange A i i' v w sq.toCommSq) ∧
          (Ext.mk₀ (supportedConstantExchange A i i' v w sq.toCommSq)).comp
              κ' (zero_add 2) =
            (κ.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) v)).comp
              (Ext.mk₀ (t.line v hT).hom) (add_zero 2)) ∧
      (∀ [NeZero N],
        ∃ κ₀ : Ext
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).obj
            (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D))
          (Scheme.finiteEtaleTateLine T N (ULift.{u + 1} (ZMod N))
            (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
              (ZMod.natCast_self N))) 2,
          SupportedKummerBoundary (ULift.{u + 1} (ZMod N)) N
            (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
              (ZMod.natCast_self N)) i hI hT κ₀ ∧
          SupportedKummerScalar
            ((Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom) N
            (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
              (ZMod.natCast_self N)) hA i κ₀ κ) := by
  sorry


/-- The unique-boundary clause of ordinary_supported_kummer, with its other witnesses hidden.
Source: Stacks 03PL, 0A45 (blueprint: lem-asd-ordinary-supported-kummer).
Proof: obtain κ and its relative boundary from ordinary_supported_kummer. Its third clause
says every other representative with this boundary equals κ, which is exactly uniqueness.
This typed projection prevents normalization of all pullback and scalar witnesses in consumers.
-/
theorem ordinary_supported_kummer_uniqueBoundary (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    ∃! κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2,
      SupportedKummerBoundary A N hA i hI hT κ := by
  exact supported_cartier_boundary_existsUnique T N hN A hA hT i hI

end AlgebraicGeometry.Etale
