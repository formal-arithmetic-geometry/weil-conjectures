/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.SfDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Pro-étale direct image for finite-Tor constructible complexes

Source: Weil conjectures blueprint,
`literature/blueprint/master/blueprint/sec-six-functors/sk-cor-sf-direct-image-ctf/`
`cor-sf-direct-image-ctf-proetale.md` (blueprint: cor-sf-direct-image-ctf-proetale).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- For a separated finite-type map of finite-type schemes over the fixed algebraic closure,
bounded constructibility and the specified Tor interval are preserved by the canonical
finite-coefficient pro-étale derived direct image, with the source-dimension shift.

Source: Weil conjectures blueprint, `sec-six-functors/sk-cor-sf-direct-image-ctf`,
node order 2195 (blueprint: cor-sf-direct-image-ctf-proetale).

Proof plan:
1. Apply `lem-sf-proetale-constructible-origin` to intrinsic bounded constructibility,
obtaining a bounded constructible étale complex `K'` and `K ≅ ν_X^* K'`. In particular
`K'` is bounded below; the derived comparison, not only the sheaf comparison, is used.
2. The coefficient prime is invertible over `D.k` since `l ≠ D.p`. Apply clause (ii)
of `lem-sf-comparison-tor-amplitude` to reflect exactly the interval `[a,b]` to `K'`.
3. Apply `cor-sf-direct-image-ctf-nonproper` to `f` and `K'`. Its hypotheses are finite
type over `D.k`, separated finite type of `f`, the source dimension bound, and the
constructibility and interval already checked. Thus `L = Rf_{Et,*} K'` is bounded
constructible of Tor amplitude `[a,b+2d]`.
4. Finite type makes `f` quasi-compact. Its relative diagonal is a closed immersion
by separatedness (`def-weil-proper-morphism`), hence proper by clause (c) of
`lem-weil-pbc-proper-fp-permanence`, hence finite type and quasi-compact.
Thus `f` is also quasi-separated (`def-weil-quasi-separated-morphism`).
5. Apply `prop-weil-pbc-comparison-direct-image` to the bounded-below `K'` and the
quasi-compact quasi-separated `f`. Combine its isomorphism with `Rf_*` of the origin
isomorphism to obtain `Rf_{Proet,*} K ≅ ν_Y^* L`.
6. Clause (i) of `lem-sf-comparison-tor-amplitude` makes `ν_Y^* L` intrinsically
bounded constructible with interval `[a,b+2d]`. Transfer both properties through the
last isomorphism: cohomology sheaves, also after tensoring with each degree-zero
module sheaf, are isomorphic. This treats the original arbitrary intrinsic `K`.
-/
theorem finiteCoefficientDirectImage_boundedConstructible_torAmplitude
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (X Y : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (d : ℕ) (hd : topologicalKrullDim X.left ≤ (d : WithBot ℕ∞))
    (a b : ℤ)
    {K : Scheme.proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing l E n)}
    (hK : WeilConjectures.finiteTorConstructible l E n hn X.left K)
    (hTor : Scheme.HasProEtaleTorAmplitude X.left
      (Padic.coefficientExtensionRing l E n) K a b) :
    Scheme.intrinsicFiniteTorsionConstructible l E n hn Y.left
        ((Scheme.proEtaleConstantDerivedDirectImage f.left
          (Padic.coefficientExtensionRing l E n)).obj K) ∧
      Scheme.HasProEtaleTorAmplitude Y.left (Padic.coefficientExtensionRing l E n)
        ((Scheme.proEtaleConstantDerivedDirectImage f.left
          (Padic.coefficientExtensionRing l E n)).obj K) a (b + 2 * (d : ℤ)) := by
  sorry

end AlgebraicGeometry.ProEtale
