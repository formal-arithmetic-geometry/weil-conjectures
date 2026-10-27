/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefNativeOpenTensorPrimitives

/-! # Existence of finite native open tensor data

This is the finite coefficient-stage part of the construction in
[sites-cohomology.tex, Tag 0GL1], separated from the sequence-site datum.
(blueprint: lem-coef-native-open-tensor-finite-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Every positive finite coefficient stage admits the native open tensor datum.
Source: Stacks sites-modules.tex 0E8I, sites-cohomology.tex 0GL1 and 0G7E,
and Homology 012Z.
(blueprint: lem-coef-native-open-tensor-finite-existence).

Proof: localize the ambient pro-etale site at the open object. An object
of the open site is sent to its composite with j; its inverse is supplied by
factorization through the open. Covers are unchanged. The constant-ring
identification is the identity on constant sections, so the coefficient ring
on the open is the restricted ambient coefficient ring. Transport the
localized module restriction and extension along these site and ring
identifications. The direct-sum insertion and sheafification units agree
with the specified native unit, which identifies the adjunctions. Take right
to be the native module direct image, with its restriction adjunction.

Restriction takes a pure tensor to the tensor of its restricted sections.
The balanced tensor universal property, followed by sheafification, gives
pullTensor and its inverse. Checking on pure tensors proves pullPure and
pullNaturality. Apply ringed-topos pullback preservation of flat-term K-flat
complexes to this restriction: its two conclusions give pullKFlat and pullFlat.

For M on the open and N on the ambient site, transpose unit_M tensor identity
followed by pullTensor inverse under the native extension adjunction. The
localized extension/tensor formula of 0E8I identifies this map with the inverse
of the projection isomorphism. Indeed both adjuncts send a pure tensor to the
unit insertion of its first factor tensored with the second factor. This
proves ordinaryInverse. Naturality of the unit and pullTensor, and injectivity
of the adjunction Hom equivalence, give ordinaryNaturality.

In total degree k, take the direct sum over a+b=k of the ordinary comparison.
Extension preserves these sums because it is a left adjoint. Define the inverse
by the direct sum of the inverses. Naturality of the ordinary comparison for
the two differentials shows that these maps commute with d tensor 1 and with
(-1)^a times 1 tensor d, hence are inverse chain maps. Their definition on
coproduct insertions proves summand; ordinary naturality on each insertion
proves chainNaturality. This is the totalization argument of 0GL1/012Z.

Fix n throughout and use the constant sheaf of compactSupportSystemLevel l E n.
The transported functors are StrictTower.moduleJ and modulePullback, and the
constant-section identification is StrictTower.constantRingIso. Thus the
section equation is exactly the one specified by finitePullSection. This
construction needs neither a sequence-site datum nor compatibility between
different n. The case n=0 is the first positive quotient, not a zero-th power.
The empty open and the zero coefficient ring satisfy the same formulas. -/
theorem nativeOpenTensor_finite_exists {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    ∃ Dn : NativeOpenTensorPrimitives.FiniteOpenCochainsData l E j n, True := by
  sorry

end WeilConjectures.CoefSupportOpenTensor
