/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q51
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Nilpotent
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Nilpotence and extension of the ground field

Source: Milne, Algebraic Groups (2017), Definition 6.24, Remark 6.25, p.131,
Definition 6.34, Remark 6.35, Proposition 6.38, p.133, and Propositions 2.46--2.48,
pp.54--55; agent synthesis for scalar extension of the descending central series
(blueprint: lem-sfb-nilpotence-field-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Nilpotence of a smooth connected affine finite-type group is invariant under
arbitrary extension of its ground field.
Source: Milne, Definition 6.24, Remark 6.25, Proposition 6.38 and Proposition 2.47;
agent synthesis of these results, with faithful-flat injectivity from Stacks 05CK
(blueprint: lem-sfb-nilpotence-field-extension).

Proof:
1. Set C₀ = G and Cⱼ₊₁ = [G,Cⱼ] by
   lem-sfb-smooth-connected-relative-commutator. Each Cⱼ is a smooth connected
   normal closed subgroup, and Cⱼ₊₁ is contained in Cⱼ. Its minimality is among
   all closed subgroups containing the commutators, with no regularity assumption.
2. The commutator map G × Cⱼ → G has affine finite-type source, by
   lem-weil-pbc-fibre-product-affine-spectra and
   lem-sfb-finite-type-composition-base-change. It sends the rational identity
   pair to the identity. Normality gives c(g,h)⁻¹ = c(g⁻¹,ghg⁻¹), so its image
   is inversion stable on every algebra. Containment in a closed subgroup is
   equivalent to factorization, by testing the universal point of G × Cⱼ
   (def-weil-affine-spectrum, def-weil-closed-immersion). Thus
   lem-sfb-pointed-generated-subgroup-field-extension shows that (Cⱼ₊₁)_K is
   minimal among closed subgroups containing the base-changed commutator map.
   Products and group operations commute with base change (def-pc-base-change).
3. A nilpotent series over k base changes to one over K: closed immersions are
   preserved by lem-weil-pbc-proper-fp-permanence, and on every K-algebra its
   points, normality, and commutator inclusions are the same after restriction
   to k-algebras (def-sc-group-scheme-subgroup). Its endpoints remain G_K and 1.
4. Conversely suppose H₀ through Hₛ is a nilpotent series over K. Inductively
   (Cⱼ)_K is contained in Hⱼ: the commutator condition and the universal-point
   test give factorization through Hⱼ₊₁, then the minimality from step 2 gives
   (Cⱼ₊₁)_K ⊆ Hⱼ₊₁. Hence (Cₛ)_K = 1. No smoothness or connectedness of the
   competing Hⱼ is needed.
5. Write Cₛ = Spec B with identity augmentation ε : B → k. The affine-product
   lemma identifies its extension with Spec (B ⊗ K). Since the extended identity
   is an isomorphism, (b - ε(b)1) ⊗ 1 = 0. The extension is faithfully flat by
   lem-sfb-nonzero-field-algebra-faithfully-flat; tensor injectivity from
   lem-weil-pbc-faithfully-flat-universally-injective gives b = ε(b)1.
   Thus Cₛ = 1 and the Cⱼ form a nilpotent series over k. For s = 0 the same
   argument gives G = 1, so zero-length series are included. -/
theorem isNilpotentGroupScheme_iff_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : Grp (Over (Spec (.of k))))
    (haff : IsAffine G.X.left)
    (hft : LocallyOfFiniteType G.X.hom) (hqc : QuasiCompact G.X.hom)
    (hsm : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left) :
    IsNilpotentGroupScheme G ↔
      IsNilpotentGroupScheme
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj G) := by
  sorry

end AlgebraicGeometry
