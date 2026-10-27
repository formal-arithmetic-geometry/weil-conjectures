/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.IntegralStratumHomFormula
public import Sheaf.AlgebraicGeometry.CohomologicalDimension

/-!
# The sections bound for the integral derived dual on classical torsion sheaves

Source: blueprint `sk-lem-int-ext.proof.md`, paragraph (2), finite-reduction bullets.
(blueprint: lem-sf-integral-dual-torsion-heart-sections).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- On a classical prime-power torsion heart object, tensor by the derived dual of a
finite constant integral local model followed by derived sections has amplitude `[0,s+1]`.
The target sheaf need not be constructible or annihilated by one uniform prime power.

Source: blueprint `sk-lem-int-ext.proof.md`, paragraph (2), second and third bullets;
`lem-sf-integral-stratum-reduction-ext-bound`, steps 4 and 8--9;
Stacks Tags 08JJ, 099Y and 08J5.
(blueprint: lem-sf-integral-dual-torsion-heart-sections).

Proof: resolve each finite constant local model of L by two finite free integral
modules. Termwise duality identifies its derived dual with the dual resolution in
[0,1]. Hence its tensor with any heart object has cohomology only in [0,1]. First
suppose F is killed by a fixed prime power. The corresponding uniformizer quotient
of the dual has a bounded finite-free constant local model, hence is constructible
and classical by finite-coefficient comparison. Descend this dual and F to the etale
site; finite Tor comparison and the tensor pullback comparison identify their tensor
with the actual integral tensor after restriction of scalars. Thus its cohomology
is classical and torsion. For general F, use the exact filtered colimit of its
prime-power kernels: derived tensor and comparison inverse image preserve this
colimit, so the same classicality and torsion assertions hold. This uses no inverse
limit. For each of the two cohomology sheaves, module sections and abelian sections
agree by the forgetful derived-pushforward comparison, checked at each finite scalar
level; the absolute cd definition bounds their sections in [0,s]. The two truncation
triangles, shift compatibility and the long exact cohomology sequence give [0,s+1]
for the tensor complex. The zero sheaf, zero model and empty S give zero complexes. -/
theorem integral_dual_torsion_heart_sections
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S)
    (hmodel : HasFiniteConstantLocalModel (integralCoefficientRing l E) S L)
    (s : ℕ)
    (hs : (s : WithTop ℕ) = cohomologicalDimension l (Fact.out : l.Prime) S)
    (F : pulledBackModuleObjects (integralCoefficientRing l E) S)
    (hF : IsClassicalAbelian F.X)
    (htors : IsEllPowerTorsion l (Fact.out : l.Prime) F.X) :
    ∀ q : ℤ, q < 0 ∨ (s : ℤ) + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
        ((integralStratumDerivedSections l E S).obj
          ((integralStratumDualTensor l E S L).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
