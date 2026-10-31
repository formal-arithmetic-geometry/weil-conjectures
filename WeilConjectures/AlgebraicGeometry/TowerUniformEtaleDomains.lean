/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerP1CtfData
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections

/-! # Uniform towers have bounded-below etale origins -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerP1Uniform

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Uniformly bounded constructible towers lie in the bounded-below etale-origin
subcategory, in the section-normalized presentation, on any scheme.

Source: Stacks Tag 09AL, lemma-compare-constructible-derived; the domain argument in
step 2 of lem-sp-tower-p1-uniform-ctf-domains.
(blueprint: lem-sp-uniform-tower-etale-domains)

Proof: choose the common lower cohomological bound r from the tower predicate.
Exact level evaluation commutes with homology. A tower whose levels are zero is zero:
its section modules at every pair (n,U) are zero. Thus all homology towers below r
vanish. The exact realization equivalence preserves this lower bound.
For each n, finiteRing_constructibleDerived_origin applied to the bounded constructible
intrinsic level supplies an etale complex L and its comparison isomorphism. Its bounded
cohomology makes L bounded below. Factor intrinsic comparison through fixed-coefficient
comparison and the canonical constant-ring realization equivalence. The realization
counit, together with the section-normalized evaluation comparison, identifies that
image with the nth evaluation of the realized tower. Package its fixed-coefficient
comparison image as the bounded-below level and retain (L,alpha) as the origin witness.
Each n is treated separately; no compatible choice of etale antecedents is required.
The argument works for the zero tower and for an empty scheme. -/
theorem uniformTower_etale_domains
    (base : SpTowerShriek.Base l E) (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T)
    (K : spDerivedCoefficientTowers l E T D)
    (hK : spConstructibleTorTowers l E T D K) :
    (∃ a : ℤ, DerivedCategory.IsGE
      ((spTowerShriekRealization l E base T D).functor.obj K) a) ∧
    ∀ n : ℕ, Nonempty (SpTowerShriek.Origin l E base T n
      ((spTowerShriekRealization l E base T D).functor.obj K)) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerP1Uniform
