/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerP1CtfData
import WeilConjectures.AlgebraicGeometry.CompactSupportUniformTorBound
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

/-! # Proper projective-line image preserves uniform constructible towers -/

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

/-- Proper direct image along the projective line preserves the unnormalized uniform
constructible finite-Tor tower category.

Source: step 3 of lem-sp-tower-p1-uniform-ctf-domains, sk-lem-sp-tower-bound and
Stacks Tags 01NG, 01V6 and the compact-support uniform Tor bound.
(blueprint: lem-sp-tower-p1-proper-ctf)

Proof: q is proper by projective-space properness. The proved instance
ProjectiveLine.smoothOfRelativeDimension_one gives pure relative dimension one. Both
schemes are separated and of finite type over k. Obtain the base and operations of
tower_shriek_levels, and apply sp_tower_bound with them to the identity-open
compactification of q and the input uniform Tor interval [a,b]. Exact identity extension is
naturally the identity: its adjunction is the identity
adjunction on sections, transported through the ordinary realization.
The section-normalized proper pushforward is identified with that
compactification composite by uniqueness of right adjoints and of total right derived
functors.
Hence its levels are constructible and have Tor interval [a,b+2]. The uniform bound,
tested on the coefficient module itself, gives cohomology in the same interval.
Transport along the exact section-normalized realization and its evaluation
comparisons gives spConstructibleTorTowers in the original coordinates. No reduction
morphism is inverted. Empty schemes and zero objects satisfy the same containing bounds. -/
theorem towerP1_push_ctf
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (hlp : l ≠ p)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (hS : IsUnit (l : Γ(S, ⊤))) (c : TowerClasses l E S hS)
    (DS : SpCoefficientTowersAbelian l E S)
    (DP : SpCoefficientTowersAbelian l E (ProjectiveLine S))
    (M : spDerivedCoefficientTowers l E (ProjectiveLine S) DP)
    (hM : spConstructibleTorTowers l E (ProjectiveLine S) DP M) :
    spConstructibleTorTowers l E S DS ((push l E c DS DP).obj M) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerP1Uniform
