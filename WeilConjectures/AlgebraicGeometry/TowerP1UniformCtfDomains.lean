/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerP1CtfData
import WeilConjectures.AlgebraicGeometry.TowerUniformEtaleDomains
import WeilConjectures.AlgebraicGeometry.TowerP1ProperCtf
import WeilConjectures.AlgebraicGeometry.TowerP1LevelCtfModel

/-! # Uniform constructible finite-Tor domains for the projective-line tower functors

Source: the standing-setting restriction and Levels of the projective-line tower proof.
The definitions are re-exported unchanged from TowerP1CtfData. -/

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

private theorem bounds_of_constructibleTor (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (K : spDerivedCoefficientTowers l E T D)
    (hK : spConstructibleTorTowers l E T D K) :
    ∃ r s a b : ℤ, r ≤ s ∧ a ≤ b ∧ bounds l E T D K r s a b := by
  obtain ⟨r, s, a, b, hrs, hab, h⟩ := hK.2
  refine ⟨r, s, a, b, hrs, hab, fun n ↦ ?_⟩
  exact ⟨(DerivedCategory.isGE_iff _ r).2 (fun i hi ↦ (h n).1 i (.inl hi)),
    (DerivedCategory.isLE_iff _ s).2 (fun i hi ↦ (h n).1 i (.inr hi)),
    (hK.1 n).2.1, (h n).2⟩

private theorem constructibleTor_of_bounds (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (K : spDerivedCoefficientTowers l E T D)
    (r s a b : ℤ) (hrs : r ≤ s) (hab : a ≤ b)
    (hK : bounds l E T D K r s a b) : spConstructibleTorTowers l E T D K := by
  have hv (n : ℕ) (i : ℤ) (hi : i < r ∨ s < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((spDerivedCoefficientEvaluation l E T D n).obj K)) := by
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff _ r).1 (hK n).1 i hi
    · exact (DerivedCategory.isLE_iff _ s).1 (hK n).2.1 i hi
  refine ⟨fun n ↦ ⟨⟨r, s, hrs, hv n⟩, (hK n).2.2.1, a, b, (hK n).2.2.2⟩,
    r, s, a, b, hrs, hab, fun n ↦ ⟨hv n, (hK n).2.2.2⟩⟩

/-- The domain inclusions, the two functor restrictions, the precise shift-two bounds,
and retained global and affine-local models, without normalization or an adjunction.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, standing-setting
restriction; Stacks Tags 09AL, 03TT, 0963, 06YQ
(blueprint: lem-sp-tower-p1-uniform-ctf-domains).

Proof plan:
1. By lem-pur-twist-sheaf-locally-free the ring of integers is finite free over Z_l;
its ell-power quotients are finite Noetherian rings. The projective-space properness
and standard-chart lemmas show q is proper and smooth of pure relative dimension one.
Finite type and separated composition put P in the standing setting; both schemes
are Noetherian by finite type over a field.
2. det-sp-coefficient-towers-abelian computes cohomology levelwise and detects zero.
The uniform lower bound therefore bounds the whole tower below. Apply
lem-weil-pbc-finite-ring-constructible-derived-origin at each level and
lem-weil-pbc-qcqs-over-affine with det-pe-finite-tor-comparison-noetherian to obtain
retained etale origins with the same cohomological and Tor intervals. There is no
compatibility requirement between origins at different levels.
3. Specialize sk-lem-sp-tower-bound to the identity-open compactification of proper q.
det-sp-tower-bound-uniform with d=1 supplies common output bounds [a,b+2], and
constructible finite-Tor levels. Identity extension by zero is the identity.
4. lem-sf-etale-flat-constructible supplies a flat constructible representative in
[a,b]. lem-asd-finite-etale-twist-line trivializes the root line on an etale cover.
lem-sp-etale-pullback-line-flat-model with shift 2 makes the actual pulled-back
line model flat, constructible, supported in [a-2,b-2] and K-flat. Its cohomology
in degree j is q^*H^(j+2) tensor the line, giving [r-2,s-2]. Its prescribed pulled-back
finite locally closed strata and common trivializing covers prove constructibility.
5. lem-coef-semilinear-derived-sections evaluates the tower operations levelwise.
lem-sp-etale-chart-comparison-isos identifies the actual inverse-image, root-line
and shift expressions with the etale model. Exact comparison preserves cohomology;
lem-sf-comparison-pullback-exact and lem-weil-pbc-ringed-topos-flat-module-pullback
preserve the flat terms, and lem-weil-pbc-independent-bounded-flat-kflat gives
K-flatness. The same endpoints work at every level.
6. For an affine open U, lem-weil-pbc-noetherian-open-subscheme-noetherian and the
pullback-line-flat-model lemma with the unit line and shift zero restrict the etale
model to U without changing its intervals. Apply that lemma again to P1_U with the
root line and shift 2. The chart-comparison restriction square identifies this
model with the restriction along ProjectiveSpace.map of the actual output level.
The global construction in steps 4-5 already gives the identical intervals globally.
All bounds are containing bounds; zero objects and empty schemes or opens are allowed.
-/
theorem towerP1_uniform_ctf_domains
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hlp : l ≠ p)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (hS : IsUnit (l : Γ(S, ⊤))) (c : TowerClasses l E S hS)
    (DS : SpCoefficientTowersAbelian l E S)
    (DP : SpCoefficientTowersAbelian l E (ProjectiveLine S)) :
    (∀ (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T),
      (T = S ∨ T = ProjectiveLine S) →
      ∀ K : spDerivedCoefficientTowers l E T D,
        spConstructibleTorTowers l E T D K →
        (∃ a : ℤ, DerivedCategory.IsGE
          ((spTowerShriekRealization l E c.base T D).functor.obj K) a) ∧
        ∀ n : ℕ, Nonempty (SpTowerShriek.Origin l E c.base T n
          ((spTowerShriekRealization l E c.base T D).functor.obj K))) ∧
    (∀ M : spDerivedCoefficientTowers l E (ProjectiveLine S) DP,
      spConstructibleTorTowers l E (ProjectiveLine S) DP M →
      spConstructibleTorTowers l E S DS ((push l E c DS DP).obj M)) ∧
    (∀ K : spDerivedCoefficientTowers l E S DS,
      spConstructibleTorTowers l E S DS K →
      spConstructibleTorTowers l E (ProjectiveLine S) DP ((pullTwist l E c DS DP).obj K)) ∧
    (∀ (K : spDerivedCoefficientTowers l E S DS) (r s a b : ℤ),
      bounds l E S DS K r s a b →
      bounds l E (ProjectiveLine S) DP ((pullTwist l E c DS DP).obj K)
        (r - 2) (s - 2) (a - 2) (b - 2) ∧
      ∀ n : ℕ,
        Nonempty (LocalModel (SpTowerShriek.R l E n) (l ^ (n + 1))
          (SpTowerClasses.coefficient_annihilates l E n) S
          ((spDerivedCoefficientEvaluation l E S DS n).obj K)
          ((spDerivedCoefficientEvaluation l E (ProjectiveLine S) DP n).obj
            ((pullTwist l E c DS DP).obj K)) r s a b) ∧
        ∀ (U : S.Opens), IsAffineOpen U →
          Nonempty (LocalModel (SpTowerShriek.R l E n) (l ^ (n + 1))
            (SpTowerClasses.coefficient_annihilates l E n) U.toScheme
            ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) U.ι).obj
              ((spDerivedCoefficientEvaluation l E S DS n).obj K))
            ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n)
              (ProjectiveSpace.map (ULift.{u} (Fin 2)) U.ι)).obj
                ((spDerivedCoefficientEvaluation l E (ProjectiveLine S) DP n).obj
                  ((pullTwist l E c DS DP).obj K))) r s a b)) := by
  have hlevels (K : spDerivedCoefficientTowers l E S DS) (r s a b : ℤ)
      (hK : bounds l E S DS K r s a b) :
      bounds l E (ProjectiveLine S) DP ((pullTwist l E c DS DP).obj K)
        (r - 2) (s - 2) (a - 2) (b - 2) := by
    intro n
    exact (towerP1_level_ctf_model l E p k _hlp S hS c DS DP K n r s a b (hK n)).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T D _ K hK
    exact uniformTower_etale_domains l E c.base T D K hK
  · intro M hM
    exact towerP1_push_ctf l E p k _hlp S hS c DS DP M hM
  · intro K hK
    obtain ⟨r, s, a, b, hrs, hab, h⟩ := bounds_of_constructibleTor l E S DS K hK
    exact constructibleTor_of_bounds l E (ProjectiveLine S) DP
      ((pullTwist l E c DS DP).obj K) (r - 2) (s - 2) (a - 2) (b - 2)
      (by omega) (by omega) (hlevels K r s a b h)
  · intro K r s a b hK
    refine ⟨hlevels K r s a b hK, fun n ↦ ?_⟩
    exact (towerP1_level_ctf_model l E p k _hlp S hS c DS DP K n r s a b (hK n)).2

end AlgebraicGeometry.ProEtale.SpTowerP1Uniform
