/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
import Sheaf.Paper.SmoothPurityTowerLevels
import Sheaf.Paper.ConstantModelTorAmplitude
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.SmoothPurityCoefficientTowers
import Sheaf.Paper.CompactSupportUniformTorBound

/-!
# Compactly supported direct image preserves constructible towers

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
statement and proof (blueprint: sk-lem-sp-tower-bound).

The sequence-site presentation is transported along its section-normalized equivalence
with the recorded coefficient towers. All natural indices denote the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary derived equivalence induced by the section-normalized presentation.
Source: blueprint, coefficient towers and compactification composite
(blueprint: sk-lem-sp-tower-bound). -/
def spTowerShriekRealization (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) :
    spDerivedCoefficientTowers l E T D ≌ SpTowerShriek.D l E T :=
  letI := D.hasDerived
  letI := b.realizationAdditive T
  (b.realization T).mapDerivedCategory

/-- The actual compactification operation, in the recorded coefficient-tower category.
It is exact termwise open extension followed by total derived proper direct image,
transported by the section-normalized equivalences on source and target.
Source: blueprint, displayed definition of Rf_!,bullet
(blueprint: sk-lem-sp-tower-bound). -/
def spTowerCompactSupport (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DX : SpCoefficientTowersAbelian l E X) (DY : SpCoefficientTowersAbelian l E Y) :
    spDerivedCoefficientTowers l E X DX ⥤ spDerivedCoefficientTowers l E Y DY :=
  (spTowerShriekRealization l E b X DX).functor ⋙ SpTowerShriek.F l E b o c ⋙
    (spTowerShriekRealization l E b Y DY).inverse

/-- Compact support preserves the unnormalized constructible finite-Tor tower category.
The first clause gives the bounded-below domain and codomain of the displayed functor;
the second is its natural level identification; the third is preservation of Dctf.
Both smooth pure dimension d and the stated general fibre bound are included.

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
statement and the uniform-interval proof (blueprint: sk-lem-sp-tower-bound).

Proof:
1. By sk-def-sp-normalized-towers choose uniform Tor bounds [a,b] on the input.
Test det-def-sfb-constructible-tor-amplitude with the coefficient module itself:
its cohomology vanishes outside [a,b]. Kernels and cokernels of the towers are
componentwise by sk-def-sp-coefficient-towers, so cohomology is componentwise.
Thus the tower is bounded below. The exact section-normalized presentation
preserves this conclusion and all its level cohomology.
2. Apply det-sp-tower-shriek-levels, clause (1), to the chosen compactification.
Its Fcomparison identifies every level naturally with finite-coefficient Rf_!.
Exact open extension and bounded-below right derivation preserve a lower bound;
transport by the exact presentation gives the first two clauses below.
3. Apply det-sp-tower-bound-uniform to each input level. The ramification formula
ell = unit times uniformizer^e, e > 0, identifies the actual ell-power quotient
with the finite uniformizer-power quotient of exponent e(n+1). It is killed by
ell^(n+1). The geometric hypotheses bound the fibres of f itself. In the smooth
case pure relative dimension d gives that bound. The finite theorem gives output
constructibility and Tor interval [a,b+2d], independent of n.
4. Test the output Tor interval with its degree-zero tensor unit: output cohomology
also vanishes outside [a,b+2d]. This supplies exactly the uniform cohomological and
Tor intervals in spConstructibleTorTowers. Normalization is never used. -/
theorem sp_tower_bound
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hlp : l ≠ p)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (d : ℕ) (_hd : SmoothOfRelativeDimension d f.left ∨
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ Y.left),
        topologicalKrullDim (pullback f.left s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (c : Compactification f.left)
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (DX : SpCoefficientTowersAbelian l E X.left)
    (DY : SpCoefficientTowersAbelian l E Y.left) :
    (∀ C : spDerivedCoefficientTowers l E X.left DX,
      (∃ a : ℤ, @DerivedCategory.IsGE (spCoefficientTowers l E X.left) _ _ DX.hasDerived C a) →
      ∃ a : ℤ, @DerivedCategory.IsGE (spCoefficientTowers l E Y.left) _ _ DY.hasDerived
        ((spTowerCompactSupport l E b o c DX DY).obj C) a) ∧
    (∀ n : ℕ, Nonempty
      (@DerivedCategory.Plus.ι (spCoefficientTowers l E X.left) _ _ DX.hasDerived ⋙
          spTowerCompactSupport l E b o c DX DY ⋙ spDerivedCoefficientEvaluation l E Y.left DY n ≅
        @DerivedCategory.Plus.ι (spCoefficientTowers l E X.left) _ _ DX.hasDerived ⋙
          spDerivedCoefficientEvaluation l E X.left DX n ⋙ SpTowerShriek.finiteF l E b c n)) ∧
    (∀ C : spDerivedCoefficientTowers l E X.left DX,
      spConstructibleTorTowers l E X.left DX C →
      (∃ a : ℤ, @DerivedCategory.IsGE (spCoefficientTowers l E X.left) _ _ DX.hasDerived C a) ∧
      spConstructibleTorTowers l E Y.left DY ((spTowerCompactSupport l E b o c DX DY).obj C)) := by
  sorry

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
