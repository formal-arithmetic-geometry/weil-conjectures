/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralCompactificationBridgeWords
public import WeilConjectures.SixFunctors.ConstantSemilinearGeneratorComparison
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.SfCbcCompactSupportCompositionLimit
public import WeilConjectures.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.SixFunctors.IntegralCompactificationComparisonData
import WeilConjectures.SixFunctors.ConstantOrdinaryCompactificationComparison
import WeilConjectures.SixFunctors.SemilinearOrdinaryCompactificationComparison
import WeilConjectures.SixFunctors.IntegralConstantCompleteTransport

/-! # Integral compactification comparison bridge

Source: blueprint main-20261015, fix-lem-exchanges, proof Step 5; the additional
constant/semilinear comparison obligation
(blueprint: lem-sf-integral-compactification-comparison-bridge).

The helpers fix the small-site coordinate transports by sections and adjunction mates.
The two composition maps are constructed independently, before any finite evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralCompactificationBridge
open IntegralSystemRealization GeneratorReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section FiniteField
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [IsSeparated (Z ↘ Spec (.of D.k))]
  {f : X ⟶ Y} {g : Y ⟶ Z}
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [g.IsOver (Spec (.of D.k))] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

/-- The integral compactification comparison bridge, as equality of actual integral
morphisms, with its naturality on the supplied domain. The definition `completedComparison` uses
exactly the source's coordinate formula,
with the actual recursive strict-word comparison. Full faithfulness on complete
objects uniquely determines its components, independently of the semilinear composite.

Source: blueprint main-20261015, fix-lem-exchanges (2),(4), proof Step 5; the additional
normalization obligation (blueprint: lem-sf-integral-compactification-comparison-bridge).

Proof, Step 1: scalar restriction gives U R = R^T H and H L = L^T U with their actual
units. Step 2: for d : L A -> F, the adjunct of d inverse is e_A R(d inverse);
applying L and composing with the unit gives d inverse by naturality and the triangle.
Step 3: the direct identification for a compactification is the universal proper/limit
comparison followed by the open reduction mate and inverse completion unit, then the
projection-normalized strict-quotient realization. Its adjunct is therefore exactly
r_v = e R(d_v inverse). Step 4: the generator comparison identifies its scalar restriction
with the recursively normalized q for the two-letter word; it uses the same coefficients,
quotient transitions, and completion unit. Step 5: the word adjunct is a_v = H(d_v inverse).
Step 6: recursion for the concatenated word gives H of d_g inverse, followed by L B_g
R(d_f inverse), followed by L B_g(e). Step 7: the proper/open scalar mate and its unit
and counit identify beta with the normalized constant-tower beta, including the unital
compositors. Step 8: substitute these identities in the defining coordinate equation and use
faithfulness of H on
the complete integral source and target. Naturality follows from the naturality of every canonical
factor and uniqueness of the lift under the complete-coefficient equivalence. Step 9: for identity
compactifications the triangles identify
F_id with L R and d_id with its identity; an empty open or zero input gives zero objects
and the unique map between them. No finite evaluation or arbitrary realization is used. -/
theorem integralCompactificationComparisonBridge
    (o : IntegralSystemRealization.Operations l E) (r : Realizations l E D o)
    (t : Compactification.Triangle f g)
    [QuasiCompact t.cf.i] [QuasiCompact t.cg.i] [QuasiCompact t.cfg.i] [QuasiCompact t.q]
    (af : sfCbcModelExtension t.cf.i (constantRing l E) ⊣
      (sfCbcMorphism t.cf.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ag : sfCbcModelExtension t.cg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ah : sfCbcModelExtension t.cfg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cfg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    :
    (∀ (K : sfIntegralConstructibleCategory l E X) (lo hi torLo torHi : ℤ),
      bridgeDomain l E D.k (coefficientPrimeUnit l D hl) o t K lo hi torLo torHi →
      completedComparison l E D.k (coefficientPrimeUnit l D hl) t af ag ah K =
        semilinearComparison l E D.k (coefficientPrimeUnit l D hl) o r t K) ∧
    (∀ (K K' : sfIntegralConstructibleCategory l E X) (m : K ⟶ K')
      (lo hi torLo torHi : ℤ),
      bridgeDomain l E D.k (coefficientPrimeUnit l D hl) o t K lo hi torLo torHi →
      bridgeDomain l E D.k (coefficientPrimeUnit l D hl) o t K' lo hi torLo torHi →
      (sfIntegralConstructible l E Z).ι.map
          ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
            t.cf E ⋙ sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
              t.cg E).map m) ≫
        semilinearComparison l E D.k (coefficientPrimeUnit l D hl) o r t K' =
      semilinearComparison l E D.k (coefficientPrimeUnit l D hl) o r t K ≫
        (sfIntegralConstructible l E Z).ι.map
          ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
            t.cfg E).map m)) := by
  have hs (K : sfIntegralConstructibleCategory l E X) (lo hi torLo torHi : ℤ)
      (hK : bridgeDomain l E D.k (coefficientPrimeUnit l D hl) o t K lo hi torLo torHi) :=
    semilinearOrdinaryCompactificationComparison l E D hl o r t K lo hi torLo torHi hK
  constructor
  · intro K lo hi torLo torHi hK
    let A := (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
      t.cg E).obj
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
          t.cf E).obj K)
    let B := (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
      t.cfg E).obj K
    apply ((integralConstantCompleteTransport l E Z).2 A B).1
    have hc := constantOrdinaryCompactificationComparison l E D.k
      (coefficientPrimeUnit l D hl) r t af ag ah K hK.1.1.1 hK.2.1.1.1
      hK.1.2.1.1.1 hK.2.1.2.1.1.1 hK.2.2.1.2.1.1.1
    exact (completedComparison_existsUnique l E D.k (coefficientPrimeUnit l D hl)
      t af ag ah K).exists.choose_spec |>.trans (hc.symm.trans
        (congrArg ((H l E Z).map) (hs K lo hi torLo torHi hK).symm))
  · intro K K' m lo hi torLo torHi hK hK'
    rw [hs K lo hi torLo torHi hK, hs K' lo hi torLo torHi hK']
    exact (ordinaryComparison l E D.k (coefficientPrimeUnit l D hl)
      r t).naturality m

end FiniteField
end WeilConjectures.IntegralCompactificationBridge
