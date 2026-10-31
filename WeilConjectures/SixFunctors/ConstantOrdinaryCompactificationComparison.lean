/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralCompactificationOrdinaryComposition
public import WeilConjectures.SixFunctors.IntegralCompactificationComparisonData

/-! # Constant words and ordinary integral composition

Source: blueprint fix-lem-exchanges Step 5; Stacks 0941 and 0F7B--0F7D
(blueprint: lem-sf-constant-ordinary-compactification-comparison).
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

section Integral
variable (k : Type u) [Field k] (hl : IsUnit (l : k))
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y ⟶ Z}
  [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [g.IsOver (Spec (.of k))] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

/-- Constant-word composition is the image of ordinary completed-ring composition.
This comparison involves no semilinear system operation or reduction-limit counit.

Source: blueprint fix-lem-exchanges Step 5; Stacks 0941 and 0F7B--0F7D;
bridge proof Steps 1, 4, 6 and the constant-coefficient part of Step 7
(blueprint: lem-sf-constant-ordinary-compactification-comparison).

Proof: restrict completed-ring direct image and open extension to constant scalars,
using the section-normalized direct comparison and the inverse-image mate for open
extension. The completion unit gives the open sigma. Reduction of that unit followed
by the one-letter q cancels the inverse reduced unit. The proper q is the
counit-tensor comparison; its adjunct is the universal direct-image/limit map.
For each of the three compactifications, apply these two generator calculations in
order. The recursive q formula for the concatenated word then identifies its a
with the composite of the two single-word comparisons and the intermediate
completion counit. Apply the normalized proper/open mate to the same square:
coefficient restriction preserves its inverse-image square, clopen projection,
unit and counit. Mate pasting therefore preserves gamma, and adjunction conjugation
preserves the direct and open compositors, including t.i_q and t.p_g. Thus the
constant beta is the restriction of completedShriekIntegralA, with exactly the site-model
transports in its definition. Substitute these generator and beta equalities in
constantComparison. The three projection-normalized compact-support realization
isomorphisms are the factors of ordinaryComparison, so cancellation gives the
asserted equality. Completeness of each open output justifies the inverse completion
units; the stated finite-Tor conditions stay in the input generator domains.
For an identity letter this is the unit/counit triangle identity, and for an empty
open or zero object it is the unique zero map. All calculations are on actual
strict derived towers, before finite evaluation. -/
theorem constantOrdinaryCompactificationComparison
    {D : FiniteFieldDatum.{u}} {o : IntegralSystemRealization.Operations l E}
    (r : Realizations l E D o) (t : Compactification.Triangle f g)
    [QuasiCompact t.cf.i] [QuasiCompact t.cg.i] [QuasiCompact t.q]
    (af : sfCbcModelExtension t.cf.i (constantRing l E) ⊣
      (sfCbcMorphism t.cf.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ag : sfCbcModelExtension t.cg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ah : sfCbcModelExtension t.cfg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cfg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (K : sfIntegralConstructibleCategory l E X)
    (_hK : finiteTorConstructibleIntegral l E X K.obj)
    (_hF : finiteTorConstructibleIntegral l E Y
      ((sfCompactSupportFiniteIntegralFunctor l k hl t.cf E).obj K).obj)
    (_hf : sfIntegralConstructible l E t.cf.Z ((ringedOpen l E t.cf.i).obj K.obj))
    (_hg : sfIntegralConstructible l E t.cg.Z ((ringedOpen l E t.cg.i).obj
      ((sfCompactSupportFiniteIntegralFunctor l k hl t.cf E).obj K).obj))
    (_hh : sfIntegralConstructible l E t.cfg.Z ((ringedOpen l E t.cfg.i).obj K.obj)) :
    (H l E Z).map ((ordinaryComparison l E k hl r t).app K) =
      constantComparison l E k hl t af ag ah K := by sorry

end Integral
end WeilConjectures.IntegralCompactificationBridge
