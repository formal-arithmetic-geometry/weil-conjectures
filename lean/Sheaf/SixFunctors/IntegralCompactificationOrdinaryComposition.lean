/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.SixFunctors.CompletedShriekCompositionLaws
public import Sheaf.Paper.QcqsCompactSupportRealization
public import WeilConjectures.Compactification.Triangle

/-! # Ordinary integral compactification composition

Source: blueprint fix-lem-exchanges Step 5; Stacks 0941 and 0F7B--0F7D
(blueprint: def-sf-integral-ordinary-compactification-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralCompactificationBridge
open IntegralSystemRealization

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

/-- Ordinary compact-support composition in the published integral coordinates.
Every factor is a natural transformation, so naturality is part of the construction.
Source: Stacks 0F7B--0F7D; blueprint fix-lem-exchanges Step 5
(blueprint: def-sf-integral-ordinary-compactification-composition). -/
def ordinaryComparison {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (r : Realizations l E D o) (t : Compactification.Triangle f g)
    [QuasiCompact t.cf.i] [QuasiCompact t.cg.i] [QuasiCompact t.q] :
    (sfCompactSupportFiniteIntegralFunctor l k hl t.cf E ⋙
      sfCompactSupportFiniteIntegralFunctor l k hl t.cg E) ⋙
        (sfIntegralConstructible l E Z).ι ⟶
    sfCompactSupportFiniteIntegralFunctor l k hl t.cfg E ⋙
        (sfIntegralConstructible l E Z).ι :=
  whiskerLeft (sfCompactSupportFiniteIntegralFunctor l k hl t.cf E)
    (sfQcqsCompactSupportRealization l E k hl t.cg).inv ≫
  whiskerRight (sfQcqsCompactSupportRealization l E k hl t.cf).inv
    (ringedOpen l E t.cg.i ⋙ ringedPush l E t.cg.g) ≫
  whiskerLeft (sfIntegralConstructible l E X).ι (completedShriekIntegralA l E r t) ≫
  (sfQcqsCompactSupportRealization l E k hl t.cfg).hom

end Integral
end WeilConjectures.IntegralCompactificationBridge
