/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleContinuousCohomologyLimit
public import WeilConjectures.AlgebraicGeometry.MilnorTower

/-!
# Continuous pro-étale cohomology

Source: Weil conjectures blueprint, latest, sec-proetale-coefficients,
`sk-prop-pe-continuous-cohomology`; Stacks Project, Tags 0CQD and 07KY.
(blueprint: sk-prop-pe-continuous-cohomology).

The `milnorTowerCokernel` in the statement is the canonical cokernel model for
`lim^1` of a tower of abelian groups.  The derived-limit predicate in the
first clause is the one already used by
`continuousCohomology_limit`.
-/

@[expose] public section

set_option autoImplicit false

universe t w w'

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ProEtale

/-- The comparison, Milnor exact sequence, naturality, and finite-level vanishing
for an epimorphic inverse system of abelian sheaves on the small pro-étale site.

Proof (source: blueprint `sk-prop-pe-continuous-cohomology.proof.md`):
1. Apply `continuousCohomology_limit` to the epimorphic tower at the terminal
   object `Scheme.ProEt.mk (𝟙 X)`.  Its second conclusion is the displayed
   derived-global-sections versus derived-inverse-limit comparison.
2. Apply the Milnor short-exact construction to the resulting derived-limit
   triangle.  In degree `q`, its left endpoint is the cokernel of `1 - T` on
   the product of the `H^(q-1)` groups, namely `milnorTowerCokernel`; its maps
   are `milnorTowerCokernelMap` and `limMap`, giving the two naturality squares.
3. For a tower of finite `(q-1)`-st cohomology groups, descending images
   stabilize, so the same `1 - T` map is epi and its cokernel is zero; the
   right map in the short exact sequence is consequently an isomorphism.
The sentence that the first term can be nonzero records that epimorphic sheaf
transitions do not imply surjectivity on cohomology and imposes no extra
hypothesis.
(blueprint: sk-prop-pe-continuous-cohomology).
-/
theorem continuousCohomology
    (X : Scheme.{t})
    [HasDerivedCategory.{w} (continuousCohomologyAbelianSheaves X)]
    [HasDerivedCategory.{w'} AddCommGrpCat.{t + 1}]
    (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
    (ht : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) :
    IsDerivedLimit
        (K := fun n : ℕ ↦
          (continuousCohomologyGlobalSections X).obj (F.obj (op n)))
        (fun n : ℕ ↦ (continuousCohomologyGlobalSections X).map
          (F.map (homOfLE (Nat.le_succ n)).op))
        ((continuousCohomologyGlobalSections X).obj (limit F)) ∧
      ∀ q : ℤ,
        ∃ (a : ∀ (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (_ : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)),
            milnorTowerCokernel
                (F ⋙ continuousCohomologyGlobalSections X ⋙
                  DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} (q - 1)) ⟶
              (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q).obj
                ((continuousCohomologyGlobalSections X).obj (limit F)))
          (b : ∀ (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (_ : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)),
            (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q).obj
                ((continuousCohomologyGlobalSections X).obj (limit F)) ⟶
              limit (F ⋙ continuousCohomologyGlobalSections X ⋙
                DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q)),
          (∀ (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)),
            ∃ h : a F hF ≫ b F hF = 0,
              (ShortComplex.mk (a F hF) (b F hF) h).ShortExact) ∧
          (∀ (F G : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op))
            (hG : ∀ n : ℕ, Epi (G.map (homOfLE (Nat.le_succ n)).op))
            (f : F ⟶ G),
            milnorTowerCokernelMap
                (Functor.whiskerRight
                  (Functor.whiskerRight f (continuousCohomologyGlobalSections X))
                  (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} (q - 1))) ≫
                a G hG =
              a F hF ≫
                (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q).map
                  ((continuousCohomologyGlobalSections X).map (limMap f)) ∧
            (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q).map
                  ((continuousCohomologyGlobalSections X).map (limMap f)) ≫
                b G hG =
              b F hF ≫ limMap
                (Functor.whiskerRight
                  (Functor.whiskerRight f (continuousCohomologyGlobalSections X))
                  (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q))) ∧
          (∀ (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) (n : ℕᵒᵖ),
            b F hF ≫ limit.π
                (F ⋙ continuousCohomologyGlobalSections X ⋙
                  DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q) n =
              (DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} q).map
                ((continuousCohomologyGlobalSections X).map (limit.π F n))) ∧
          (∀ (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
            (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)),
            (∀ n : ℕᵒᵖ, Finite
              ((F ⋙ continuousCohomologyGlobalSections X ⋙
                DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} (q - 1)).obj n)) →
            IsZero (milnorTowerCokernel
              (F ⋙ continuousCohomologyGlobalSections X ⋙
                DerivedCategory.homologyFunctor AddCommGrpCat.{t + 1} (q - 1)))) := by
  sorry

end AlgebraicGeometry.ProEtale
