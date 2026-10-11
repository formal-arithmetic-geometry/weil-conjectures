/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Single-complex criterion for derived direct-image base change

Source: Stacks Project, perfect.tex, Tags 0DJ8, 0DJ9 and 0DJA(1)
(blueprint: lem-pc-rf-base-change-single-complex-criterion).
-/

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false
namespace AlgebraicGeometry

/-- The single-complex base-change criterion, with G an actual bounded-above
complex of quasi-coherent modules and its ordinary termwise tensor pullback.

Proof (the three steps of the node):
1. Apply lem-pc-rf-single-complex-inherited-tensor-condition (Tag 0DJA(1)) to
   K = Q(G), K' = Q(g'^*G), and the canonical left-derived counit at G.
   The stated stalk hypothesis therefore holds for E tensor-derived Q(G),
   with comparison to Lg'^*E tensor-derived Q(g'^*G).
2. Apply lem-pc-rf-single-complex-qcqs-induction (Tag 0DJ9) to these two
   tensor objects. Quasi-coherence follows from termwise quasi-coherence of
   G, pullback preserving quasi-coherence, and derived tensor preserving it.
   The inherited stalk condition implies invertibility of the composite.
3. The composite is exactly the canonical base-change map: first use the
   recorded derived base-change map, then the canonical derived tensor
   comparison τ (pinned by its uniquely characterising predicate
   `IsCanonicalPullbackTensorComparison`), followed by tensoring the
   left-derived counit at G with Lg'^*E.
Source: Stacks Project, perfect.tex, Tags 0DJ8, 0DJ9 and 0DJA(1)
(blueprint: lem-pc-rf-base-change-single-complex-criterion). -/
theorem singleComplexBaseChangeCriterion
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hG_bound : ∃ b : ℤ, G.IsStrictlyLE b)
    (hG_qcoh : ∀ i : ℤ, (G.X i).IsQuasicoherent)
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq
      (DerivedCategory.Q.obj G)
      (DerivedCategory.Q.obj
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj G))
      ((SingleComplexBaseChange.counit g').app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj G)))
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback g').obj (A ⊗ B) ⟶
        (derivedPullback g').obj A ⊗ (derivedPullback g').obj B)
    (hτ : IsCanonicalPullbackTensorComparison g' τ) :
    IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w (E ⊗ DerivedCategory.Q.obj G) ≫
      (schemeDerivedDirectImage f').map
        (τ E (DerivedCategory.Q.obj G) ≫
          (derivedPullback g').obj E ◁ (SingleComplexBaseChange.counit g').app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj G))) := by
  sorry

end AlgebraicGeometry
