/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-!
# Lifting compatible derived maps of sequential towers

Source: Stacks Project, Injectives, Tag 079P, and Derived Categories, Tag 070I;
sequential homotopy correction as written in the DAG proof
(blueprint: lem-weil-pbc-sequential-tower-evaluation-full).

The natural-number index `n` denotes the positive level `n + 1` of the source.
-/

@[expose] public section

universe u wA wB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {τ : GrothendieckTopology C}
  (R : Sheaf τ RingCat.{u})
  [HasDerivedCategory.{wA} (ringedSiteModules.{u} R)]
  [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)]

/-- Exact evaluation of a strict tower induces evaluation on its derived category.
Source: Stacks Project, Derived Categories, Tag 05RU, and the levelwise exactness of
functor categories (blueprint: lem-weil-pbc-sequential-tower-evaluation-full).
Here `n` denotes positive level `n + 1`. -/
noncomputable abbrev sequentialTowerDerivedEvaluation (n : ℕ) :
    DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ⥤
      DerivedCategory (ringedSiteModules.{u} R) :=
  ((evaluation ℕᵒᵖ (ringedSiteModules.{u} R)).obj (op n)).mapDerivedCategory

/-- The canonical derived transition from level `n + 2` to level `n + 1`.
Source: Stacks Project, Derived Categories, Tags 05RU and 08TC
(blueprint: lem-weil-pbc-sequential-tower-evaluation-full).
This is the localization lift of the degreewise tower transition, using the canonical
factorizations of the exact evaluation functors. No arbitrary transition is chosen. -/
noncomputable def sequentialTowerDerivedTransition (n : ℕ) :
    sequentialTowerDerivedEvaluation R (n + 1) ⟶ sequentialTowerDerivedEvaluation R n :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) (ComplexShape.up ℤ))
    _ _ (sequentialTowerDerivedEvaluation R (n + 1)) (sequentialTowerDerivedEvaluation R n)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (ringedSiteModules.{u} R)).map (homOfLE (Nat.le_succ n)).op)
        (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- Compatible derived evaluation maps lift to a map of strict derived towers; every
levelwise invertible lift is invertible. Source: Stacks Project, Injectives, Tag 079P,
and Derived Categories, Tag 070I, with the sequential correction argument below
(blueprint: lem-weil-pbc-sequential-tower-evaluation-full).

Proof plan:
1. Represent `X,Y` by strict tower complexes `P,V`. The small module diagram category
is Grothendieck abelian by `lem-weil-pbc-small-module-diagrams-grothendieck`. Resolve `V`
by a K-injective tower complex `J` with injective tower objects in each degree, using
`lem-pur-kinjective-degreewise-existence`. Exact evaluation preserves quasi-isomorphisms
by `lem-weil-tower-category-levelwise-abelian`; transport the specified maps to `P_n,J_n`.
2. For an injective tower `T`, extend the map from the staircase `L_n(T_n)` to `T` across
its monic inclusion into `L_{n+1}(T_n)` by `def-sp-injective-resolutions`. At level `n`
this extension is the identity, so its next component splits `T_{n+1} → T_n`.
Choose these sections in every degree of `J`, without requiring differential compatibility.
3. By `lem-weil-tower-evaluation-kinjective`, each `J_n` is K-injective. The bijection
`lem-weil-pbc-kinjective-hom-derived` represents each specified map by a chain map `a_n`
and makes each adjacent commutation defect null-homotopic.
4. Inductively set `b_0 = a_0`. Given `b_n`, choose a homotopy `H` for
`t a_{n+1} - b_n t`, lift it degreewise using the sections, and subtract
`d H̃ + H̃ d` from `a_{n+1}`. This is a null-homotopic chain-map correction. Since
`t H̃ = H` and `t` commutes with differentials, the corrected map commutes strictly
with the adjacent transition and still represents the prescribed derived map.
5. Adjacent commutation implies all naturality equations. Assemble the corrected maps
into a strict tower chain map, localize, and transport back to `X,Y` by
`def-weil-abstract-derived-category`. Its evaluations are the prescribed maps.
Individual homotopies need not assemble into a tower homotopy; no uniqueness is claimed.
6. For ANY lift with invertible evaluations, represent it by a chain map into `J`
using `lem-weil-pbc-kinjective-hom-derived` in the tower category. All evaluated cohomology
maps are invertible. Cohomology is levelwise by `lem-weil-tower-category-levelwise-abelian`,
and component inverses are natural. Thus the tower chain map is a quasi-isomorphism,
so its localization, and hence the lift, is invertible. -/
theorem sequentialTowerEvaluation_full
    (X Y : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{u} R))
    (f : ∀ n : ℕ, (sequentialTowerDerivedEvaluation R n).obj X ⟶
      (sequentialTowerDerivedEvaluation R n).obj Y)
    (hf : ∀ n : ℕ, f (n + 1) ≫ (sequentialTowerDerivedTransition R n).app Y =
      (sequentialTowerDerivedTransition R n).app X ≫ f n) :
    (∃ g : X ⟶ Y, ∀ n : ℕ, (sequentialTowerDerivedEvaluation R n).map g = f n) ∧
    (∀ g : X ⟶ Y, (∀ n : ℕ, (sequentialTowerDerivedEvaluation R n).map g = f n) →
      (∀ n : ℕ, IsIso (f n)) → IsIso g) := by
  sorry

end CategoryTheory
