/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.CategoryTheory.RelativeCyclicRestrictionModel
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.CategoryTheory.ProfiniteInvariantsFilteredContinuity
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import Sheaf.CategoryTheory.ArrowExactColimits
import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Filtered colimits of the canonical cyclic comparison

Source: blueprint, six-functors direct-images proof, paragraph (3), filtered passage;
the agent-formulated auxiliary obligation has no exact external reference yet.
(blueprint: lem-sfb-filtered-cyclic-comparison-transfer)

The cyclic total and its normalized comparison are those of the relative cyclic model,
with trivial residual group. All colimit arrows are fixed by their actual coprojections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate)

namespace CategoryTheory.RelativeCyclic

variable (A : CondensedBar.Ring.{u})
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Ordinary derived invariants on modules in degree zero, in the full action category.
Source: blueprint paragraph (3), filtered passage
(blueprint: lem-sfb-filtered-cyclic-comparison-transfer). -/
def cyclicComparisonSource : Equivariant A H ⥤ DerivedCategory.{u + 1} (Modules A) :=
  DerivedCategory.singleFunctor (Equivariant A H) 0 ⋙ CondensedDerivedRestriction.derived A H

/-- The recorded two-column total of the restricted module, forgetting the trivial residual
factor. Its coordinates give N in degrees zero and one, with differential u(1)-1.
Source: blueprint paragraph (3), filtered passage
(blueprint: lem-sfb-filtered-cyclic-comparison-transfer). -/
def cyclicComparisonComplex (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H) :
    Equivariant A H ⥤ CochainComplex (Modules A) ℤ :=
  inflate v ⋙ addTrivialResidual A ⋙
    HomologicalComplex.single (Equivariant A (PUnit.{u + 1} × Z.{u})) (.up ℤ) 0 ⋙
    K.functor ⋙ (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
      (.up ℤ)

/-- QK(N), using the actual cyclic total rather than an unrelated two-term complex.
Source: blueprint paragraph (3), filtered passage
(blueprint: lem-sfb-filtered-cyclic-comparison-transfer). -/
def cyclicComparisonTarget (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H) :
    Equivariant A H ⥤ DerivedCategory.{u + 1} (Modules A) :=
  cyclicComparisonComplex A K v ⋙ DerivedCategory.Q

/-- The scalar canonical comparison: derived cyclic restriction followed by inverse lambda.
The single-complex and trivial-residual identifications are the recorded canonical ones.
By forgetBeta this is exactly c^1 after forgetting the trivial residual action.
Source: blueprint paragraph (3), filtered passage
(blueprint: lem-sfb-filtered-cyclic-comparison-transfer). -/
def cyclicComparison {K : TotalModel A PUnit.{u + 1}}
    (C : HasComparison A PUnit.{u + 1} K) (v : Z.{u} →ₜ* H) (M : Equivariant A H) :
    (cyclicComparisonSource A).obj M ⟶ (cyclicComparisonTarget A K v).obj M :=
  (CondensedDerivedRestriction.groupMap A v).app
      ((DerivedCategory.singleFunctor _ 0).obj M) ≫
    (CondensedDerivedRestriction.derived A Z).map
      (((inflate (R := A.toMon) v).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
    (CondensedDerivedRestriction.derived A Z).map (DerivedCategory.Q.map
      ((HomologicalComplex.single (Equivariant A Z.{u}) (.up ℤ) 0).map
          ((unitResidualIso A).inv.app ((inflate v).obj M)) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (forgetResidual A PUnit.{u + 1} Z) (.up ℤ) 0).inv.app
          ((addTrivialResidual A).obj ((inflate v).obj M)))) ≫
    (forgottenLambda A PUnit.{u + 1} C
      (single A (PUnit.{u + 1} × Z) ((addTrivialResidual A).obj ((inflate v).obj M)))).inv

/-- Cohomology of ordinary derived invariants, in every integer degree.
Source: blueprint paragraph (3), filtered passage
(blueprint: lem-sfb-filtered-cyclic-comparison-transfer). -/
def cyclicSourceCohomology (q : ℤ) : Equivariant A H ⥤ Modules A :=
  cyclicComparisonSource A ⋙ DerivedCategory.homologyFunctor (Modules A) q

/-- Cohomology of the cyclic total, in every integer degree.
Source: blueprint paragraph (3), filtered passage
(blueprint: lem-sfb-filtered-cyclic-comparison-transfer). -/
def cyclicTargetCohomology (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H) (q : ℤ) :
    Equivariant A H ⥤ Modules A :=
  cyclicComparisonTarget A K v ⋙ DerivedCategory.homologyFunctor (Modules A) q

/-- Actual coprojection comparisons for filtered sheaf colimits are invertible, commute
with c = lambda inverse after beta, and transfer invertibility of c from all stages.
The witness m is the colimit of H^q(c_i), characterized by every original coprojection.
Source: blueprint direct-images proof, paragraph (3), filtered passage
(blueprint: lem-sfb-filtered-cyclic-comparison-transfer).

Proof:
1. Apply lem-sfb-profinite-invariants-filtered-continuity. Forgetting creates the sheaf
   colimit with induced action. For q >= 0 its canonical comparison is colimit.post.
2. Equivariance identifies the colimit of the arrows u(1)-1 with the same arrow on the
   sheaf colimit. Exact filtered colimits (lem-pc-module-filtered-colimits-tensor) and
   lem-sfb-arrow-exact-colimits identify kernels and cokernels with their canonical legs.
   These compute degrees zero and one of the cyclic total; all other degrees vanish.
3. The nonnegative bar/resolution total of lem-sfb-condensed-derived-invariant-bar has
   zero negative cohomology. Colimits of zero diagrams are zero, giving both comparisons
   and all four zero objects in negative degrees.
4. Naturality of beta and inverse lambda gives naturality of c at each coprojection.
   Apply H^q and the colimit universal property: the unique map with the displayed legs
   is colim H^q(c_i), and the resulting square commutes in every integer degree.
5. If all c_i are invertible, their inverses are natural and induce the inverse of m.
   The square and the two comparison isomorphisms make H^q(c_colim) invertible for all q.
   DerivedCategory.isIso_iff (lem-weil-pbc-unbounded-derived-iso-cohomology) concludes.
No monic transitions, density, finite generation, completeness or dimension bound enter.
-/
theorem filtered_cyclic_comparison_transfer
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    {K : TotalModel A PUnit.{u + 1}} (C : HasComparison A PUnit.{u + 1} K)
    (v : Z.{u} →ₜ* H) (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (N : I ⥤ Equivariant A H) :
    (∀ q : ℤ,
      IsIso (colimit.post N (cyclicSourceCohomology A q)) ∧
      IsIso (colimit.post N (cyclicTargetCohomology A K v q)) ∧
      (∃ m : colimit (N ⋙ cyclicSourceCohomology A q) ⟶
          colimit (N ⋙ cyclicTargetCohomology A K v q),
        (∀ i : I, colimit.ι (N ⋙ cyclicSourceCohomology A q) i ≫ m =
          (DerivedCategory.homologyFunctor (Modules A) q).map
              (cyclicComparison A C v (N.obj i)) ≫
            colimit.ι (N ⋙ cyclicTargetCohomology A K v q) i) ∧
        colimit.post N (cyclicSourceCohomology A q) ≫
            (DerivedCategory.homologyFunctor (Modules A) q).map
              (cyclicComparison A C v (colimit N)) =
          m ≫ colimit.post N (cyclicTargetCohomology A K v q)) ∧
      (q < 0 →
        IsZero (colimit (N ⋙ cyclicSourceCohomology A q)) ∧
        IsZero ((cyclicSourceCohomology A q).obj (colimit N)) ∧
        IsZero (colimit (N ⋙ cyclicTargetCohomology A K v q)) ∧
        IsZero ((cyclicTargetCohomology A K v q).obj (colimit N)))) ∧
    ((∀ i : I, IsIso (cyclicComparison A C v (N.obj i))) →
      IsIso (cyclicComparison A C v (colimit N))) := by
  sorry

end CategoryTheory.RelativeCyclic
