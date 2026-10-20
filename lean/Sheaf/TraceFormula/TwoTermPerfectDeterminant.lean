/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module
public import Sheaf.TraceFormula.TwoTermPerfectDeterminantData
import Sheaf.TraceFormula.TwoTermPerfectTorWindow
import Sheaf.TraceFormula.TwoTermDeterminantPullbackCoherence
import Sheaf.TraceFormula.AffineTwoTermDeterminant
import Sheaf.TraceFormula.TwoTermDeterminantAffineDescent

/-! # Determinants of two-term perfect complexes

Source: Stacks Project, Tags 0FJI, 0FJM, 0FJX and 0FJY.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
variable [d : ∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The local two-term condition is the perfect Tor window `[-1,0]`, and the
normalized determinant functor exists with coherent arbitrary pullback.
The slice localizations choose presentations of D(O_U); they impose no geometric condition.
Source: Stacks Project, Tags 0FJX and 0FJY, with the affine good-diagram construction
in More on Algebra, Tags 0FJI and 0FJM
(blueprint: lem-trf-two-term-perfect-determinant).

Proof:
1. Apply the proved Tor-window equivalence. Locally trivializing the two terms gives a
finite free K-flat complex supported in the two-term interval, so its tensor has the
required vanishings, which are open-local. Conversely the finite free residue model has
ranks equal to residue Betti numbers; the Tor vanishings kill all terms outside [-1,0].
The same explicit models prove membership of displayed models, zero and arbitrary pullbacks.
2. Identify the section-normalized adjunction with the original tensor adjunction by its
unit on sections. The normalized universal composition lift is therefore the recorded
lift from the original K-flat counits. The existing coherence theorem gives its identity,
unit and associativity comparisons.
3. Apply the affine good-diagram construction: adding a contractible finite free summand
makes both legs surjective quasi-isomorphisms. Their kernel-normalized determinant maps
compose through fibre products; composing with a fixed homotopy inverse gives independence
of diagrams. The split kernel and pure-wedge formulas give arbitrary scalar extension,
including the compatible local exterior, zero and evaluation families.
4. Apply affine descent to this cartesian system. The supplied compatibility equations
make transitions agree on affine refinements of overlaps; effective descent glues objects
and maps. Full faithfulness proves the functor laws and all model, evaluation, naturality
and pullback equations, without requiring affine overlaps or separatedness.
5. Assemble the original record from these data. The identity normalization is the left
unit law of the fixed derived composition comparison, evaluated at the identity morphism.
-/
theorem exists_twoTermPerfectDeterminantData
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    (∀ (X : Scheme.{u}) (L : schemeDerivedCategory X),
      isTwoTermPerfect X L ↔ Scheme.IsPerfect X L ∧
        ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ),
          i < -1 ∨ 0 < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
            (L ⊗ (DerivedCategory.singleFunctor _ 0).obj M))) ∧
      Nonempty (TwoTermPerfectDeterminantData.{u, w}) := by
  obtain ⟨κ⟩ := exists_twoTermDeterminantPullbackCoherence.{u, w}
  obtain ⟨A⟩ := exists_affineTwoTermDeterminantData κ
  obtain ⟨D⟩ := descend_affineTwoTermDeterminantData κ A
  refine ⟨isTwoTermPerfect_iff_perfect_tor, ⟨{
    functor := D.functor
    invertible := D.invertible
    model_mem := twoTermPerfect_model
    modelIso := D.modelIso
    zero_mem := twoTermPerfect_zero
    zeroIso := D.zeroIso
    acyclic := D.acyclic
    pullback_mem := twoTermPerfect_pullback
    pullbackIso := D.pullbackIso
    pullback_naturality := D.pullback_naturality
    derivedId := κ.derivedId
    derivedComp := κ.derivedComp
    derivedComp_normalization := κ.composition_normalization
    derivedId_normalization := fun X ↦ (κ.left_unit (𝟙 X)).symm
    pullback_id := D.pullback_id
    pullback_comp := D.pullback_comp }⟩⟩

end AlgebraicGeometry
