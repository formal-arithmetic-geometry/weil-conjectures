/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy
public import Sheaf.Algebra.Homology.FilteredTensorGradedComparison
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.Algebra.Homology.FilteredQuasiIsoFractions
import Sheaf.Algebra.Homology.SplitCellComplexKFlat
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Simultaneous K-flat replacement of finite filtered complexes

Source: Stacks Project, More on Algebra, Tag 0H7X (finite-label resolution),
Derived Categories, Tags 05S1 and 05S2, and Categories, Tags 04VI and 04VJ
(blueprint: lem-kun-finite-filtered-kflat-replacement).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable (R : Type u) [CommRing R]

/-- The full subcategory of good objects in the finite filtered homotopy category.
The existing predicate includes flatness of all terms, steps and graded terms, and
K-flatness of their complexes. Source: Stacks, Tags 0H7X and 05S2
(blueprint: lem-kun-finite-filtered-kflat-replacement). -/
abbrev GoodFiniteFilteredModuleHomotopy :=
  ObjectProperty.FullSubcategory
    (fun K : FiniteFilteredModuleHomotopy R ↦ HasKunnethFiltration K.as.obj)

/-- The full inclusion of good filtered complexes, on filtered homotopy classes.
Source: Stacks, Tags 0H7X and 05S2
(blueprint: lem-kun-finite-filtered-kflat-replacement). -/
noncomputable def goodFiniteFilteredModuleInclusion :
    GoodFiniteFilteredModuleHomotopy R ⥤ FiniteFilteredModuleHomotopy R :=
  ObjectProperty.ι (fun K : FiniteFilteredModuleHomotopy R ↦ HasKunnethFiltration K.as.obj)

/-- Filtered quasi-isomorphisms restricted to good complexes.
Source: Stacks, Tags 05S1 and 05S2
(blueprint: lem-kun-finite-filtered-kflat-replacement). -/
def goodFiniteFilteredModuleQuasiIso :
    MorphismProperty (GoodFiniteFilteredModuleHomotopy R) :=
  (finiteFilteredModuleQuasiIso R).inverseImage (goodFiniteFilteredModuleInclusion R)

/-- Simultaneous free K-flat replacement, the inclusion-induced localization equivalence,
and roofs and their equality criterion within good finite filtered complexes.
Source: Stacks, Tags 0H7X, 05S1, 05S2, 04VI and 04VJ, finite-interval specialization
(blueprint: lem-kun-finite-filtered-kflat-replacement).

Proof:
1. For fixed bounds `a < b`, start with a zero-differential free complex on cycles in
   `FʲK`, labelled only by `a ≤ j < b`. Filter by labels `j ≥ i`. This surjects on the
   cohomology of every step, including the underlying complex (label `a`).
2. At stage `m`, for each cycle `z` in a step whose image is a boundary, attach a fresh
   generator of degree one lower with differential `z` and image a chosen preimage of
   that boundary. Index generators by stage as well as degree, label and cycle. The
   inclusions split degreewise, on steps and graded terms; their quotients have zero
   differential and free terms.
3. Take the union. Finite support puts every cycle in one stage; the next stage kills
   each kernel class. Thus the underlying and step maps are quasi-isomorphisms, with
   the same bounds and no bound on cochain degrees.
4. The short exact step/graded sequences and their natural long exact sequences
   (lem-weil-pbc-complex-ses-homology-long-exact and
   lem-weil-pbc-complex-ses-long-exact-naturality) give the graded quasi-isomorphisms
   by the five-lemma diagram chase detailed in the DAG proof.
5. The subsets of generators with label at least `i`, or exactly `i`, give the step
   and graded bases. Free modules are tensor-flat by the finite-support description
   of direct sums. Apply lem-kun-split-cell-complex-kflat to the exhaustive split
   cell filtrations of the underlying, step and graded complexes to obtain goodness.
6. Use lem-kun-filtered-quasi-isomorphism-fractions for ambient right fractions.
   Resolve the intermediate object in each Ore square and cancellation diagram;
   compose its replacement with the ambient denominator. This proves the same
   fraction calculus within the full good subcategory.
7. Every ambient object is isomorphic to its good replacement after localization.
   By lem-pc-right-fraction-representation, every ambient arrow between good objects
   is a roof; resolving its middle object gives a roof entirely in good objects.
8. By lem-pc-right-fraction-common-refinement, equality of two roofs is witnessed by
   a common refinement. Resolve its middle object as well, giving equality in the
   good localization. Thus inclusion is fully faithful and essentially surjective.
   Choose representatives of objects and lift arrows through these hom-set bijections
   to obtain an inverse equivalence and the displayed comparison with inclusion.
   Choosing chain-map representatives of homotopy classes yields the asserted roofs;
   their equalities are modulo filtration-preserving homotopy. No functorial resolution
   is chosen. -/
theorem finiteFiltered_kFlat_replacement :
    (∀ (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a b : ℤ),
      a < b → K.filtration.step a = ⊤ → K.filtration.step b = ⊥ →
      ∃ (P : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (f : P ⟶ K),
        HasKunnethFiltration P ∧ P.filtration.step a = ⊤ ∧
        P.filtration.step b = ⊥ ∧ QuasiIso f.hom ∧
        (∀ i : ℤ, QuasiIso (FilteredObject.restrictionSteps f i)) ∧
        (∀ i : ℤ, QuasiIso (FilteredObject.gradedMapSteps f i)) ∧
        (∀ n : ℤ, Module.Free R (P.obj.X n)) ∧
        (∀ i n : ℤ, Module.Free R
          ((P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ).X n)) ∧
        (∀ i n : ℤ, Module.Free R ((P.filtration.gradedPiece i).X n))) ∧
    (∃ E : (goodFiniteFilteredModuleQuasiIso R).Localization ≌
        (finiteFilteredModuleQuasiIso R).Localization,
      Nonempty ((goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ≅
        goodFiniteFilteredModuleInclusion R ⋙ (finiteFilteredModuleQuasiIso R).Q)) ∧
    (∀ (A B : GoodFiniteFilteredModuleHomotopy R)
      (φ : (goodFiniteFilteredModuleQuasiIso R).Q.obj A ⟶
        (goodFiniteFilteredModuleQuasiIso R).Q.obj B),
      ∃ (T : GoodFiniteFilteredModuleHomotopy R) (s : T ⟶ A) (t : T ⟶ B)
        (hs : goodFiniteFilteredModuleQuasiIso R s),
        φ = Localization.Construction.wInv s hs ≫
          (goodFiniteFilteredModuleQuasiIso R).Q.map t) ∧
    (∀ (A B T₁ T₂ : GoodFiniteFilteredModuleHomotopy R)
      (s₁ : T₁ ⟶ A) (s₂ : T₂ ⟶ A) (t₁ : T₁ ⟶ B) (t₂ : T₂ ⟶ B)
      (hs₁ : goodFiniteFilteredModuleQuasiIso R s₁)
      (hs₂ : goodFiniteFilteredModuleQuasiIso R s₂),
      Localization.Construction.wInv s₁ hs₁ ≫
          (goodFiniteFilteredModuleQuasiIso R).Q.map t₁ =
        Localization.Construction.wInv s₂ hs₂ ≫
          (goodFiniteFilteredModuleQuasiIso R).Q.map t₂ ↔
        ∃ (T : GoodFiniteFilteredModuleHomotopy R) (r₁ : T ⟶ T₁) (r₂ : T ⟶ T₂),
          r₁ ≫ s₁ = r₂ ≫ s₂ ∧ goodFiniteFilteredModuleQuasiIso R (r₁ ≫ s₁) ∧
          r₁ ≫ t₁ = r₂ ≫ t₂) := by
  sorry

end CochainComplex
