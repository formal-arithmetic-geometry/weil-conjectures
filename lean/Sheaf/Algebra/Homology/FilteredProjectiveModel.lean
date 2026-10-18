/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.Algebra.Homology.TwoStepFilteredModuleDerived
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import WeilConjectures.CategoryTheory.PBCFiltration
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Sheaf.Algebra.Homology.FilteredProjectiveComparison
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# A finite projective model of a two-step filtered endomorphism

Source: Stacks Project, Tags 03TB and 03TJ; blueprint main-20261015,
prop-trf-trace-formal-laws, proof of clause (2)
(blueprint: lem-trf-filtered-projective-model).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A two-step filtered derived object with perfect graded pieces, together with any
localized endomorphism, admits a bounded finite-projective filtered chain model.
The restricted and quotient maps represent the induced graded endomorphisms.
Filtration preservation is encoded by a commutative square of complexes; it does
not require equality of the image of a filtration step with an intersection.

Source: Stacks, Tags 03TB and 03TJ; blueprint main-20261015,
prop-trf-trace-formal-laws, proof of clause (2).

Proof, following the six steps of the node:
1. Choose a pair representing the filtered object and finite-projective models of
its two perfect graded objects (`def-pc-perfect-ring-complex`). Good truncation
above a common cohomology bound gives a bounded-above pair and a filtered
quasi-isomorphism to the original pair. The quotient is a quasi-isomorphism by
lifting cycles in the truncation degree and correcting in the subcomplex.
2. Use `lem-trf-filtered-projective-comparison` to replace this pair by a
bounded-above pair with projective graded modules. Degreewise projectivity splits
the inclusion and quotient. The total differential has diagonal entries the two
graded differentials and an off-diagonal chain map into the shifted subcomplex.
3. By `lem-pc-ring-derived-map-representative`, represent the graded derived
isomorphisms and the transported off-diagonal map on bounded finite-projective
models by chain maps. Equality in the derived category gives a chain homotopy;
the negative differential on the shift determines its sign.
4. The off-diagonal map defines a block differential on the sum of the two
finite-projective complexes. The chain homotopy gives the off-diagonal entry of
a filtered quasi-isomorphism from this model to the projective pair of step 2.
The coordinate inclusion and projection give degreewise splitting. The terms
are finitely generated projective and the union of the two degree ranges bounds
all three complexes.
5. Conjugate the given endomorphism by the resulting filtered isomorphism. The
unrestricted-target Hom bijection of `lem-trf-filtered-projective-comparison`
represents it by a filtration-preserving chain endomorphism.
6. Restriction and quotient preserve filtered homotopies and filtered
quasi-isomorphisms, hence descend to the canonical graded functors. Applying
them to the conjugacy identity gives exactly the two graded conjugacy identities.
(blueprint: lem-trf-filtered-projective-model). -/
theorem exists_filteredProjectiveModel {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (P : TwoStepModuleDerived A)
    (hP : ∀ c : Bool, DerivedCategory.IsPerfectRingComplex ((twoStepGraded A c).obj P))
    (uP : P ⟶ P) :
    ∃ M : TwoStepModuleComplex A,
      (∃ a b : ℤ,
        M.obj.right.IsStrictlyGE a ∧ M.obj.right.IsStrictlyLE b ∧
        ∀ c : Bool, ((twoStepGradedComplex A c).obj M).IsStrictlyGE a ∧
          ((twoStepGradedComplex A c).obj M).IsStrictlyLE b) ∧
      (∀ n : ℤ,
        (Module.Finite A (M.obj.right.X n) ∧ Module.Projective A (M.obj.right.X n)) ∧
        ∀ c : Bool, Module.Finite A (((twoStepGradedComplex A c).obj M).X n) ∧
          Module.Projective A (((twoStepGradedComplex A c).obj M).X n)) ∧
      (ShortComplex.mk M.obj.hom (cokernel.π M.obj.hom)
        (cokernel.condition M.obj.hom)).ShortExact ∧
      (∀ n : ℤ, ∃ s : (cokernel M.obj.hom).X n ⟶ M.obj.right.X n,
        s ≫ (cokernel.π M.obj.hom).f n = 𝟙 _) ∧
      ∃ j : (twoStepModuleQ A).obj M ≅ P, ∃ ū : M ⟶ M,
        (twoStepModuleQ A).map ū ≫ j.hom = j.hom ≫ uP ∧
        ∀ c : Bool,
          DerivedCategory.Q.map ((twoStepGradedComplex A c).map ū) ≫
              (twoStepGraded A c).map j.hom =
            (twoStepGraded A c).map j.hom ≫ (twoStepGraded A c).map uP := by
  sorry

end CochainComplex
