/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel

/-! # The canonical comparison from module Hom complexes to derived Hom

Source: Stacks Project, More on Algebra, Tags 0A5Y and 0A65,
section-RHom and equation-internal-hom.
(blueprint: def-trf-module-hom-complex-derived-comparison)

The evaluation is the existing map uniquely specified on pure-tensor summands.
The comparison is its localized left transpose after the native tensorator.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace ModuleCat

/-- Signed evaluation on the ordinary product Hom complex: on the (p,q) tensor
summand it sends x tensor f to (-1)^(p*q) f(x), with the actual Hom projection
`f.v p (p+q) rfl`. The coordinate clause of the existing
`CochainComplex.projective_hom_evaluation_model` determines the map uniquely,
by the tensor and direct-sum universal properties, for arbitrary unbounded E,I.
Its evaluation clause has no projectivity or boundedness hypothesis.
This is the same defining expression as `coinductionHomEvaluation`, exposed
under the definition node without importing the coinduction-adjunction theorem.
Source: Stacks Project, Tags 0A5Y and 0A65, section-RHom.
(blueprint: def-trf-module-hom-complex-derived-comparison) -/
def moduleHomComplexEvaluation {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (E I : CochainComplex (ModuleCat.{u} R) ℤ) :
    E ⊗ CochainComplex.moduleHomComplex E I ⟶ I :=
  (Classical.choose (Classical.choose_spec
    (CochainComplex.projective_hom_evaluation_model R))) E I

/-- The canonical map Q Hom(E,I) -> RHom(QE,QI), defined by left transposing
localized signed evaluation after the native localization tensorator. No choice
of a derived isomorphism or additional hypothesis enters this definition.
For K-injective I it is the canonical representative comparison of derived Hom.
This is definitionally the same map as the existing `coinductionHomComparison`.
Source: Stacks Project, Tags 0A5Y and 0A65, equation-internal-hom.
(blueprint: def-trf-module-hom-complex-derived-comparison) -/
def moduleHomComplexDerivedComparison {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (E I : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj (CochainComplex.moduleHomComplex E I) ⟶
      (ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj I) :=
  MonoidalClosed.curry
    (Functor.LaxMonoidal.μ DerivedCategory.Q E (CochainComplex.moduleHomComplex E I) ≫
      DerivedCategory.Q.map (moduleHomComplexEvaluation E I))

end ModuleCat
