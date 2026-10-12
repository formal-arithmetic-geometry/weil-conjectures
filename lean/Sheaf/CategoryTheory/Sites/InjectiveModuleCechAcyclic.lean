/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Sheaf.CategoryTheory.SiteCechComplex

import Mathlib.Algebra.Homology.ShortComplex.Ab
import Sheaf.CategoryTheory.InjectiveModulePresheaf
import Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact

/-!
# Čech acyclicity of injective module sheaves on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 03FC
(lemma-injective-module-trivial-cech), and Tag 03FD
(blueprint: lem-weil-pbc-ringed-site-injective-module-cech-acyclic).
-/

@[expose] public section

universe u v w r s

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option linter.unusedVariables false in
/-- Positive Čech cohomology of the underlying abelian sheaf of an injective module
sheaf vanishes for every covering and every choice of the covering's fibre products.
Source: Stacks Project, Cohomology on Sites, Tag 03FC, via Tags 03FB and 03AT;
the underlying-abelian identification is used in Tag 03FD.
(blueprint: lem-weil-pbc-ringed-site-injective-module-cech-acyclic)

Proof:
1. Exact sheafification is left adjoint to inclusion, so the injective module sheaf
is injective as a presheaf of modules
(lem-weil-pbc-ringed-site-injective-module-injective-presheaf).
2. Form the free module presheaf chain complex on the iterated fibre products.
It is exact in positive degrees (lem-weil-pbc-ringed-site-free-cech-complex-exact):
at each object, decompose it over maps to the covered object. The summand on the
set of lifts contracts by adjoining a chosen lift
(lem-weil-pbc-power-set-complex-contractible); an empty lift set gives the zero complex.
3. Yoneda for free module presheaves (lem-weil-pbc-free-yoneda-presheaf-module)
and Hom out of a direct sum identify Hom from this chain complex with the product
of sections defining the Čech cochain complex. Precomposition by its face maps
is restriction along the omitted-factor projections, giving the same differential.
4. Apply the exact contravariant Hom functor into the injective presheaf from step 1
to the complex from step 2. Its positive cohomology vanishes, hence so does Čech cohomology.
5. Forgetting module structures preserves the sections and restriction maps, so this
is precisely the Čech complex of the underlying abelian presheaf. -/
theorem injective_module_cech_cohomology_isZero
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{r})
    [HasSheafify J.toGrothendieck AddCommGrpCat.{s}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{s}]
    (I : SheafOfModules.{s} R) [Injective I]
    {T : Type w} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
  sorry

end CategoryTheory
