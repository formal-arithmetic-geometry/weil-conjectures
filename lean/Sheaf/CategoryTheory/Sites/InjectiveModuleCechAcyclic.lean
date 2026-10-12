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

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/- The former independent-universe signature is refuted by Triangle.false_signature.
The repaired statement aligns homs, rings, module values and cover indices at v;
free representables now belong to the category in which injectivity is assumed.
The report retains the complete certificate for the old signature. -/

set_option linter.unusedVariables false in
/-- Positive Čech cohomology of the underlying abelian sheaf of an injective module
sheaf vanishes for every covering and every choice of the covering's fibre products.
Homs, rings, module values and covering indices all lie in universe v.
Source: Stacks Project, Cohomology on Sites, Tag 03FC, via Tags 03FB and 03AT;
the underlying-abelian identification is used in Tag 03FD.
(blueprint: lem-weil-pbc-ringed-site-injective-module-cech-acyclic)

Proof: exact module sheafification is left adjoint to inclusion, so its right
adjoint sends I to an injective module presheaf (Tag 03FB). For p=q+1, the
presheaf cocycle-lifting theorem (Tag 03FC, using 03AS, 03F5 and 03AT) supplies a
primitive for every q+1 cocycle. Its free module complex and Yoneda argument
apply because homs, rings, values and indices share v. Identify the differentials
of the constructed CochainComplex.of with differentialValue. Mathlib's elementwise
criterion for exactness of abelian groups proves ExactAt (q+1), whose homology is
zero. The forgetful presheaf has the same sections and restrictions, giving exactly
the stated cohomologyFunctor. This includes p=1, empty families and zero modules. -/
theorem injective_module_cech_cohomology_isZero
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{v})
    [HasSheafify J.toGrothendieck AddCommGrpCat.{v}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (I : SheafOfModules.{v} R) [Injective I]
    {T : Type v} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
  have : Injective I.val := injective_module_sheaf_injective_presheaf R I
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  change IsZero ((S.complex I.val.presheaf).homology (q + 1))
  apply HomologicalComplex.ExactAt.isZero_homology
  apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
    q (q + 1) (q + 2) (by simp) (by simp)).2
  rw [ShortComplex.ab_exact_iff]
  intro c hc
  change (CochainComplex.of.d (S.cochains I.val.presheaf)
    (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
  rw [CochainComplex.of_d] at hc
  obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift
    R.obj I.val f hom S q c hc
  refine ⟨b, ?_⟩
  change (CochainComplex.of.d (S.cochains I.val.presheaf)
    (S.differential I.val.presheaf) q (q + 1)) b = c
  rw [CochainComplex.of_d]
  exact hb

end CategoryTheory
