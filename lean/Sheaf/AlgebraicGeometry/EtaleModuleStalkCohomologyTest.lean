/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Module geometric stalks compute and detect unbounded cohomology

Source: Stacks Project, etale-cohomology.tex, Tags 03PT(3) and 03PU;
sites-modules.tex, Tags 03DA and 04EQ; sites-cohomology.tex, Tag 0DJJ;
derived.tex, Tag 015F (blueprint: lem-sf-etale-module-stalk-cohomology-test).

Constant-coefficient modules use the project's module-valued sheaf encoding.
`pointSmallEtale t |>.sheafFiber` is the pointed-neighbourhood colimit, computed
in modules, so its scalar action and maps are the induced A-linear ones.
The derived functor below is the existing exact-functor localization, on the full
unbounded derived categories. All comparisons are natural isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] CategoryTheory.GrothendieckTopology.Point.sheafFiber_additive

namespace AlgebraicGeometry.Etale

/-- Forgetting coefficients on module-valued étale sheaves preserves kernels,
images, quotients and cohomology, naturally in an unbounded complex.
Source: Stacks Project, sites-modules.tex, Tag 03DA; homology.tex, Tag 010N
(blueprint: lem-sf-etale-module-stalk-cohomology-test).

Proof: step 1 of the node. The forgetful functor is faithful and exact by
lem-weil-pbc-module-sheaves-colimits-forgetful(1). Kernels are computed sectionwise
and cokernels by sheafifying sectionwise cokernels, in both categories. Images
are kernels of cokernels; quotients are cokernels of inclusions. Apply
lem-sp-exact-functor-preserves-homology to the three terms in each degree to
obtain the natural cohomology comparison. -/
theorem etaleModuleForget_preserves_cohomology
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    PreservesFiniteLimits (sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})) ∧
    PreservesFiniteColimits (sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})) ∧
    (∀ (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (f : F ⟶ G),
      Nonempty (image ((sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map f) ≅
        (sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj (image f))) ∧
    (∀ i : ℤ, Nonempty
      ((sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor
            (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ) i ≅
        HomologicalComplex.homologyFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (ComplexShape.up ℤ) i ⋙
          sheafCompose T.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}))) := by
  sorry

/-- Forgetting an ordinary module structure preserves kernels, images, quotients
and cohomology, naturally in arbitrary integer-indexed complexes.
Source: Stacks Project, homology.tex, Tag 010N; the module description in
sites-modules.tex, Tag 03DA (blueprint: lem-sf-etale-module-stalk-cohomology-test).

Proof: step 1 of the node. A kernel or image is the same additive subgroup with
restricted action. A quotient has the same additive cosets, with a[m] = [am].
Thus forgetting preserves kernels and cokernels and hence finite limits and
colimits. The image comparison respects both factorization maps; the homology
comparison is the induced quotient-of-cycles comparison and is natural. -/
theorem moduleForget_preserves_cohomology (A : Type (u + 1)) [CommRing A] :
    PreservesFiniteLimits (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) ∧
    PreservesFiniteColimits (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) ∧
    (∀ (M N : ModuleCat.{u + 1} A) (f : M ⟶ N),
      Nonempty (image ((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map f) ≅
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (image f))) ∧
    (∀ i : ℤ, Nonempty
      ((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) i ≅
        HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (ComplexShape.up ℤ) i ⋙
          forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})) := by
  sorry

/-- The geometric module stalk is additive and exact.
Source: Stacks Project, etale-cohomology.tex, Tag 03PT(3), and sites-modules.tex,
Tag 04EQ (blueprint: lem-sf-etale-module-stalk-cohomology-test).

Proof: steps 2 and 3 of the node. On germs define a[m] = [a_V m], where a_V is
the constant section supplied by def-weil-pbc-constant-sheaf. Semilinear
restrictions make this well defined; module identities hold on representatives.
Morphisms and sums of morphisms respect that action on representatives.
Forgetting gives the abelian stalk. Apply step 1 and
prop-weil-pbc-geometric-stalks-exact to a short exact sequence, then check
exactness of ordinary modules on the underlying abelian groups. -/
theorem etaleModuleStalk_exact
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).Additive ∧
    PreservesFiniteLimits ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)) ∧
    PreservesFiniteColimits ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)) := by
  sorry

/-- Applying the geometric module stalk termwise preserves quasi-isomorphisms.
Source: Stacks Project, homology.tex, Tag 010N; derived.tex, Tag 015F
(blueprint: lem-sf-etale-module-stalk-cohomology-test).

Proof: step 4 of the node. Apply lem-weil-pbc-exact-functor-complex-cohomology
and exactness above. In degree i the comparison identifies the stalk of the
kernel and image with the kernel and image of the stalk differentials. Taking
the quotient gives an A-linear isomorphism, natural in complex maps. Hence a
map invertible on every cohomology remains so after termwise stalks. Only the
three consecutive terms are involved, so no boundedness is needed. -/
theorem etaleModuleStalk_preserves_quasiIso
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    {C D : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (f : C ⟶ D) (hf : QuasiIso f) :
    QuasiIso ((((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  sorry

/-- The unbounded derived module stalk is induced by the termwise stalk functor.
Source: Stacks Project, derived.tex, Tag 015F(3)-(4), Definition 05RU
(blueprint: lem-sf-etale-module-stalk-cohomology-test).

Proof: step 5 of the node. The preceding quasi-isomorphism preservation permits
localization. Apply lem-weil-pbc-exact-functor-derived-factorization: the existing
mapDerivedCategory is this localized functor and mapDerivedCategoryFactors is
the natural representative comparison. No resolution or truncation is used. -/
theorem etaleModuleStalk_derived_factors
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    Nonempty
      (_root_.DerivedCategory.Q ⋙
          ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).mapDerivedCategory ≅
        ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ _root_.DerivedCategory.Q) := by
  sorry

/-- Cohomology commutes naturally and A-linearly with the unbounded derived stalk.
Source: Stacks Project, sites-cohomology.tex, Tag 0DJJ, converse proof;
derived.tex, Tag 015F (blueprint: lem-sf-etale-module-stalk-cohomology-test).

Proof: steps 4 and 5 of the node. Exactness gives the natural comparison on
complexes by the kernel/image/quotient computation. The representative
comparison of etaleModuleStalk_derived_factors and
 def-weil-derived-cohomology-sheaves identifies both sides on Q(C). Naturality
for quasi-isomorphisms also gives naturality for their inverses, by composition
with inverse maps. All localized morphisms are generated by complex maps and
these inverses, so the comparison descends naturally to the derived category.
All maps are morphisms in ModuleCat A, and therefore A-linear. -/
theorem etaleModuleStalk_cohomology_iso
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) (i : ℤ) :
    Nonempty
      (_root_.DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) i ⋙
          (pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A) ≅
        ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
          _root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i) := by
  sorry

/-- Vanishing of each cohomology sheaf is detected by all derived geometric stalks.
Source: Stacks Project, etale-cohomology.tex, Tag 03PU; sites-cohomology.tex,
Tag 0DJJ (blueprint: lem-sf-etale-module-stalk-cohomology-test).

Proof: steps 1-6 of the node. First forgetting modules preserves kernels,
cokernels, images, quotients and cohomology by
lem-weil-pbc-module-sheaves-colimits-forgetful and
lem-sp-exact-functor-preserves-homology. Next the action a[m] = [a_V m] is well
defined on pointed-neighbourhood germs and makes the stalk maps A-linear.
By prop-weil-pbc-geometric-stalks-exact this module stalk is exact. Applying
lem-weil-pbc-exact-functor-complex-cohomology gives the natural cohomology
comparison on unbounded complexes and preservation of quasi-isomorphisms.
By lem-weil-pbc-exact-functor-derived-factorization it descends to the full
derived categories, with naturality also for inverses of quasi-isomorphisms.
If the cohomology sheaf is zero, its stalks and hence the corresponding stalk
cohomology modules vanish. Conversely, if those modules vanish, the comparison
makes all abelian stalks of the underlying cohomology sheaf zero. Apply
lemma-weil-pbc-geometric-stalk-conservative to the morphism from zero to that
abelian sheaf. It is an isomorphism, so that sheaf is zero. Faithfulness of the
module forgetful functor then gives id = 0 for the module sheaf, making it zero.
On an empty scheme the condition on geometric points is vacuous, and the same
conservativity argument applies. No boundedness, finiteness, constructibility
or Noetherian hypothesis enters any step. -/
theorem etaleModuleStalk_cohomology_test
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (E : DerivedCategoryModule A T) (i : ℤ) :
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj E) ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).obj
          (((pointSmallEtale t).sheafFiber
            (A := ModuleCat.{u + 1} A)).mapDerivedCategory.obj E)) := by
  sorry

end AlgebraicGeometry.Etale
