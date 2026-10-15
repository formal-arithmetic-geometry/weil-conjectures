/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.InjectiveModulePresheaf
import Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact
import Sheaf.CategoryTheory.SiteSesCechH1Surjective
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Injectives and the module Čech acyclicity criterion

Source: Stacks Project, Cohomology on Sites, Tags 03F9, 03FB, 03FC;
blueprint, Proper base change, Injectives and the Cech acyclicity criterion
(blueprint: lem-weil-pbc-cech-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option linter.unusedVariables false in
/-- Injective module sheaves are Čech-acyclic; finite-basis Čech-acyclic module sheaves
have zero positive derived sections. The last clause computes derived sections on every
injective resolution in module sheaves, rather than resolving the underlying abelian sheaf.
`products` chooses the iterated products, and `hproducts` expresses closure of the basis
for these choices. Ordered tuples, including repetitions, are built into `SiteCechComplex`.
Source: Stacks Project, Cohomology on Sites, Tags 03F9, 03FB, 03FC
(blueprint: lem-weil-pbc-cech-criterion).

Proof:
1. The finite basis coverings are cofinal by `hrefine`; their chosen iterated products
   lie in the basis by `hproducts` (def-weil-pbc-site-cech-complex). No coproduct in C is used.
2. An injective module sheaf is an injective module presheaf by
   lem-weil-pbc-ringed-site-injective-module-injective-presheaf. The cocycle lifting of
   lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift makes every positive cocycle
   a boundary. The shared universe contains the required free module presheaves.
3. Module sheaves form a Grothendieck abelian category by
   lem-weil-pbc-ring-sheaves-grothendieck, hence have enough injectives by
   lem-sp-grothendieck-enough-injectives. Embed a Čech-acyclic A into an injective I and
   take Q = I/A. The underlying abelian sheaves form a short exact sequence: kernels
   are sectionwise (def-weil-sheaf-of-modules-category), and module sheafification has
   underlying abelian sheafification (def-weil-presheaf-modules-sheafification).
4. For U in B, lem-weil-pbc-site-ses-cech-h1-surjective gives I(U) → Q(U) surjective.
   Indeed lift a section locally on a finite basis refinement. The differences form an
   A-valued one-cocycle on overlaps. Its primitive adjusts the lifts to agree, so they
   glue. Left exactness then gives a short exact section sequence on each basis object.
5. Finite products of these sequences over all ordered tuples are short exact in each
   degree. Naturality commutes with alternating restrictions. The long exact sequence
   of lem-weil-pbc-complex-ses-homology-long-exact shows positive Čech cohomology of Q
   vanishes, between the zero groups for I and A.
6. Evaluation is additive and left exact. Apply lem-weil-pbc-derived-functor-long-exact
   and lem-weil-pbc-derived-functor-injective-vanishing in module sheaves. Surjectivity
   in step 4 gives H¹(U,A)=0. For q>1 dimension shifting identifies H^q(U,A) with
   H^(q-1)(U,Q). Induct on q for all Čech-acyclic A, using step 5 for Q. Finally use
   InjectiveResolution.isoRightDerivedObj (def-sp-left-exact-additive) to compute on
   any chosen module injective resolution of M. -/
theorem module_cech_acyclicity_criterion
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{u})
    (B : Set C)
    (hbasis : ∀ U : C, ∃ (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
      Presieve.ofArrows V f ∈ J U ∧ ∀ t, V t ∈ B)
    (products : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
      U ∈ B → (∀ t, V t ∈ B) → Presieve.ofArrows V f ∈ J U → SiteCechComplex V f)
    (hproducts : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U)
      (hU : U ∈ B) (hV : ∀ t, V t ∈ B) (hc : Presieve.ofArrows V f ∈ J U)
      (p : ℕ) (a : Fin (p + 1) → T), (products U T V f hU hV hc).W p a ∈ B)
    (hrefine : ∀ (U : C), U ∈ B →
      ∀ (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
      Presieve.ofArrows V f ∈ J U →
      ∃ (m : ℕ) (W : Fin m → C) (g : ∀ a, W a ⟶ U),
        (∀ a, W a ∈ B) ∧ Presieve.ofArrows W g ∈ J U ∧
          ∀ a, ∃ (t : T) (k : W a ⟶ V t), k ≫ f t = g a) :
    (∀ (I : ringedSiteModules.{u} R), Injective I →
      ∀ (U : C) (m : ℕ) (V : Fin m → C) (f : ∀ a, V a ⟶ U),
        U ∈ B → (∀ a, V a ∈ B) → Presieve.ofArrows V f ∈ J U →
        ∀ (S : SiteCechComplex V f) (p : ℕ), 0 < p →
          IsZero ((S.cohomologyFunctor p).obj I.val.presheaf)) ∧
    (∀ (M : ringedSiteModules.{u} R),
      (∀ (U : C) (m : ℕ) (V : Fin m → C) (f : ∀ a, V a ⟶ U),
        U ∈ B → (∀ a, V a ∈ B) → Presieve.ofArrows V f ∈ J U →
        ∀ (S : SiteCechComplex V f) (p : ℕ), 0 < p →
          IsZero ((S.cohomologyFunctor p).obj M.val.presheaf)) →
      ∀ (U : C), U ∈ B → ∀ (q : ℕ), 0 < q →
        ∀ (I : InjectiveResolution M),
          IsZero ((((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex).homology q)) := by
  sorry

end CategoryTheory
