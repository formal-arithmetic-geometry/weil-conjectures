/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic

/-!
# Continuous precomposition and injective-module Čech complexes

Source: Stacks Project, Cohomology on Sites, Tag 0D6X, proof, using Tag 03FC
(blueprint: lem-trf-continuous-precomposition-injective-module-cech).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option linter.unusedVariables false in
/-- Continuous precomposition gives ring and module sheaves, the projection-characterized
covering-nerve isomorphisms, their specified cochain comparison, its bounded-below derived
image, and positive Čech vanishing for module-injective coefficients.

The first two sheaf predicates bundle respectively the literal ring precomposition and
`PresheafOfModules.pushforward₀OfCommRingCat`: the latter already has exactly the inherited
sectionwise scalar action and restrictions. Thus no new module structure is chosen.

Source: Stacks Project, Cohomology on Sites, Tag 0D6X, proof; Sites 00WV, 00WW;
Cohomology on Sites 03AM, 03FC; Derived Categories 05RU.
(blueprint: lem-trf-continuous-precomposition-injective-module-cech)

Proof:
1. Continuous precomposition preserves the underlying set and abelian sheaf conditions
   (lem-weil-pbc-site-continuous-pushforward-sheaf). Algebraic sheafness is detected on
   underlying sets (lem-weil-pbc-algebraic-sheaf-iff-underlying-sets). The existing module
   presheaf pushforward uses precisely I(u(h)), R(u(h)), and the original scalar actions.
2. Apply lem-trf-continuous-cover-nerve-comparison to the fixed cover. Continuity gives
   the image cover and preserves pullbacks of each covering arrow along any map.
   Induction on tuple length gives c, uniquely specified by its projections. Its
   index-map compatibility for Fin.succAbove gives the omitted-factor equation below.
3. In each nonnegative degree set A(s)(t)=I(c(t).inv)(s(t)); its inverse is restriction
   along c(t).hom. Functoriality proves both inverse equations. The omitted-factor
   equation commutes A with each restriction; sum with signs (-1)^j to commute with
   the differential of def-weil-pbc-site-cech-complex. This yields the cochain iso e.
4. Extend e by zero to integer degrees. Both complexes are strictly zero below zero,
   hence bounded below. Localization carries the inverse equations to D+(Ab); the
   displayed equation identifies its underlying morphism with Q applied to A.
5. Apply lem-weil-pbc-ringed-site-injective-module-cech-acyclic to the image cover.
   It needs injectivity as a module sheaf only. The cochain iso transports its zero
   positive cohomology to the original cover. No abelian-injectivity is used. -/
theorem continuous_precomposition_injective_module_cech
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    [HasDerivedCategory.{u + 1} AddCommGrpCat.{u}]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (F : C ⥤ D)
    (hcover : ∀ (X : C) (A : Presieve X), A ∈ J X → A.map F ∈ K (F.obj X))
    (hpullback : ∀ (X Y Z : C) (A : Presieve X), A ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), A a → PreservesLimit (cospan a b) F)
    (R : Sheaf K.toGrothendieck CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose K.toGrothendieck
      (forget₂ CommRingCat RingCat)).obj R)) [Injective I] :
    Presheaf.IsSheaf J.toGrothendieck (F.op ⋙ R.obj) ∧
    Presheaf.IsSheaf J.toGrothendieck
      (((PresheafOfModules.pushforward₀OfCommRingCat F R.obj).obj I.val).presheaf) ∧
    ∀ (T : Type u) (U : C) (f : T → C) (a : ∀ t, f t ⟶ U),
      Presieve.ofArrows f a ∈ J U →
      ∀ (S : SiteCechComplex f a)
        (P : SiteCechComplex (fun t ↦ F.obj (f t)) (fun t ↦ F.map (a t))),
      ∃ c : ∀ (n : ℕ) (t : Fin (n + 1) → T), F.obj (S.W n t) ≅ P.W n t,
        (∀ (n : ℕ) (t : Fin (n + 1) → T) (k : Fin (n + 1)),
          (c n t).hom ≫ P.pr n t k = F.map (S.pr n t k)) ∧
        (∀ (n : ℕ) (t : Fin (n + 2) → T) (j : Fin (n + 2)),
          F.map (S.indexMap t j.succAbove) ≫ (c n (t ∘ j.succAbove)).hom =
            (c (n + 1) t).hom ≫ P.indexMap t j.succAbove) ∧
        ∃ e : S.complex (F.op ⋙ I.val.presheaf) ≅ P.complex I.val.presheaf,
          (∀ (n : ℕ) (s : S.cochains (F.op ⋙ I.val.presheaf) n)
            (t : Fin (n + 1) → T),
            (e.hom.f n s) t = I.val.presheaf.map ((c n t).inv.op) (s t)) ∧
          (∃ (hS : CochainComplex.plus AddCommGrpCat.{u}
              ((S.integerComplexFunctor).obj (F.op ⋙ I.val.presheaf)))
            (hP : CochainComplex.plus AddCommGrpCat.{u}
              ((P.integerComplexFunctor).obj I.val.presheaf)),
            ∃ d :
              (DerivedCategory.Plus.Q (C := AddCommGrpCat.{u})).obj
                ⟨S.integerComplexFunctor.obj (F.op ⋙ I.val.presheaf), hS⟩ ≅
              (DerivedCategory.Plus.Q (C := AddCommGrpCat.{u})).obj
                ⟨P.integerComplexFunctor.obj I.val.presheaf, hP⟩,
              (DerivedCategory.Plus.ι (C := AddCommGrpCat.{u})).map d.hom =
                (DerivedCategory.Q (C := AddCommGrpCat.{u})).map
                ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).map e.hom)) ∧
          ∀ (q : ℕ), 0 < q →
            IsZero ((S.cohomologyFunctor q).obj (F.op ⋙ I.val.presheaf)) := by
  sorry

end CategoryTheory
