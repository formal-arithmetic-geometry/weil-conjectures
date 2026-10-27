/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # A covering collection of acyclic objects detects derived inverse limits

Source: Stacks Project, Cohomology on Sites, Tag 0BKY
(blueprint: lem-sfb-site-basis-inverse-limit-acyclic).
-/

@[expose] public section

set_option autoImplicit false

universe c v r w wT wA uA vA

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The first right derived inverse limit of an abelian-group tower, using exactly
`lim.rightDerived 1` and the structural witnesses of Tag 07KW.
Source: Stacks Project, More on Algebra, Tag 07KW
(blueprint: lem-sfb-site-basis-inverse-limit-acyclic). -/
noncomputable abbrev basisTowerFirstDerivedLimit (A : ℕᵒᵖ ⥤ AddCommGrpCat.{r}) :=
  letI := roosTowerEnoughInjectives.{r}
  letI := roosLimitAdditive.{r}
  ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r}).rightDerived 1).obj A

/-- On a covering collection, positive module-derived evaluation is the homology of
unbounded derived sections on the degree-zero embedding. No abelian-sheaf cohomology
is substituted for module cohomology.
Source: Stacks Project, Cohomology on Sites, Tags 0BKY and 0D6K
(blueprint: lem-sfb-site-basis-inverse-limit-acyclic). -/
noncomputable abbrev basisModuleCohomology
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max c v r}) (U : C) (p : ℕ)
    [HasDerivedCategory.{w} (ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O))]
    [HasDerivedCategory.{wA} AddCommGrpCat.{max c v r}]
    (M : ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} (p : ℤ)).obj
    ((siteModuleDerivedSections.{c, v, r, w, wA} J O U).obj
      ((DerivedCategory.singleFunctor _ 0).obj M))

/-- The ordinary-limit comparison for a specified total right derived limit.
The inverse of Mathlib's single-complex comparison identifies `(lim F)[0]` with
`lim(F[0])`; the next arrow is exactly the given derived-functor unit.
Source: Stacks Project, Cohomology on Sites, Tag 0BKY
(blueprint: lem-sfb-site-basis-inverse-limit-acyclic). -/
noncomputable def basisInverseLimitComparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{wT} (ℕᵒᵖ ⥤ A)]
    (F : ℕᵒᵖ ⥤ A) (RF : DerivedCategory.{wT} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF) :
    (DerivedCategory.singleFunctor A 0).obj (limit F) ⟶
      RF.obj ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj F) :=
  DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A) (ComplexShape.up ℤ) 0).inv.app F) ≫
    η.app ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj F)

/-- The comparison from ordinary inverse limit to total right derived inverse limit
is invertible under the covering-acyclicity and sectionwise R¹-lim hypotheses.
`RF, η` are any presentation of the total right derived inverse-limit functor;
the displayed arrow first identifies the degree-zero ordinary limit with the
termwise limit of the degree-zero tower, then applies its specified derived unit.
The index `n : ℕ` denotes the original index `n + 1`.

Source: Stacks Project, Cohomology on Sites, Tag 0BKY
(blueprint: lem-sfb-site-basis-inverse-limit-acyclic).

Proof:
1. The strict-tower theorem lem-weil-pbc-ringed-strict-tower-homotopy-limit
   supplies the total derived limit and its Roos triangle. On a K-injective tower
   resolution the comparison is the limit of the resolution map, so its composites
   with the derived projections are the ordinary limit projections
   (def-pur-sheaf-inverse-limit).
2. By prop-pur-kinjective-resolutions-exist and lem-sp-grothendieck-enough-injectives,
   a module has a nonnegative injective resolution. It is K-injective by
   lem-weil-pbc-bounded-below-injectives-kinjective. Its evaluation has no negative
   cohomology and degree zero is the section group, naturally in the module.
3. Apply lem-kun-site-rgamma-derived-limit and lem-pc-derived-limit-milnor-sequence.
   At each basis object the hypotheses give zero cohomology outside degree zero
   for the derived limit. In degree zero the edge map is the ordinary limit of
   sections and its composites are the specified projections. Thus it carries
   the comparison to the sectionwise-limit identification.
4. Exact module sheafification (lem-weil-pbc-ringed-site-module-sheafification-exact)
   takes the presheaf kernel/image quotient of evaluated cohomology to the
   cohomology sheaf; this is natural in the derived object.
5. On the covering collection the map on degree-zero cohomology is bijective,
   and the other cohomology presheaves vanish. They are therefore locally
   bijective on every object. Apply lem-weil-pbc-site-sheafification-iso-locally-bijective
   and def-weil-presheaf-modules-sheafification to obtain the same assertions
   for module cohomology sheaves.
6. By lem-weil-pbc-unbounded-derived-iso-cohomology the specified comparison is
   an isomorphism. Derived evaluation then gives positive-degree vanishing for
   the ordinary limit on every basis object. -/
theorem site_basis_inverseLimit_acyclic
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O))]
    [HasDerivedCategory.{wT} (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O))]
    [HasDerivedCategory.{wA} AddCommGrpCat.{max c v r}]
    (F : ℕᵒᵖ ⥤ ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O))
    (B : Set C)
    (_hcover : ∀ X : C, ∃ (I : Type (max c v)) (U : I → C) (a : ∀ i, U i ⟶ X),
      Sieve.generate (Presieve.ofArrows U a) ∈ J X ∧ ∀ i, U i ∈ B)
    (_hacyclic : ∀ U ∈ B, ∀ (n p : ℕ), 0 < p →
      IsZero (basisModuleCohomology.{c, v, r, w, wA} J O U p (F.obj (op n))))
    (_hlim : ∀ U ∈ B, IsZero (basisTowerFirstDerivedLimit
      (F ⋙ siteModuleSections.{c, v, r} J O U)))
    (RF : DerivedCategory.{wT} (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{max c v r, max c v r, v, c}
        ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)))
    (η : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r, max c v r, v, c}
        ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) (ComplexShape.up ℤ))] :
    ∃ (_hproduct : HasProduct (fun n : ℕ ↦
      (DerivedCategory.singleFunctor _ 0).obj (F.obj (op n)))),
      IsIso (basisInverseLimitComparison F RF η) ∧
      IsDerivedLimit
        (K := fun n : ℕ ↦ (DerivedCategory.singleFunctor
          (ringedSiteModules.{max c v r, max c v r, v, c} ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) 0).obj
              (F.obj (op n)))
        (fun n : ℕ ↦ (DerivedCategory.singleFunctor _ 0).map
          (F.map (homOfLE (Nat.le_succ n)).op))
        (RF.obj ((DerivedCategory.singleFunctor _ 0).obj F)) ∧
      (∀ U ∈ B, ∀ p : ℕ, 0 < p →
        IsZero (basisModuleCohomology.{c, v, r, w, wA} J O U p (limit F))) := by
  sorry

end CategoryTheory
