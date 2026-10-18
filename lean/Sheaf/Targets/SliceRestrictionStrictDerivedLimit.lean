/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Slice restriction and strict derived limits

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941, with sites-modules.tex,
Tag 03DJ (blueprint: lem-sp-slice-restriction-strict-derived-limit).
-/

@[expose] public section

set_option autoImplicit false

universe u v w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The levelwise restriction functor on strict towers over a localized site.
Source: sites-modules.tex, Tags 03DJ and 04IX (blueprint:
lem-sp-slice-restriction-strict-derived-limit). -/
noncomputable abbrev sliceTowerRestriction
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C) :
    (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ⥤
      (ℕᵒᵖ ⥤ ringedSiteModules.{r} (Sheaf.over R U)) :=
  (Functor.whiskeringRight (ℕᵒᵖ) (ringedSiteModules.{r} R)
    (ringedSiteModules.{r} (Sheaf.over R U))).obj (SheafOfModules.overFunctor R U)

/-- The derived functor induced by levelwise slice restriction.
Source: sites-modules.tex, Tags 03DJ and 04IX (blueprint:
lem-sp-slice-restriction-strict-derived-limit). -/
noncomputable abbrev sliceTowerDerivedRestriction
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify (J.over U) AddCommGrpCat.{r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} (Sheaf.over R U))]
    [(SheafOfModules.overFunctor R U).Additive]
    [PreservesFiniteLimits (sliceTowerRestriction R U)]
    [PreservesFiniteColimits (sliceTowerRestriction R U)] :
    DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ⥤
      DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} (Sheaf.over R U)) :=
  (sliceTowerRestriction R U).mapDerivedCategory

/-- Termwise inverse limit of a complex of strict module towers.
Source: Stacks 0940 and 0941 (blueprint: lem-sp-slice-restriction-strict-derived-limit). -/
noncomputable abbrev sliceStrictTowerLimitComplex
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) :=
  (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ⥤
    ringedSiteModules.{r} R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The actual underived restriction/limit comparison, degreewise `limit.post`.
Source: Stacks 04IX and 0940 (blueprint: lem-sp-slice-restriction-strict-derived-limit).
Its components are the maps induced by the restricted limit cone, hence the identity
on compatible tuples. No comparison map is supplied as an arbitrary parameter. -/
noncomputable def sliceStrictTowerLimitComparison
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    [(SheafOfModules.overFunctor.{r} R U).Additive]
    (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ℤ) :
    ((SheafOfModules.overFunctor R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((sliceStrictTowerLimitComplex R).obj I) ⟶
      (sliceStrictTowerLimitComplex (Sheaf.over R U)).obj
        (((sliceTowerRestriction R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) where
  f i := limit.post (I.X i) (SheafOfModules.overFunctor R U)
  comm' i j _ := (limit.map_post (I.d i j) (SheafOfModules.overFunctor R U)).symm

/-- The canonical nth projection of a termwise strict-tower limit complex.
Source: Stacks 0940 (blueprint: lem-sp-slice-restriction-strict-derived-limit). -/
noncomputable abbrev sliceStrictTowerLimitProjection
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r})
    (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ℤ) (n : ℕ) :=
  (NatTrans.mapHomologicalComplex
    (lim.π (C := ringedSiteModules.{r} R) (op n)) (ComplexShape.up ℤ)).app I

/-- Restriction to a slice commutes canonically with total right derived strict inverse limit.

Source: Stacks 0940 and 0941, with 04IX and 03DJ
(blueprint: lem-sp-slice-restriction-strict-derived-limit).

The existential exactness witnesses express properties of the fixed restrictions, not
additional assumptions. The units and their right-derived universal properties specify
actual total derived limits. They are invertible on K-injective towers. The displayed
normalization specifies the comparison on complexes; the last equation is compatibility
with every derived tower projection on K-injective representatives. Here `n : ℕ` means the
paper's index `n + 1`.

In particular, take any complex representing H and its strict multiplication-by-a tower.
The fixed restriction functor keeps section modules and sends each scalar transition to
multiplication by the restricted scalar. The same comparison therefore gives the stated
multiplication-tower isomorphism for every global a, including zero and one.

Proof:
1. Lift the exact extension-by-zero/restriction adjunction componentwise to strict towers
   (lem-pur-site-restriction-module-adjunction-exact). The Hom bijections are compatible
   with transitions by naturality; exactness is levelwise
   (lem-weil-tower-category-levelwise-abelian). Both fixed restrictions induce derived
   functors, because exactness preserves quasi-isomorphisms.
2. Apply lem-weil-pbc-right-adjoint-preserves-kinjective to the tower adjunction: its
   exact left adjoint makes restriction preserve K-injectivity in the tower category.
3. Ordinary module-sheaf limits are sectionwise compatible tuples. Restriction keeps
   these tuples, so limit.post is an isomorphism and commutes with all projections
   and differentials (def-pur-localized-ringed-site).
4. Use lem-weil-pbc-ringed-strict-tower-homotopy-limit on the original and slice sites
   to obtain the two derived limits and units. For a K-injective resolution q : X → I,
   restricted q is still a quasi-isomorphism with K-injective target. Thus the two
   derived limits are computed by restriction of lim I and by lim of restricted I.
   Step 3 identifies them and gives precisely the normalization below.
5. By lem-weil-pbc-kinjective-hom-derived, maps are homotopy classes of maps between
   K-injective resolutions. The tuple comparison is natural and additive, so respects
   homotopies and descends to the natural isomorphism e, independently of resolution.
6. The nth projection is lim I → I_n; invert the unit and the evaluated resolution
   quasi-isomorphism to get its derived projection. Step 3 proves the last equation.
   Restriction preserves scalar transitions sectionwise. Apply the same result to a
   multiplication-by-a representative tower; levelwise quasi-isomorphisms ensure it
   is independent of the chosen representative of H. -/
theorem sliceRestrictionStrictDerivedLimit
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{max u v r})
    (_hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R)]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r} (Sheaf.over R U))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} (Sheaf.over R U))] :
    ∃ (_hadd : (SheafOfModules.overFunctor.{max u v r} R U).Additive)
      (_hfl : PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v r} R U))
      (_hfc : PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v r} R U))
      (_htl : PreservesFiniteLimits (sliceTowerRestriction R U))
      (_htc : PreservesFiniteColimits (sliceTowerRestriction R U))
      (L : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R) ⥤
        DerivedCategory.{w} (ringedSiteModules.{max u v r} R))
      (LU : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} (Sheaf.over R U)) ⥤
        DerivedCategory.{w} (ringedSiteModules.{max u v r} (Sheaf.over R U)))
      (η : sliceStrictTowerLimitComplex R ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ L)
      (ηU : sliceStrictTowerLimitComplex (Sheaf.over R U) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ LU)
      (e : L ⋙ (SheafOfModules.overFunctor R U).mapDerivedCategory ≅
        sliceTowerDerivedRestriction R U ⋙ LU),
      L.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R)
          (ComplexShape.up ℤ)) ∧
      LU.IsRightDerivedFunctor ηU
        (HomologicalComplex.quasiIso
          (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} (Sheaf.over R U)) (ComplexShape.up ℤ)) ∧
      (∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) ∧
      (∀ I, CochainComplex.IsKInjective I → IsIso (ηU.app I)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R) ℤ),
        (SheafOfModules.overFunctor R U).mapDerivedCategory.map (η.app I) ≫
            e.hom.app (DerivedCategory.Q.obj I) ≫
            LU.map ((sliceTowerRestriction R U).mapDerivedCategoryFactors.hom.app I) =
          (SheafOfModules.overFunctor R U).mapDerivedCategoryFactors.hom.app
              ((sliceStrictTowerLimitComplex R).obj I) ≫
            DerivedCategory.Q.map (sliceStrictTowerLimitComparison R U I) ≫
            ηU.app (((sliceTowerRestriction R U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R) ℤ),
        CochainComplex.IsKInjective I →
        ∃ (_hη : IsIso (η.app I))
          (_hηU : IsIso (ηU.app (((sliceTowerRestriction R U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I))),
          ∀ n : ℕ,
            e.hom.app (DerivedCategory.Q.obj I) ≫
                LU.map ((sliceTowerRestriction R U).mapDerivedCategoryFactors.hom.app I) ≫
                inv (ηU.app (((sliceTowerRestriction R U).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj I)) ≫
                DerivedCategory.Q.map (sliceStrictTowerLimitProjection (Sheaf.over R U)
                  (((sliceTowerRestriction R U).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj I) n) =
              (SheafOfModules.overFunctor R U).mapDerivedCategory.map (inv (η.app I)) ≫
                (SheafOfModules.overFunctor R U).mapDerivedCategoryFactors.hom.app
                  ((sliceStrictTowerLimitComplex R).obj I) ≫
                DerivedCategory.Q.map
                  (((SheafOfModules.overFunctor R U).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map (sliceStrictTowerLimitProjection R I n))) := by
  sorry

end CategoryTheory
