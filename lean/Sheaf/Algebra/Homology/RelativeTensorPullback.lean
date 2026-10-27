/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension

/-! # Relative tensor and derived pullback on arbitrary ringed topoi

Source: Stacks Project, Cohomology on Sites, Tag 08I6,
`lemma-variant-derived-pullback` (blueprint: lem-sfb-ringed-topos-relative-tensor-pullback).

The relative tensor retains the action of the target ring. It is specified by an actual
complex-valued bifunctor, its underlying scalar-restricted total tensor, and its scalar
formula. The derived comparison is normalized on every flat-term K-flat representative.
All auxiliary definitions below merely name existing constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe uC vC uD vD r w
universe uA vA uB vB wA wB

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.SemilinearSections (Mod res)

namespace SheafOfModules.RelativeTensorPullback

/-- Flat-term K-flat representatives, using the recorded tensor-acyclicity predicate.
Source: Stacks, Tags 06YN and 06YS
(blueprint: lem-sfb-ringed-topos-relative-tensor-pullback). -/
def flatRepresentatives {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (A : Sheaf J CommRingCat.{r}) :
    ObjectProperty (CochainComplex (Mod J A) ℤ) :=
  fun P ↦ P.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ, IsFlatOnSite (J := J) (R := A) (P.X n)

/-- The existing signed direct-sum total tensor, with its two variables uncurried.
Source: Stacks, Tag 06YM
(blueprint: lem-sfb-ringed-topos-relative-tensor-pullback). -/
abbrev total {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (A : Sheaf J CommRingCat.{r}) :=
  Functor.uncurry.obj ((curriedTensor (Mod J A)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

/-- The localization of the full subcategory of flat-term K-flat representatives.
Source: Stacks, Tags 06YS and 06YU
(blueprint: lem-sfb-ringed-topos-relative-tensor-pullback). -/
abbrev qRep {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (A : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (Mod J A)] :=
  (flatRepresentatives A).ι ⋙
    @DerivedCategory.Q (Mod J A) _ _ ‹HasDerivedCategory.{w} (Mod J A)›

/-- Total tensor followed by localization, on the specified resolving class.
Source: Stacks, Tag 06YU
(blueprint: lem-sfb-ringed-topos-relative-tensor-pullback). -/
abbrev tensorRep {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (A : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (Mod J A)] :=
  ((flatRepresentatives A).ι.prod (flatRepresentatives A).ι) ⋙ total A ⋙
    @DerivedCategory.Q (Mod J A) _ _ ‹HasDerivedCategory.{w} (Mod J A)›

/-- The local pure tensor in a fixed summand of the actual signed total complex.
Source: Stacks, Tags 06YM and 08I6
(blueprint: lem-sfb-ringed-topos-relative-tensor-pullback). -/
def totalPure {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (A : Sheaf J CommRingCat.{r})
    (P H : CochainComplex (Mod J A) ℤ) (p q n : ℤ) (hpq : p + q = n)
    (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (H.X q).val.obj U) :
    (((total A).obj (P, H)).X n).val.obj U :=
  (CochainComplex.ιMapBifunctor P H (curriedTensor (Mod J A)) p q n hpq).val.app U
    (ringedComparisonPure A (P.X p) (H.X q) U x y)

/-- The derived pullback comparison on complex localizations.

Source: Stacks Project, Cohomology on Sites, Tags 06YY and 07A4
(blueprint: lem-sfb-ringed-topos-relative-tensor-pullback).

This is the explicit composite transporting the homotopy-category comparison through
the quotient comparison isomorphisms; it is included here so the statement does not
depend on an uncited theorem module.
-/
noncomputable def pullbackComplexComparison
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (L : A ⥤ B) [L.Additive]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    LF.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj
      ((L.mapHomologicalComplex (.up ℤ)).obj P) :=
  LF.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
    epsilon.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((L.mapHomologicalComplex (.up ℤ)).obj P)

/-- Canonical relative tensor comparison for an arbitrary ringed-topos morphism.

Source: Stacks Project, Cohomology on Sites, Tag 08I6,
`lemma-variant-derived-pullback`
(blueprint: lem-sfb-ringed-topos-relative-tensor-pullback).

`L`, `V`, `adj`, `I`, and `c` spell out the geometric morphism and structural map.
`uStar`, `hobj`, and `hmap` specify its actual tensor pullback. `TA` and `TC`, with
`rA` and `rC`, are presentations of the recorded derived tensor by resolving classes.
The output `T` is the relative total tensor with the A-action on its first factor;
`under` identifies its underlying complex with the existing tensor over RI. `b` has
both ordinary balanced formulas, on every summand. `Urel` is its derived bifunctor;
`rrel` computes it on representatives. `alpha` is a natural isomorphism in D(A),
normalized by the final representative equation, rather than an arbitrary isomorphism.

Proof plan:
1. Resolve E and G by flat-term K-flat P and Q (lem-pc-kflat-resolution).
   Factor the ringed morphism through RI = inverse-image B. Pullback preservation
   (lem-weil-pbc-ringed-pullback-preserves-kflat) makes I(Q) and uStar(Q) K-flat
   with flat terms; lem-weil-pbc-ringed-topoi-derived-pullback computes LF on Q.
2. Form total(P tensor_RI I(Q)) with A acting through P. Resolve Res(P) over RI.
   Tensoring its resolution with K-flat I(Q) is a quasi-isomorphism, by
   lem-weil-pbc-total-tensor-homotopy-cone-signs. Thus its underlying derived
   RI-object is the tensor of Res(E) with inverse-image G; Res(P) need not be K-flat.
3. In each bidegree use x tensor (a tensor h) maps to ax tensor h, with inverse
   x tensor h maps to x tensor (1 tensor h). Balancing proves the inverse laws.
   Extend local pairings by lem-pc-sites-module-sheafification-bilinear-extension
   and the sheaf tensor universal property (def-pur-sheaf-tensor-product).
   Taking direct sums gives the chain isomorphism b: both differentials send a
   generator to a dx tensor h plus (-1)^p ax tensor dh (def-pc-tensor-complex-sheaves).
4. Both formulas commute with maps of P and Q. K-flat tensor preserves the
   quasi-isomorphisms inverted in either variable. Detect quasi-isomorphisms after
   scalar restriction. Apply lem-weil-pbc-site-derived-tensor-descent in both
   variables to descend T and b, giving Urel, rrel and alpha. Naturality persists
   for inverse denominators, giving independence of resolutions and the displayed
   representative normalization. No flatness of c, boundedness, or Tor bound is used.
-/
theorem relativeTensorPullback
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A RI : Sheaf J CommRingCat.{r}} {B : Sheaf K CommRingCat.{r}}
    (L : Sheaf K (Type r) ⥤ Sheaf J (Type r))
    (V : Sheaf J (Type r) ⥤ Sheaf K (Type r))
    (adj : L ⊣ V) [PreservesFiniteLimits L]
    (I : AlgebraicInverseImage L B RI) (c : RI ⟶ A)
    [I.modules.Additive]
    (uStar : Mod K B ⥤ Mod J A)
    (hobj : ∀ M : Mod K B, uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : Mod K B} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (Mod J A)] [HasDerivedCategory.{w} (Mod J RI)]
    [HasDerivedCategory.{w} (Mod K B)]
    (LF : DerivedCategory (Mod K B) ⥤ DerivedCategory (Mod J A))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (Mod K B) (.up ℤ)))
    (TA : DerivedCategory (Mod J A) × DerivedCategory (Mod J A) ⥤
      DerivedCategory (Mod J A))
    (TC : DerivedCategory (Mod J RI) × DerivedCategory (Mod J RI) ⥤
      DerivedCategory (Mod J RI))
    (rA : tensorRep.{uC, vC, r, w} A ≅
      ((qRep.{uC, vC, r, w} A).prod (qRep.{uC, vC, r, w} A)) ⋙ TA)
    (rC : tensorRep.{uC, vC, r, w} RI ≅
      ((qRep.{uC, vC, r, w} RI).prod (qRep.{uC, vC, r, w} RI)) ⋙ TC) :
    ∃ (T : CochainComplex (Mod J A) ℤ × CochainComplex (Mod J RI) ℤ ⥤
          CochainComplex (Mod J A) ℤ)
      (under : T ⋙ (res c).mapHomologicalComplex (.up ℤ) ≅
        (((res c).mapHomologicalComplex (.up ℤ)).prod (𝟭 _)) ⋙ total RI)
      (b : ((𝟭 _).prod (uStar.mapHomologicalComplex (.up ℤ))) ⋙ total A ≅
        ((𝟭 _).prod (I.modules.mapHomologicalComplex (.up ℤ))) ⋙ T),
      (∀ (P : CochainComplex (Mod J A) ℤ) (H : CochainComplex (Mod J RI) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (W : Cᵒᵖ)
        (a : A.obj.obj W) (x : (P.X p).val.obj W) (h : (H.X q).val.obj W),
        ((under.inv.app (P, H)).f n).val.app W
            (totalPure RI (((res c).mapHomologicalComplex (.up ℤ)).obj P) H
              p q n hpq W (a • x) h) =
          a • @id (((T.obj (P, H)).X n).val.obj W)
            (((under.inv.app (P, H)).f n).val.app W
              (totalPure RI (((res c).mapHomologicalComplex (.up ℤ)).obj P) H
                p q n hpq W x h))) ∧
      (∀ (P : CochainComplex (Mod J A) ℤ) (Q : CochainComplex (Mod K B) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (W : Cᵒᵖ)
        (x : (P.X p).val.obj W) (a : A.obj.obj W)
        (h : (I.modules.obj (Q.X q)).val.obj W),
        ((under.hom.app (P, (I.modules.mapHomologicalComplex (.up ℤ)).obj Q)).f n).val.app W
          (((b.hom.app (P, Q)).f n).val.app W
            (totalPure A P ((uStar.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq W x
              ((eqToHom (hobj (Q.X q)).symm).val.app W
                (ringedComparisonScalarSection c (I.modules.obj (Q.X q)) W a h)))) =
          totalPure RI (((res c).mapHomologicalComplex (.up ℤ)).obj P)
            ((I.modules.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq W (a • x) h) ∧
      (∀ (P : CochainComplex (Mod J A) ℤ) (Q : CochainComplex (Mod K B) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (W : Cᵒᵖ)
        (x : (P.X p).val.obj W) (h : (I.modules.obj (Q.X q)).val.obj W),
        ((b.inv.app (P, Q)).f n).val.app W
          (((under.inv.app (P, (I.modules.mapHomologicalComplex (.up ℤ)).obj Q)).f n).val.app W
            (totalPure RI (((res c).mapHomologicalComplex (.up ℤ)).obj P)
              ((I.modules.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq W x h)) =
          totalPure A P ((uStar.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq W x
            ((eqToHom (hobj (Q.X q)).symm).val.app W
              (ringedComparisonScalarSection c (I.modules.obj (Q.X q)) W 1 h))) ∧
      ∃ (IDer : DerivedCategory (Mod K B) ⥤ DerivedCategory (Mod J RI))
        (rI : DerivedCategory.Q ⋙ IDer ≅
          I.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (Urel : DerivedCategory (Mod J A) × DerivedCategory (Mod K B) ⥤
          DerivedCategory (Mod J A))
        (rrel : ((flatRepresentatives A).ι.prod
          ((flatRepresentatives B).ι ⋙ I.modules.mapHomologicalComplex (.up ℤ))) ⋙
            T ⋙ DerivedCategory.Q ≅ ((qRep.{uC, vC, r, w} A).prod (qRep.{uD, vD, r, w} B)) ⋙ Urel)
        (alpha : ((𝟭 _).prod LF) ⋙ TA ≅ Urel),
        Nonempty (Urel ⋙ (res c).mapDerivedCategory ≅
          (((res c).mapDerivedCategory).prod IDer) ⋙ TC) ∧
        ∀ (P : (flatRepresentatives A).FullSubcategory)
          (Q : (flatRepresentatives B).FullSubcategory),
          ∃ hQ : flatRepresentatives A
            ((uStar.mapHomologicalComplex (.up ℤ)).obj Q.obj),
            TA.map
                (X := (DerivedCategory.Q.obj P.obj, LF.obj (DerivedCategory.Q.obj Q.obj)))
                (Y := (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj
                  ((uStar.mapHomologicalComplex (.up ℤ)).obj Q.obj)))
                (CategoryTheory.Prod.mkHom (𝟙 _)
                  (pullbackComplexComparison uStar LF epsilon Q.obj)) ≫
                rA.inv.app (P, ⟨(uStar.mapHomologicalComplex (.up ℤ)).obj Q.obj, hQ⟩) ≫
                  DerivedCategory.Q.map (b.hom.app (P.obj, Q.obj)) ≫ rrel.hom.app (P, Q) =
              alpha.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) := by
  sorry

end SheafOfModules.RelativeTensorPullback
