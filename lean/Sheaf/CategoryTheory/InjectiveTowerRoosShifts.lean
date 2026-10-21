/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.TowerProductFunctor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.CategoryTheory.KInjectiveBridge
import Sheaf.CategoryTheory.StrictRoosHomotopyFunctor
import Sheaf.Algebra.Homology.EndomorphismFibreCoordinateCalculus
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Injective tower Roos comparisons and signed integer shifts

Source: Stacks Project, sites-cohomology.tex, Tag 0941; derived.tex, Tags 014E,
070I, 08BJ and 0BK6; homology.tex, Tag 011G. Blueprint main-20261015,
sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md, coefficient comparisons.
(blueprint: lem-pur-injective-tower-roos-shifts)

The cone, its coordinates and its kernel inclusion are the existing `roosF`, `roosχ`
and `roosι`. Natural-number level n denotes positive level n+1. Products below are
products of complexes, with their actual projections; their localized fans are proved
limiting, so no exactness of products of arbitrary module sheaves is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a b w uC vC r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory.InjectiveTowerRoos

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

variable [HasLimitsOfShape ℕᵒᵖ A]

/-- The actual product of the ordinary limit-cone components.
Source: Stacks Tag 0941 (blueprint: lem-pur-injective-tower-roos-shifts). -/
noncomputable abbrev inclusion (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    limit I.asFunctor ⟶ roosP I :=
  Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))

/-- The insertion boundary in the inverse rotation of the fixed cone triangle.
Source: Stacks Tags 014E and 0941
(blueprint: lem-pur-injective-tower-roos-shifts).
In the coordinates `roosχ` this is b ↦ (b,0), with the canonical [-1][1] reindexing. -/
noncomputable abbrev boundary (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    roosP I ⟶ (roosF.obj I)⟦(1 : ℤ)⟧ :=
  (CochainComplex.mappingCone.triangle (roosU I)).invRotate.mor₃

variable [HasDerivedCategory.{w} A]

/-- Localize a specified termwise shift comparison and apply the localization's shift.
Source: Stacks Tags 011G and 0941
(blueprint: lem-pur-injective-tower-roos-shifts). -/
noncomputable def localizedShift
    (F : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ)
    (cs : F.CommShift ℤ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m : ℤ) :
    DerivedCategory.Q.obj (F.obj (I⟦m⟧)) ⟶ (DerivedCategory.Q.obj (F.obj I))⟦m⟧ :=
  DerivedCategory.Q.map ((Functor.commShiftIso F (self := cs) m).hom.app I) ≫
    (DerivedCategory.Q.commShiftIso m).hom.app (F.obj I)

/-- The actual localized product of limit projections, in the termwise derived-product model.
Source: Stacks Tag 0941 (blueprint: lem-pur-injective-tower-roos-shifts). -/
noncomputable abbrev projection (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.obj (limit I.asFunctor) ⟶ DerivedCategory.Q.obj (roosP I) :=
  DerivedCategory.Q.map (inclusion I)

end CategoryTheory.InjectiveTowerRoos

namespace CategoryTheory

/-- The injective-tower comparison uses the actual kernel inclusion and the normalized
signed shifts, including the boundary sign, without exactness of arbitrary products.

Source: Stacks Project, sites-cohomology.tex, Tag 0941; derived.tex, Tags 070I,
08BJ, 0BK6 and 014E; homology.tex, Tag 011G; blueprint main-20261015,
sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md, coefficient comparisons.
(blueprint: lem-pur-injective-tower-roos-shifts)

Proof plan:
1. For an injective tower J, the prefix tower E_n(J_n) embeds monomorphically in
E_{n+1}(J_n). Extend the map to J corresponding to id at level n. Its level n+1
component splits the transition (def-sp-injective-resolutions and levelwise abelianness).
2. Evaluate the K-injective tower using lem-weil-tower-evaluation-kinjective. Apply
lem-pc-ringed-space-product-kinjective to its evaluated complexes: their termwise product
is K-injective and its localized projections form a product fan.
3. Write h=1-s. Its kernel is the actual termwise limit, with inclusion j. Choose
transition splittings u_n in each degree. The recursion a_0=0,
a_{n+1}=u_n(a_n-pr_n) gives h a=id. Thus h is degreewise split epi.
4. Apply lem-weil-degreewise-epi-kernel-cocone-qis. Its kernel comparison is precisely
roosι=(0,j), and is a quasi-isomorphism with all actual limit-cone components.
5. Inverse-rotate the cone triangle with third arrow -pr_x. The first arrow is pr_x,
and the boundary is insertion in y. Localize and transport by Q(roosι). This gives the
displayed distinguished Roos triangle with first arrow Qj and middle arrow Q(1-s).
The total-derived-limit computation in lem-weil-pbc-ringed-strict-tower-homotopy-limit
identifies its first object with L(N); the final normalization equation retains q:X→I.
6. Apply the endomorphism-fibre coordinate calculus to h and reorder (v,u) as (y,x).
The shift comparison is ((-1)^r y,x), its inverse has the same signs, and augmentation
commutes with it. Zero and addition coherence are the CommShift laws. Shifts preserve
K-injectivity by shifting acyclic sources back, and preserve injective terms by reindexing.
7. Projection to x commutes with shift. Insertion in y acquires (-1)^r. Conjugate the
second identity by Q(roosι)[1] to obtain exactly the signed boundary identity below,
using shiftFunctorComm for [1][r]=[r][1].
8. For maps of chosen resolutions, universal properties give naturality of j and of
the cone maps. The unique normalized transported boundary is therefore natural too.
K-injective Hom_K=Hom_D (lem-weil-pbc-kinjective-hom-derived) and the compatible tower
homotopy functor (lem-pur-strict-roos-homotopy-functor) descend these identities through
localization and make them independent of a resolution comparison up to homotopy.
The formulas apply to all integer r, zero complexes, and the zero coefficient ring. -/
theorem injectiveTowerRoosShifts
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] (R : Sheaf J RingCat.{r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{r, r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R)] :
    ∃ (csP : (InjectiveTowerRoos.productFunctor
        (A := ringedSiteModules.{r, r} R)).CommShift ℤ)
      (csL : (roosLimitFunctor (A := ringedSiteModules.{r, r} R)).CommShift ℤ)
      (csC : (roosF (A := ringedSiteModules.{r, r} R)).CommShift ℤ)
      (δ : ∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ,
        DerivedCategory.Q.{w}.obj (roosP I) ⟶
          (DerivedCategory.Q.{w}.obj (limit I.asFunctor))⟦(1 : ℤ)⟧),
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        (m q : ℤ) (n : ℕ),
        ((Functor.commShiftIso InjectiveTowerRoos.productFunctor (self := csP) m).hom.app I).f q ≫
            ((roosP I).shiftFunctorObjXIso m q (q + m) rfl).hom ≫
            (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n).f (q + m) =
          (Pi.π (fun k : ℕ ↦ (I⟦m⟧).asFunctor.obj (op k)) n).f q ≫
            ((I.shiftFunctorObjXIso m q (q + m) rfl).hom).app (op n)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        (m q : ℤ) (n : ℕ),
        ((Functor.commShiftIso roosLimitFunctor (self := csL) m).hom.app I).f q ≫
            (CochainComplex.shiftFunctorObjXIso (limit I.asFunctor) m q (q + m) rfl).hom ≫
            (limit.π I.asFunctor (op n)).f (q + m) =
          (limit.π (I⟦m⟧).asFunctor (op n)).f q ≫
            ((I.shiftFunctorObjXIso m q (q + m) rfl).hom).app (op n)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (m p : ℤ),
        ((Functor.commShiftIso roosF (self := csC) m).hom.app I).f (p + 1) ≫
            ((roosF.obj I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom ≫
            (roosχ I (p + m)).hom =
          (roosχ (I⟦m⟧) p).hom ≫ biprod.map
            (m.negOnePow •
              (((Functor.commShiftIso InjectiveTowerRoos.productFunctor
                (self := csP) m).hom.app I).f p ≫
                ((roosP I).shiftFunctorObjXIso m p (p + m) rfl).hom))
            (((Functor.commShiftIso InjectiveTowerRoos.productFunctor
                (self := csP) m).hom.app I).f (p + 1) ≫
              ((roosP I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (m p : ℤ),
        ((Functor.commShiftIso roosF (self := csC) m).inv.app I).f (p + 1) ≫
            (roosχ (I⟦m⟧) p).hom =
          ((roosF.obj I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom ≫
            (roosχ I (p + m)).hom ≫ biprod.map
              (m.negOnePow •
                (((roosP I).shiftFunctorObjXIso m p (p + m) rfl).inv ≫
                  ((Functor.commShiftIso InjectiveTowerRoos.productFunctor
                    (self := csP) m).inv.app I).f p))
              (((roosP I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).inv ≫
                ((Functor.commShiftIso InjectiveTowerRoos.productFunctor
                  (self := csP) m).inv.app I).f (p + 1))) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (m : ℤ),
        roosι (I⟦m⟧) ≫ (Functor.commShiftIso roosF (self := csC) m).hom.app I =
          (Functor.commShiftIso roosLimitFunctor (self := csL) m).hom.app I ≫ (roosι I)⟦m⟧') ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        [I.IsKInjective] (_hIinj : ∀ i : ℤ, Injective (I.X i)),
        (∀ (i : ℤ) (n : ℕ), IsSplitEpi ((I.X i).map (homOfLE (Nat.le_succ n)).op)) ∧
        (∀ n : ℕ, CochainComplex.IsKInjective (I.asFunctor.obj (op n))) ∧
        (roosP I).IsKInjective ∧
        Nonempty (IsLimit (DerivedCategory.Q.{w}.mapCone
          (limit.cone (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n)))))) ∧
        QuasiIso (roosι I) ∧
        ∃ ε : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
            DerivedCategory.Q.{w}.obj (roosF.obj I),
          ε.hom = DerivedCategory.Q.map (roosι I) ∧
          Triangle.mk (InjectiveTowerRoos.projection I) (DerivedCategory.Q.map (roosU I))
            (δ I) ∈ distTriang (DerivedCategory.{w} (ringedSiteModules.{r, r} R)) ∧
          δ I ≫ ε.hom⟦(1 : ℤ)⟧' =
            DerivedCategory.Q.map (InjectiveTowerRoos.boundary I) ≫
              (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I) ∧
          (∀ m : ℤ,
            InjectiveTowerRoos.projection (I⟦m⟧) ≫
                InjectiveTowerRoos.localizedShift InjectiveTowerRoos.productFunctor csP I m =
              InjectiveTowerRoos.localizedShift roosLimitFunctor csL I m ≫
                (InjectiveTowerRoos.projection I)⟦m⟧' ∧
            δ (I⟦m⟧) ≫
                (InjectiveTowerRoos.localizedShift roosLimitFunctor csL I m)⟦(1 : ℤ)⟧' =
              m.negOnePow •
                (InjectiveTowerRoos.localizedShift InjectiveTowerRoos.productFunctor csP I m ≫
                  (δ I)⟦m⟧' ≫
                  (shiftFunctorComm (DerivedCategory.{w} (ringedSiteModules.{r, r} R))
                    (1 : ℤ) m).hom.app (DerivedCategory.Q.obj (limit I.asFunctor))))) ∧
      (∀ (I I' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        [I.IsKInjective] [I'.IsKInjective]
        (_hIinj : ∀ i : ℤ, Injective (I.X i)) (_hI'inj : ∀ i : ℤ, Injective (I'.X i))
        (f : I ⟶ I'),
        DerivedCategory.Q.map (roosPmap f) ≫ δ I' =
          δ I ≫ (DerivedCategory.Q.map (roosLimitFunctor.map f))⟦(1 : ℤ)⟧') ∧
      (∀ (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ⥤
            DerivedCategory.{w} (ringedSiteModules.{r, r} R))
        (η : roosLimitFunctor ⋙
          DerivedCategory.Q.{w} (C := ringedSiteModules.{r, r} R) ⟶
          DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ⋙ RF)
        (_hRF : RF.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) (ComplexShape.up ℤ)))
        (_hη : ∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ,
          I.IsKInjective → IsIso (η.app I))
        (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (q : X ⟶ I)
        [QuasiIso q] [I.IsKInjective] (_hIinj : ∀ i : ℤ, Injective (I.X i)),
        ∃ d : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅ RF.obj (DerivedCategory.Q.obj X),
          d.hom ≫ RF.map (DerivedCategory.Q.map q) = η.app I ∧
          Triangle.mk (d.inv ≫ InjectiveTowerRoos.projection I)
            (DerivedCategory.Q.map (roosU I)) (δ I ≫ d.hom⟦(1 : ℤ)⟧') ∈
              distTriang (DerivedCategory.{w} (ringedSiteModules.{r, r} R))) := by
  sorry

end CategoryTheory
