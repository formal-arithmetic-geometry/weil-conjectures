/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.FiniteDirectImageComposition
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Successive transposes through the finite derived compositor

Source: Stacks Project, Cohomology on Sites, Tags 07A6, 0D6D and 0D6E;
Categories, Tag 0DV0 (blueprint: lem-pur-ordinary-derived-composite-transpose).

We use the published fixed-scalar presentation of D(T_proet, A): the ordinary
unbounded derived category of sheaves of modules over the size lift of A.
Pullback is the existing K-flat derived pullback, its adjunction is the canonical
derived adjunction, and the right comparison is the specified K-injective compositor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

private theorem successive_transpose
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') {M : C} {Q : D} {N : E}
    (w : M ⟶ R.obj Q) (v : Q ⟶ R'.obj N) :
    ((a.comp b).homEquiv M N).symm (w ≫ R.map v) =
      L'.map (L.map w ≫ a.counit.app Q) ≫ (L'.map v ≫ b.counit.app N) := by
  rw [Adjunction.comp_homEquiv]
  change (b.homEquiv _ _).symm ((a.homEquiv _ _).symm (w ≫ R.map v)) = _
  rw [Adjunction.homEquiv_naturality_right_symm]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]

private theorem transpose_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (c : L' ⟶ L) {M : C} {N : D} (h : M ⟶ R.obj N) :
    L'.map (h ≫ (conjugateEquiv a b c).app N) ≫ b.counit.app N =
      c.app M ≫ (a.homEquiv M N).symm h := by
  rw [Functor.map_comp, Category.assoc, conjugateEquiv_counit,
    c.naturality_assoc, Adjunction.homEquiv_counit]

private theorem derived_compositor_conjugate
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (finiteDirectImageComposition A f g).inv =
      conjugateEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom := by
  have : (lowerStar (ModuleCat.{u + 1} A) f).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  have hadj {S T : Scheme.{u}} (h : S ⟶ T) :
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h
        ).mapDerivedCategoryRightDerivedAdjunction =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).ofNatIsoLeft
        (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctorIsoMapDerivedCategory := by
    refine ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h
      ).mapHomotopyCategory (.up ℤ)).derived_eq_ofNatIsoLeft
      (HomotopyCategory.quasiIso _ (.up ℤ))
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
      (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctorIsoMapDerivedCategory.symm ?_
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom]
    have hfac := congr_app
      (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
        (upperStar (ModuleCat.{u + 1} A) h)) K
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hfac
    exact (Iso.eq_inv_comp
      ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctorIsoMapDerivedCategory.app
        (DerivedCategory.Qh.obj K))).2 hfac
  change (Functor.rightDerivedFunctorCompIso'
    (lowerStar (ModuleCat.{u + 1} A) f) (lowerStar (ModuleCat.{u + 1} A) g)
    (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom = _
  rw [Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
    _ (upperStarComp (ModuleCat.{u + 1} A) f g) (by
      simp [upperStarComp])]
  rw [hadj, hadj, hadj]
  ext K
  simp [conjugateEquiv_apply_app, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso]


/-- Successive transposition agrees with transposition along the composite, with
both specified canonical comparison maps, on all ordinary unbounded derived objects.
Source: Stacks Project, Tags 07A6, 0D6D, 0D6E and Categories Tag 0DV0
(blueprint: lem-pur-ordinary-derived-composite-transpose).

Proof:
1. The exact finite-coefficient inverse image has a right adjoint preserving
K-injective complexes. The ordinary upperStarComp and lowerStarComp are adjunction
mates. Apply the generic right-derived composition conjugacy theorem to them.
2. Compare the exact-map derived adjunction with the K-flat derived adjunction
using their left-derived counit factorization. Transporting conjugation through
this comparison identifies finiteDirectImageComposition inverse with the mate
of leftDerivedUpperStarComp, with precisely the published normalizations.
3. The counit equation for conjugation, followed by naturality of the left
comparison, identifies transposition along the composite with transposition by
the composite Hom bijection. Cancellation of the compositor with its inverse
gives the first displayed equality.
4. Expand the composite Hom bijection as the two successive Hom bijections.
Naturality in the right-hand object and the counit formula give the successive
transpose of w followed by R_g(v). Precompose with the pullback comparison and
cancel the compositor with its inverse for the second equality. The same
calculation without that precomposition is the final clause. -/
theorem ordinaryDerivedCompositeTranspose
    (P : PurityFiniteSetting.{u})
    (X Y B : Over (Spec (CommRingCat.of P.field.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    (f : X ⟶ Y) (g : Y ⟶ B)
    (M : DerivedCategory (Sheaf (ProEt.topology B.left) (ModuleCat.{u + 1} P.Coefficient)))
    (Q : DerivedCategory (Sheaf (ProEt.topology Y.left) (ModuleCat.{u + 1} P.Coefficient)))
    (N : DerivedCategory (Sheaf (ProEt.topology X.left) (ModuleCat.{u + 1} P.Coefficient)))
    (w : M ⟶ (lowerStar (ModuleCat.{u + 1} P.Coefficient) g.left).rightDerivedFunctor.obj Q)
    (v : Q ⟶ (lowerStar (ModuleCat.{u + 1} P.Coefficient) f.left).rightDerivedFunctor.obj N) :
    (upperStar (ModuleCat.{u + 1} P.Coefficient) (f.left ≫ g.left)).leftDerivedFunctor.map
        (w ≫ (lowerStar (ModuleCat.{u + 1} P.Coefficient) g.left).rightDerivedFunctor.map v ≫
          (finiteDirectImageComposition P.Coefficient f.left g.left).inv.app N) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
          (f.left ≫ g.left)).counit.app N =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f.left g.left).hom.app M ≫
        (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) g.left).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f.left)).homEquiv
            M N).symm
          ((w ≫ (lowerStar (ModuleCat.{u + 1} P.Coefficient) g.left).rightDerivedFunctor.map v ≫
            (finiteDirectImageComposition P.Coefficient f.left g.left).inv.app N) ≫
              (finiteDirectImageComposition P.Coefficient f.left g.left).hom.app N) ∧
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f.left g.left).hom.app M ≫
        (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) g.left).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f.left)).homEquiv
            M N).symm
          ((w ≫ (lowerStar (ModuleCat.{u + 1} P.Coefficient) g.left).rightDerivedFunctor.map v ≫
            (finiteDirectImageComposition P.Coefficient f.left g.left).inv.app N) ≫
              (finiteDirectImageComposition P.Coefficient f.left g.left).hom.app N) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f.left g.left).hom.app M ≫
        (upperStar (ModuleCat.{u + 1} P.Coefficient) f.left).leftDerivedFunctor.map
          ((upperStar (ModuleCat.{u + 1} P.Coefficient) g.left).leftDerivedFunctor.map w ≫
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
              g.left).counit.app Q) ≫
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) f.left).leftDerivedFunctor.map v ≫
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
            f.left).counit.app N) ∧
    (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) g.left).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f.left)).homEquiv
          M N).symm
        (w ≫ (lowerStar (ModuleCat.{u + 1} P.Coefficient) g.left).rightDerivedFunctor.map v) =
      (upperStar (ModuleCat.{u + 1} P.Coefficient) f.left).leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) g.left).leftDerivedFunctor.map w ≫
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
            g.left).counit.app Q) ≫
      ((upperStar (ModuleCat.{u + 1} P.Coefficient) f.left).leftDerivedFunctor.map v ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
          f.left).counit.app N) := by
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) g.left
  let b := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f.left
  let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f.left g.left
  have hs := successive_transpose a b w v
  have ht := transpose_conjugate (a.comp b)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
      (f.left ≫ g.left)) c.hom
    (w ≫ (lowerStar (ModuleCat.{u + 1} P.Coefficient) g.left).rightDerivedFunctor.map v)
  rw [← derived_compositor_conjugate] at ht
  refine ⟨?_, ?_, hs⟩
  · simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id] using ht
  · simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id] using
      congrArg (fun t ↦ c.hom.app M ≫ t) hs

end WeilConjectures.PurityFiniteSetting
