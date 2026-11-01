/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels

/-! # Integral-representative transport for rational Verdier composition

This is the localization step in the composition equation.  It is stated only on
integral representatives; the enclosing rational category has exactly these objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

attribute [local irreducible] CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.homComplexFunctor WeilConjectures.IntegralHom.totalTensor
  WeilConjectures.IntegralHom.homModelMap WeilConjectures.IntegralHom.projection
  WeilConjectures.IntegralHom.evaluate

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem map_heq {C C' : Type*} [Category* C] [Category* C']
    (F : C ⥤ C') {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases hf
  rfl

private theorem contra_map_heq {C C' : Type*} [Category* C] [Category* C']
    (F : Cᵒᵖ ⥤ C') {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : HEq f g) : HEq (F.map f.op) (F.map g.op) := by
  cases hx
  cases hy
  cases hf
  rfl

private theorem app_heq {C C' : Type*} [Category* C] [Category* C']
    {F G : C ⥤ C'} (a : F ⟶ G) {X Y : C} (h : X = Y) :
    HEq (a.app X) (a.app Y) := by
  cases h
  rfl

/--
The normalized comparison equation on an integral representative.
Source: blueprint thm-coef-rational-verdier, proof step 7, composition clause;
the localization of the integral beta composition equation.

Proof: localize the beta component of `CompositionConclusion`, transport its
endpoints through the normalized associator equation, and use the three
`ExtensionProperties` comparison normalizations.  The pure-tensor clause of
`Datum.pure`, additivity of the dual functors, and functoriality of scalar
localization extend the equality from integral arrows to the localized arrow.
The construction is independent of the choice of representative, so this
integral-representative form is sufficient for the raw localization category.
(blueprint: lem-coef-rational-verdier-composition-equation).
-/
theorem localized_extension_composition
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (H : Type u) [Field H] [Algebra (Padic l) H] [FiniteDimensional (Padic l) H]
    (i : F →ₐ[Padic l] G) (j : G →ₐ[Padic l] H)
    (wF : IntegralFiniteExtension.DualizingDatum l X D hl F)
    (wG : IntegralFiniteExtension.DualizingDatum l X D hl G)
    (wH : IntegralFiniteExtension.DualizingDatum l X D hl H)
    (A : Datum D l hl X F wF) (B : Datum D l hl X G wG) (C : Datum D l hl X H wH)
    (a : scalar l X F G i ⋙ scalar l X G H j ≅ scalar l X F H (j.comp i))
    (hnorm : ∀ K : sfIntegralConstructibleCategory l F X,
      HEq (a.hom.app ((sfRationalConstructibleLocalization l F X).obj K))
        ((sfRationalConstructibleLocalization l H X).map
          (ObjectProperty.homMk
            (X := (integralScalar l X G H j).obj ((integralScalar l X F G i).obj K))
            (Y := (integralScalar l X F H (j.comp i)).obj K)
            (IntegralFiniteExtension.comp l F G i X H j K.obj K.property.1).hom)))
    (eFG : Extension D l hl X F G i wF wG A B)
    (eGH : Extension D l hl X G H j wG wH B C)
    (eFH : Extension D l hl X F H (j.comp i) wF wH A C)
    (hFG : ExtensionProperties D l hl X F G i wF wG A B eFG)
    (hGH : ExtensionProperties D l hl X G H j wG wH B C eGH)
    (hFH : ExtensionProperties D l hl X F H (j.comp i) wF wH A C eFH)
    (hcomp : IntegralFiniteExtension.CompositionConclusion l F G i X D hl wF wG
      A.ordinary B.ordinary H j wH C.ordinary) :
    ∀ K : sfIntegralConstructibleCategory l F X,
      (scalar l X G H j).map
          (eFG.comparison.hom.app (op ((sfRationalConstructibleLocalization l F X).obj K))) ≫
          eGH.comparison.hom.app
            (op ((scalar l X F G i).obj ((sfRationalConstructibleLocalization l F X).obj K))) =
        a.hom.app
            (A.dual.obj (op ((sfRationalConstructibleLocalization l F X).obj K))) ≫
          eFH.comparison.hom.app ((op ((sfRationalConstructibleLocalization l F X).obj K))) ≫
            C.dual.map
              (a.hom.app ((sfRationalConstructibleLocalization l F X).obj K)).op := by
  let QF := sfRationalConstructibleLocalization l F X
  let QG := sfRationalConstructibleLocalization l G X
  let QH := sfRationalConstructibleLocalization l H X
  let T := integralScalar l X F G i
  let U := integralScalar l X G H j
  let V := integralScalar l X F H (j.comp i)
  let R := scalar l X F G i
  let S := scalar l X G H j
  let W := scalar l X F H (j.comp i)
  let IF := IntegralVerdier.restrictedDual l F X wF.omega.obj A.preserves
  let IG := IntegralVerdier.restrictedDual l G X wG.omega.obj B.preserves
  let IH := IntegralVerdier.restrictedDual l H X wH.omega.obj C.preserves
  let bFG (K : sfIntegralConstructibleCategory l F X) :
      T.obj (IF.obj (op K)) ⟶ IG.obj (op (T.obj K)) :=
    ObjectProperty.homMk
      (IntegralFiniteExtension.beta l F G i X D hl wF wG A.ordinary B.ordinary
        K.obj K.property.1)
  let bGH (K : sfIntegralConstructibleCategory l G X) :
      U.obj (IG.obj (op K)) ⟶ IH.obj (op (U.obj K)) :=
    ObjectProperty.homMk
      (IntegralFiniteExtension.beta l G H j X D hl wG wH B.ordinary C.ordinary
        K.obj K.property.1)
  let bFH (K : sfIntegralConstructibleCategory l F X) :
      V.obj (IF.obj (op K)) ⟶ IH.obj (op (V.obj K)) :=
    ObjectProperty.homMk
      (IntegralFiniteExtension.beta l F H (j.comp i) X D hl wF wH A.ordinary C.ordinary
        K.obj K.property.1)
  let c (K : sfIntegralConstructibleCategory l F X) : U.obj (T.obj K) ≅ V.obj K :=
    ObjectProperty.isoMk _ (IntegralFiniteExtension.comp l F G i X H j K.obj K.property.1)
  have hbeta (K : sfIntegralConstructibleCategory l F X) :
      U.map (bFG K) ≫ bGH (T.obj K) =
        (c (IF.obj (op K))).hom ≫ bFH K ≫ IH.map (c K).hom.op := by
    have hb : U.map (bFG K) ≫ bGH (T.obj K) ≫ IH.map (c K).inv.op =
        (c (IF.obj (op K))).hom ≫ bFH K := by
      apply ObjectProperty.hom_ext
      exact hcomp.2.2.2.2.1 K
    have hb' : (U.map (bFG K) ≫ bGH (T.obj K)) ≫ (IH.mapIso (c K).op).inv =
        (c (IF.obj (op K))).hom ≫ bFH K := by
      simpa only [Functor.mapIso_inv, Iso.op_inv, Category.assoc] using hb
    simpa only [Functor.mapIso_hom, Iso.op_hom, Category.assoc] using
      (IH.mapIso (c K).op).comp_inv_eq.mp hb'
  have hR (K : sfRationalConstructibleCategory l F X) :
      R.obj K = QG.obj (T.obj K.obj) :=
    sfRationalScalarExtension_obj l F X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) G i K
  have hS (K : sfRationalConstructibleCategory l G X) :
      S.obj K = QH.obj (U.obj K.obj) :=
    sfRationalScalarExtension_obj l G X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) H j K
  have hW (K : sfRationalConstructibleCategory l F X) :
      W.obj K = QH.obj (V.obj K.obj) :=
    sfRationalScalarExtension_obj l F X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
      H (j.comp i) K
  intro K
  have hDK : A.dual.obj (op (QF.obj K)) = QF.obj (IF.obj (op K)) := A.objects _
  have hTK : R.obj (QF.obj K) = QG.obj (T.obj K) := hR _
  have hRDK : R.obj (A.dual.obj (op (QF.obj K))) =
      QG.obj (T.obj (IF.obj (op K))) := by rw [hDK, hR]; rfl
  have hDTK : B.dual.obj (op (R.obj (QF.obj K))) =
      QG.obj (IG.obj (op (T.obj K))) := by rw [hTK, B.objects]; rfl
  have hsource : S.obj (R.obj (A.dual.obj (op (QF.obj K)))) =
      QH.obj (U.obj (T.obj (IF.obj (op K)))) := by rw [hRDK, hS]; rfl
  have hmiddle : S.obj (B.dual.obj (op (R.obj (QF.obj K)))) =
      QH.obj (U.obj (IG.obj (op (T.obj K)))) := by rw [hDTK, hS]; rfl
  have hUTK : S.obj (R.obj (QF.obj K)) = QH.obj (U.obj (T.obj K)) := by
    rw [hTK, hS]; rfl
  have htarget : C.dual.obj (op (S.obj (R.obj (QF.obj K)))) =
      QH.obj (IH.obj (op (U.obj (T.obj K)))) := by rw [hUTK, C.objects]; rfl
  have hVDK : W.obj (A.dual.obj (op (QF.obj K))) =
      QH.obj (V.obj (IF.obj (op K))) := by rw [hDK, hW]; rfl
  have hVK : W.obj (QF.obj K) = QH.obj (V.obj K) := hW _
  have hDVK : C.dual.obj (op (W.obj (QF.obj K))) =
      QH.obj (IH.obj (op (V.obj K))) := by rw [hVK, C.objects]; rfl
  have hfirst : HEq (S.map (eFG.comparison.hom.app (op (QF.obj K))))
      (QH.map (U.map (bFG K))) := by
    have hb := map_heq S hRDK hDTK (hFG.2.1 K)
    have ht := sfRationalScalarExtension_map_tmul l G X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) H j _ _ (bFG K) 1
    simp only [map_one] at ht
    exact hb.trans ht
  have hsecond : HEq (eGH.comparison.hom.app (op (R.obj (QF.obj K))))
      (QH.map (bGH (T.obj K))) :=
    (app_heq eGH.comparison.hom (congrArg op hTK)).trans (hGH.2.1 (T.obj K))
  have hassoc : HEq (a.hom.app (A.dual.obj (op (QF.obj K))))
      (QH.map (c (IF.obj (op K))).hom) :=
    (app_heq a.hom hDK).trans (hnorm (IF.obj (op K)))
  have hthird : HEq (C.dual.map (a.hom.app (QF.obj K)).op)
      (QH.map (IH.map (c K).hom.op)) := by
    have hm := contra_map_heq C.dual hUTK hVK (hnorm K)
    have hp : HEq (C.dual.map (QH.map (c K).hom).op)
        (QH.map (IH.map (c K).hom.op)) := C.pure _ _ (c K).hom 1
    exact hm.trans hp
  have hleft := heq_comp hsource hmiddle htarget hfirst hsecond
  have hright := heq_comp hsource hVDK htarget hassoc
    (heq_comp hVDK hDVK htarget (hFH.2.1 K) hthird)
  have hi := congrArg QH.map (hbeta K)
  simp only [Functor.map_comp] at hi
  exact eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))

end WeilConjectures.RationalVerdier
