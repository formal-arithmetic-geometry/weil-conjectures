/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryPullbackTransition
import all WeilConjectures.SmoothPurity.Compact.CompactSupportOpenScalarRestriction

/-! # Ordinary open evaluation and horizontal coefficient maps

For an open immersion `j`, we define the ordinary open evaluation comparison between extension
by zero of coefficient systems and levelwise extension by zero, and show that it commutes with
the horizontal coefficient transition maps.

## Implementation details

Ordinary open evaluation is defined as the inverse of the normalized restriction mate,
transported by the unit-preserving single-level comparison. The compatibility with horizontal
maps is checked on transposes under the extension-by-zero/restriction adjunction; no flatness
or cartesian condition is used.

## References

* [Stacks, Tags 03DI, 03DA and 0941](https://stacks.math.columbia.edu/tag/03DI)
* Zheng, 4.1 and 4.10
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf presheafToSheaf
namespace WeilConjectures

private theorem horizontalOpenMate
    {S T A B C D : Type*}
    [Category S] [Category T] [Category A] [Category B] [Category C] [Category D]
    {L : S ⥤ T} {R : T ⥤ S} (a : L ⊣ R)
    {Lm : A ⥤ B} {Rm : B ⥤ A} (am : Lm ⊣ Rm)
    {Ln : C ⥤ D} {Rn : D ⥤ C} (an : Ln ⊣ Rn)
    (Em : S ⥤ A) (En : S ⥤ C) (Fm : T ⥤ B) (Fn : T ⥤ D)
    (p : C ⥤ A) (q : D ⥤ B)
    (em : R ⋙ Em ≅ Fm ⋙ Rm) (en : R ⋙ En ≅ Fn ⋙ Rn)
    (dm : L ⋙ Fm ≅ Em ⋙ Lm) (dn : L ⋙ Fn ≅ En ⋙ Ln)
    (t : Em ⟶ En ⋙ p) (s : Fm ⟶ Fn ⋙ q)
    (k : q ⋙ Rm ⟶ Rn ⋙ p) (c : p ⋙ Lm ⟶ Ln ⋙ q)
    (hm : ∀ N, Em.map (a.unit.app N) ≫ em.hom.app (L.obj N) ≫
      Rm.map (dm.hom.app N) = am.unit.app (Em.obj N))
    (hn : ∀ N, En.map (a.unit.app N) ≫ en.hom.app (L.obj N) ≫
      Rn.map (dn.hom.app N) = an.unit.app (En.obj N))
    (hk : ∀ M, t.app (R.obj M) ≫ p.map (en.hom.app M) =
      em.hom.app M ≫ Rm.map (s.app M) ≫ k.app (Fn.obj M))
    (hc : ∀ N, am.unit.app (p.obj N) ≫ Rm.map (c.app N) ≫ k.app (Ln.obj N) =
      p.map (an.unit.app N)) (N : S)
    [Mono (k.app (Ln.obj (En.obj N)))] :
    s.app (L.obj N) ≫ q.map (dn.hom.app N) =
      dm.hom.app N ≫ Lm.map (t.app N) ≫ c.app (En.obj N) := by
  apply (cancel_epi (dm.inv.app N)).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (am.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  apply (cancel_mono (k.app (Ln.obj (En.obj N)))).mp
  have hm' : am.unit.app (Em.obj N) ≫ Rm.map (dm.inv.app N) =
      Em.map (a.unit.app N) ≫ em.hom.app (L.obj N) := by
    rw [← hm N]
    simp only [Category.assoc, ← Rm.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [Category.assoc]
  have hk' := k.naturality (dn.hom.app N)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hk'
  rw [reassoc_of% hm', hk']
  rw [← reassoc_of% (hk (L.obj N))]
  rw [reassoc_of% (t.naturality (a.unit.app N))]
  have hn' := congrArg p.map (hn N)
  simp only [Functor.map_comp] at hn'
  rw [hn']
  rw [← reassoc_of% (am.unit.naturality (t.app N)), hc]

private theorem horizontalIsoTransport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (p : C ⥤ A) (q : D ⥤ B)
    {Jm Km : A ⥤ B} {Jn Kn : C ⥤ D} (xm : Jm ≅ Km) (xn : Jn ≅ Kn)
    (c : p ⋙ Km ≅ Kn ⋙ q) {U : B} {V : D} {M : A} {N : C}
    (em : U ⟶ Jm.obj M) (en : V ⟶ Jn.obj N)
    (s : M ⟶ p.obj N) (t : U ⟶ q.obj V)
    (h : t ≫ q.map en = em ≫ Jm.map s ≫
      (Functor.isoWhiskerLeft p xm ≪≫ c ≪≫
        Functor.isoWhiskerRight xn.symm q).hom.app N) :
    t ≫ q.map (en ≫ xn.hom.app N) =
      (em ≫ xm.hom.app M) ≫ Km.map s ≫ c.hom.app N := by
  rw [q.map_comp, ← Category.assoc, h]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc, ← q.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  rw [reassoc_of% (xm.hom.naturality s)]
  erw [Category.comp_id]

private theorem inverseMate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (E : A ⥤ C) (F : B ⥤ D)
    (d : R ⋙ E ≅ F ⋙ R')
    [IsIso ((mateEquiv a b).symm d.hom)] (N : A) :
    E.map (a.unit.app N) ≫ d.hom.app (L.obj N) ≫
      R'.map ((asIso ((mateEquiv a b).symm d.hom)).inv.app N) =
        b.unit.app (E.obj N) := by
  rw [← Category.assoc, unit_mateEquiv_symm a b d.hom N, Category.assoc,
    ← R'.map_comp]
  change b.unit.app (E.obj N) ≫ R'.map
    ((asIso ((mateEquiv a b).symm d.hom)).hom.app N ≫
      (asIso ((mateEquiv a b).symm d.hom)).inv.app N) = _
  rw [Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary open-evaluation mate is an isomorphism (before localization). -/
theorem compactSupportOrdinaryOpenMate_isIso
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :
    IsIso ((mateEquiv
      (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.StrictTower.moduleJAdj (compactSupportSystemLevel l E n) j)).symm
      (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j n).hom) := by
  exact ProEtale.VaryingRing.ordinaryOpenMateIso (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j n

/-- Ordinary open evaluation, defined as the inverse of the normalized restriction mate,
then transported by the unit-preserving single-level comparison. -/
def compactSupportOrdinaryOpenEvaluation {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j ⋙ coefficientSequenceEvaluation l E Z n ≅
      coefficientSequenceEvaluation l E X n ⋙
        sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)) := by
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  have := compactSupportOrdinaryOpenMate_isIso l E j n
  exact (asIso ((mateEquiv (ProEtale.VaryingRing.moduleJAdj R q j)
      (ProEtale.StrictTower.moduleJAdj (R n) j)).symm
        (ProEtale.VaryingRing.moduleEvalG R q j n).hom)).symm ≪≫
    Functor.isoWhiskerLeft _
      (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1)))

private def nativeSystemOpen {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    coefficientSequenceModules.{u, u} l E X ⥤ coefficientSequenceModules.{u, u} l E Z :=
  ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j

private def nativeLevelRestriction {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    normalizedDVRModules l E Z n ⥤ normalizedDVRModules l E X n :=
  ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) j

private def nativeSystemRestriction {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] :
    coefficientSequenceModules.{u, u} l E Z ⥤ coefficientSequenceModules.{u, u} l E X :=
  ProEtale.VaryingRing.pull (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j

private def nativeSystemOpenAdj {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    nativeSystemOpen l E j ⊣ nativeSystemRestriction l E j :=
  ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j

private def nativeRestrictionEval {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    nativeSystemRestriction l E j ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Z n ⋙ nativeLevelRestriction l E j n :=
  ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j n

private def nativeOpenEval {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    nativeSystemOpen l E j ⋙ coefficientSequenceEvaluation l E Z n ≅
      coefficientSequenceEvaluation l E X n ⋙
        ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j := by
  have := compactSupportOrdinaryOpenMate_isIso l E j n
  exact (asIso ((mateEquiv
    (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.StrictTower.moduleJAdj (compactSupportSystemLevel l E n) j)).symm
    (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j n).hom)).symm

private theorem nativeOpenEval_unit {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) (N : coefficientSequenceModules.{u, u} l E X) :
    (coefficientSequenceEvaluation l E X n).map
        ((ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).unit.app N) ≫
      (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j n).hom.app
          ((ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) j).obj N) ≫
      (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) j).map
        ((nativeOpenEval l E j n).hom.app N) =
    (ProEtale.StrictTower.moduleJAdj (compactSupportSystemLevel l E n) j).unit.app
      ((coefficientSequenceEvaluation l E X n).obj N) := by
  have := compactSupportOrdinaryOpenMate_isIso l E j n
  exact inverseMate_unit
    (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.StrictTower.moduleJAdj (compactSupportSystemLevel l E n) j)
    (coefficientSequenceEvaluation l E X n) (coefficientSequenceEvaluation l E Z n)
    (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j n) N

private theorem nativeOpenTransition {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules.{u, u} l E X) :
    (compactSupportOrdinaryCoefficientTransition l E Z h).app
        ((ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj M) ≫
      (proEtaleCoefficientRestrictScalars Z (compactSupportLevelQuotient l E m n h)).map
        ((nativeOpenEval l E j n).hom.app M) =
    (nativeOpenEval l E j m).hom.app M ≫
      (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E m) j).map
        ((compactSupportOrdinaryCoefficientTransition l E X h).app M) ≫
      (scalarJ j (compactSupportLevelQuotient l E m n h)).hom.app
        ((coefficientSequenceEvaluation l E X n).obj M) := by
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  have := compactSupportScalarPullback_isIso j (compactSupportLevelQuotient l E m n h)
  exact horizontalOpenMate (nativeSystemOpenAdj l E j)
    (ProEtale.StrictTower.moduleJAdj (R m) j) (ProEtale.StrictTower.moduleJAdj (R n) j)
    (coefficientSequenceEvaluation l E X m) (coefficientSequenceEvaluation l E X n)
    (coefficientSequenceEvaluation l E Z m) (coefficientSequenceEvaluation l E Z n)
    (proEtaleCoefficientRestrictScalars X (compactSupportLevelQuotient l E m n h))
    (proEtaleCoefficientRestrictScalars Z (compactSupportLevelQuotient l E m n h))
    (nativeRestrictionEval l E j m) (nativeRestrictionEval l E j n)
    (nativeOpenEval l E j m) (nativeOpenEval l E j n)
    (compactSupportOrdinaryCoefficientTransition l E X h)
    (compactSupportOrdinaryCoefficientTransition l E Z h)
    (compactSupportScalarPullback j (compactSupportLevelQuotient l E m n h))
    (scalarJ j (compactSupportLevelQuotient l E m n h)).hom
    (nativeOpenEval_unit l E j m) (nativeOpenEval_unit l E j n)
    (compactSupportOrdinaryPullbackTransition l E j h)
    (scalarJ_unit j (compactSupportLevelQuotient l E m n h)) M

/-- Ordinary open evaluation commutes with the horizontal coefficient transitions
`B_m → B_n`, before passing to complexes and localization. -/
theorem compactSupportOrdinaryOpenTransition
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    {m n : ℕ} (h : n ≤ m) (M : coefficientSequenceModules.{u, u} l E X) :
    (compactSupportOrdinaryCoefficientTransition l E Z h).app
        ((ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj M) ≫
      (proEtaleCoefficientRestrictScalars Z
        (compactSupportLevelQuotient l E m n h)).map
          ((compactSupportOrdinaryOpenEvaluation l E j n).hom.app M) =
    (compactSupportOrdinaryOpenEvaluation l E j m).hom.app M ≫
      (sfIntrinsicExtensionByZero j
        (Padic.coefficientExtensionRing l E (m + 1))).map
          ((compactSupportOrdinaryCoefficientTransition l E X h).app M) ≫
      (sfOpenRestriction j (compactSupportLevelQuotient l E m n h)).hom.app
        ((coefficientSequenceEvaluation l E X n).obj M) := by
  exact horizontalIsoTransport
    (proEtaleCoefficientRestrictScalars X (compactSupportLevelQuotient l E m n h))
    (proEtaleCoefficientRestrictScalars Z (compactSupportLevelQuotient l E m n h))
    (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (m + 1)))
    (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1)))
    (sfOpenRestriction j (compactSupportLevelQuotient l E m n h))
    ((nativeOpenEval l E j m).hom.app M) ((nativeOpenEval l E j n).hom.app M)
    ((compactSupportOrdinaryCoefficientTransition l E X h).app M)
    ((compactSupportOrdinaryCoefficientTransition l E Z h).app
      ((ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j).obj M))
    (nativeOpenTransition l E j h M)

end WeilConjectures
