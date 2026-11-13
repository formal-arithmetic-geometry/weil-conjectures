/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportOpenScalarRestriction
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectImageTransition
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryPullbackUnit

/-! # Horizontal compatibility of native inverse image

Source: Stacks Project, Tags 03DA, 03D3 and 0941; Zheng 4.1.
(blueprint: lem-weil-compact-support-ordinary-pullback-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf presheafToSheaf
attribute [local irreducible] ProEtale.VaryingRing.moduleAdj Functor.leftAdjoint
namespace WeilConjectures

private theorem horizontalLeftMate
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
    (d : Rn ⋙ p ⟶ q ⋙ Rm) (c : p ⋙ Lm ⟶ Ln ⋙ q)
    (hm : ∀ N, Em.map (a.unit.app N) ≫ em.hom.app (L.obj N) ≫
      Rm.map (dm.hom.app N) = am.unit.app (Em.obj N))
    (hn : ∀ N, En.map (a.unit.app N) ≫ en.hom.app (L.obj N) ≫
      Rn.map (dn.hom.app N) = an.unit.app (En.obj N))
    (hd : ∀ M, t.app (R.obj M) ≫ p.map (en.hom.app M) ≫ d.app (Fn.obj M) =
      em.hom.app M ≫ Rm.map (s.app M))
    (hc : ∀ N, am.unit.app (p.obj N) ≫ Rm.map (c.app N) =
      p.map (an.unit.app N) ≫ d.app (Ln.obj N))
    (N : S) :
    s.app (L.obj N) ≫ q.map (dn.hom.app N) =
      dm.hom.app N ≫ Lm.map (t.app N) ≫ c.app (En.obj N) := by
  apply (cancel_epi (dm.inv.app N)).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (am.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hm' : am.unit.app (Em.obj N) ≫ Rm.map (dm.inv.app N) =
      Em.map (a.unit.app N) ≫ em.hom.app (L.obj N) := by
    rw [← hm N]
    simp only [Category.assoc, ← Rm.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [reassoc_of% hm']
  rw [← reassoc_of% (hd (L.obj N))]
  rw [reassoc_of% (t.naturality (a.unit.app N))]
  have hn' := congrArg p.map (hn N)
  simp only [Functor.map_comp] at hn'
  have hd' := d.naturality (dn.hom.app N)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hd'
  rw [← hd', reassoc_of% hn']
  rw [← reassoc_of% (am.unit.naturality (t.app N)), hc]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def systemPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientSequenceModules.{u, u} l E Y ⥤ coefficientSequenceModules.{u, u} l E X :=
  ProEtale.VaryingRing.pull (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) f

private def systemPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientSequenceModules.{u, u} l E X ⥤ coefficientSequenceModules.{u, u} l E Y :=
  ProEtale.VaryingRing.push (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) f

private def systemAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    systemPull l E f ⊣ systemPush l E f :=
  ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f

private def evP {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    systemPush l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) f :=
  ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f n

private def evG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    systemPull l E f ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙
        ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) f :=
  ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f n

set_option profiler true in
private theorem systemEval_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : coefficientSequenceModules.{u, u} l E Y) :
    (coefficientSequenceEvaluation l E Y n).map ((systemAdj l E f).unit.app N) ≫
      (evP l E f n).hom.app ((systemPull l E f).obj N) ≫
      (ProEtale.StrictTower.moduleDirectImage (compactSupportSystemLevel l E n) f).map
        ((evG l E f n).hom.app N) =
    (proEtaleConstantRingAdjunction (Padic.coefficientExtensionRing l E (n + 1)) f).unit.app
      ((coefficientSequenceEvaluation l E Y n).obj N) := by
  exact compactSupportOrdinaryPullbackUnit l E f n N

set_option profiler true in
/-- Horizontal maps of ordinary coefficient systems commute with native inverse image.
Source: Stacks Project, Tags 03DA, 03D3 and 0941; Zheng 4.1.
(blueprint: lem-weil-compact-support-ordinary-pullback-transition).
Proof: direct image and coefficient evaluation keep the same section carriers. The
horizontal map is the actual presheaf restriction along (n,V) to (m,V), and product
base change preserves that arrow. Transpose that sectionwise square using the
specified inverse-image adjunctions and the normalization of moduleEvalG. The scalar
inverse-image comparison is the inverse mate of the direct-image scalar square,
so its unit equation gives the required last factor. -/
theorem compactSupportOrdinaryPullbackTransition {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) (N : coefficientSequenceModules.{u, u} l E Y) :
    (compactSupportOrdinaryCoefficientTransition l E X h).app
        ((ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f).obj N) ≫
      (proEtaleCoefficientRestrictScalars X (compactSupportLevelQuotient l E m n h)).map
        ((ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f n).hom.app N) =
    (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f m).hom.app N ≫
      (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E m) f).map
        ((compactSupportOrdinaryCoefficientTransition l E Y h).app N) ≫
      (compactSupportScalarPullback f (compactSupportLevelQuotient l E m n h)).app
        ((coefficientSequenceEvaluation l E Y n).obj N) := by
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  refine horizontalLeftMate (systemAdj l E f)
    (proEtaleConstantRingAdjunction (Padic.coefficientExtensionRing l E (m + 1)) f)
    (proEtaleConstantRingAdjunction (Padic.coefficientExtensionRing l E (n + 1)) f)
    (coefficientSequenceEvaluation l E Y m) (coefficientSequenceEvaluation l E Y n)
    (coefficientSequenceEvaluation l E X m) (coefficientSequenceEvaluation l E X n)
    (proEtaleCoefficientRestrictScalars Y (compactSupportLevelQuotient l E m n h))
    (proEtaleCoefficientRestrictScalars X (compactSupportLevelQuotient l E m n h))
    (evP l E f m) (evP l E f n)
    (evG l E f m) (evG l E f n)
    (compactSupportOrdinaryCoefficientTransition l E Y h)
    (compactSupportOrdinaryCoefficientTransition l E X h)
    (compactSupportScalarDirectImage f (compactSupportLevelQuotient l E m n h)).hom
    (compactSupportScalarPullback f (compactSupportLevelQuotient l E m n h))
    ?_ ?_ (compactSupportOrdinaryDirectImageTransition l E f h) ?_ N
  · intro Q
    exact systemEval_unit l E f m Q
  · intro Q
    exact systemEval_unit l E f n Q
  · intro M
    exact (unit_mateEquiv_symm
      (proEtaleConstantRingAdjunction (Padic.coefficientExtensionRing l E (n + 1)) f)
      (proEtaleConstantRingAdjunction (Padic.coefficientExtensionRing l E (m + 1)) f)
      (compactSupportScalarDirectImage f (compactSupportLevelQuotient l E m n h)).hom
      M).symm

end WeilConjectures
