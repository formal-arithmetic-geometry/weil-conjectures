/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.Compactification.NagataCompactification
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.CategoryTheory.ExactDerivedAdjunctionBounds
import Mathlib.CategoryTheory.HomCongr

/-!
# Closed affine charts and normalized dualizing composition

Source: main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraph 2 and the counit sentence of paragraph 3
(blueprint: lem-coef-dualizing-closed-chart).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem restrictedAdjoints_unique
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty C)
    {F G : C ⥤ D} {RF RG : D ⥤ C} (af : F ⊣ RF) (ag : G ⊣ RG)
    (e : P.ι ⋙ G ≅ P.ι ⋙ F) (L : D)
    (ha : P (RF.obj L)) (hb : P (RG.obj L)) :
    ∃! θ : RF.obj L ≅ RG.obj L,
      e.inv.app ⟨RF.obj L, ha⟩ ≫ G.map θ.hom ≫ ag.counit.app L =
        af.counit.app L := by
  let A : P.FullSubcategory := ⟨RF.obj L, ha⟩
  let B : P.FullSubcategory := ⟨RG.obj L, hb⟩
  let h (Z : P.FullSubcategory) : (Z ⟶ A) ≃ (Z ⟶ B) :=
    ((ObjectProperty.fullyFaithfulι P).homEquiv (X := Z) (Y := A)).trans
      ((af.homEquiv Z.obj L).symm.trans
        ((Iso.homCongr (e.app Z).symm (Iso.refl L)).trans
          ((ag.homEquiv Z.obj L).trans
            ((ObjectProperty.fullyFaithfulι P).homEquiv (X := Z) (Y := B)).symm)))
  have hm (Z : P.FullSubcategory) (g : Z ⟶ A) :
      P.ι.map (h Z g) =
        (ag.homEquiv Z.obj L) (e.hom.app Z ≫ (af.homEquiv Z.obj L).symm g.hom) := by
    simp [h, Iso.homCongr, Functor.FullyFaithful.homEquiv]
    rfl
  have hn {Z Z' : P.FullSubcategory} (f : Z' ⟶ Z) (g : Z ⟶ A) :
      h Z' (f ≫ g) = f ≫ h Z g := by
    apply P.ι.map_injective
    rw [hm, P.ι.map_comp, hm]
    change (ag.homEquiv _ _) (e.hom.app Z' ≫ (af.homEquiv _ _).symm
      (f.hom ≫ g.hom)) = f.hom ≫
        (ag.homEquiv _ _) (e.hom.app Z ≫ (af.homEquiv _ _).symm g.hom)
    have he : e.hom.app Z' ≫ F.map f.hom = G.map f.hom ≫ e.hom.app Z :=
      (e.hom.naturality f).symm
    rw [af.homEquiv_naturality_left_symm, ← Category.assoc, he,
      Category.assoc, ag.homEquiv_naturality_left]
    rfl
  let θ := Yoneda.ext A B (fun {Z} ↦ h Z) (fun {Z} ↦ (h Z).symm)
    (fun _ ↦ Equiv.symm_apply_apply _ _) (fun _ ↦ Equiv.apply_symm_apply _ _) hn
  have hθ : θ.hom = h A (𝟙 A) := rfl
  have hc : e.inv.app A ≫ G.map (P.ι.map θ.hom) ≫ ag.counit.app L =
      af.counit.app L := by
    have hh : (ag.homEquiv A.obj L).symm (P.ι.map θ.hom) =
        e.hom.app A ≫ af.counit.app L := by
      rw [hθ, hm, Equiv.symm_apply_apply]
      change e.hom.app A ≫ (af.homEquiv A.obj L).symm (𝟙 A.obj) = _
      rw [af.homEquiv_counit, F.map_id, Category.id_comp]
    rw [ag.homEquiv_counit] at hh
    rw [hh]
    simp
  refine ⟨P.ι.mapIso θ, hc, ?_⟩
  intro ψ hψ
  apply Iso.ext
  apply (ag.homEquiv A.obj L).symm.injective
  rw [ag.homEquiv_counit, ag.homEquiv_counit]
  apply (cancel_epi (e.inv.app A)).1
  exact hψ.trans hc.symm

private theorem restrictedCompositeAdjoints_unique
    {C B D : Type*} [Category C] [Category B] [Category D] (P : ObjectProperty C)
    {F : C ⥤ D} {Fi : C ⥤ B} {Fp : B ⥤ D}
    {RF : D ⥤ C} {Ri : B ⥤ C} {Rp : D ⥤ B}
    (af : F ⊣ RF) (ai : Fi ⊣ Ri) (ap : Fp ⊣ Rp)
    (e : P.ι ⋙ (Fi ⋙ Fp) ≅ P.ι ⋙ F) (L : D)
    (ha : P (RF.obj L)) (hb : P (Ri.obj (Rp.obj L))) :
    ∃! θ : RF.obj L ≅ Ri.obj (Rp.obj L),
      (e.inv.app ⟨RF.obj L, ha⟩ ≫ Fp.map (Fi.map θ.hom) ≫
        Fp.map (ai.counit.app (Rp.obj L))) ≫ ap.counit.app L = af.counit.app L := by
  obtain ⟨θ, hθ, huniq⟩ := restrictedAdjoints_unique P af (ai.comp ap) e L ha hb
  refine ⟨θ, ?_, ?_⟩
  · simpa only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj,
      Category.assoc] using hθ
  · intro ψ hψ
    apply huniq ψ
    simpa only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj,
      Category.assoc] using hψ

-- Keep the representing objects explicit: converting their names inside `e.inv.app`
-- would unfold the large geometric comparison during kernel checking.
private theorem restrictedCompositeAdjoints_unique_objects
    {C B D : Type*} [Category C] [Category B] [Category D] (P : ObjectProperty C)
    {F : C ⥤ D} {Fi : C ⥤ B} {Fp : B ⥤ D}
    {RF : D ⥤ C} {Ri : B ⥤ C} {Rp : D ⥤ B}
    (af : F ⊣ RF) (ai : Fi ⊣ Ri) (ap : Fp ⊣ Rp)
    (e : P.ι ⋙ (Fi ⋙ Fp) ≅ P.ι ⋙ F) (L : D)
    (A : C) (B' : B) (hA : A = RF.obj L) (hB : B' = Rp.obj L)
    (ha : P A) (hb : P (Ri.obj B'))
    (c : (A ⟶ Ri.obj B') → (F.obj A ⟶ Fp.obj B'))
    (hc : ∀ f, c f = e.inv.app ⟨A, ha⟩ ≫ Fp.map (Fi.map f) ≫
      Fp.map (ai.counit.app B')) :
    ∃! θ : A ≅ Ri.obj B',
      c θ.hom ≫ eqToHom (congrArg Fp.obj hB) ≫ ap.counit.app L =
        eqToHom (congrArg F.obj hA) ≫ af.counit.app L := by
  subst A B'
  simp only [eqToHom_refl, Category.id_comp] at *
  apply (existsUnique_congr _).mp
    (restrictedCompositeAdjoints_unique P af ai ap e L ha hb)
  intro θ
  rw [hc]

namespace AlgebraicGeometry.Etale

/-- Identify closed derived pushforward with compact support on bounded-below objects,
using the identity-open compactification and the recorded refinement comparison.
Source: main-20261015, finite-dualizing proof, paragraph 2
(blueprint: lem-coef-dualizing-closed-chart). -/
def coefClosedChartPlusPushforwardIso
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i] :
    (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctorPlus ≅
      rightDerivedLowerShriekPlus (ModuleCat.{u + 1} R) i :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryPlusNatIso
        (openImmersionLowerShriekId (ModuleCat.{u + 1} R) Y) ≪≫
        Functor.mapDerivedCategoryPlusIdIso _).symm _ ≪≫
    rightDerivedLowerShriekOfCompactificationPlusIso R
      (Compactification.ofIsProper i) (HasCompactification.compactification i)

/-- The canonical comparison `F_P Ri_* -> F_Y`, restricted to `D+`. The construction
uses precisely bounded-below compact-support composition, with closed pushforward
normalized by its identity-open compactification; it makes no unbounded composition claim.
Source: main-20261015, finite-dualizing proof, paragraph 2
(blueprint: lem-coef-dualizing-closed-chart). -/
def coefClosedChartComposition
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P s : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ s) (aY : Y ⟶ s) (h : i ≫ p = aY)
    [HasCompactification p] [HasCompactification aY]
    [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)] :
    _root_.DerivedCategory.Plus.ι ⋙
        ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} R) p) ≅
      _root_.DerivedCategory.Plus.ι ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} R) aY :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctorPlusCompatibility.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} R) p).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (coefClosedChartPlusPushforwardIso R i) _ ≪≫
        rightDerivedLowerShriekPlusCompIso R i p ≪≫
        rightDerivedLowerShriekPlusCongr R h) _ ≪≫
    rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} R) aY

/-- Transport a closed counit through the canonical bounded-below composition.
This is the actual composite morphism, not an independently supplied comparison.
Source: main-20261015, finite-dualizing proof, paragraph 3
(blueprint: lem-coef-dualizing-closed-chart). -/
def coefClosedChartCompositeCounit
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P s : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ s) (aY : Y ⟶ s) (h : i ≫ p = aY)
    [HasCompactification p] [HasCompactification aY]
    [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)]
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (L : DerivedCategoryModule R P)
    (f : K.obj ⟶ (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.rightAdjoint.obj L) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} R) aY).obj K.obj ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} R) p).obj L :=
  (coefClosedChartComposition R i p aY h).inv.app K ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} R) p).map
      ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.map f) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} R) p).map
      ((Adjunction.ofIsLeftAdjoint
        (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor).counit.app L)

/-- The closed-chart clauses for one coefficient ring. All objects and adjunctions
are the ordinary small-etale ones. The unique comparison is normalized by the
structural counit through the canonical bounded-below composition comparison.
Source: main-20261015, finite-dualizing proof, paragraph 2 and paragraph 3
(blueprint: lem-coef-dualizing-closed-chart). -/
structure CoefClosedChartProperties
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P s : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ s) (aY : Y ⟶ s) (h : i ≫ p = aY)
    [HasCompactification p] [HasCompactification aY]
    [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)] : Prop where
  exact_limits : PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} R) i)
  exact_colimits : PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} R) i)
  identity_open : Nonempty
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
        (Compactification.ofIsProper i) ≅
      (lowerStar (ModuleCat.{u + 1} R) i).mapDerivedCategory)
  derived_pushforward : Nonempty
    ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ≅
      (lowerStar (ModuleCat.{u + 1} R) i).mapDerivedCategory)
  cohomology : ∀ q : ℤ, Nonempty
    ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⋙
        _root_.DerivedCategory.homologyFunctor _ q ≅
      _root_.DerivedCategory.homologyFunctor _ q ⋙ lowerStar (ModuleCat.{u + 1} R) i)
  closed_boundedBelow : ∀ L : DerivedCategoryModule R P,
    _root_.DerivedCategory.TStructure.t.plus L →
    _root_.DerivedCategory.TStructure.t.plus
      ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.rightAdjoint.obj L)
  omegaY_boundedBelow : _root_.DerivedCategory.TStructure.t.plus
    (dualizingComplex R aY)
  omegaP_boundedBelow : _root_.DerivedCategory.TStructure.t.plus
    (dualizingComplex R p)
  closed_omegaP_boundedBelow : _root_.DerivedCategory.TStructure.t.plus
    ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.rightAdjoint.obj
      (dualizingComplex R p))

/-- The unique counit-normalized identification of the two representing objects.
The bound is used only to apply the canonical bounded-below composition comparison.
Source: main-20261015, finite-dualizing proof, paragraph 3
(blueprint: lem-coef-dualizing-closed-chart). -/
def CoefClosedChartNormalization
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P s : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ s) (aY : Y ⟶ s) (h : i ≫ p = aY)
    [HasCompactification p] [HasCompactification aY]
    [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)]
    (hY : _root_.DerivedCategory.TStructure.t.plus
      (dualizingComplex R aY)) : Prop :=
  ∃! θ : dualizingComplex R aY ≅
      (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.rightAdjoint.obj
        (dualizingComplex R p),
    coefClosedChartCompositeCounit R i p aY h
        ⟨dualizingComplex R aY, hY⟩
        (dualizingComplex R p) θ.hom ≫
      (rightDerivedUpperShriekAdjunction R p).counit.app
        (constantComplex R s) =
      (rightDerivedUpperShriekAdjunction R aY).counit.app
        (constantComplex R s)

/-- Install the coefficient finiteness and compactifications that follow from the
geometric hypotheses, then state the closed-chart clauses. These are consequences,
not extra hypotheses. The coefficient lift is the common small-etale size convention.
Source: main-20261015, finite-dualizing proof, paragraph 2
(blueprint: lem-coef-dualizing-closed-chart). -/
def CoefClosedChartAt
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (j : ℕ) (hj : 1 ≤ j)
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (k : Type u) [Field k] (p : P ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (h : i ≫ p = aY) : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E j) :=
    Padic.finite_coefficientExtensionRing l E j hj
  letI : HasCompactification (i ≫ p) := HasCompactification.of_eq h.symm
  ∃ H : CoefClosedChartProperties
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E j)) i p aY h,
    CoefClosedChartNormalization
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E j)) i p aY h H.omegaY_boundedBelow

attribute [local irreducible] coefClosedChartComposition

private theorem closedChartCounit_eq
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P s : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ s) (aY : Y ⟶ s) (h : i ≫ p = aY)
    [HasCompactification p] [HasCompactification aY]
    [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)]
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (L : DerivedCategoryModule R P)
    (f : K.obj ⟶ (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.rightAdjoint.obj L) :
    coefClosedChartCompositeCounit R i p aY h K L f =
      (coefClosedChartComposition R i p aY h).inv.app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} R) p).map
          ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.map f) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} R) p).map
          ((Adjunction.ofIsLeftAdjoint
            (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor).counit.app L) := by
  rfl

private theorem closedChartNormalization
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (k : Type u) [Field k] (p : P ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    (h : i ≫ p = aY) [HasCompactification p] [HasCompactification aY]
    [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)]
    (hY : _root_.DerivedCategory.TStructure.t.plus
      (dualizingComplex R aY))
    (hI : _root_.DerivedCategory.TStructure.t.plus
      ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.rightAdjoint.obj
        (dualizingComplex R p))) :
    CoefClosedChartNormalization R i p aY h hY := by
  simpa only [CoefClosedChartNormalization, eqToHom_refl, Category.id_comp,
    Category.comp_id] using restrictedCompositeAdjoints_unique_objects _
    (rightDerivedUpperShriekAdjunction R aY)
    (Adjunction.ofIsLeftAdjoint (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor)
    (rightDerivedUpperShriekAdjunction R p)
    (coefClosedChartComposition R i p aY h) (constantComplex R (Spec (.of k)))
    (dualizingComplex R aY)
    (dualizingComplex R p) rfl rfl hY hI
    (coefClosedChartCompositeCounit R i p aY h
      ⟨dualizingComplex R aY, hY⟩
      (dualizingComplex R p))
    (fun f ↦ closedChartCounit_eq R i p aY h
      ⟨dualizingComplex R aY, hY⟩
      (dualizingComplex R p) f)

private theorem closedChartProperties
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (k : Type u) [Field k] (p : P ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    (h : i ≫ p = aY) [HasCompactification p] [HasCompactification aY]
    [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)] :
    ∃ H : CoefClosedChartProperties R i p aY h,
      CoefClosedChartNormalization R i p aY h H.omegaY_boundedBelow := by
  let F := lowerStar (ModuleCat.{u + 1} R) i
  let FD := F.rightDerivedFunctor
  let ai : FD ⊣ FD.rightAdjoint := Adjunction.ofIsLeftAdjoint FD
  have hI (L : DerivedCategoryModule R P)
      (hL : _root_.DerivedCategory.TStructure.t.plus L) :
      _root_.DerivedCategory.TStructure.t.plus (FD.rightAdjoint.obj L) := by
    obtain ⟨b, hb⟩ := hL
    have : L.IsGE b := hb
    refine ⟨b, ?_⟩
    exact exactDerivedAdjunction_isGE F FD
      (Functor.isoWhiskerLeft _ F.rightDerivedFunctorIsoMapDerivedCategory ≪≫
        F.mapDerivedCategoryFactors) ai L b
  have hunit : _root_.DerivedCategory.TStructure.t.plus
      (constantComplex R (Spec (.of k))) :=
    ⟨0, _root_.DerivedCategory.TStructure.t.isGE_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0⟩
  have hY : _root_.DerivedCategory.TStructure.t.plus
      (dualizingComplex R aY) :=
    plus_rightDerivedUpperShriek_obj R aY _ hunit
  have hP : _root_.DerivedCategory.TStructure.t.plus
      (dualizingComplex R p) :=
    plus_rightDerivedUpperShriek_obj R p _ hunit
  let H : CoefClosedChartProperties R i p aY h := {
    exact_limits := inferInstance
    exact_colimits := inferInstance
    identity_open := ⟨Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} R) Y) _ ≪≫
      Functor.leftUnitor _ ≪≫ F.rightDerivedFunctorIsoMapDerivedCategory⟩
    derived_pushforward := ⟨F.rightDerivedFunctorIsoMapDerivedCategory⟩
    cohomology := fun q ↦ ⟨Functor.isoWhiskerRight
      F.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
        (F.mapDerivedCategoryHomologyFunctorIso q).symm⟩
    closed_boundedBelow := hI
    omegaY_boundedBelow := hY
    omegaP_boundedBelow := hP
    closed_omegaP_boundedBelow := hI _ hP }
  exact ⟨H, closedChartNormalization R i k p aY h hY (hI _ hP)⟩

/- The coefficient-theoretic part of the closed-chart construction.

This is the remaining bounded-below compact-support and dualizing comparison argument
after a closed affine-space chart has been chosen. It is split from the geometric
existence theorem so that the two coefficient levels can be proved independently.
Source: main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraphs 2--3
(blueprint: lem-coef-dualizing-closed-chart-properties). -/
/- The one-level coefficient package is the remaining local argument. -/
/-- For one finite coefficient stage, the closed pushforward, bounded-below
dualizing, compact-support composition, and counit-normalization clauses hold.

Source: main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraphs 2--3.  The proof first applies
the boundary adjunction restriction to obtain the ambient bounded-below
adjunctions, then transports exactness of closed direct image to module sheaves.
The exact derived factorization identifies the identity-open compact support with
termwise direct image, and the exact adjunction bound gives the lower bound for
the closed right adjoint.  Finally the bounded-below compact-support composition
comparison and uniqueness of right adjoints produce the counit-normalized
isomorphism.  This is strictly the one-stage component of the two-stage chart
argument, and is left as the next proof item.
(blueprint: lem-coef-dualizing-closed-chart-single). -/
theorem coefClosedChartAt_single_of_closed_chart
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (j : ℕ) (hj : 1 ≤ j)
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (k : Type u) [Field k] (p : P ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (h : i ≫ p = aY) : CoefClosedChartAt l E j hj i k p aY h := by
  let : Finite (Padic.coefficientExtensionRing l E j) :=
    Padic.finite_coefficientExtensionRing l E j hj
  let : HasCompactification (i ≫ p) := HasCompactification.of_eq h.symm
  exact closedChartProperties
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E j)) i k p aY h

theorem coefClosedChartAt_of_closed_chart
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (k : Type u) [Field k] (p : P ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (h : i ≫ p = aY) :
    CoefClosedChartAt l E m hm i k p aY h ∧
      CoefClosedChartAt l E n (hm.trans hmn) i k p aY h := by
  exact ⟨coefClosedChartAt_single_of_closed_chart l E m hm i k p aY h,
    coefClosedChartAt_single_of_closed_chart l E n (hm.trans hmn) i k p aY h⟩

set_option linter.unusedVariables false in
/-- Every affine separated finite-type scheme has a closed affine-space chart with
exact ordinary pushforward and the counit-normalized dualizing composition at both
positive coefficient levels. Both representing objects are independently bounded below.

Source: main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraph 2 and paragraph 3
(blueprint: lem-coef-dualizing-closed-chart).

Proof:
1. Write Y = Spec D. Finite type gives a surjection from a polynomial ring in finitely
   many variables onto D (lem-pc-affine-finite-type-algebra and
   def-weil-pbc-finite-type-algebra). The affine criterion for a closed immersion
   (lem-weil-pbc-closed-immersion-affine-cover-criterion) gives the chart over k.
2. Closed immersions are finite and proper. The polynomial projection is separated
   and finite type. This includes the empty source and zero variables.
3. At each positive coefficient stage, lem-weil-boundary-etale-adjunction-restriction
   supplies Noetherianity, compactifications, and D+-preserving ambient structural
   adjoints. Applying them to the degree-zero coefficient object bounds omegaY and
   omegaP without coefficient change.
4. lem-pur-etale-supported-kernel-adjunction gives exact closed abelian pushforward.
   The forgetful-compatible module direct image, kernels and cokernels transfer this
   to all module sheaves, without constructibility.
5. lem-weil-pbc-exact-functor-derived-factorization identifies unbounded derived
   pushforward with termwise pushforward. The identity-open compactification therefore
   gives Ri! = Ri* = i*, and lem-weil-pbc-exact-functor-complex-cohomology gives the
   natural cohomology isomorphism in every integer degree.
6. By lem-pur-exact-derived-adjunction-bounds(1), the closed right adjoint preserves
   every lower bound, hence D+ and the bound for I omegaP.
7. lem-amb-etale-compact-comparisons supplies the canonical composition on D+.
   Restrict all the ambient adjunctions using the independent bounds just established.
8. Compose adjunctions (def-weil-pbc-composite-adjunction) and use uniqueness of right
   adjoints (det-sp-unique-right-adjoint). Their unique counit-compatible identification
   at the coefficient object is theta. The composite counit is Fp(e) followed by
   epsilonP; transposing through the canonical composition gives the displayed equation.
-/
theorem exists_coefDualizingClosedChart
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of D.k))
    [IsAffine Y] [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    ∃ (r : ℕ) (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))),
      IsClosedImmersion i ∧ ∀ [hi : IsClosedImmersion i],
      i ≫ (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k)) = aY ∧
      IsFinite i ∧ IsProper i ∧ LocallyOfFiniteType i ∧ QuasiCompact i ∧
      ∀ h : i ≫ (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘
          Spec (.of D.k)) = aY,
        CoefClosedChartAt l E m hm i D.k
          (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k)) aY h ∧
        CoefClosedChartAt l E n (hm.trans hmn) i D.k
          (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k)) aY h := by
  obtain ⟨r, i, hi_over, hclosed⟩ :=
    exists_isClosedImmersion_affineSpace_of_isAffine aY
  let P := AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))
  let p : P ⟶ Spec (.of D.k) := P ↘ Spec (.of D.k)
  have : IsClosedImmersion i := hclosed
  refine ⟨r, i, hclosed, ?_⟩
  intro hi
  let : IsClosedImmersion i := hi
  have hfinite : IsFinite i := inferInstance
  have hproper : IsProper i := inferInstance
  have hlft : LocallyOfFiniteType i := inferInstance
  have hqc : QuasiCompact i := inferInstance
  refine ⟨hi_over, hfinite, hproper, hlft, hqc, ?_⟩
  intro h
  exact coefClosedChartAt_of_closed_chart l E m n hm hmn i D.k p aY h

end AlgebraicGeometry.Etale
