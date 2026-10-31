/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
import WeilConjectures.CategoryTheory.ExactDerivedCohomologyCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.FdCondensedPullbackFrobenius
import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.Mathlib.Algebra.Homology.ExactSequence
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Condensed immersion restriction and local Frobenius

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-prop-wgen-relative-line/lem-zl-morphism-open-closed-reduction.proof.md,
Restriction and Part 2 (blueprint: lem-zl-condensed-immersion-local).

All categories below use the actual finite-subextension-valued condensed Qbar ring.
The bounded condition uses the ordinary derived category, without a finite-Tor or
completeness condition. The comparisons are the specified exact-derived and module
inverse-image comparisons. The strict-pair categories carry no asserted triangulation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj

section CohomologyCoherence

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategoryHomologyFunctorIso
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso

private theorem exact_square_homology (F : A ⥤ B) (P : A ⥤ A) (Q : B ⥤ B)
    [F.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (β : F ⋙ Q ≅ P ⋙ F) (r : ℤ) (K : DerivedCategory A) :
    Q.map ((F.mapDerivedCategoryHomologyFunctorIso r).inv.app K) ≫
        β.hom.app ((DerivedCategory.homologyFunctor A r).obj K) ≫
        F.map ((P.mapDerivedCategoryHomologyFunctorIso r).hom.app K) =
      (Q.mapDerivedCategoryHomologyFunctorIso r).hom.app (F.mapDerivedCategory.obj K) ≫
        (DerivedCategory.homologyFunctor B r).map
          (((Functor.mapDerivedCategoryCompIso F Q).symm ≪≫
            Functor.mapDerivedCategoryNatIso β ≪≫
            Functor.mapDerivedCategoryCompIso P F).hom.app K) ≫
        (F.mapDerivedCategoryHomologyFunctorIso r).inv.app (P.mapDerivedCategory.obj K) := by
  have hFQ := (Functor.exactDerivedCohomologyCoherence F Q r).1 K
  have hPF := (Functor.exactDerivedCohomologyCoherence P F r).1 K
  have hβ := Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_naturality β r K
  apply (cancel_epi (Q.map ((F.mapDerivedCategoryHomologyFunctorIso r).hom.app K))).1
  apply (cancel_mono ((F.mapDerivedCategoryHomologyFunctorIso r).hom.app
    (P.mapDerivedCategory.obj K))).1
  simp only [← Q.map_comp_assoc, Iso.hom_inv_id_app, Q.map_id, Category.id_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← hPF]
  simp only [← Category.assoc]
  rw [hβ, ← hFQ]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  have hid := ((DerivedCategory.homologyFunctor B r).mapIso
    ((Functor.mapDerivedCategoryCompIso F Q).app K)).hom_inv_id
  dsimp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hid
  rw [reassoc_of% hid]
  erw [Category.comp_id]

private theorem transported_square_homology (F : A ⥤ B) (P : A ⥤ A) (Q : B ⥤ B)
    [F.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (β : F ⋙ Q ≅ P ⋙ F) (L : DerivedCategory A ⥤ DerivedCategory B)
    (e : L ≅ F.mapDerivedCategory) (r : ℤ) (K : DerivedCategory A) :
    let H := DerivedCategory.homologyFunctor B r
    let c := Functor.isoWhiskerRight e H ≪≫
      (F.mapDerivedCategoryHomologyFunctorIso r).symm
    let δ := Functor.isoWhiskerRight e Q.mapDerivedCategory ≪≫
      (Functor.mapDerivedCategoryCompIso F Q).symm ≪≫
      Functor.mapDerivedCategoryNatIso β ≪≫ Functor.mapDerivedCategoryCompIso P F ≪≫
      Functor.isoWhiskerLeft P.mapDerivedCategory e.symm
    Q.map (c.hom.app K) ≫ β.hom.app ((DerivedCategory.homologyFunctor A r).obj K) ≫
        F.map ((P.mapDerivedCategoryHomologyFunctorIso r).hom.app K) =
      (Q.mapDerivedCategoryHomologyFunctorIso r).hom.app (L.obj K) ≫
        H.map (δ.hom.app K) ≫ c.hom.app (P.mapDerivedCategory.obj K) := by
  dsimp only
  have h := exact_square_homology F P Q β r K
  have hn := (Q.mapDerivedCategoryHomologyFunctorIso r).hom.naturality (e.hom.app K)
  dsimp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  rw [h]
  rw [← reassoc_of% hn]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  have hid := ((DerivedCategory.homologyFunctor B r).mapIso
    (e.app (P.mapDerivedCategory.obj K))).inv_hom_id
  dsimp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hid
  rw [reassoc_of% hid]

private theorem transported_square_weil_homology
    (F : A ⥤ B) (P : A ⥤ A) (Q : B ⥤ B)
    [F.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (β : F ⋙ Q ≅ P ⋙ F) (L : DerivedCategory A ⥤ DerivedCategory B)
    (e₀ : L ≅ F.mapDerivedCategory) (r : ℤ)
    (δ : L ⋙ Q.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ L)
    (c : L ⋙ DerivedCategory.homologyFunctor B r ≅
      DerivedCategory.homologyFunctor A r ⋙ F)
    (hδ : δ = Functor.isoWhiskerRight e₀ Q.mapDerivedCategory ≪≫
      (Functor.mapDerivedCategoryCompIso F Q).symm ≪≫
      Functor.mapDerivedCategoryNatIso β ≪≫ Functor.mapDerivedCategoryCompIso P F ≪≫
      Functor.isoWhiskerLeft P.mapDerivedCategory e₀.symm)
    (hc : c = Functor.isoWhiskerRight e₀ (DerivedCategory.homologyFunctor B r) ≪≫
      (F.mapDerivedCategoryHomologyFunctorIso r).symm)
    (S : ObjectProperty (IsoAlgebra P.mapDerivedCategory)) :
    ∃ e : S.ι ⋙ IsoAlgebra.mapOfNatIso (F := P.mapDerivedCategory)
      (G := Q.mapDerivedCategory) (L := L) δ ⋙
          IsoAlgebra.mapOfNatIso (F := Q.mapDerivedCategory) (G := Q)
            (L := DerivedCategory.homologyFunctor B r)
            (Q.mapDerivedCategoryHomologyFunctorIso r) ≅
        S.ι ⋙ IsoAlgebra.mapOfNatIso (F := P.mapDerivedCategory) (G := P)
            (L := DerivedCategory.homologyFunctor A r)
            (P.mapDerivedCategoryHomologyFunctorIso r) ⋙
          IsoAlgebra.mapOfNatIso (F := P) (G := Q) (L := F) β,
      ∀ K : S.FullSubcategory, (e.hom.app K).hom.f = c.hom.app K.obj.carrier := by
  have hsq (K : DerivedCategory A) :
      Q.map (c.hom.app K) ≫ β.hom.app ((DerivedCategory.homologyFunctor A r).obj K) ≫
          F.map ((P.mapDerivedCategoryHomologyFunctorIso r).hom.app K) =
        (Q.mapDerivedCategoryHomologyFunctorIso r).hom.app (L.obj K) ≫
          (DerivedCategory.homologyFunctor B r).map (δ.hom.app K) ≫
            c.hom.app (P.mapDerivedCategory.obj K) := by
    rw [hδ, hc]
    exact transported_square_homology F P Q β L e₀ r K
  let T := IsoAlgebra.mapOfNatIso (F := P.mapDerivedCategory)
      (G := Q.mapDerivedCategory) (L := L) δ
  let HX := IsoAlgebra.mapOfNatIso (F := P.mapDerivedCategory) (G := P)
            (L := DerivedCategory.homologyFunctor A r)
            (P.mapDerivedCategoryHomologyFunctorIso r)
  let HY := IsoAlgebra.mapOfNatIso (F := Q.mapDerivedCategory) (G := Q)
            (L := DerivedCategory.homologyFunctor B r)
            (Q.mapDerivedCategoryHomologyFunctorIso r)
  let M := IsoAlgebra.mapOfNatIso (F := P) (G := Q) (L := F) β
  have hw (K : IsoAlgebra P.mapDerivedCategory) :
      Q.map (c.hom.app K.carrier) ≫ (M.obj (HX.obj K)).str.hom =
        (HY.obj (T.obj K)).str.hom ≫ c.hom.app K.carrier := by
    simp only [M, HX, HY, T, IsoAlgebra.mapOfNatIso_obj_str,
      IsoAlgebra.mapOfNatIso_obj_carrier, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hsq K.carrier)]
    congr 2
    exact (c.hom.naturality K.str.hom).symm
  let e : T ⋙ HY ≅ HX ⋙ M := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ (Algebra.isoMk (c.app K.carrier) (hw K)))
    (fun {K K'} f ↦ ObjectProperty.hom_ext _
      (Algebra.Hom.ext (c.hom.naturality f.hom.f)))
  exact ⟨Functor.isoWhiskerLeft S.ι e, fun _ ↦ rfl⟩

private theorem named_square_weil_homology
    (F : A ⥤ B) (P : A ⥤ A) (Q : B ⥤ B)
    [F.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (β : F ⋙ Q ≅ P ⋙ F) (L : DerivedCategory A ⥤ DerivedCategory B)
    (e₀ : L ≅ F.mapDerivedCategory) (r : ℤ)
    (δ : L ⋙ Q.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ L)
    (c : L ⋙ DerivedCategory.homologyFunctor B r ≅
      DerivedCategory.homologyFunctor A r ⋙ F)
    (hδ : δ = Functor.isoWhiskerRight e₀ Q.mapDerivedCategory ≪≫
      (Functor.mapDerivedCategoryCompIso F Q).symm ≪≫
      Functor.mapDerivedCategoryNatIso β ≪≫ Functor.mapDerivedCategoryCompIso P F ≪≫
      Functor.isoWhiskerLeft P.mapDerivedCategory e₀.symm)
    (hc : c = Functor.isoWhiskerRight e₀ (DerivedCategory.homologyFunctor B r) ≪≫
      (F.mapDerivedCategoryHomologyFunctorIso r).symm)
    (S : ObjectProperty (IsoAlgebra P.mapDerivedCategory))
    (T : IsoAlgebra P.mapDerivedCategory ⥤ IsoAlgebra Q.mapDerivedCategory)
    (HX : IsoAlgebra P.mapDerivedCategory ⥤ IsoAlgebra P)
    (HY : IsoAlgebra Q.mapDerivedCategory ⥤ IsoAlgebra Q)
    (M : IsoAlgebra P ⥤ IsoAlgebra Q)
    (hT : T = IsoAlgebra.mapOfNatIso δ)
    (hHX : HX = IsoAlgebra.mapOfNatIso (P.mapDerivedCategoryHomologyFunctorIso r))
    (hHY : HY = IsoAlgebra.mapOfNatIso (Q.mapDerivedCategoryHomologyFunctorIso r))
    (hM : M = IsoAlgebra.mapOfNatIso β) :
    ∃ e : S.ι ⋙ T ⋙ HY ≅ S.ι ⋙ HX ⋙ M,
      ∀ K : S.FullSubcategory, HEq (e.hom.app K).hom.f (c.hom.app K.obj.carrier) := by
  subst T HX HY M
  obtain ⟨e, he⟩ := transported_square_weil_homology F P Q β L e₀ r δ c hδ hc S
  exact ⟨e, fun K ↦ heq_of_eq (he K)⟩

end CohomologyCoherence


private theorem named_weil_structure {C E : Type*} [Category C] [Category E]
    (L : C ⥤ E) (P : C ⥤ C) (Q : E ⥤ E) (β : L ⋙ Q ≅ P ⋙ L)
    (T : IsoAlgebra P ⥤ IsoAlgebra Q) (hT : T = IsoAlgebra.mapOfNatIso β)
    (K : IsoAlgebra P) :
    HEq (β.app K.carrier ≪≫ L.mapIso K.str) ((T.obj K).str) := by
  subst T
  exact heq_of_eq (IsoAlgebra.mapOfNatIso_obj_str β K).symm

namespace WeilConjectures.CondensedImmersion

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]

/-- The ambient strict pairs, using the recorded exact derived Frobenius action.
Source: latest blueprint, Restriction, strict Weil convention
(blueprint: lem-zl-condensed-immersion-local). -/
abbrev Ambient (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  IsoAlgebra (CondensedRing.StrictWeil.action (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius T₀))

/-- Bounded constructible strict pairs, with ambient derived morphisms.
This is a restriction by the existing bounded-constructible predicate, not by finite Tor.
Source: latest blueprint, Restriction, ordinary D_cons convention
(blueprint: lem-zl-condensed-immersion-local). -/
def constructible (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] : ObjectProperty (Ambient D l T₀) :=
  fun K ↦ boundedConstructible
    (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left) K.carrier

variable {W₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The actual geometric base change of the model map.
Source: latest blueprint, Restriction, h = h_0 base changed to k
(blueprint: lem-zl-condensed-immersion-local). -/
def geometricMap (h₀ : W₀ ⟶ X₀) : (D.geometricFiber W₀).left ⟶
    (D.geometricFiber X₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left

/-- The specified inverse-image compositor for the Frobenius square h g_W = g_X h.
The square is the commutativity clause of the existing
`FiniteFieldDatum.frobenius_square_cartesian` (lem-weil-frobenius-square-cartesian).
Source: latest blueprint, Restriction, induced Weil structure
(blueprint: lem-zl-condensed-immersion-local). -/
def moduleSquare (h₀ : W₀ ⟶ X₀) :
    CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (geometricMap D h₀) ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius W₀).hom ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius X₀).hom ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (geometricMap D h₀) :=
  (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
    ⟨(D.frobenius_square_cartesian W₀ X₀ h₀).2.2.2.2.1⟩).symm

/-- Pullback of ordinary Weil modules: beta followed by h^*(theta).
Source: latest blueprint, Restriction, induced Weil structure
(blueprint: lem-zl-condensed-immersion-local). -/
def modulePull (h₀ : W₀ ⟶ X₀) := IsoAlgebra.mapOfNatIso (moduleSquare D l h₀)

/-- The same square on the actual total left derived functor, canonically transported
from the exact termwise functor, with no choice of a comparison isomorphism.
Source: latest blueprint, Restriction and Part 2, cohomology comparisons
(blueprint: lem-zl-condensed-immersion-local). -/
def derivedSquare (h₀ : W₀ ⟶ X₀) :
    CondensedRing.moduleObjectDerivedPullback (Profinite.padicAlgClRingObj l)
        (geometricMap D h₀) ⋙
      CondensedRing.StrictWeil.action (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius W₀) ≅
    CondensedRing.StrictWeil.action (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius X₀) ⋙
      CondensedRing.moduleObjectDerivedPullback (Profinite.padicAlgClRingObj l)
        (geometricMap D h₀) :=
  Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj l) (geometricMap D h₀)) _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleSquare D l h₀) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj l) (geometricMap D h₀)).symm

/-- The actual Lh^* with its induced strict Weil datum.
Source: latest blueprint, Restriction and Part 2
(blueprint: lem-zl-condensed-immersion-local). -/
def derivedPull (h₀ : W₀ ⟶ X₀) : Ambient D l X₀ ⥤ Ambient D l W₀ :=
  IsoAlgebra.mapOfNatIso (derivedSquare D l h₀)

/-- Cohomology of strict pairs, with the structure induced by exact Frobenius pullback.
Source: latest blueprint, Restriction, cohomology Weil structure
(blueprint: lem-zl-condensed-immersion-local). -/
def cohomology (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] (r : ℤ) :
    Ambient D l T₀ ⥤ condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius T₀).hom :=
  IsoAlgebra.mapOfNatIso
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius T₀).hom).mapDerivedCategoryHomologyFunctorIso r)

/-- The canonical cycles-and-boundaries cohomology comparison for the total Lh^*.
Source: latest blueprint, Restriction and Part 2
(blueprint: lem-zl-condensed-immersion-local). -/
def comparison (h₀ : W₀ ⟶ X₀) (r : ℤ) :
    CondensedRing.moduleObjectDerivedPullback (Profinite.padicAlgClRingObj l)
        (geometricMap D h₀) ⋙ DerivedCategory.homologyFunctor _ r ≅
      DerivedCategory.homologyFunctor _ r ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (geometricMap D h₀) :=
  Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj l) (geometricMap D h₀)) _ ≪≫
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (geometricMap D h₀)).mapDerivedCategoryHomologyFunctorIso r).symm

/-- Exact restriction on constructible Weil sheaves, both standard half-lines, and
bounded constructibility. Short exactness is tested on the underlying module sequence;
its arrows already commute with the specified Weil maps.
Source: latest blueprint, Restriction and Part 2
(blueprint: lem-zl-condensed-immersion-local). -/
def ExactAssertions (h₀ : W₀ ⟶ X₀) : Prop :=
  (∀ F : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom,
    IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber W₀).left)
      (((modulePull D l h₀).obj F.obj).carrier)) ∧
  (∀ (A B C : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius X₀).hom) (f : A ⟶ B) (g : B ⟶ C),
    Mono f.hom.hom.f → Epi g.hom.hom.f →
    (ComposableArrows.mk₂ f.hom.hom.f g.hom.hom.f).Exact →
    Mono ((modulePull D l h₀).map f.hom).hom.f ∧
      Epi ((modulePull D l h₀).map g.hom).hom.f ∧
      (ComposableArrows.mk₂ ((modulePull D l h₀).map f.hom).hom.f
        ((modulePull D l h₀).map g.hom).hom.f).Exact) ∧
  (∀ (K : (constructible D l X₀).FullSubcategory) (n : ℤ),
    (DerivedCategory.IsLE K.obj.carrier n →
      DerivedCategory.IsLE (((derivedPull D l h₀).obj K.obj).carrier) n) ∧
    (DerivedCategory.IsGE K.obj.carrier n →
      DerivedCategory.IsGE (((derivedPull D l h₀).obj K.obj).carrier) n) ∧
    constructible D l W₀ ((derivedPull D l h₀).obj K.obj))

/-- A natural Weil isomorphism whose underlying component is exactly comparison.
Thus neither the underlying isomorphism nor its equivariance is an arbitrary choice.
Source: latest blueprint, Restriction and Part 2
(blueprint: lem-zl-condensed-immersion-local). -/
def CohomologyAssertions (h₀ : W₀ ⟶ X₀) : Prop :=
  ∀ r : ℤ, ∃ e : (constructible D l X₀).ι ⋙ derivedPull D l h₀ ⋙ cohomology D l W₀ r ≅
      (constructible D l X₀).ι ⋙ cohomology D l X₀ r ⋙ modulePull D l h₀,
    ∀ K : (constructible D l X₀).FullSubcategory,
      (e.hom.app K).hom.f = (comparison D l h₀ r).hom.app K.obj.carrier

/-- The canonical fibre isomorphism, obtained by evaluating the inverse module compositor.
The equality only identifies the chosen compatible geometric points.
Source: latest blueprint, Restriction, identical stalks
(blueprint: lem-zl-condensed-immersion-local). -/
def fibreComparison (h₀ : W₀ ⟶ X₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : z ≫ geometricMap D h₀ = x) (M : CondensedModule.Modules l
      (D.geometricFiber X₀).left) :
    CondensedModule.fibre l D
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (geometricMap D h₀)).obj M) z ≅
      CondensedModule.fibre l D M x :=
  (CondensedRing.pointSections l D.k).mapIso
    (((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l)
      z (geometricMap D h₀)).app M).symm ≪≫
        (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) w).app M)

/-- Local Frobenius on the actual condensed fibre, at precisely the residue degree.
Source: latest blueprint, Restriction, identical local geometric Frobenius
(blueprint: lem-zl-condensed-immersion-local). -/
def localOperator (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l) (D.geometricFrobenius T₀).hom)
    (s : {s : T₀.left // s ∈ closedPoints T₀.left})
    (ι : T₀.left.residueField s.val →+* D.k)
    (hι : ι.comp (T₀.hom.residueFieldAlgebraMap s.val) = algebraMap D.k₀ D.k) :=
  CondensedModule.operator l D (D.geometricFrobenius T₀).hom F.carrier F.str
    (localClosedPoint D T₀ s ι hι) (localClosedPointDegree D T₀ s - 1)
    (localClosedPoint_return D T₀ s ι hι)

/-- Closedness, the actual residue-field isomorphism, and the canonical fibre/Frobenius
square for every compatible pair of lifts and every constructible Weil sheaf.
Source: latest blueprint, Restriction and Part 2
(blueprint: lem-zl-condensed-immersion-local). -/
def LocalAssertions (h₀ : W₀ ⟶ X₀) : Prop :=
  ∀ z : {z : W₀.left // z ∈ closedPoints W₀.left},
    ∃ hx : h₀.left z.val ∈ closedPoints X₀.left,
      IsIso (h₀.left.residueFieldMap z.val) ∧
      ∀ (ιz : W₀.left.residueField z.val →+* D.k)
        (hz : ιz.comp (W₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k)
        (ιx : X₀.left.residueField (h₀.left z.val) →+* D.k)
        (hιx : ιx.comp (X₀.hom.residueFieldAlgebraMap (h₀.left z.val)) =
          algebraMap D.k₀ D.k)
        (w : localClosedPoint D W₀ z ιz hz ≫ geometricMap D h₀ =
          localClosedPoint D X₀ ⟨h₀.left z.val, hx⟩ ιx hιx)
        (F : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius X₀).hom),
        localOperator D l W₀ ((modulePull D l h₀).obj F.obj) z ιz hz ≫
            (fibreComparison D l h₀ (localClosedPoint D W₀ z ιz hz)
              (localClosedPoint D X₀ ⟨h₀.left z.val, hx⟩ ιx hιx) w F.obj.carrier).hom =
          (fibreComparison D l h₀ (localClosedPoint D W₀ z ιz hz)
              (localClosedPoint D X₀ ⟨h₀.left z.val, hx⟩ ιx hιx) w F.obj.carrier).hom ≫
            localOperator D l X₀ F.obj ⟨h₀.left z.val, hx⟩ ιx hιx

section Proofs

attribute [local irreducible] CondensedModule.operator CondensedModule.transport
  CondensedModule.fibre CondensedRing.upperStar CondensedRing.pointSections
  CondensedRing.upperStarComp CondensedRing.upperStarSquareComparison
  fdCondensedFibreComparison fdCondensedPullbackWeilIso

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derivedSquare_normalization (h₀ : W₀ ⟶ X₀) :
    let H := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (geometricMap D h₀)
    let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom
    let Q := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius W₀).hom
    let e := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.padicAlgClRingObj l) (geometricMap D h₀)
    derivedSquare D l h₀ = Functor.isoWhiskerRight e Q.mapDerivedCategory ≪≫
      (Functor.mapDerivedCategoryCompIso H Q).symm ≪≫
      Functor.mapDerivedCategoryNatIso (F := H ⋙ Q) (G := P ⋙ H) (moduleSquare D l h₀) ≪≫
      Functor.mapDerivedCategoryCompIso P H ≪≫
      Functor.isoWhiskerLeft P.mapDerivedCategory e.symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  rfl

private theorem comparison_normalization (h₀ : W₀ ⟶ X₀) (r : ℤ) :
    comparison D l h₀ r =
      Functor.isoWhiskerRight
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (Profinite.padicAlgClRingObj l) (geometricMap D h₀))
        (DerivedCategory.homologyFunctor
          (CondensedModule.Modules l (D.geometricFiber W₀).left) r) ≪≫
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (geometricMap D h₀)).mapDerivedCategoryHomologyFunctorIso r).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  rfl


private theorem cohomology_assertions (h₀ : W₀ ⟶ X₀) : CohomologyAssertions D l h₀ := by
  intro r
  obtain ⟨e, he⟩ := named_square_weil_homology
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (geometricMap D h₀))
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius W₀).hom)
    (moduleSquare D l h₀) _
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.padicAlgClRingObj l) (geometricMap D h₀)) r
    (derivedSquare D l h₀) (comparison D l h₀ r)
    (derivedSquare_normalization D l h₀) (comparison_normalization D l h₀ r)
    (constructible D l X₀)
    (derivedPull D l h₀) (cohomology D l X₀ r) (cohomology D l W₀ r)
    (modulePull D l h₀) rfl rfl rfl rfl
  exact ⟨e, fun K ↦ eq_of_heq (he K)⟩

private theorem exact_assertions (h₀ : W₀ ⟶ X₀) : ExactAssertions D l h₀ := by
  let H := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (geometricMap D h₀)
  have hc (M) (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left) M) :
      IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber W₀).left)
        (H.obj M) :=
    CondensedRing.isConstructibleModuleObject_upperStar _ _ M hM
  refine ⟨fun F ↦ hc F.obj.carrier F.property, ?_, ?_⟩
  · intro A B C f g hf hg he
    let := hf
    let := hg
    exact ⟨inferInstanceAs (Mono (H.map f.hom.hom.f)),
      inferInstanceAs (Epi (H.map g.hom.hom.f)), he.map_mk₂ H⟩
  · intro K n
    have hz (r : ℤ)
        (h : IsZero ((DerivedCategory.homologyFunctor _ r).obj K.obj.carrier)) :
        IsZero ((DerivedCategory.homologyFunctor _ r).obj
          (((derivedPull D l h₀).obj K.obj).carrier)) :=
      (H.map_isZero h).of_iso ((comparison D l h₀ r).app K.obj.carrier)
    refine ⟨fun h ↦ (DerivedCategory.isLE_iff _ n).mpr
      (fun r hr ↦ hz r ((DerivedCategory.isLE_iff _ n).mp h r hr)),
      fun h ↦ (DerivedCategory.isGE_iff _ n).mpr
        (fun r hr ↦ hz r ((DerivedCategory.isGE_iff _ n).mp h r hr)), ?_⟩
    obtain ⟨⟨a, b, hab⟩, hcons⟩ :=
      (mem_boundedConstructible_iff _ K.obj.carrier).mp K.property
    apply (mem_boundedConstructible_iff _ _).mpr
    refine ⟨⟨a, b, fun r hr ↦ hz r (hab r hr)⟩, fun r ↦ ?_⟩
    exact IsConstructibleModuleObject.of_iso ((comparison D l h₀ r).app K.obj.carrier).symm
      (hc _ (hcons r))

private theorem fdGeometricBaseChange_eq (h₀ : W₀ ⟶ X₀) :
    fdGeometricBaseChange D W₀ X₀ h₀ = geometricMap D h₀ := rfl

private theorem pullback_str_eq (h₀ : W₀ ⟶ X₀)
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom) :
    fdCondensedPullbackWeilIso l (geometricMap D h₀)
        (D.geometricFrobenius W₀).hom (D.geometricFrobenius X₀).hom
        ⟨(D.frobenius_square_cartesian W₀ X₀ h₀).2.2.2.2.1⟩ F.carrier F.str =
      ((modulePull D l h₀).obj F).str := by
  have he : fdCondensedPullbackWeilIso l (geometricMap D h₀)
        (D.geometricFrobenius W₀).hom (D.geometricFrobenius X₀).hom
        ⟨(D.frobenius_square_cartesian W₀ X₀ h₀).2.2.2.2.1⟩ F.carrier F.str =
      (moduleSquare D l h₀).app F.carrier ≪≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (geometricMap D h₀)).mapIso F.str := by
    unfold fdCondensedPullbackWeilIso fdEvaluateWeilPullback
    apply Iso.ext
    rfl
  exact he.trans (eq_of_heq (named_weil_structure _ _ _ (moduleSquare D l h₀)
    (modulePull D l h₀) rfl F))

private theorem pullback_operator_eq (h₀ : W₀ ⟶ X₀)
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left) (n : ℕ)
    (h : z ≫ localPositivePower (D.geometricFrobenius W₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    CondensedModule.operator l D (D.geometricFrobenius W₀).hom
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (geometricMap D h₀)).obj
        F.carrier)
      (fdCondensedPullbackWeilIso l (geometricMap D h₀)
        (D.geometricFrobenius W₀).hom (D.geometricFrobenius X₀).hom
        ⟨(D.frobenius_square_cartesian W₀ X₀ h₀).2.2.2.2.1⟩ F.carrier F.str) z n h =
    CondensedModule.operator l D (D.geometricFrobenius W₀).hom
      (((modulePull D l h₀).obj F).carrier) (((modulePull D l h₀).obj F).str) z n h := by
  rw [pullback_str_eq]
  rfl

private theorem fibreComparison_eq (h₀ : W₀ ⟶ X₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (w : z ≫ geometricMap D h₀ = x)
    (M : CondensedModule.Modules l (D.geometricFiber X₀).left) :
    fdCondensedFibreComparison D l (geometricMap D h₀) z x w M =
      fibreComparison D l h₀ z x w M := by
  unfold fdCondensedFibreComparison fibreComparison
  rfl

private theorem fdLocal_congr {S T : Scheme.{u}} (f f' : S ⟶ T) (hf : f = f')
    (gS : S ⟶ S) (gT : T ⟶ T) (sq : CommSq gS f f gT) (sq' : CommSq gS f' f' gT)
    (M : CondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) gT).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ S) (x : Spec (.of D.k) ⟶ T)
    (w : z ≫ f = x) (w' : z ≫ f' = x) (nS nT : ℕ)
    (hS : z ≫ localPositivePower gS nS =
      localPositivePower (frobeniusPointIso D).hom nS ≫ z)
    (hT : x ≫ localPositivePower gT nT =
      localPositivePower (frobeniusPointIso D).hom nT ≫ x) (e : ℕ) :
    fdCondensedPullbackLocalAssertions D l f gS gT sq M θ z x w nS nT hS hT e ↔
      fdCondensedPullbackLocalAssertions D l f' gS gT sq' M θ z x w' nS nT hS hT e := by
  subst f'
  rfl

private theorem spectrum_one {K : Type*} [Field K] {M N : ModuleCat K}
    (c : M ≅ N) (A : End M) (B : End N) (e : ℕ) (he : e = 1)
    (h : fdCondensedSpectrumAssertions c A B e) : A ≫ c.hom = c.hom ≫ B := by
  have h := h.1
  simpa only [he, pow_one, ModuleCat.ofHom_hom] using h

private theorem local_identity [IsSeparated W₀.hom] [IsSeparated X₀.hom]
    (h₀ : W₀ ⟶ X₀) (z : {z : W₀.left // z ∈ closedPoints W₀.left})
    (hx : h₀.left z.val ∈ closedPoints X₀.left)
    (ιz : W₀.left.residueField z.val →+* D.k)
    (hz : ιz.comp (W₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k)
    (ιx : X₀.left.residueField (h₀.left z.val) →+* D.k)
    (hιx : ιx.comp (X₀.hom.residueFieldAlgebraMap (h₀.left z.val)) = algebraMap D.k₀ D.k)
    (w : localClosedPoint D W₀ z ιz hz ≫ geometricMap D h₀ =
      localClosedPoint D X₀ ⟨h₀.left z.val, hx⟩ ιx hιx)
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)
    (he : h₀.left.residueDegree z.val = 1)
    (h : fdCondensedClosedPullbackAssertions D l W₀ X₀ h₀ z hx ιz hz ιx hιx w F) :
    localOperator D l W₀ ((modulePull D l h₀).obj F) z ιz hz ≫
        (fibreComparison D l h₀ (localClosedPoint D W₀ z ιz hz)
          (localClosedPoint D X₀ ⟨h₀.left z.val, hx⟩ ιx hιx) w F.carrier).hom =
      (fibreComparison D l h₀ (localClosedPoint D W₀ z ιz hz)
          (localClosedPoint D X₀ ⟨h₀.left z.val, hx⟩ ιx hιx) w F.carrier).hom ≫
        localOperator D l X₀ F ⟨h₀.left z.val, hx⟩ ιx hιx := by
  unfold fdCondensedClosedPullbackAssertions at h
  have h := (fdLocal_congr D l _ _ (fdGeometricBaseChange_eq D h₀)
    (D.geometricFrobenius W₀).hom (D.geometricFrobenius X₀).hom
    _ ⟨(D.frobenius_square_cartesian W₀ X₀ h₀).2.2.2.2.1⟩
    _ _ _ _ _ w _ _ _ _ _).mp h
  have h := spectrum_one _ _ _ _ he h
  rw [fibreComparison_eq, pullback_operator_eq] at h
  exact h

private theorem local_assertions (hEll : l ≠ D.p)
    [IsSeparated W₀.hom] [IsSeparated X₀.hom]
    (h₀ : W₀ ⟶ X₀) [IsImmersion h₀.left] : LocalAssertions D l h₀ := by
  have : CompactSpace (D.geometricFiber X₀).left := by
    change CompactSpace (pullback X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme)
    infer_instance
  have : IsLocallyNoetherian (D.geometricFiber X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  have hgen := fdCondensedPullbackFrobenius D l hEll W₀ X₀ h₀
  intro z
  obtain ⟨hx, _, _, _, hlocal⟩ := hgen.2 z
  have : IsIso (h₀.left.residueFieldMap z.val) :=
    Scheme.Hom.isIso_residueFieldMap h₀.left z.val
  refine ⟨hx, inferInstance, ?_⟩
  intro ιz hz ιx hιx w F
  have hF := (adicConstructibilityPredicateComparison l (D.geometricFiber X₀).left
    (Profinite.padicAlgClRingObj l) (.algebraicClosure)).1 F.obj.carrier |>.mp F.property
  have he : h₀.left.residueDegree z.val = 1 := by
    let := (h₀.left.residueFieldMap z.val).hom.toAlgebra
    change Module.finrank (X₀.left.residueField (h₀.left z.val))
      (W₀.left.residueField z.val) = 1
    exact Module.finrank_of_bijective_algebraMap
      (ConcreteCategory.bijective_of_isIso (h₀.left.residueFieldMap z.val))
  exact local_identity D l h₀ z hx ιz hz ιx hιx w F.obj he
    (hlocal ιz hz ιx hιx w F.obj hF)

end Proofs

/-- Immersion restriction is exact, commutes canonically with cohomology as Weil objects,
and identifies local geometric Frobenius on the canonical fibres.
Source: latest blueprint, lem-zl-morphism-open-closed-reduction.proof.md,
Restriction and Part 2 (blueprint: lem-zl-condensed-immersion-local).

Proof:
1. The existing exact upperStar instances preserve monos, epis and exact pairs.
   Constructibility is preserved by isConstructibleModuleObject_upperStar.
2. The specified total-derived comparison identifies cohomology with exact pullback.
   Transfer zero objects and constructibility along it to preserve both half-lines
   and bounded constructibility.
3. Exact-derived cohomology coherence for the two composites in the Frobenius square,
   and naturality under its comparison, prove equivariance. Transport this equality
   through the total-derived comparison, then use naturality in the derived Weil map.
   Lift the resulting natural isomorphism to strict pairs, with unchanged components.
4. The general Frobenius pullback theorem gives closedness of the image point.
   Mathlib's immersion residue-field theorem makes the actual residue map an
   isomorphism, and its bijectivity implies residue degree one.
5. The adic constructibility-predicate comparison supplies the premise of the general
   pullback Frobenius formula. The formula uses the same canonical fibre comparison
   and Weil lift; substituting residue degree one gives the required identity.
   Empty schemes and the zero sheaf require no exceptions. -/
theorem immersion_local (hEll : l ≠ D.p) [IsSeparated W₀.hom] [IsSeparated X₀.hom]
    (h₀ : W₀ ⟶ X₀) [IsImmersion h₀.left] :
    ExactAssertions D l h₀ ∧ CohomologyAssertions D l h₀ ∧ LocalAssertions D l h₀ := by
  exact ⟨exact_assertions D l h₀, cohomology_assertions D l h₀,
    local_assertions D l hEll h₀⟩

end WeilConjectures.CondensedImmersion
