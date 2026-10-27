/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerPartialNerveCoordinates
public import Sheaf.Paper.KummerNormalizedChart

/-! # Resolved geometric successive root descent
Source: direct-image proof paragraph (3), successive augmented root nerves.
(blueprint: def-sfb-kummer-successive-descent).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
universe u u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory Limits Opposite AlgebraicTopology
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.KummerPartialNerve
open Profinite.CondensedAction
open CategoryTheory.CondensedBar

/-- Localization of a geometric nonnegative complex in the published site universe.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def smallQ (R : Ring.{u}) (S : Scheme.{u}) :
    CochainComplex (CondensedRing.KummerModules R.X S) ℕ ⥤
      DerivedCategory (CondensedRing.KummerModules R.X S) :=
  ComplexShape.embeddingUpNat.extendFunctor _ ⋙ DerivedCategory.Q

/-- Alternating cofaces followed by the finite diagonal sum, on a diagram of complexes.
Source: direct-image proof (3), signs (blueprint: def-sfb-kummer-successive-descent). -/
def diagonalTotalFunctor (R : Ring.{u}) (S : Scheme.{u}) :
    (SimplexCategory ⥤ SimplexCategory ⥤ CochainComplex (CondensedRing.KummerModules R.X S) ℕ) ⥤
      CochainComplex (CondensedRing.KummerModules R.X S) ℕ :=
  Functor.uncurry ⋙ (Functor.whiskeringLeft _ _ _).obj (Functor.diag SimplexCategory) ⋙
    alternatingCofaceMapComplex _ ⋙
      HomologicalComplex₂.totalFunctor _ (.up ℕ) (.up ℕ) (.up ℕ)

/-- Inner-first finite total, with differential d_o + (-1)^a d_i + (-1)^(a+b) d_res.
Source: direct-image proof (3), signs (blueprint: def-sfb-kummer-successive-descent). -/
def iteratedTotalFunctor (R : Ring.{u}) (S : Scheme.{u}) :
    (SimplexCategory ⥤ SimplexCategory ⥤ CochainComplex (CondensedRing.KummerModules R.X S) ℕ) ⥤
      CochainComplex (CondensedRing.KummerModules R.X S) ℕ :=
  (Functor.whiskeringRight _ _ _).obj
      (alternatingCofaceMapComplex _ ⋙
        HomologicalComplex₂.totalFunctor _ (.up ℕ) (.up ℕ) (.up ℕ)) ⋙
    alternatingCofaceMapComplex _ ⋙
      HomologicalComplex₂.totalFunctor _ (.up ℕ) (.up ℕ) (.up ℕ)

/-- The canonical coprojection from diagonal degree n and resolution degree z.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def diagonalSummand (R : Ring.{u}) (S : Scheme.{u})
    (B : SimplexCategory ⥤ SimplexCategory ⥤
      CochainComplex (CondensedRing.KummerModules R.X S) ℕ)
    (n z r : ℕ) (h : n + z = r) :
    ((B.obj (.mk n)).obj (.mk n)).X z ⟶ ((diagonalTotalFunctor R S).obj B).X r :=
  HomologicalComplex₂.ιTotal ((alternatingCofaceMapComplex _).obj
    (Functor.diag SimplexCategory ⋙ Functor.uncurry.obj B)) (.up ℕ) n z r h

/-- The canonical coprojection from (outer,inner,resolution) degree (n,m,z).
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def iteratedSummand (R : Ring.{u}) (S : Scheme.{u})
    (B : SimplexCategory ⥤ SimplexCategory ⥤
      CochainComplex (CondensedRing.KummerModules R.X S) ℕ)
    (n m z r t : ℕ) (h : m + z = r) (h' : n + r = t) :
    ((B.obj (.mk n)).obj (.mk m)).X z ⟶ ((iteratedTotalFunctor R S).obj B).X t :=
  HomologicalComplex₂.ιTotal ((alternatingCofaceMapComplex _).obj (B.obj (.mk n)))
    (.up ℕ) m z r h ≫
    HomologicalComplex₂.ιTotal ((alternatingCofaceMapComplex _).obj
      (B ⋙ alternatingCofaceMapComplex _ ⋙
        HomologicalComplex₂.totalFunctor _ (.up ℕ) (.up ℕ) (.up ℕ))) (.up ℕ) n r t h'

set_option backward.isDefEq.respectTransparency false in
/-- Exact point pullback commutes with extension by zero and localization.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def pullComplexIso (R : Ring.{u}) [HasDerivedCategory.{u + 2} (Modules R.toMon)]
    (S : Scheme.{u}) (K : CochainComplex (Modules R.toMon) ℕ) :
    (smallQ R S).obj
        ((((upperStarFromPoint S).mapMod R.X).mapHomologicalComplex (.up ℕ)).obj K) ≅
      (CondensedRing.kummerPointPullBig R S).obj (productBarQ.obj K) :=
  (DerivedCategory.Q.mapIso
    (K.mapExtendIso ComplexShape.embeddingUpNat ((upperStarFromPoint S).mapMod R.X))).symm ≪≫
      ((CondensedRing.kummerPointPullBigFactors R S).app _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Apply derived internal-Hom representatives and exact point pullback termwise.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def homPullComplex (R : Ring.{u}) (S : Scheme.{u}) (P : Profinite.{u}) :
    CochainComplex (Modules R.toMon) ℕ ⥤
      CochainComplex (CondensedRing.KummerModules R.X S) ℕ :=
  (Mod.ihom (freeParameter R P) ⋙
    (upperStarFromPoint S).mapMod R.X).mapHomologicalComplex (.up ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary extension-by-zero comparison for internal Hom followed by point pullback.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def homPullExtendIso (R : Ring.{u}) (S : Scheme.{u}) (P : Profinite.{u})
    (K : CochainComplex (Modules R.toMon) ℕ) :=
  K.mapExtendIso ComplexShape.embeddingUpNat
    (Mod.ihom (freeParameter R P) ⋙ (upperStarFromPoint S).mapMod R.X)

section Geometric
variable (R : Ring.{u}) {V T W U S : Scheme.{u}}
  {G H : Profinite.{u}} [CommGroup G] [IsTopologicalGroup G]
  [CommGroup H] [IsTopologicalGroup H]
  {action : ProfiniteCoefficientAction V (Profinite.of (G × H))}
  {v : V ⟶ W} {hv : action.act ≫ v = coefficientParameterProjection _ _ ≫ v}

/-- The actual double nerve's section functor, before resolving or totalizing.
All operators are the published adjunction-unit restriction maps on schemes over W.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def doubleImage (N : DoubleNerve G H action v hv) (a : W ⟶ U) (s : S ⟶ U) :
    CondensedRing.KummerModules R.X W ⥤
      (SimplexCategory × SimplexCategory ⥤ CondensedRing.KummerModules R.X S) :=
  (((prodOpEquiv (C := SimplexCategory) (D := SimplexCategory)).functor ⋙
      Functor.uncurry.obj N.diagram).rightOp ⋙ CondensedRing.overSections R.X W ⋙
    (Functor.whiskeringRight _ _ _).obj
      (CondensedRing.lowerStar R.X a ⋙ CondensedRing.upperStar R.X s)).flip

/-- Resolve the whole double section diagram on a single nonnegative resolution.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def doubleResolution (N : DoubleNerve G H action v hv) (a : W ⟶ U) (s : S ⟶ U)
    [(doubleImage R N a s).Additive]
    (I : CochainComplex (CondensedRing.KummerModules R.X W) ℕ) :
    SimplexCategory ⥤ SimplexCategory ⥤
      CochainComplex (CondensedRing.KummerModules R.X S) ℕ :=
  Functor.curry.obj (((doubleImage R N a s).mapHomologicalComplex (.up ℕ)).obj I).asFunctor

/-- Restriction along the actual double-nerve coordinates, then the full-root counit mate.
Source: direct-image proof (3), column squares
(blueprint: def-sfb-kummer-successive-descent). -/
def doubleGeometricMap (N : DoubleNerve G H action v hv)
    (j : V ⟶ T) (q : T ⟶ U) (a : W ⟶ U) (_hj : j ≫ q = v ≫ a)
    (i : S ⟶ T) (s : S ⟶ U) (hi : i ≫ q = s)
    (L : CondensedRing.KummerModules R.X W) (M : Modules R.toMon)
    (e : (CondensedRing.upperStar R.X v).obj L ≅
      ((upperStarFromPoint V).mapMod R.X).obj M)
    (I : InjectiveResolution M) (n m : ℕ)
    (d : CondensedRing.KummerParameterizedTerm R j q i s hi (parameters G H n m) M I)
    (h : (N.coordinates n m).inv.left ≫
        (((N.diagram.obj (op (.mk n))).obj (op (.mk m))).hom ≫ a) =
      coefficientParameterMap j (parameters G H n m) ≫
        CondensedRing.kummerFullParameterMap q (parameters G H n m)) :=
  CondensedRing.kummerImageTransport R.X (N.coordinates n m).inv.left
    (((N.diagram.obj (op (.mk n))).obj (op (.mk m))).hom ≫ a)
    (coefficientParameterMap j (parameters G H n m) ≫
      CondensedRing.kummerFullParameterMap q (parameters G H n m)) s h _ _
    (CondensedRing.kummerSquareDerivedModuleIso R (N.coordinates n m).inv.left
      ((N.diagram.obj (op (.mk n))).obj (op (.mk m))).hom
      (coefficientParameterProjection V (parameters G H n m)) v
      (N.coordinates n m).inv.w L M e (coefficientParameterMap j (parameters G H n m))) ≫
    d.geometricMap R j q i s hi (parameters G H n m) M I
end Geometric

/-- Normalization of a localized total comparison by a specified coherent roof.
All functors and arrows are explicit, so the equation does not expand the concrete
finite-total construction during elaboration.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def TotalRoofNormalized
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (Q : D ⥤ E)
    {X Y Z : C} (g : X ⟶ Y) (b : X ⟶ Z) {P : E}
    (comparison : Q.obj (F.obj Y) ≅ P) (barComparison : Q.obj (F.obj Z) ≅ P) : Prop :=
  Q.map (F.map g) ≫ comparison.hom = Q.map (F.map b) ≫ barComparison.hom

section Descent
variable (R : Ring.{u}) (G H : Profinite.{u}) [CommGroup G] [IsTopologicalGroup G]
  [CommGroup H] [IsTopologicalGroup H] [e : Environment R G H]

/-- Actual point pullback of every term and operator of the fixed product bar resolution.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def doubleBar (S : Scheme.{u}) (I : CochainComplex (ActionModule R.toMon (G × H)) ℕ) :
    SimplexCategory ⥤ SimplexCategory ⥤
      CochainComplex (CondensedRing.KummerModules R.X S) ℕ :=
  e.bar.onComplex I ⋙ (Functor.whiskeringRight _ _ _).obj
    (((upperStarFromPoint S).mapMod R.X).mapHomologicalComplex (.up ℕ))

/-- Coherent resolved geometric columns, fixed by actual coordinate restrictions,
full-root counit mates and internal-Hom evaluation on every double parameter.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
structure SuccessiveColumnData {V T W U S : Scheme.{u}}
    {action : ProfiniteCoefficientAction V (Profinite.of (G × H))}
    {v : V ⟶ W} {hv : action.act ≫ v = coefficientParameterProjection _ _ ≫ v}
    (N : DoubleNerve G H action v hv)
    (j : V ⟶ T) (q : T ⟶ U) (a : W ⟶ U) (_hj : j ≫ q = v ≫ a)
    (i : S ⟶ T) (s : S ⟶ U) (hi : i ≫ q = s)
    (L : CondensedRing.KummerModules R.X W) (M : ActionModule R.toMon (G × H))
    (punctured : (CondensedRing.upperStar R.X v).obj L ≅
      ((upperStarFromPoint V).mapMod R.X).obj M.module)
    (I : InjectiveResolution L) (J : InjectiveResolution M)
    (K : InjectiveResolution M.module)
    (underlying : K.cocomplex ≅
      ((forgetAction (A := R) (G := G × H)).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    [(doubleImage R N a s).Additive] where
  common : SimplexCategory ⥤ SimplexCategory ⥤
    CochainComplex (CondensedRing.KummerModules R.X S) ℕ
  geometric : common ⟶ doubleResolution R N a s I.cocomplex
  bar : common ⟶ doubleBar R G H S J.cocomplex
  terms : ∀ n m : ℕ, CondensedRing.KummerParameterizedTerm R j q i s hi
    (parameters G H n m) M.module K
  coordinate_toBase : ∀ n m : ℕ, (N.coordinates n m).inv.left ≫
      (((N.diagram.obj (op (.mk n))).obj (op (.mk m))).hom ≫ a) =
    coefficientParameterMap j (parameters G H n m) ≫
      CondensedRing.kummerFullParameterMap q (parameters G H n m)
  columnComposition : ∀ n m : ℕ,
    ((doubleResolution R N a s I.cocomplex).obj (.mk n)).obj (.mk m) ≅
      ((CondensedRing.upperStar R.X
          ((N.diagram.obj (op (.mk n))).obj (op (.mk m))).hom ⋙
        CondensedRing.lowerStar R.X
          (((N.diagram.obj (op (.mk n))).obj (op (.mk m))).hom ≫ a) ⋙
        CondensedRing.upperStar R.X s).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  term : ∀ (B : ActionModule R.toMon (G × H)) (n m : ℕ),
    (productBarEvaluation R.toMon n m).obj (e.bar.cochains.obj B) ≅
      (e.full.functions.functor (parameters G H n m)).obj B.module
  barColumn : ∀ n m : ℕ,
    ((doubleBar R G H S J.cocomplex).obj (.mk n)).obj (.mk m) ≅
      (homPullComplex R S (parameters G H n m)).obj K.cocomplex

/-- All column normalization laws for the supplied concrete double-resolution data.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def SuccessiveColumnLaws {V T W U S : Scheme.{u}}
    {action : ProfiniteCoefficientAction V (Profinite.of (G × H))}
    {v : V ⟶ W} {hv : action.act ≫ v = coefficientParameterProjection _ _ ≫ v}
    (N : DoubleNerve G H action v hv)
    (j : V ⟶ T) (q : T ⟶ U) (a : W ⟶ U) (_hj : j ≫ q = v ≫ a)
    (i : S ⟶ T) (s : S ⟶ U) (hi : i ≫ q = s)
    (L : CondensedRing.KummerModules R.X W) (M : ActionModule R.toMon (G × H))
    (punctured : (CondensedRing.upperStar R.X v).obj L ≅
      ((upperStarFromPoint V).mapMod R.X).obj M.module)
    (I : InjectiveResolution L) (J : InjectiveResolution M)
    (K : InjectiveResolution M.module)
    (underlying : K.cocomplex ≅
      ((forgetAction (A := R) (G := G × H)).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    [(doubleImage R N a s).Additive]
    (d : SuccessiveColumnData R G H N j q a _hj i s hi L M punctured I J K underlying) : Prop :=
  (∀ n m : ℕ, QuasiIso ((d.geometric.app (.mk n)).app (.mk m)))
    ∧ (∀ n m : ℕ, QuasiIso ((d.bar.app (.mk n)).app (.mk m)))
    ∧ (∀ n m z : ℕ, HEq ((d.columnComposition n m).hom.f z) (
    (CondensedRing.upperStar R.X s).map
      ((CondensedRing.lowerStarComp R.X
        ((N.diagram.obj (op (.mk n))).obj (op (.mk m))).hom a).hom.app
          ((CondensedRing.upperStar R.X
            ((N.diagram.obj (op (.mk n))).obj (op (.mk m))).hom).obj (I.cocomplex.X z)))))
    ∧ (∀ (B : ActionModule R.toMon (G × H)) (n m : ℕ)
    (P Q : Profinite.{u}) (f : Q ⟶ P) (g : C(Q, parameters G H n m))
    (x : sectionModule R.toMon
      ((productBarEvaluation R.toMon n m).obj (e.bar.cochains.obj B)) P),
    (e.full.functions.evaluate (parameters G H n m) P B.module
      (((d.term B n m).hom.hom.hom.app (op P)) x)).val Q f g =
      B.module.X.obj.map
        (CompHausLike.ofHom _ (f.hom.hom.prodMk g)).op (e.bar.sections B n m P x))
    ∧ (∀ n m z : ℕ, HEq ((d.barColumn n m).hom.f z) (
    ((upperStarFromPoint S).mapMod R.X).map
      ((d.term (J.cocomplex.X z) n m).hom ≫
        (e.full.functions.internalHom (parameters G H n m)).hom.app (J.cocomplex.X z).module ≫
        (Mod.ihom (freeParameter R (parameters G H n m))).map (underlying.inv.f z))))
    ∧ (∀ n m : ℕ,
    (smallQ R S).map ((d.geometric.app (.mk n)).app (.mk m)) ≫
      (smallQ R S).map (d.columnComposition n m).hom ≫
      CondensedRing.kummerImageColumnMap R.X
        ((N.diagram.obj (op (.mk n))).obj (op (.mk m))).hom
        (((N.diagram.obj (op (.mk n))).obj (op (.mk m))).hom ≫ a) s I ≫
      doubleGeometricMap R N j q a _hj i s hi L M.module punctured K n m
        (d.terms n m) (d.coordinate_toBase n m) =
    (smallQ R S).map ((d.bar.app (.mk n)).app (.mk m)) ≫
      (smallQ R S).map (d.barColumn n m).hom ≫
      (DerivedCategory.Q.mapIso
        (homPullExtendIso R S (parameters G H n m) K.cocomplex)).inv ≫
      (((upperStarFromPoint S).mapMod R.X).mapDerivedCategoryFactors.app
        (((Mod.ihom (freeParameter R (parameters G H n m))).mapHomologicalComplex
          (.up ℤ)).obj K.cochainComplex)).inv ≫
      CondensedRing.kummerHomResolutionEvaluation R S (parameters G H n m) K)

/-- Resolved columns and their normalization laws for the supplied double-resolution data.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
structure SuccessiveColumns {V T W U S : Scheme.{u}}
    {action : ProfiniteCoefficientAction V (Profinite.of (G × H))}
    {v : V ⟶ W} {hv : action.act ≫ v = coefficientParameterProjection _ _ ≫ v}
    (N : DoubleNerve G H action v hv)
    (j : V ⟶ T) (q : T ⟶ U) (a : W ⟶ U) (_hj : j ≫ q = v ≫ a)
    (i : S ⟶ T) (s : S ⟶ U) (hi : i ≫ q = s)
    (L : CondensedRing.KummerModules R.X W) (M : ActionModule R.toMon (G × H))
    (punctured : (CondensedRing.upperStar R.X v).obj L ≅
      ((upperStarFromPoint V).mapMod R.X).obj M.module)
    (I : InjectiveResolution L) (J : InjectiveResolution M)
    (K : InjectiveResolution M.module)
    (underlying : K.cocomplex ≅
      ((forgetAction (A := R) (G := G × H)).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    [(doubleImage R N a s).Additive] where
  data : SuccessiveColumnData R G H N j q a _hj i s hi L M punctured I J K underlying
  laws : SuccessiveColumnLaws R G H N j q a _hj i s hi L M punctured I J K underlying data

set_option backward.isDefEq.respectTransparency true

/-- The two finite totalizations and their actual augmentations over a fixed resolved
geometric double diagram. Every component, comparison and gamma normalization is
retained; fixing the diagram avoids repeatedly expanding its section construction.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
structure SuccessiveTotalData (S : Scheme.{u}) (M : ActionModule R.toMon (G × H))
    (J : InjectiveResolution M)
    (B : SimplexCategory ⥤ SimplexCategory ⥤
      CochainComplex (CondensedRing.KummerModules R.X S) ℕ)
    (base : CochainComplex (CondensedRing.KummerModules R.X S) ℕ) where
  barDiagonal : (diagonalTotalFunctor R S).obj (doubleBar R G H S J.cocomplex) ≅
    (((upperStarFromPoint S).mapMod R.X).mapHomologicalComplex (.up ℕ)).obj
      (e.bar.diagonalTotal J.cocomplex)
  barIterated : (iteratedTotalFunctor R S).obj (doubleBar R G H S J.cocomplex) ≅
    (((upperStarFromPoint S).mapMod R.X).mapHomologicalComplex (.up ℕ)).obj
      (e.bar.iteratedTotal J.cocomplex)
  diagonalComparison :
    (smallQ R S).obj ((diagonalTotalFunctor R S).obj
      B) ≅
      (CondensedRing.kummerPointPullBig R S).obj
        (productBarQ.obj (e.bar.diagonalTotal J.cocomplex))
  iteratedComparison :
    (smallQ R S).obj ((iteratedTotalFunctor R S).obj
      B) ≅
      (CondensedRing.kummerPointPullBig R S).obj
        (productBarQ.obj (e.bar.iteratedTotal J.cocomplex))
  sectionUnit :
    base ⟶
        (B.obj (.mk 0)).obj (.mk 0)
  diagonalAugmentation :
    base ⟶
        (diagonalTotalFunctor R S).obj B
  augmentation :
    base ⟶
        (iteratedTotalFunctor R S).obj B
  [diagonalAugmentation_iso : IsIso ((smallQ R S).map diagonalAugmentation)]
  [augmentation_iso : IsIso ((smallQ R S).map augmentation)]
  gamma : (CondensedRing.kummerPointPullBig R S).obj
      (productBarQ.obj (e.bar.diagonalTotal J.cocomplex)) ≅
    (CondensedRing.kummerPointPullBig R S).obj
      ((e.inner.functor.rightDerivedFunctor ⋙ e.outer.functor.rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))

/-- All component, augmentation, gamma and theta laws for the fixed totalization data.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def SuccessiveTotalLaws (S : Scheme.{u}) (M : ActionModule R.toMon (G × H))
    (J : InjectiveResolution M)
    (B : SimplexCategory ⥤ SimplexCategory ⥤
      CochainComplex (CondensedRing.KummerModules R.X S) ℕ)
    (base : CochainComplex (CondensedRing.KummerModules R.X S) ℕ)
    (d : SuccessiveTotalData R G H S M J B base) : Prop :=
  letI := d.diagonalAugmentation_iso
  letI := d.augmentation_iso
  (∀ n z r : ℕ, ∀ h : n + z = r,
    HEq (diagonalSummand R S (doubleBar R G H S J.cocomplex) n z r h ≫
        d.barDiagonal.hom.f r)
      (((upperStarFromPoint S).mapMod R.X).map
        ((e.bar.diagonalDouble J.cocomplex).ιTotal (.up ℕ) n z r h)))
    ∧ (∀ n m z r t : ℕ, ∀ (h : m + z = r) (h' : n + r = t),
    HEq (iteratedSummand R S (doubleBar R G H S J.cocomplex) n m z r t h h' ≫
        d.barIterated.hom.f t)
      (((upperStarFromPoint S).mapMod R.X).map
        (HomologicalComplex₂.ιTotal ((alternatingCofaceMapComplex _).obj
          ((e.bar.onComplex J.cocomplex).obj (.mk n))) (.up ℕ) m z r h ≫
            (e.bar.iteratedDouble J.cocomplex).ιTotal (.up ℕ) n r t h')))
    ∧ (∀ z : ℕ, HEq (d.diagonalAugmentation.f z)
    (d.sectionUnit.f z ≫
      diagonalSummand R S B 0 z z (Nat.zero_add z)))
    ∧ (∀ z : ℕ, HEq (d.augmentation.f z)
    (d.sectionUnit.f z ≫
      iteratedSummand R S B
        0 0 z z z (Nat.zero_add z) (Nat.zero_add z)))
    ∧ (d.diagonalComparison.inv ≫ inv ((smallQ R S).map d.diagonalAugmentation) ≫
        (smallQ R S).map d.augmentation ≫ d.iteratedComparison.hom =
      (CondensedRing.kummerPointPullBig R S).map
        ((e.comparison M J).augmentations.comparison e.inflation))
    ∧ (d.gamma.hom =
      d.diagonalComparison.inv ≫ inv ((smallQ R S).map d.diagonalAugmentation) ≫
        (smallQ R S).map d.augmentation ≫ d.iteratedComparison.hom ≫
          (Environment.iteratedInvariantIso R G H S M J).hom)
    ∧ ((CondensedRing.kummerPointPullBig R S).map
        (e.full.invariants.functor.rightDerivedFunctor.map (degreeZeroIso M).inv ≫
          (e.comparison M J).diagonalIso.hom) ≫
        d.gamma.hom =
      (CondensedRing.kummerPointPullBig R S).map
        ((productBarDerivedComparison e.outer e.inner e.full.invariants e.inflation).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj M)))

/-- The finite totalization data with all component and augmentation laws.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
structure SuccessiveTotals (S : Scheme.{u}) (M : ActionModule R.toMon (G × H))
    (J : InjectiveResolution M)
    (B : SimplexCategory ⥤ SimplexCategory ⥤
      CochainComplex (CondensedRing.KummerModules R.X S) ℕ)
    (base : CochainComplex (CondensedRing.KummerModules R.X S) ℕ) where
  data : SuccessiveTotalData R G H S M J B base
  laws : SuccessiveTotalLaws R G H S M J B base data

/-- Coherent normalized successive geometric descent. Its roof commutes with every
operator before finite totalization. Every column is fixed by the actual coordinate
restriction, root-tower counit mate, and internal-Hom evaluation. Both finite-total
comparisons are prescribed on the coherent roof, and the augmentation is geometric.
Source: direct-image proof (3), successive augmented nerves
(blueprint: def-sfb-kummer-successive-descent). -/
structure SuccessiveDescent {V T W U S : Scheme.{u}}
    {action : ProfiniteCoefficientAction V (Profinite.of (G × H))}
    {v : V ⟶ W} {hv : action.act ≫ v = coefficientParameterProjection _ _ ≫ v}
    (N : DoubleNerve G H action v hv)
    (j : V ⟶ T) (q : T ⟶ U) (a : W ⟶ U) (_hj : j ≫ q = v ≫ a)
    (i : S ⟶ T) (s : S ⟶ U) (hi : i ≫ q = s)
    (L : CondensedRing.KummerModules R.X W) (M : ActionModule R.toMon (G × H))
    (punctured : (CondensedRing.upperStar R.X v).obj L ≅
      ((upperStarFromPoint V).mapMod R.X).obj M.module)
    (I : InjectiveResolution L) (J : InjectiveResolution M)
    (K : InjectiveResolution M.module)
    (underlying : K.cocomplex ≅
      ((forgetAction (A := R) (G := G × H)).mapHomologicalComplex (.up ℕ)).obj J.cocomplex) where
  [image_additive : (doubleImage R N a s).Additive]
  columns : SuccessiveColumns R G H N j q a _hj i s hi L M punctured I J K underlying
  totals : SuccessiveTotals R G H S M J (doubleResolution R N a s I.cocomplex)
    (((CondensedRing.lowerStar R.X a ⋙ CondensedRing.upperStar R.X s).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex)
  diagonal_normalization : TotalRoofNormalized (diagonalTotalFunctor R S) (smallQ R S)
    columns.data.geometric columns.data.bar totals.data.diagonalComparison
    ((smallQ R S).mapIso totals.data.barDiagonal ≪≫
      pullComplexIso R S (e.bar.diagonalTotal J.cocomplex))
  iterated_normalization : TotalRoofNormalized (iteratedTotalFunctor R S) (smallQ R S)
    columns.data.geometric columns.data.bar totals.data.iteratedComparison
    ((smallQ R S).mapIso totals.data.barIterated ≪≫
      pullComplexIso R S (e.bar.iteratedTotal J.cocomplex))
  diagonal_roof_iso : IsIso ((smallQ R S).map
    ((diagonalTotalFunctor R S).map columns.data.geometric))
  iterated_roof_iso : IsIso ((smallQ R S).map
    ((iteratedTotalFunctor R S).map columns.data.geometric))
  sectionUnit_components : ∀ z : ℕ, HEq (totals.data.sectionUnit.f z)
    ((CondensedRing.lowerStar R.X a ⋙ CondensedRing.upperStar R.X s).map
      ((CondensedRing.overSectionUnit R.X
        ((N.diagram.obj (op (.mk 0))).obj (op (.mk 0)))).app (I.cocomplex.X z)))

section Arrows
variable {R G H} {V T W U S : Scheme.{u}}
  {action : ProfiniteCoefficientAction V (Profinite.of (G × H))}
  {v : V ⟶ W} {hv : action.act ≫ v = coefficientParameterProjection _ _ ≫ v}
  {N : DoubleNerve G H action v hv}
  {j : V ⟶ T} {q : T ⟶ U} {a : W ⟶ U} {hj : j ≫ q = v ≫ a}
  {i : S ⟶ T} {s : S ⟶ U} {hi : i ≫ q = s}
  {L : CondensedRing.KummerModules R.X W} {M : ActionModule R.toMon (G × H)}
  {punctured : (CondensedRing.upperStar R.X v).obj L ≅
    ((upperStarFromPoint V).mapMod R.X).obj M.module}
  {I : InjectiveResolution L} {J : InjectiveResolution M}
  {K : InjectiveResolution M.module}
  {underlying : K.cocomplex ≅
    ((forgetAction (A := R) (G := G × H)).mapHomologicalComplex (.up ℕ)).obj J.cocomplex}

/-- The successive geometric augmentation, in the ordinary derived category.
It is the resolved actual unit augmentation followed by the coherent roof and
specified iterated invariant comparison; no arbitrary derived arrow is chosen.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def SuccessiveDescent.augmentationArrow
    (d : SuccessiveDescent R G H N j q a hj i s hi L M punctured I J K underlying) :
    CondensedRing.kummerOpenImage R.X a s L ⟶
      (CondensedRing.kummerPointPullBig R S).obj
        ((e.inner.functor.rightDerivedFunctor ⋙ e.outer.functor.rightDerivedFunctor).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) :=
  (CondensedRing.kummerResolutionComparison R.X a s I).hom ≫
    (smallQ R S).map d.totals.data.augmentation ≫ d.totals.data.iteratedComparison.hom ≫
      (Environment.iteratedInvariantIso R G H S M J).hom

/-- Every boundary restriction retains an actual resolved successive geometric
model, whose augmentation arrow is exactly the canonical pullback of the original.
Identity and composite restrictions are included, with the published composition
and point-pullback identifications, rather than an arbitrary comparison map.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-successive-descent). -/
def SuccessiveDescent.Refines
    (d : SuccessiveDescent R G H N j q a hj i s hi L M punctured I J K underlying) : Prop :=
  ∀ (S' : Scheme.{u}) (f : S' ⟶ S),
    ∃ restricted : SuccessiveDescent R G H N j q a hj (f ≫ i) (f ≫ s)
      ((Category.assoc f i q).trans (congrArg (fun t ↦ f ≫ t) hi))
      L M punctured I J K underlying,
      restricted.augmentationArrow =
        (CondensedRing.kummerDerivedUpperComp R.X f s).hom.app _ ≫
          (CondensedRing.upperStar R.X f).mapDerivedCategory.map d.augmentationArrow ≫
          (CondensedRing.kummerPointPullBigPullbackIso R f).hom.app _
end Arrows
end Descent
end AlgebraicGeometry.ProEtale.KummerPartialNerve
