/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionCompositionRealization
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionBinaryIterationTrianglePasting
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionBinaryTriangleSquare
import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.CompositionProjectionMate
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CompatibleCompactificationTriangle

/-! # Finite projection coherence in operation coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection

namespace WeilConjectures.CompactSupportFiniteProjection

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem paste_realized_square
    {A : Type*} [Category A] {a b c d a' b' d' : A}
    (e : a ⟶ b) (p : b ⟶ d) (q : a ⟶ c) (t : c ⟶ d)
    (sa : a ≅ a') (sb : b ≅ b') (td : d ≅ d') (tc : c ≅ d')
    (r : b' ⟶ a') (v : a' ⟶ d') (w : b' ⟶ d')
    (hs : e ≫ sb.hom ≫ r = sa.hom)
    (hp : p ≫ td.hom = sb.hom ≫ w)
    (ht : t ≫ td.hom = tc.hom)
    (hq : q ≫ tc.hom = sa.hom ≫ v)
    (hw : w = r ≫ v) : e ≫ p = q ≫ t := by
  apply (cancel_mono td.hom).1
  simp only [Category.assoc]
  rw [hp, ht, hq, hw]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ v) hs

section CoefficientCoordinates
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [AlgebraicGeometry.ProEtale.UpperStarPreservesFlat A]

@[irreducible] private def proper_coordinate
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    ((derivedTensor A Y).obj ((lowerStar A f).rightDerivedFunctor.obj K)).obj L ⟶
      (lowerStar A f).rightDerivedFunctor.obj
        (((derivedTensor A X).obj K).obj ((upperStar A f).leftDerivedFunctor.obj L)) :=
  ((rightDerivedLowerStarProjectionMap A f).app K).app L

private theorem proper_coordinate_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    proper_coordinate A f K L = ((rightDerivedLowerStarProjectionMap A f).app K).app L := by
  unfold proper_coordinate
  rfl

@[irreducible] private def open_coordinate
    {X V : Scheme.{u}} (j : X ⟶ V) [IsOpenImmersion j]
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology V) A)) :
    ((derivedTensor A V).obj
      ((openImmersionLowerShriek A j).mapDerivedCategory.obj K)).obj L ⟶
      (openImmersionLowerShriek A j).mapDerivedCategory.obj
        (((derivedTensor A X).obj K).obj ((upperStar A j).leftDerivedFunctor.obj L)) :=
  ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app L

private theorem open_coordinate_eq
    {X V : Scheme.{u}} (j : X ⟶ V) [IsOpenImmersion j]
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology V) A)) :
    open_coordinate A j K L =
      ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app L := by
  unfold open_coordinate
  rfl

private theorem coordinate_factor_formula
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    projectionTensorCoordinateComponent A c K L =
      proper_coordinate A c.g ((openImmersionLowerShriek A c.i).mapDerivedCategory.obj K) L ≫
      (lowerStar A c.g).rightDerivedFunctor.map
        (open_coordinate A c.i K ((upperStar A c.g).leftDerivedFunctor.obj L)) ≫
      (lowerStar A c.g).rightDerivedFunctor.map
        ((openImmersionLowerShriek A c.i).mapDerivedCategory.map
          (((derivedTensor A X).obj K).map
            ((leftDerivedUpperStarCompactificationIso A c).hom.app L))) := by
  rw [proper_coordinate_eq, open_coordinate_eq]
  exact projectionMapOfCompactification_app_app A c K L

private theorem coefficient_factor_formula
    {X V Y : Scheme.{u}} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion j] [IsProper q]
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    projectionTensorCoordinateComponent A
        (⟨V, q, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ q)) K L =
      proper_coordinate A q ((openImmersionLowerShriek A j).mapDerivedCategory.obj K) L ≫
      (lowerStar A q).rightDerivedFunctor.map
        (open_coordinate A j K ((upperStar A q).leftDerivedFunctor.obj L)) ≫
      (lowerStar A q).rightDerivedFunctor.map
        ((openImmersionLowerShriek A j).mapDerivedCategory.map
          (((derivedTensor A X).obj K).map
            ((leftDerivedUpperStarComp A j q).inv.app L))) := by
  rw [coordinate_factor_formula]
  simp -implicitDefEqProofs only [leftDerivedUpperStarCompactificationIso,
    Iso.trans_hom, Iso.symm_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id]

end CoefficientCoordinates

private theorem normalize_projection
    {A B C : Type*} [Category A] [Category B] [Category C]
    (T : A ⥤ A ⥤ A) (F : A ⥤ B) (G : B ⥤ C)
    {K y z : A} {v : C} {w : B}
    (a : v ⟶ G.obj w) (b : w ⟶ F.obj ((T.obj K).obj y)) (c : y ⟶ z) :
    a ≫ G.map b ≫ G.map (F.map ((T.obj K).map c)) =
      a ≫ G.map (b ≫ F.map ((T.map (𝟙 K)).app y ≫ (T.obj K).map c)) := by
  rw [T.map_id K, NatTrans.id_app, Category.id_comp, G.map_comp]

private theorem ordinary_projection_formula
    {D : FiniteFieldDatum.{u}} (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V Y : SixFunctorSpace D} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion ((geometry D).map j)] [IsProper ((geometry D).map q)]
    [IsOpenImmersion j.hom.left]
    (K : ProperOpenDerived A X.obj.left) (L : ProperOpenDerived A Y.obj.left) :
    projection (ordinary D A) (ordinaryTensor D A) j q K L =
      proper_coordinate (ModuleCat.{u + 1} A) q.hom.left
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j.hom.left).mapDerivedCategory.obj
            K) L ≫
      (lowerStar (ModuleCat.{u + 1} A) q.hom.left).rightDerivedFunctor.map
        (open_coordinate (ModuleCat.{u + 1} A) j.hom.left K
          ((upperStar (ModuleCat.{u + 1} A) q.hom.left).leftDerivedFunctor.obj L)) ≫
      (lowerStar (ModuleCat.{u + 1} A) q.hom.left).rightDerivedFunctor.map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j.hom.left).mapDerivedCategory.map
          (((derivedTensor (ModuleCat.{u + 1} A) X.obj.left).obj K).map
            ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j.hom.left q.hom.left).inv.app
              L))) := by
  let T := derivedTensor (ModuleCat.{u + 1} A) X.obj.left
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j.hom.left).mapDerivedCategory
  let G := (lowerStar (ModuleCat.{u + 1} A) q.hom.left).rightDerivedFunctor
  let Pq := (upperStar (ModuleCat.{u + 1} A) q.hom.left).leftDerivedFunctor
  let Pj := (upperStar (ModuleCat.{u + 1} A) j.hom.left).leftDerivedFunctor
  let a := proper_coordinate (ModuleCat.{u + 1} A) q.hom.left (J.obj K) L
  let b := open_coordinate (ModuleCat.{u + 1} A) j.hom.left K (Pq.obj L)
  let c := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j.hom.left q.hom.left).inv.app L
  have hr : projection (ordinary D A) (ordinaryTensor D A) j q K L =
      a ≫ G.map (b ≫ J.map ((T.map (𝟙 K)).app (Pj.obj (Pq.obj L)) ≫
        (T.obj K).map c)) := by
    dsimp only [a, b]
    rw [proper_coordinate_eq, open_coordinate_eq]
    rfl
  exact hr.trans (normalize_projection T J G a b c).symm

private theorem factor_projection_refl
    {D : FiniteFieldDatum.{u}} (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V Y : SixFunctorSpace D} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion ((geometry D).map j)] [IsProper ((geometry D).map q)]
    (K : ProperOpenDerived A X.obj.left) (L : ProperOpenDerived A Y.obj.left) :
    projectionTensorCoordinateComponent (ModuleCat.{u + 1} A)
        (sixFunctorFactorCompactification j q
          ‹IsOpenImmersion ((geometry D).map j)› ‹IsProper ((geometry D).map q)›
          (j ≫ q) rfl) K L =
      projection (ordinary D A) (ordinaryTensor D A) j q K L := by
  let : IsOpenImmersion j.hom.left := ‹IsOpenImmersion ((geometry D).map j)›
  let : IsProper q.hom.left := ‹IsProper ((geometry D).map q)›
  exact (coefficient_factor_formula (ModuleCat.{u + 1} A) j.hom.left q.hom.left K L).trans
    (ordinary_projection_formula A j q K L).symm

attribute [local irreducible] AlgebraicGeometry.ProEtale.derivedTensor
attribute [local irreducible] Functor.leftDerivedFunctor
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

private theorem faithful_square
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Faithful]
    {a b c d : A} (e : a ⟶ b) (p : b ⟶ d) (q : a ⟶ c) (t : c ⟶ d)
    (h : F.map e ≫ F.map p = F.map q ≫ F.map t) : e ≫ p = q ≫ t := by
  apply F.map_injective
  simpa only [Functor.map_comp] using h

private theorem compatible_triangle
    {D : FiniteFieldDatum.{u}} {X Y B Z : SixFunctorSpace D}
    (f : X ⟶ Y) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsOpenImmersion i.hom.left] [IsProper s.hom.left] :
    ∃ (V W : SixFunctorSpace D) (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B),
      IsOpenImmersion j.hom.left ∧ IsOpenImmersion b.hom.left ∧
      IsProper q.hom.left ∧ IsProper p.hom.left ∧ f = j ≫ q ∧ b ≫ p = q ≫ i ∧
      IsPullback b.hom.left q.hom.left p.hom.left i.hom.left ∧
      QuasiCompact b.hom.left ∧ QuasiCompact i.hom.left := by
  have : QuasiCompact i.hom.left := inferInstance
  let d : Compactification (i.hom.left ≫ s.hom.left) :=
    ⟨B.obj.left, s.hom.left, i.hom.left, rfl, inferInstance, inferInstance⟩
  obtain ⟨e, he, c, hc, hqc, hcb, hcf, hb, hqb, hq, hsq, _, _⟩ :=
    exists_compatible_compactification_triangle f.hom.left (i.hom.left ≫ s.hom.left) d
  have := Y.property.1
  have := Y.property.2
  have := B.property.1
  have := B.property.2
  have := hb
  have := hqb
  have := hq
  have := hc
  have := hqc
  let W : SixFunctorSpace D := ⟨Over.mk (e.g ≫ B.obj.hom), by
    change LocallyOfFiniteType (e.g ≫ B.obj.hom) ∧ QuasiCompact (e.g ≫ B.obj.hom)
    exact ⟨inferInstance, inferInstance⟩⟩
  let V : SixFunctorSpace D := ⟨Over.mk (pullback.snd e.g d.i ≫ Y.obj.hom), by
    change LocallyOfFiniteType (pullback.snd e.g d.i ≫ Y.obj.hom) ∧
      QuasiCompact (pullback.snd e.g d.i ≫ Y.obj.hom)
    exact ⟨inferInstance, inferInstance⟩⟩
  let q : V ⟶ Y := ⟨Over.homMk (pullback.snd e.g d.i) rfl⟩
  let p : W ⟶ B := ⟨Over.homMk e.g rfl⟩
  let b : V ⟶ W := ⟨Over.homMk (pullback.fst e.g d.i) (by
    change pullback.fst e.g d.i ≫ (e.g ≫ B.obj.hom) =
      pullback.snd e.g d.i ≫ Y.obj.hom
    rw [← Category.assoc, pullback.condition, Category.assoc, i.hom.w])⟩
  let j : X ⟶ V := ⟨Over.homMk c (by
    change c ≫ (pullback.snd e.g d.i ≫ Y.obj.hom) = X.obj.hom
    rw [← Category.assoc, hcf, f.hom.w])⟩
  refine ⟨V, W, j, b, q, p, hc, hb, hq, e.isProper, ?_, ?_, hsq, hqb, inferInstance⟩
  · apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hcf.symm
  · apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact pullback.condition

private theorem replace_map_path
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {x y : A} {a b c : B} (p p' : a ⟶ F.obj x) (q q' : x ⟶ y)
    (r : F.obj y ⟶ b) (t : b ⟶ c) (v : a ⟶ c)
    (hp : p = p') (hq : q = q') (hv : (p' ≫ F.map q') ≫ r ≫ t = v) :
    (p ≫ F.map q) ≫ r ≫ t = v := by
  rw [hp, hq]
  exact hv

private theorem raw_square_maps
    {G : Type*} [Category G] {geo : G ⥤ Scheme.{u}} (c : Calculus G geo) (t : TensorData c)
    {X V W Y B Z : G}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)] [QuasiCompact (geo.map i)]
    [IsProper (geo.map q)] [IsProper (geo.map p)] (hb : b ≫ p = q ≫ i)
    (K : c.D X) (L : c.D Z) :
    (leftMap c t j b q p i s hb K L =
      (projection c t i s ((compact c j q).obj K) L ≫
        (compact c i s).map (projection c t j q K ((c.P (i ≫ s)).obj L))) ≫
        (alpha c j b q p i s hb).app
          ((t.tensor X).obj (K, (c.P (j ≫ q)).obj ((c.P (i ≫ s)).obj L))) ≫
        (compact c (j ≫ b) (p ≫ s)).map
          ((t.tensor X).map
            (Prod.mkHom (𝟙 K) ((trianglePull c j b q p i s hb).hom.app L)))) ∧
    (rightMap c t j b q p i s hb K L =
      (t.tensor Z).map (Prod.mkHom ((alpha c j b q p i s hb).app K) (𝟙 L)) ≫
        projection c t (j ≫ b) (p ≫ s) K L) := by
  constructor
  · exact (Category.assoc _ _ _).symm
  · rfl

attribute [local irreducible] TriangleLaws

private theorem fixed_factor_projection_refl
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {X V Y : SixFunctorSpace D} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion ((geometry D).map j)] [IsProper ((geometry D).map q)]
    (K : ProperOpenDerived (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
      X.obj.left)
    (L : ProperOpenDerived (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
      Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) (j ≫ q)
      (binaryFirst j q) K L = projection (ordinary D A)
      (fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)) j q K L := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  exact factor_projection_refl _ j q K L

attribute [local irreducible] fixedComponent fixedTensor

private theorem fixed_triangle_left
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {X V W Y B Z : SixFunctorSpace D}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
    [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
    [QuasiCompact ((geometry D).map i)]
    [IsProper ((geometry D).map q)] [IsProper ((geometry D).map p)]
    [IsProper ((geometry D).map s)] (hb : b ≫ p = q ≫ i)
    (k : ProperOpenDerived (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
      X.obj.left)
    (l : ProperOpenDerived (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
      Z.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let c := ordinary D A
    let t := fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)
    (fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) (i ≫ s)
        (binarySecond i s) ((compact c j q).obj k) l ≫
      (compact c i s).map
        (fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) (j ≫ q)
          (binaryFirst j q) k ((c.P (i ≫ s)).obj l))) ≫
      (alpha c j b q p i s hb).app
        ((t.tensor X).obj (k, (c.P (j ≫ q)).obj ((c.P (i ≫ s)).obj l))) ≫
      (compact c (j ≫ b) (p ≫ s)).map ((t.tensor X).map
        (Prod.mkHom (𝟙 k) ((trianglePull c j b q p i s hb).hom.app l))) =
      leftMap c t j b q p i s hb k l := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let c := ordinary D A
  let t := fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)
  have hpf := fixed_factor_projection_refl (D := D) (C := C) (E := E) (n := n)
    (hn := hn) j q k ((c.P (i ≫ s)).obj l)
  have hpg : fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) (i ≫ s)
      (binarySecond i s) ((compact c j q).obj k) l =
      projection c t i s ((compact c j q).obj k) l := by
    exact fixed_factor_projection_refl (D := D) (C := C) (E := E) (n := n)
      (hn := hn) i s ((compact c j q).obj k) l
  exact replace_map_path (compact c i s)
    (fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) (i ≫ s)
      (binarySecond i s) ((compact c j q).obj k) l)
    (projection c t i s ((compact c j q).obj k) l)
    (fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) (j ≫ q)
      (binaryFirst j q) k ((c.P (i ≫ s)).obj l))
    (projection c t j q k ((c.P (i ≫ s)).obj l))
    ((alpha c j b q p i s hb).app
      ((t.tensor X).obj (k, (c.P (j ≫ q)).obj ((c.P (i ≫ s)).obj l))))
    ((compact c (j ≫ b) (p ≫ s)).map ((t.tensor X).map
      (Prod.mkHom (𝟙 k) ((trianglePull c j b q p i s hb).hom.app l))))
    (leftMap c t j b q p i s hb k l) hpg hpf
    (raw_square_maps c t j b q p i s hb k l).1.symm

private theorem positive_elim
    (P : ∀ (n : ℕ), 1 ≤ n → Prop)
    (h : ∀ (m : ℕ) (hm : 1 ≤ m + 1), P (m + 1) hm)
    {n : ℕ} (hn : 1 ≤ n) : P n hn := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact h m hn

private theorem triangle_laws_transport
    {G : Type*} [Category G] {geo : G ⥤ Scheme.{u}} (c : Calculus G geo)
    {t t' : TensorData c} (h : t = t') (ht : TriangleLaws c t') :
    TriangleLaws c t := by
  cases h
  exact @ht

private theorem coefficient_triangle_laws
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n} :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    TriangleLaws (ordinary D
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
      (fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)) := by
  exact positive_elim (n := n)
    (fun k hk =>
      letI := Padic.finite_coefficientExtensionRing C.l E k hk
      TriangleLaws (ordinary D
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E k)))
        (fixedScalarTensorData (D := D) (C := C) (E := E) (n := k) (hn := hk)))
    (fun m hm => by
      let := Padic.finite_coefficientExtensionRing C.l E (m + 1) hm
      exact triangle_laws_transport
        (ordinary D (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))))
        (fixedScalarTensorData_eq (D := D) (C := C) (E := E) (n := m + 1) (hn := hm))
        @(compositionProjectionMate D C.l C.different E m).1) hn

attribute [local irreducible] realization

private theorem square_on_triangle
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X V W Y B Z : SixFunctorSpace D}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
    [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
    [QuasiCompact ((geometry D).map i)]
    [IsProper ((geometry D).map q)] [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)]
    (hb : b ≫ p = q ≫ i)
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f = j ≫ q) (hg : g = i ≫ s)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    let cf := sixFunctorFactorCompactification j q
      ‹IsOpenImmersion ((geometry D).map j)› ‹IsProper ((geometry D).map q)› f hf
    let cg := sixFunctorFactorCompactification i s
      ‹IsOpenImmersion ((geometry D).map i)› ‹IsProper ((geometry D).map s)› g hg
    let cfg := sixFunctorFactorCompactification (j ≫ b) (p ≫ s)
      (mappedCompositeOpen (geo := geometry D) j b)
      (mappedCompositeProper (geo := geometry D) p s) (f ≫ g) (by
        rw [hf, hg]
        simp only [Category.assoc]
        rw [← Category.assoc q i s, ← hb]
        simp only [Category.assoc])
    binarySquareEquation S (X := X) (Y := Y) (Z := Z) f g cf cg cfg K L := by
  subst f
  subst g
  exact binary_square_on_triangle S j b q p i s hb sq K L

/-- A compatible choice of first and composite compactifications satisfies projection composition.
Source: current blueprint fix-prop-projection-formula.proof.md, composition sentence;
Cartesian compact-support compositor and compositionProjectionMate
(blueprint: lem-sf-finite-projection-binary-square).

Proof: choose a compatible Cartesian compactification triangle for f and g.
The raw proper/open triangle compositor is the canonical origin compositor by
cartesianCompactSupportCompositor. Apply the projection equation of
compositionProjectionMate, using bounded etale origins of K and of the tensor
input; finite Tor amplitude is needed only for L. The two support realizations,
finiteCompositionNormalization and finitePullCompositionNormalization identify
these arrows with the recorded support and pullback compositors. Cancel the
coefficient realization units. Use the first and total compactifications as the existential
witnesses cf and cfg; keep cg prescribed. No compactification transport is claimed.
This binary projection assertion makes no claim about
associativity of three support operations, nor invertibility of any projection. -/
theorem exists_component_binary_square
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn) :
    ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cg : Compactification g.hom.left),
    ∃ (cf : Compactification f.hom.left) (cfg : Compactification (f ≫ g).hom.left),
    ∀ (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left),
      ((partialTensor S Z).map ((S.finite.composition f g cf cg cfg).hom.app K)).app L ≫
          component S g cg ((S.finite.support f cf).obj K) L ≫
          (S.finite.support g cg).map
            (component S f cf K ((torPull S g).obj L)) =
        component S (f ≫ g) cfg K L ≫
          (S.finite.composition f g cf cg cfg).hom.app
            (((partialTensor S X).obj K).obj ((torPull S (f ≫ g)).obj L)) ≫
          (S.finite.support g cg).map ((S.finite.support f cf).map
            (((partialTensor S X).obj K).map (torPullComposition S f g L).hom)) := by
  intro X Y Z f g _ _ _ _ _ _ cg
  let Q := compactSupportProjectionSquare g cg
  let B : SixFunctorSpace D := Q.Z
  let i : Y ⟶ B := Q.i
  let s : B ⟶ Z := Q.p
  have hi : IsOpenImmersion i.hom.left := Q.open_i
  have hs : IsProper s.hom.left := Q.proper_p
  let : IsOpenImmersion i.hom.left := hi
  let : IsProper s.hom.left := hs
  obtain ⟨V, W, j, b, q, p, hj, hb, hq, hp, hf, hbp, sq, hqb, hqi⟩ :=
    @compatible_triangle D X Y B Z f i s inferInstance inferInstance inferInstance hi hs
  let := hj
  let := hb
  let := hq
  let := hp
  let := hqb
  let := hqi
  let : IsOpenImmersion ((geometry D).map j) := hj
  let : IsOpenImmersion ((geometry D).map b) := hb
  let : IsOpenImmersion ((geometry D).map i) := hi
  let : QuasiCompact ((geometry D).map b) := hqb
  let : QuasiCompact ((geometry D).map i) := hqi
  let : IsProper ((geometry D).map q) := hq
  let : IsProper ((geometry D).map p) := hp
  let : IsProper ((geometry D).map s) := hs
  have hg : g = i ≫ s := Q.factorization
  let cf := sixFunctorFactorCompactification j q hj hq f hf
  have hfg : f ≫ g = (j ≫ b) ≫ (p ≫ s) := by
    rw [hf, hg]
    simp -implicitDefEqProofs only [Category.assoc]
    rw [← Category.assoc q i s, ← hbp]
    simp -implicitDefEqProofs only [Category.assoc]
  let cfg := sixFunctorFactorCompactification (j ≫ b) (p ≫ s)
    (mappedCompositeOpen (geo := geometry D) j b)
    (mappedCompositeProper (geo := geometry D) p s) (f ≫ g) hfg
  refine ⟨cf, cfg, ?_⟩
  have hcg : cg = sixFunctorFactorCompactification i s hi hs g hg := by rfl
  rw [hcg]
  clear hcg
  intro K L
  exact square_on_triangle S j b q p i s hbp sq f g hf hg K L

end WeilConjectures.CompactSupportFiniteProjection
