/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionCompositionRealization

/-! # Pasting the binary iteration target -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection

namespace WeilConjectures.CompactSupportFiniteProjection

section PastingNormalization

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

section CoefficientCoordinates
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [AlgebraicGeometry.ProEtale.UpperStarPreservesFlat A]

-- These wrappers expose the tensor endpoints before specializing the coefficient category.
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
        ((t.tensor X).obj (k, (c.P (i ≫ s) ⋙ c.P (j ≫ q)).obj l)) ≫
      (compact c (j ≫ b) (p ≫ s)).map ((t.tensor X).map
        (Prod.mkHom (𝟙 k) ((trianglePull c j b q p i s hb).app l).hom)) =
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
      ((t.tensor X).obj (k, (c.P (i ≫ s) ⋙ c.P (j ≫ q)).obj l)))
    ((compact c (j ≫ b) (p ≫ s)).map ((t.tensor X).map
      (Prod.mkHom (𝟙 k) ((trianglePull c j b q p i s hb).app l).hom)))
    (leftMap c t j b q p i s hb k l) hpg hpf
    (raw_square_maps c t j b q p i s hb k l).1.symm

section RawTrianglePasting

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  [Finite (Padic.coefficientExtensionRing C.l E n)]

local notation "c₀" => ordinary D (ULift (Padic.coefficientExtensionRing C.l E n))
local notation "t₀" =>
  fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)

/-- Normalize the raw triangle with abstract inputs before inserting the coefficient
realization objects. This keeps their derived equivalence data out of the calculation. -/
private theorem fixed_triangle_pasting
    {X V W Y B Z : SixFunctorSpace D}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
    [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
    [QuasiCompact ((geometry D).map i)]
    [IsProper ((geometry D).map q)] [IsProper ((geometry D).map p)]
    [IsProper ((geometry D).map s)] (hb : b ≫ p = q ≫ i)
    (k : (c₀).D X) (l : (c₀).D Z) (ha : IsIso (alpha c₀ j b q p i s hb))
    {N : Type v} [cN : Category N]
    (R : @Functor ((c₀).D Z) ((c₀).category Z) N cN) {a b₀ : N} (p₀ : a ⟶ b₀)
    (sb : a ⟶ R.obj (((t₀).tensor Z).obj (((compact c₀ j q ⋙ compact c₀ i s).obj k), l)))
    (tb : b₀ ≅ R.obj ((compact c₀ j q ⋙ compact c₀ i s).obj
      (((t₀).tensor X).obj (k, ((c₀).P (j ≫ q)).obj (((c₀).P (i ≫ s)).obj l)))))
    (h : p₀ ≫ tb.hom = sb ≫ R.map
      (fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) (i ≫ s)
        (binarySecond i s) ((compact c₀ j q).obj k) l ≫ (compact c₀ i s).map
          (fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) (j ≫ q)
            (binaryFirst j q) k (((c₀).P (i ≫ s)).obj l)))) :
    p₀ ≫ (realizedTriangleTargetIso R (compact c₀ j q ⋙ compact c₀ i s)
      (compact c₀ (j ≫ b) (p ≫ s)) (alpha c₀ j b q p i s hb) ha ((t₀).tensor X) k
      ((trianglePull c₀ j b q p i s hb).app l) tb).hom =
      sb ≫ R.map (leftMap c₀ t₀ j b q p i s hb k l) := by
  rw [realizedTriangleTargetIso_hom]
  rw [← Category.assoc p₀ tb.hom _, h]
  rw [← fixed_triangle_left (D := D) (C := C) (E := E) (n := n) (hn := hn)
    j b q p i s hb k l]
  erw [← R.map_comp, Category.assoc sb, ← R.map_comp]
  exact Eq.refl _

end RawTrianglePasting

end PastingNormalization

attribute [local irreducible] fixedComponent
attribute [local irreducible] sixFunctorFiniteRealization sfIntrinsicDerivedEquivalence
  Equivalence.mapDerivedCategory AlgebraicGeometry.ProEtale.derivedTensor
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local irreducible] iterationTargetComparison iterationSourceComparison
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor

/-- Pasting iteration realization with the raw triangle arrow.
Source: coefficient transport and the Cartesian triangle calculation in
fix-prop-projection-formula.proof.md
(blueprint: lem-sf-finite-projection-binary-iteration-triangle-pasting).

Proof: apply the factor iteration realization, then use the explicit alpha and
trianglePull endpoint maps and the raw fixed triangle calculation. This statement
contains no projection component and is strictly below the fixed-triangle binary
square. -/
theorem binary_iteration_triangle_pasting
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
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left)
    (ha : letI := Padic.finite_coefficientExtensionRing C.l E n hn
      IsIso (alpha (ordinary D
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) j b q p i s hb)) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let c := ordinary D A
    let t := fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)
    let RX := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) Z
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
    let f := j ≫ q
    let g := i ≫ s
    let cf := binaryFirst j q
    let cg := binarySecond i s
    let k := RX.inverse.obj K.obj
    let l := RZ.inverse.obj L.obj
    let sb := iterationSourceComparison S (X := X) (Y := Y) (Z := Z) f g cf cg K L
    let td := binaryIterationTargetComparison S
      (X := X) (V := V) (W := W) (Y := Y) (B := B) (Z := Z) j b q p i s hb K L ha
    I.map (component S (X := Y) (Y := Z) g cg
        ((S.finite.support (X := X) (Y := Y) f cf).obj K) L ≫
      (S.finite.support (X := Y) (Y := Z) g cg).map
        (component S (X := X) (Y := Y) f cf K ((torPull S (X := Y) (Y := Z) g).obj L))) ≫
      td.hom = sb.hom ≫ RZ.functor.map
        (leftMap c t j b q p i s hb k l) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) X
  let RZ := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) Z
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
  exact fixed_triangle_pasting (D := D) (C := C) (E := E) (n := n) (hn := hn)
    j b q p i s hb (RX.inverse.obj K.obj) (RZ.inverse.obj L.obj) ha RZ.functor
    (I.map (component S (i ≫ s) (binarySecond i s)
      ((S.finite.support (j ≫ q) (binaryFirst j q)).obj K) L ≫
      (S.finite.support (i ≫ s) (binarySecond i s)).map
        (component S (j ≫ q) (binaryFirst j q) K ((torPull S (i ≫ s)).obj L))))
    (iterationSourceComparison S (j ≫ q) (i ≫ s) (binaryFirst j q) (binarySecond i s) K L).hom
    (iterationTargetComparison S (j ≫ q) (i ≫ s) (binaryFirst j q) (binarySecond i s) K L)
    (iteration_realization_factors (D := D) (C := C) (E := E) (n := n) (hn := hn)
      S j q i s K L)

end WeilConjectures.CompactSupportFiniteProjection
