/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionProjection
public import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerNormalizationInduction
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor

/-! # Coordinate products and recursive exceptional adjuncts

Source: blueprint main-20261015, cor-pur-affine-space-zero-section-purity,
proof Steps 5 and 7 (blueprint: def-pur-coordinate-section-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

private theorem unique_precomp {C : Type v} [Category.{w} C]
    {X Y Z : C} (p : X ⟶ Y) [IsIso p] (t : X ⟶ Z) :
    ∃! e : Y ⟶ Z, HEq (p ≫ e) t := by
  refine ⟨inv p ≫ t, heq_of_eq (IsIso.hom_inv_id_assoc p t), ?_⟩
  intro e he
  apply (cancel_epi p).mp
  exact (eq_of_heq he).trans (IsIso.hom_inv_id_assoc p t).symm

attribute [local irreducible] targetPullbackIso projectionMap

private theorem target_ctf (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (setting P n).Coefficient) X
      (target P n X c) := by
  let S := Spec (.of P.field.k)
  let f := aX ≫ zero S c
  have h := (CoordinateTowerNormalization.target_properties P n S (𝟙 S) c).1
  have hf := constructibleFiniteTor_leftDerivedFunctor_upperStar_obj f h
  exact (DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} (setting P n).Coefficient) X).prop_of_iso
      (targetPullbackIso P n f (towerBase (𝟙 S) c) c) hf

/-- The precise projection component used in the recursion is invertible.
Source: proof Step 1 (blueprint: def-pur-coordinate-section-arrows).
Proof: each finite Tate line is locally free of rank one. Its finite tensor power
is bounded constructible and of finite Tor amplitude. Apply the recorded finite
compact projection theorem to the closed last section and the coefficient unit,
and then compose with the canonical section/unit isomorphism. -/
theorem sectionProjection_isIso (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    IsIso (sectionProjection P n B r) := by
  unfold sectionProjection
  exact sectionProjectionRaw_isIso_of_constructibleFiniteTor _ _ _ _ _ _ _
    (target_ctf P n (iteratedAffineLine B r) (towerBase aB r) 0)
    (target_ctf P n (iteratedAffineLine B r) (towerBase aB r) r)

/-- The existing supported product, in its canonical proper-compact-support source.
Transpose its recorded adjunct back through the same closed Hom bijection. This
recovers the proper closed comparison followed by supportedClass, without an
expensive kernel conversion between the two degree-zero embedding presentations.
Source: C_c in the displayed recursion
(blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def compactProduct (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (zero B c)).obj (unit P n B) ⟶ target P n (iteratedAffineLine B c) c :=
  letI := tower_noetherian (setting P n) B aB c
  (rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
    (target_plus P n _ (towerBase aB c) c)).symm (thom P n B aB c)

/-- The one-factor target normalization is the canonical coefficient unitor.
Source: shifted twist normalization
(blueprint: def-pur-coordinate-section-arrows).
Proof: unfold target and action at one. The source is the derived tensor of the
coefficient unit and the line. Transport the actual coefficient-unit comparison
and left unitor through these defining equalities. HEq fixes that exact map,
so existence and uniqueness follow, with no choice of orientation. -/
theorem oneTargetIso_existsUnique (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    ∃! e : target P n X 1 ≅ shiftedLine (setting P n) X,
      HEq e (tensorIso (setting P n).Coefficient X (coefficientUnitIso P n X)
        (Iso.refl (shiftedLine (setting P n) X)) ≪≫
          tensorUnitLeftIso (setting P n).Coefficient X (shiftedLine (setting P n) X)) := by
  refine ⟨tensorIso (setting P n).Coefficient X (coefficientUnitIso P n X)
    (Iso.refl (shiftedLine (setting P n) X)) ≪≫
      tensorUnitLeftIso (setting P n).Coefficient X (shiftedLine (setting P n) X),
    HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- The uniquely prescribed one-factor unitor, not an arbitrary endpoint iso.
Source: shifted twist normalization
(blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def oneTargetIso (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    target P n X 1 ≅ shiftedLine (setting P n) X :=
  (oneTargetIso_existsUnique P n X).exists.choose

/-- Tensor symmetry in the cached bifunctor coordinates, using the same monoidal
structure. Source: even factor interchange
(blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def tensorSwap (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    ((tensor A X).obj M).obj N ≅ ((tensor A X).obj N).obj M :=
  letI := DerivedCategory.braidedCategory'
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
  eqToIso (tensorObject_eq A X M N) ≪≫ β_ M N ≪≫
    (eqToIso (tensorObject_eq A X N M)).symm

/-- Tensor two isomorphisms and then reverse the factors by the specified
Koszul braiding. Source: ordered twist multiplication
(blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def reverseTensorIso (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M M' N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (e : M ≅ M') (f : N ≅ N') :
    ((tensor A X).obj M).obj N ≅ ((tensor A X).obj N').obj M' :=
  tensorIso A X e f ≪≫ tensorSwap A X M' N'

/-- Canonical shifted multiplication is uniquely fixed by the line unitor,
Tate pullback and the Koszul braiding. Source: twist normalization
(blueprint: def-pur-coordinate-section-arrows).
Proof: transport the displayed raw tensor isomorphism along tensorCup_eq and
target_succ. These equations identify its target with W_(r+1). HEq fixes the
actual map, so the transport exists uniquely. The shift sign is even. -/
theorem sectionTargetIso_existsUnique (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) :
    ∃! e : ((tensor (setting P n).Coefficient (iteratedAffineLine B (r + 1))).obj
      (target P n (iteratedAffineLine B (r + 1)) 1)).obj
        ((inverseImage (setting P n).Coefficient (lastProjection B r)).obj
          (target P n (iteratedAffineLine B r) r)) ≅
      target P n (iteratedAffineLine B (r + 1)) (r + 1) ,
      HEq e (reverseTensorIso (setting P n).Coefficient (iteratedAffineLine B (r + 1))
        (oneTargetIso P n (iteratedAffineLine B (r + 1)))
        (targetPullbackIso P n (lastProjection B r) (towerBase aB r) r)) := by
  refine ⟨reverseTensorIso (setting P n).Coefficient (iteratedAffineLine B (r + 1))
    (oneTargetIso P n (iteratedAffineLine B (r + 1)))
    (targetPullbackIso P n (lastProjection B r) (towerBase aB r) r), HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- The uniquely normalized shifted twist multiplication.
Source: twist normalization (blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def sectionTargetIso (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) :
    ((tensor (setting P n).Coefficient (iteratedAffineLine B (r + 1))).obj
      (target P n (iteratedAffineLine B (r + 1)) 1)).obj
        ((inverseImage (setting P n).Coefficient (lastProjection B r)).obj
          (target P n (iteratedAffineLine B r) r)) ≅
      target P n (iteratedAffineLine B (r + 1)) (r + 1) :=
  (sectionTargetIso_existsUnique P n B aB r).exists.choose

/-- Tensor an orientation with the identity and apply its target normalization.
Source: displayed a_r (blueprint: def-pur-coordinate-section-arrows). -/
def tensorArrow {C : Type v} [Category.{w} C] (T : C ⥤ C ⥤ C)
    {R R' U : C} (f : R ⟶ R') (V : C) (e : (T.obj R').obj V ≅ U) :
    (T.obj R).obj V ⟶ U :=
  (T.map f).app V ≫ e.hom

/-- The existing rank-one product in the literal last-section coordinates.
Source: the section orientation (blueprint: def-pur-coordinate-section-arrows).
Proof: X_(r+1) is definitionally the affine line over X_r and lastSection is its
zero section. Transport the existing rank-one map through these equalities.
HEq fixes the actual map, so this transport is unique. -/
theorem lastProduct_existsUnique (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    ∃! f : (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (lastSection B r)).obj (unit P n (iteratedAffineLine B r)) ⟶
        target P n (iteratedAffineLine B (r + 1)) 1,
      HEq f (@compactProduct.{u} P n (iteratedAffineLine B r) (towerBase aB r)
            (tower_geometry aB r).1 (tower_geometry aB r).2.1
            (tower_geometry aB r).2.2 1) := by
  refine ⟨@compactProduct.{u} P n (iteratedAffineLine B r) (towerBase aB r)
    (tower_geometry aB r).1 (tower_geometry aB r).2.1
    (tower_geometry aB r).2.2 1, HEq.rfl, ?_⟩
  intro f hf
  exact eq_of_heq hf

/-- The uniquely specified rank-one product in last-section coordinates.
Source: the section orientation (blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def lastProduct (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (lastSection B r)).obj (unit P n (iteratedAffineLine B r)) ⟶
        target P n (iteratedAffineLine B (r + 1)) 1 :=
  (lastProduct_existsUnique P n B aB r).exists.choose

/-- The section arrow is uniquely fixed by the displayed inverse projection,
Cartier map and normalized twist multiplication. Source: displayed a_r
(blueprint: def-pur-coordinate-section-arrows).
Proof: the iterated affine line at r+1 is the affine line over X_r, and lastSection
is its zero section. The projection is invertible, so the displayed commuting
square determines the arrow uniquely. Its solution is the inverse projection
followed by the tensor orientation and normalized target identification. -/
theorem sectionArrow_existsUnique (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    ∃! e : (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (lastSection B r)).obj (target P n (iteratedAffineLine B r) r) ⟶
    target P n (iteratedAffineLine B (r + 1)) (r + 1),
      HEq (sectionProjection P n B r ≫ e)
        (tensorArrow (tensor (setting P n).Coefficient (iteratedAffineLine B (r + 1)))
          (lastProduct P n B aB r)
          ((inverseImage (setting P n).Coefficient (lastProjection B r)).obj
            (target P n (iteratedAffineLine B r) r)) (sectionTargetIso P n B aB r)) := by
  let := sectionProjection_isIso P n B aB r
  exact unique_precomp (sectionProjection P n B r) _

/-- The actual last-coordinate supported arrow a_r: inverse proper projection,
Cartier orientation tensor identity, then normalized shifted twist multiplication.
Source: displayed definition of u_r
(blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def sectionArrow (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (lastSection B r)).obj (target P n (iteratedAffineLine B r) r) ⟶
    target P n (iteratedAffineLine B (r + 1)) (r + 1) :=
  (sectionArrow_existsUnique P n B aB r).exists.choose

/-- Every ordered finite Tate tensor power is bounded below of etale origin.
Source: proof Steps 1 and 9 (blueprint: def-pur-coordinate-section-arrows).
Proof: the constant coefficient and the finite Tate line are etale sheaves in
single degrees. Exact monoidal comparison carries their finite derived tensor
powers to the displayed objects. Their shifts give a finite lower bound. -/
theorem target_origin (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (setting P n).Coefficient) X
      (target P n X c) := by
  exact (target_ctf P n X aX c).plusEtaleOrigin

/-- The actual exceptional adjunct u_r of the specified section arrow.
Source: definition of u_r (blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def sectionAdjunct (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    target P n (iteratedAffineLine B r) r ⟶
      (rightDerivedUpperShriek (setting P n).Coefficient
        (lastSection B r)).obj (target P n (iteratedAffineLine B (r + 1)) (r + 1)) :=
  letI := tower_noetherian (setting P n) B aB (r + 1)
  rightDerivedUpperShriekHomEquiv (lastSection B r)
    (target_origin P n _ (towerBase aB r) r)
    (target_plus P n _ (towerBase aB (r + 1)) (r + 1)) (sectionArrow P n B aB r)

attribute [local irreducible] originCompositionAmbient rightDerivedUpperShriekHomEquiv
  rightDerivedUpperShriekCounit

attribute [local irreducible] compositionInverse

/-- The canonical identity normalization on compact support at c=0.
Source: proof Step 5 (blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def coordinateIdentity (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (zero B 0)).obj (unit P n B) ⟶ unit P n B :=
  ((originCompactSupportId (setting P n).Coefficient B).hom.app
    ⟨_, unit_origin P n B⟩).hom

end AlgebraicGeometry.ProEtale.AffineZeroPurity
