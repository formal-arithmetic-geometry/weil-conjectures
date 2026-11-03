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

private theorem iso_naturality_paste {C D E : Type v} [Category.{w} C]
    [Category.{w} D] [Category.{w} E] (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (P : ObjectProperty C) (e : P.ι ⋙ F ⋙ G ≅ P.ι ⋙ H)
    {T M : C} (hT : P T) (hM : P M) (u : T ⟶ M)
    {V : D} {K : E} (a : F.obj M ⟶ V) (b : G.obj V ⟶ K) :
    e.inv.app ⟨T, hT⟩ ≫ G.map (F.map u ≫ a) ≫ b =
      H.map u ≫ (e.inv.app ⟨M, hM⟩ ≫ G.map a ≫ b) := by
  have hn := e.inv.naturality (ObjectProperty.homMk u : ⟨T, hT⟩ ⟶ ⟨M, hM⟩)
  change H.map u ≫ e.inv.app ⟨M, hM⟩ =
    e.inv.app ⟨T, hT⟩ ≫ G.map (F.map u) at hn
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc, ← hn,
    Category.assoc, Category.assoc]

private theorem isIso_of_bijective_comp {C : Type v} [Category.{w} C]
    (P : ObjectProperty C) {M N : C} (hM : P M) (hN : P N) (d : M ⟶ N)
    (h : ∀ T, P T → Function.Bijective (fun u : T ⟶ M ↦ u ≫ d)) : IsIso d := by
  obtain ⟨q, hq⟩ := (h N hN).2 (𝟙 N)
  refine ⟨q, ?_, hq⟩
  apply (h M hM).1
  change (d ≫ q) ≫ d = 𝟙 M ≫ d
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t ↦ d ≫ t) hq).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))

private theorem isIso_transpose_compositor {C D E : Type v} [Category.{w} C]
    [Category.{w} D] [Category.{w} E] (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (P : ObjectProperty C) {M N : C} {V : D} {K : E} (hM : P M) (hN : P N)
    (ef : ∀ T, P T → (F.obj T ⟶ V) ≃ (T ⟶ M))
    (eg : ∀ T, P T → (G.obj (F.obj T) ⟶ K) ≃ (F.obj T ⟶ V))
    (eh : ∀ T, P T → (H.obj T ⟶ K) ≃ (T ⟶ N))
    (a : F.obj M ⟶ V) (b : G.obj V ⟶ K)
    (hf : ∀ T (hT : P T) (u : T ⟶ M), (ef T hT).symm u = F.map u ≫ a)
    (hg : ∀ T (hT : P T) (t : F.obj T ⟶ V), (eg T hT).symm t = G.map t ≫ b)
    (hh : ∀ T (hT : P T) (u : T ⟶ M) (t : H.obj M ⟶ K),
      eh T hT (H.map u ≫ t) = u ≫ eh M hM t)
    (e : P.ι ⋙ F ⋙ G ≅ P.ι ⋙ H) :
    IsIso (transposeComposition F G H P hM (eh M hM) a b e) := by
  unfold transposeComposition
  apply isIso_of_bijective_comp P hM hN
  intro T hT
  let E := ((ef T hT).symm.trans (eg T hT).symm).trans
    (((e.app ⟨T, hT⟩).homFromEquiv).trans (eh T hT))
  have he (u : T ⟶ M) : E u =
      u ≫ eh M hM (e.inv.app ⟨M, hM⟩ ≫ G.map a ≫ b) := by
    simp only [E, Equiv.trans_apply, Iso.homFromEquiv_apply, Iso.app_inv, hg, hf]
    rw [iso_naturality_paste F G H P e hT hM u, hh]
  have heq : (fun u : T ⟶ M ↦
      u ≫ eh M hM (e.inv.app ⟨M, hM⟩ ≫ G.map a ≫ b)) = E :=
    funext (fun u ↦ (he u).symm)
  rw [heq]
  exact E.bijective

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

/-- The compact-support source identification from the specified composition law.
Source: explicit supported recursion
(blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def coordinateComposition (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (r : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (zero B (r + 1))).obj (unit P n B) ≅
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (lastSection B r)).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (zero B r)).obj (unit P n B)) :=
  (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} (setting P n).Coefficient)
    (f := zero B (r + 1)) (g := zero B r ≫ lastSection B r)
    (CoordinateTowerNormalization.zero_successor B r :
      zero B r ≫ lastSection B r = zero B (r + 1)).symm).app _ ≪≫
    (originCompositionAmbient (setting P n).Coefficient (zero B r)
      (lastSection B r)).symm.app ⟨unit P n B, unit_origin P n B⟩

/-- The inverse exceptional compositor d_r, obtained by conjugating that same
compact-support composition through the pasted counits.
Source: proof Step 6 (blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def coordinateExceptionalComposition (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (rightDerivedUpperShriek (setting P n).Coefficient
      (zero B r)).obj
        ((rightDerivedUpperShriek (setting P n).Coefficient
          (lastSection B r)).obj (target P n (iteratedAffineLine B (r + 1)) (r + 1))) ⟶
    (rightDerivedUpperShriek (setting P n).Coefficient
      (zero B (r + 1))).obj (target P n (iteratedAffineLine B (r + 1)) (r + 1)) :=
  letI := tower_noetherian (setting P n) B aB r
  letI := tower_noetherian (setting P n) B aB (r + 1)
  compositionInverse (setting P n).Coefficient (zero B r) (lastSection B r)
      ⟨_, target_plus P n _ (towerBase aB (r + 1)) (r + 1)⟩ ≫
    (rightDerivedUpperShriekCongr (setting P n).Coefficient
      (f := zero B r ≫ lastSection B r) (g := zero B (r + 1))
      (CoordinateTowerNormalization.zero_successor B r :
        zero B r ≫ lastSection B r = zero B (r + 1))).hom.app _

private theorem compositionInverse_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z]
    (K : Plus A Z) : IsIso (compositionInverse A f g K) := by
  unfold compositionInverse
  exact isIso_transpose_compositor
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
    (plusEtaleOrigin_rightDerivedUpperShriek_obj f
      (plus_rightDerivedUpperShriek_obj g K.property))
    (plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) K.property)
    (fun _ hT ↦ rightDerivedUpperShriekHomEquiv f hT
      (plus_rightDerivedUpperShriek_obj g K.property))
    (fun _ hT ↦ rightDerivedUpperShriekHomEquiv g
      (hT.rightDerivedLowerShriek_obj f) K.property)
    (fun _ hT ↦ rightDerivedUpperShriekHomEquiv (f ≫ g) hT K.property)
    (rightDerivedUpperShriekCounit f _ (plus_rightDerivedUpperShriek_obj g K.property))
    (rightDerivedUpperShriekCounit g K.obj K.property)
    (fun _ hT u ↦ rightDerivedUpperShriekHomEquiv_symm_apply f hT _ u)
    (fun _ hT t ↦ rightDerivedUpperShriekHomEquiv_symm_apply g
      (hT.rightDerivedLowerShriek_obj f) K.property t)
    (fun _ hT u t ↦ rightDerivedUpperShriekHomEquiv_naturality_left
      (f ≫ g) hT _ K.property u t)
    (originCompositionAmbient A f g)

/-- The conjugate compositor is an isomorphism, since compact-support composition
is an isomorphism and both closed Hom bijections are adjunction bijections.
Source: proof Step 6 (blueprint: def-pur-coordinate-section-arrows).
Proof: the compact-support compositor and its inverse are conjugate through the
two adjunctions. Their composites are identities by naturality and the triangle
identities. The defining pasted-counit map is precisely this inverse conjugate. -/
theorem coordinateExceptionalComposition_isIso (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    IsIso (coordinateExceptionalComposition P n B aB r) := by
  let := tower_noetherian (setting P n) B aB r
  let := tower_noetherian (setting P n) B aB (r + 1)
  have := compositionInverse_isIso (setting P n).Coefficient (zero B r) (lastSection B r)
    ⟨_, target_plus P n _ (towerBase aB (r + 1)) (r + 1)⟩
  unfold coordinateExceptionalComposition
  infer_instance

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

/-- The identity exceptional comparison at rank zero, transposed from the specified
compact-support identity. Source: empty-product normalization
(blueprint: def-pur-coordinate-section-arrows). -/
@[irreducible]
def coordinateIdentityAdjunct (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    unit P n B ⟶ (rightDerivedUpperShriek (setting P n).Coefficient
      (zero B 0)).obj (target P n B 0) :=
  letI := tower_noetherian (setting P n) B aB 0
  rightDerivedUpperShriekHomEquiv (zero B 0) (unit_origin P n B)
    (target_plus P n B aB 0) (coordinateIdentity P n B)

end AlgebraicGeometry.ProEtale.AffineZeroPurity
