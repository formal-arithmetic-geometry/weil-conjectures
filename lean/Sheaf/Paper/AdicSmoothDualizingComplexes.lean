/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.Paper.SmoothTrace
public import Sheaf.Paper.AdicSmoothDualizingFiniteComparison
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.SfIntegralConstructibleTriangulated

/-! # Adic and rational smooth dualizing complexes

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-cor-sp-all-coefficients/cor-pur-adic-and-rational-smooth-dualizing-complexes.md
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
universe u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w₁ w₂
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures
namespace AdicSmoothDualizing

open AlgebraicGeometry.Scheme

attribute [local irreducible] PurCompactSupport.image
  sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar

private theorem transport_counit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
    (F : C ⥤ D) (G : D ⥤ C) (F' : C' ⥤ D') (G' : D' ⥤ C')
    (TX : C ⥤ C') (TY : D ⥤ D')
    (q : F ⋙ TY ≅ TX ⋙ F') (b : G ⋙ TX ≅ TY ⋙ G')
    (L : D) (eps : F.obj (G.obj L) ⟶ L)
    (eps' : F'.obj (G'.obj (TY.obj L)) ⟶ TY.obj L)
    (hc : q.hom.app (G.obj L) ≫ F'.map (b.hom.app L) ≫ eps' = TY.map eps)
    {M : C} (e : G.obj L ≅ M) :
    eps' = F'.map ((b.symm.app L ≪≫ TX.mapIso e).hom) ≫
      q.inv.app M ≫ TY.map (F.map e.inv ≫ eps) := by
  apply (cancel_epi (q.hom.app (G.obj L) ≫ F'.map (b.hom.app L))).mp
  rw [Category.assoc, hc]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← F'.map_comp_assoc]
  simp only [b.hom_inv_id_app]
  dsimp only [Functor.comp_obj] at *
  rw [F'.map_id, Category.id_comp]
  have hnat : F'.map (TX.map e.hom) ≫ q.inv.app M =
      q.inv.app (G.obj L) ≫ TY.map (F.map e.hom) := by
    simpa only [Functor.comp_map] using q.inv.naturality e.hom
  rw [reassoc_of% hnat]
  simp only [← TY.map_comp, Iso.hom_inv_id_app_assoc]
  rw [← F.map_comp_assoc, e.hom_inv_id, F.map_id, Category.id_comp]

/-- The source's completed coefficient unit with Tate twist and even shift.
Only its finite-Tor membership is asserted here; its data is the existing root
line tensor power in a genuine single complex.
Source: corollary proof, the completed unit and its twist
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: the root line is locally free of rank one and derived complete. The signed
twist definition at nonnegative d is exactly line P T d. Its finite reductions
are flat lines in degree zero. The shift gives common Tor interval [-2d,-2d].
Thus this is in the recorded complete finite-Tor constructible subcategory. -/
theorem integralTwist_mem (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension T
      (((DerivedCategory.singleFunctor _ 0).obj (line P T d))⟦2 * (d : ℤ)⟧) := by
  let : ∀ x : T, Invertible (P.coefficients.l : T.residueField x) := fun x ↦
    (show IsUnit (P.coefficients.l : T.residueField x) by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk T aT x).map (T.residue x).hom).invertible
  rw [← (integral_residue_tor P.field P.coefficients.l P.coefficients.different
    P.extension T).2]
  apply (sfIntegralConstructible P.coefficients.l P.extension T).le_shift
    (2 * (d : ℤ)) _
  exact intrinsicIntegralCoefficientTwist_mem P.field P.coefficients.l
    P.coefficients.different P.extension T (d : ℤ)

/-- The full-subcategory restriction of the existing completed Tate coefficient object.
Source: corollary proof, Lambda_X(d)[2d]
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def integralTwist (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension T :=
  ⟨((DerivedCategory.singleFunctor _ 0).obj (line P T d))⟦2 * (d : ℤ)⟧,
    integralTwist_mem P T aT d⟩

/-- The actual quotient projection, transposed under the tensor-unit-normalized
coefficient adjunction and then shifted. Its target is identified with the finite
purity twist through the root-normalized finite comparison above.
Source: corollary proof, reduction-normalized integral reconstruction
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def twistReduction (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n) T)).obj (integralTwist P T aT d).obj ⟶
      (sfIntrinsicDerivedEquivalence T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
        ((levelSetting P n).diagonalTwist T d) :=
  let φ := PurCompactSupport.projection P.coefficients.l P.extension
    (n + 1) (Nat.succ_pos n) T
  letI := PurCompactSupport.scalarCommShift φ
  ((pbcDerivedExtend φ).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
    (shiftFunctor _ (2 * (d : ℤ))).map
      (((pbcDerivedScalarAdjunction φ).homEquiv _ _).symm
        ((DerivedCategory.singleFunctor _ 0).map (lineProjection P T n d) ≫
          ((pbcRestrict φ).mapDerivedCategorySingleFunctor 0).inv.app _)) ≫
    (finitePowerComparison P T aT n d).inv

/-- The finite coefficient unit is bounded below after exact site comparison.
Source: corollary proof, finite counit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: exact comparison carries the degree-zero constant sheaf to its degree-zero
inverse image. All negative cohomology sheaves vanish, so zero is a lower bound. -/
theorem finiteUnitPlus (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.TStructure.t.plus
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit P.Coefficient T)) := by
  refine ⟨0, ?_⟩
  change DerivedCategory.IsGE
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit P.Coefficient T)) 0
  exact Functor.isGE_mapDerivedCategory_obj _ _ 0

variable (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]

/-- The recorded Nagata compactification of the structure morphism.
Source: corollary proof, compact-support functor
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def compactification : Compactification (X ↘ Spec (.of P.field.k)) :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X
    (Spec (.of P.field.k)) (X ↘ Spec (.of P.field.k))
  HasCompactification.compactification (X ↘ Spec (.of P.field.k))

/-- The normalized finite integration map. Its orientation is the published
coordinate-counit-normalized diagonal purity isomorphism. Every other factor is a
specified proper/open or coefficient-realization comparison and the actual counit.
Source: corollary proof, normalized finite trace at the coefficient unit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def finiteIntegration (n d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) (compactification P X)).obj
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
          ((levelSetting P n).diagonalTwist X d)) ⟶
      (levelSetting P n).coefficientUnit (Spec (.of P.field.k)) :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X
    (Spec (.of P.field.k)) (X ↘ Spec (.of P.field.k))
  (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n
      (compactification P X)).hom.app _ ≫
    (ProEtale.sfIntrinsicCompactSupportComparison (levelSetting P n).Ring
      (compactification P X)).hom.app _ ≫
    (sfIntrinsicDerivedEquivalence (Spec (.of P.field.k)) (levelSetting P n).Ring).functor.map
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} (levelSetting P n).Coefficient)
        (X ↘ Spec (.of P.field.k))).map
        ((levelSetting P n).diagonalDualizingObject d (X ↘ Spec (.of P.field.k))
          (𝟙 (Spec (.of P.field.k)))).inv ≫
        ProEtale.rightDerivedUpperShriekCounit (X ↘ Spec (.of P.field.k)) _
          (finiteUnitPlus (levelSetting P n) (Spec (.of P.field.k))))

/-- An integral integration map is normalized precisely when its reductions are the
specified finite integration maps, through actual scalar-extension and root comparisons.
Source: corollary proof, adic reconstruction of the normalized counit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def IsNormalizedIntegralIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))]
    (t : (PurCompactSupport.image
        (PurCompactSupport.completed P.coefficients.l P.extension) (compactification P X)).obj
          (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).obj) : Prop :=
  ∀ n : ℕ,
    (PurCompactSupport.comparison (PurCompactSupport.reduction P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) (compactification P X)).app
          (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj ≫
      (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) (compactification P X)).map
          (twistReduction P X (X ↘ Spec (.of P.field.k)) n d) ≫
      finiteIntegration P X n d =
    (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n) (Spec (.of P.field.k)))).map t ≫
        twistReduction P (Spec (.of P.field.k)) (𝟙 _) n 0

/-- The selected finite extension in the coefficient-system coordinates.
Source: corollary coefficient conventions
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev fieldStage : ConstructibleExceptionalCoefficients.FieldStage.{u} P.coefficients.l where
  carrier := P.extension

/-- The structure morphism is a morphism over its base field.
Source: the structure-morphism convention of the corollary
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: the structure morphism of Spec k over itself is Spec.map of the identity,
which is the identity by Spec.map_id, so the required triangle commutes by the
right identity law. -/
theorem structureIsOver : (X ↘ Spec (.of P.field.k)).IsOver (Spec (.of P.field.k)) := by
  have _ : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) := inferInstance
  have _ : QuasiCompact (X ↘ Spec (.of P.field.k)) := inferInstance
  have _ : IsSeparated (X ↘ Spec (.of P.field.k)) := inferInstance
  apply (Scheme.Hom.isOver_iff _).2
  change (X ↘ Spec (.of P.field.k)) ≫ Spec.map
    (CommRingCat.ofHom (algebraMap P.field.k P.field.k)) = _
  have h : CommRingCat.ofHom (algebraMap P.field.k P.field.k) =
      𝟙 (CommRingCat.of P.field.k) := rfl
  rw [h, Spec.map_id, Category.comp_id]

attribute [instance] structureIsOver

variable (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
  P.field P.coefficients.different (f := X ↘ Spec (.of P.field.k)))

/-- The exceptional coefficient operation in any of the three stages of the corollary.
This is the recorded normalized constructible adjunction, not a new choice of adjoint.
Source: corollary, Ra_X! and Ra_X^!
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev operation (s : ConstructibleExceptionalCoefficients.Stage.{u} P.coefficients.l) :=
  S.ring.operation (compactification P X) s

/-- The integral counit read on the twisted coefficient object through an identification
of the dualizing complex. This expression retains the actual adjunction counit.
Source: corollary, integral counit clause
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def integralCounit (d : ℕ)
    (e : (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      integralTwist P X (X ↘ Spec (.of P.field.k)) d) :=
  (operation P X S (.integral (fieldStage P))).F.map e.inv ≫
    (operation P X S (.integral (fieldStage P))).adjunction.counit.app
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0)

/-- The same counit in ordinary completed-coefficient compact-support coordinates.
The left realization is normalized by the proper/open construction in the existing system.
Source: corollary, RΓ_c and the completed coefficient unit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def integralCounitAmbient (d : ℕ)
    (e : (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      integralTwist P X (X ↘ Spec (.of P.field.k)) d) :
    (PurCompactSupport.image
        (PurCompactSupport.completed P.coefficients.l P.extension) (compactification P X)).obj
          (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).obj :=
  (S.ring.left (compactification P X)
      (.integral (fieldStage P))).inv.app
        (integralTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension
      (Spec (.of P.field.k))).ι.map (integralCounit P X S d e)

/-- The integral clause of the corollary, including its canonical normalization.
The unit is the completed regular coefficient module (power zero), and its reduction
at every positive level is the free rank-one finite coefficient unit.

Source: current blueprint cor-pur-adic-and-rational-smooth-dualizing-complexes,
proof Step 1 and normalized-integration paragraph
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: apply thm-pur-adic-reconstruction to the completed coefficient unit.
Each finite reduction is the free coefficient module with Tor interval [0,0].
The finite purity maps are isomorphisms and their scalar-naturality makes them a
map of normalized systems. Reconstruction gives an isomorphism from the completed
twisted pullback of the unit to its exceptional pullback. Pullback of the completed
unit is the completed unit on X. Invert the reconstructed isomorphism to obtain e.
The reconstructed counit reduces to the finite normalized smooth trace: its factors
are finite purity followed by the exceptional counit. The root projections,
coefficient multiplication and even-shift comparisons are precisely twistReduction.
Thus its normalization is the displayed IsNormalizedIntegralIntegration predicate.
For uniqueness transpose under the exceptional adjunction and reduce to the same
finite purity morphism at every level. Use the already constructed isomorphism to
identify the dualizing object with the shifted line. Degree-zero full faithfulness
then identifies a difference with an ordinary endomorphism of that completed line.
The root projections and completed coefficient projections are jointly injective, so
an endomorphism vanishing at every finite quotient is zero. Thus the isomorphisms agree.
No uniqueness assertion about arbitrary triangulated homotopy-limit maps is used. -/
theorem existsUnique_integralIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    ∃! e : (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
        integralTwist P X (X ↘ Spec (.of P.field.k)) d,
      IsNormalizedIntegralIntegration P X d (integralCounitAmbient P X S d e) := by
  sorry

/-- The canonical integral identification is selected only after its normalized
integration property has determined it uniquely.
Source: corollary, omega_X = O_E,X(d)[2d]
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def integralIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S (.integral (fieldStage P))).G.obj
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
        integralTwist P X (X ↘ Spec (.of P.field.k)) d :=
  (existsUnique_integralIdentification P X S d).exists.choose

attribute [local irreducible] integralIdentification

/-- The rational coefficient unit and its shifted twist, using the literal
rationalization of the same completed integral representatives.
Source: corollary proof Step 2, rationalization
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def rationalTwist (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
    (fieldStage P) T).obj (integralTwist P T aT d)

/-- The rational identification is exactly the transported inverse integral purity map.
Source: corollary proof Step 2, coefficient comparison for exceptional pullback
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def rationalIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S (.rational (fieldStage P))).G.obj
        (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      rationalTwist P X (X ↘ Spec (.of P.field.k)) d :=
  ((S.fields.rationalizationComparison (compactification P X) (fieldStage P)).b.symm.app
    (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) ≪≫
  (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
    (fieldStage P) X).mapIso (integralIdentification P X S d)

attribute [local irreducible] rationalIdentification

set_option maxHeartbeats 1600000 in
-- The elaboration of this declaration ran out of the default 200000 heartbeats in the red global
-- build of 2026-10-25 against the newer dependencies; the statement is unchanged.
/-- Rational integration is the specified scalar transport of normalized integral
integration, through the compact-support coefficient comparison.
Source: corollary proof Steps 2--3
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def rationalIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S (.rational (fieldStage P))).F.obj
        (rationalTwist P X (X ↘ Spec (.of P.field.k)) d) ⟶
      rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0 :=
  (S.fields.rationalizationComparison (compactification P X) (fieldStage P)).q.inv.app
      (integralTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
      (fieldStage P) (Spec (.of P.field.k))).map
        (integralCounit P X S d (integralIdentification P X S d))

/-- The selected field's index in the recorded common-stage category.
Source: corollary proof Step 2, descent of a finite coefficient stage
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def fieldIndex : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar :=
  ⟨P.extension, P.finiteExtension⟩

/-- The prescribed small-model transport, retaining its actual algebra equivalence.
Source: corollary proof Step 2, common-stage size convention
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def modelEmbedding : P.extension →ₐ[Padic P.coefficients.l]
    AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (fieldIndex P) :=
  (Shrink.algEquiv (Padic P.coefficients.l) P.extension).symm.toAlgHom

/-- Scalar transport to that small coefficient model uses the existing rational tensor
functor, with no equality imposed on coefficient and site universes.
Source: corollary proof Step 2, common-stage descent
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev modelScalar (T : Scheme.{u}) :=
  ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l P.coefficients.Qbar
    (fieldStage P)
    (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
      (fieldIndex P)) (modelEmbedding P) T

/-- The actual common-stage inclusion of the selected coefficient field.
Source: corollary proof Step 2, Qbar coefficients
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev commonInclusion (T : Scheme.{u}) :=
  ConstructibleExceptionalCoefficients.commonInclusion P.coefficients.l P.coefficients.Qbar
    T (fieldIndex P)

/-- The closed coefficient unit and its twist represented over the selected finite
stage. The representative uses the actual size transport and common-stage inclusion.
Source: corollary proof Step 2, Qbar_X(d)[2d]
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def closedTwist (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  (commonInclusion P T).obj ((modelScalar P T).obj (rationalTwist P T aT d))

/-- Transport the rational identification first through the specified small-model
coefficient change and then through the common-stage exceptional comparison.
Source: corollary proof Step 2, transported Qbar purity
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def closedIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S .closed).G.obj (closedTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      closedTwist P X (X ↘ Spec (.of P.field.k)) d :=
  ((S.common.commonComparison (compactification P X) (fieldIndex P)).b.symm.app
      ((modelScalar P (Spec (.of P.field.k))).obj
        (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0))) ≪≫
    (commonInclusion P X).mapIso
      (((S.fields.rationalComparison (compactification P X) (fieldStage P)
          (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
            (fieldIndex P)) (modelEmbedding P)).b.symm.app
              (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) ≪≫
        (modelScalar P X).mapIso (rationalIdentification P X S d))

attribute [local irreducible] closedIdentification

/-- Qbar integration is common-stage descent of the same rationalized integral map.
The compact-support comparisons are the published normalized q maps.
Source: corollary proof Step 3, transported normalized integration
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def closedIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S .closed).F.obj
        (closedTwist P X (X ↘ Spec (.of P.field.k)) d) ⟶
      closedTwist P (Spec (.of P.field.k)) (𝟙 _) 0 :=
  (S.common.commonComparison (compactification P X) (fieldIndex P)).q.inv.app
      ((modelScalar P X).obj (rationalTwist P X (X ↘ Spec (.of P.field.k)) d)) ≫
    (commonInclusion P (Spec (.of P.field.k))).map
      ((S.fields.rationalComparison (compactification P X) (fieldStage P)
          (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
            (fieldIndex P)) (modelEmbedding P)).q.inv.app
              (rationalTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
        (modelScalar P (Spec (.of P.field.k))).map (rationalIntegration P X S d))

/-- The rational and algebraically closed counit clauses of the smooth dualizing
corollary. Together with existsUnique_integralIdentification these cover exactly
O_E, E and Qbar_l; none of the three integration maps has an arbitrary scalar factor.
The functors on Spec k are the sheaf coordinates of the recorded ordinary compact
cohomology, so applying the recorded coefficient-point fibre gives RΓ_c -> Lambda.

Source: current blueprint cor-pur-adic-and-rational-smooth-dualizing-complexes
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: Step 1 is existsUnique_integralIdentification: reconstruct finite normalized
purity at the completed unit, identify its pullback with the completed unit on X,
and invert. Step 2 applies rationalization to that inverse, with the exceptional
coefficient comparison b. Size-transport the same rational representative and descend
it to the common-stage category to get the Qbar identification. These are exactly
rationalIdentification and closedIdentification, so they invert transported purity.
Step 3 applies the counit equation of each recorded coefficient comparison. It says
that q inverse followed by the scalar-extended old trace is the new counit after
compact-support image of the transported identification. First use rationalization,
then the small-model field change, then common-stage inclusion. Finite normalization
is inherited from the coordinate Kummer orientation in finiteIntegration; on affine
space its ordered product of normalized A1 classes integrates to one. No global
fundamental class or assertion that integration is invertible is made for arbitrary X.
Finally the coefficient-point fibre identifies the unit with the scalar coefficient
complex and the compact-support value with the recorded RΓ_c. -/
theorem adic_and_rational_smooth_dualizing_complexes (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    IsNormalizedIntegralIntegration P X d
      (integralCounitAmbient P X S d (integralIdentification P X S d)) ∧
    ((operation P X S (.rational (fieldStage P))).adjunction.counit.app
        (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0) =
      (operation P X S (.rational (fieldStage P))).F.map
          (rationalIdentification P X S d).hom ≫ rationalIntegration P X S d) ∧
    ((operation P X S .closed).adjunction.counit.app
        (closedTwist P (Spec (.of P.field.k)) (𝟙 _) 0) =
      (operation P X S .closed).F.map
          (closedIdentification P X S d).hom ≫ closedIntegration P X S d) := by
  let R := S.fields.rationalizationComparison (compactification P X) (fieldStage P)
  let := R.shiftX
  let := R.shiftY
  have hr : (operation P X S (.rational (fieldStage P))).adjunction.counit.app
      (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0) =
      (operation P X S (.rational (fieldStage P))).F.map
        (rationalIdentification P X S d).hom ≫ rationalIntegration P X S d := by
    unfold rationalIdentification rationalIntegration integralCounit
    exact transport_counit _ _ _ _ _ _ R.q R.b _ _ _
      (R.comparison.counit _) (integralIdentification P X S d)
  refine ⟨?_, hr, ?_⟩
  · unfold integralIdentification
    exact (existsUnique_integralIdentification P X S d).exists.choose_spec
  · let E := ConstructibleExceptionalCoefficients.commonField P.coefficients.l
      P.coefficients.Qbar (fieldIndex P)
    let M := S.fields.rationalComparison (compactification P X) (fieldStage P)
      E (modelEmbedding P)
    let C := S.common.commonComparison (compactification P X) (fieldIndex P)
    let := M.shiftX
    let := M.shiftY
    let := C.shiftX
    let := C.shiftY
    let A := operation P X S (.rational E)
    let eM := (M.b.symm.app (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) ≪≫
      (modelScalar P X).mapIso (rationalIdentification P X S d)
    let tM := M.q.inv.app (rationalTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
      (modelScalar P (Spec (.of P.field.k))).map (rationalIntegration P X S d)
    have hri : (operation P X S (.rational (fieldStage P))).F.map
        (rationalIdentification P X S d).inv ≫
        (operation P X S (.rational (fieldStage P))).adjunction.counit.app
          (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0) =
        rationalIntegration P X S d := by
      rw [hr, ← Functor.map_comp_assoc, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    have hm : A.adjunction.counit.app
        ((modelScalar P (Spec (.of P.field.k))).obj
          (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) = A.F.map eM.hom ≫ tM := by
      dsimp only [eM, tM]
      rw [← hri]
      exact transport_counit _ _ _ _ _ _ M.q M.b _ _ _
        (M.comparison.counit _) (rationalIdentification P X S d)
    have hmi : A.F.map eM.inv ≫ A.adjunction.counit.app
        ((modelScalar P (Spec (.of P.field.k))).obj
          (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) = tM := by
      rw [hm, ← Functor.map_comp_assoc, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    unfold closedIdentification closedIntegration
    change _ = (operation P X S .closed).F.map
      ((C.b.symm.app ((modelScalar P (Spec (.of P.field.k))).obj
        (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) ≪≫
        (commonInclusion P X).mapIso eM).hom) ≫
      C.q.inv.app ((modelScalar P X).obj
        (rationalTwist P X (X ↘ Spec (.of P.field.k)) d)) ≫
      (commonInclusion P (Spec (.of P.field.k))).map tM
    rw [← hmi]
    exact transport_counit _ _ _ _ _ _ C.q C.b _ _ _ (C.comparison.counit _) eM

end AdicSmoothDualizing
end WeilConjectures
