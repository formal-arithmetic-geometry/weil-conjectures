/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.AmbientCompleteRawSystem
public import Sheaf.Paper.FiniteStagePairCategory
public import Sheaf.Paper.PbcQbarCategory
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Idempotents.Biproducts

public import Sheaf.CategoryTheory.StageSystemFunctorDescent

/-! # Ambient complete coefficient categories

Source: literature/blueprint/slopmaster2/src/version/sketch/32_smooth_base_change.tex,
lines 1191--1228, 1291--1345 and 1412--1438
(blueprint: def-sbc-ambient-complete-coefficient-categories).

This file records the ambient and constructible finite-stage categories, their
Karoubi completions, and the common-stage pair categories. The tensor transitions
are fixed by integral tensor and raw localization. Both
finite-stage and outer idempotents are retained in the common-stage categories.

## Main definitions

* `pbcAmbientCompleteSystem` and `pbcConstructibleCompleteSystem`: canonical tensors.
* `pbcAmbientCompleteQbarCategory` and `pbcConstructibleCompleteQbarCategory`:
  the two nested Karoubi categories.
* `pbcConstructibleCompleteQbarInclusion`: the canonical descended inclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.Idempotents

universe a b c x y z
variable {C : Type a} [Category.{x} C] {D : Type b} [Category.{y} D]
  {H : Type c} [Category.{z} H]

/-- Karoubi extension preserves composition by the identical object/projector/arrow formulas.
Source: sketch32, lines 1291--1311 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
def coefficientCompositionIso (F : C ⥤ D) (G : D ⥤ H) :
    (functorExtension₂ _ _).obj (F ⋙ G) ≅
      (functorExtension₂ _ _).obj F ⋙ (functorExtension₂ _ _).obj G := Iso.refl _

end CategoryTheory.Idempotents

namespace AlgebraicGeometry.Scheme

/-- The constructible rational stage before idempotent completion.
Source: sketch32, lines 1204--1207 (blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcConstructibleCompleteStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) : Type (u + 2) :=
  WeilConjectures.PbcRationalConstructible l (pbcFiniteField.{u} l Ω E) W

/-- The finite-stage ambient Karoubi category.
Source: sketch32, lines 1204--1207 (blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcAmbientCompleteKaroubiStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :=
  Idempotents.Karoubi (pbcAmbientCompleteStage l Ω W E)

/-- The finite-stage constructible Karoubi category.
Source: sketch32, lines 1204--1207 (blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcConstructibleCompleteKaroubiStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :=
  Idempotents.Karoubi (pbcConstructibleCompleteStage l Ω W E)

/-- The canonical finite-stage constructible-to-ambient inclusion after Karoubi completion.
Source: sketch32, lines 1204--1207 (blueprint: def-sbc-ambient-complete-coefficient-categories). -/
noncomputable def pbcConstructibleCompleteInclusion
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcConstructibleCompleteKaroubiStage l Ω W E ⥤
      pbcAmbientCompleteKaroubiStage l Ω W E :=
  (Idempotents.functorExtension₂ _ _).obj
    (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
  [IsNoetherian W]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
  [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]

variable {E F G : Padic.FiniteCoefficientFields l Ω}

/-- Extend the actual ambient rational tensor to every finite-stage projector.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcAmbientCompleteKaroubiTransition (h : E ≤ F) :
    pbcAmbientCompleteKaroubiStage l Ω W E ⥤ pbcAmbientCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂ _ _).obj (pbcAmbientCompleteRawTransition l Ω W h)

/-- Extend the existing constructible rational tensor to every finite-stage projector.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcConstructibleCompleteKaroubiTransition (h : E ≤ F) :
    pbcConstructibleCompleteKaroubiStage l Ω W E ⥤
      pbcConstructibleCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂ _ _).obj
    (pbcScalarExtension l Ω W hDim.out hInv.out h)

/-- Ambient balancing extended by its actual projector-sandwiched components.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcAmbientCompleteKaroubiAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcAmbientCompleteKaroubiTransition l Ω W h ⋙
        pbcAmbientCompleteKaroubiTransition l Ω W k ≅
      pbcAmbientCompleteKaroubiTransition l Ω W (h.trans k) :=
  (Idempotents.coefficientCompositionIso (pbcAmbientCompleteRawTransition l Ω W h)
    (pbcAmbientCompleteRawTransition l Ω W k)).symm ≪≫
      (Idempotents.functorExtension₂ _ _).mapIso (pbcAmbientCompleteRawAssociator l Ω W h k)

/-- Constructible balancing extended by its actual projector-sandwiched components.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcConstructibleCompleteKaroubiAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcConstructibleCompleteKaroubiTransition l Ω W h ⋙
        pbcConstructibleCompleteKaroubiTransition l Ω W k ≅
      pbcConstructibleCompleteKaroubiTransition l Ω W (h.trans k) :=
  (Idempotents.coefficientCompositionIso (pbcScalarExtension l Ω W hDim.out hInv.out h)
    (pbcScalarExtension l Ω W hDim.out hInv.out k)).symm ≪≫
      (Idempotents.functorExtension₂ _ _).mapIso
        (pbcScalarAssociator l Ω W hDim.out hInv.out h k)

/-- The Karoubi-extended balanced comparisons inherit both tensor pentagons.
Source: sketch32, lines 1291--1338
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: the composition adapters are identities. Expand Mathlib's extension
components, move the projectors through comparisons by naturality, and cancel
repeated projectors by idempotence. The two raw tensor pentagons give the two
underlying equalities. Faithfulness of Karoubi arrows gives the result. -/
theorem pbcCompleteKaroubi_cocycle (h : E ≤ F) (k : F ≤ G)
    {H : Padic.FiniteCoefficientFields l Ω} (j : G ≤ H) :
    (∀ P : pbcAmbientCompleteKaroubiStage l Ω W E,
      (pbcAmbientCompleteKaroubiTransition l Ω W j).map
          ((pbcAmbientCompleteKaroubiAssociator l Ω W h k).hom.app P) ≫
        (pbcAmbientCompleteKaroubiAssociator l Ω W (h.trans k) j).hom.app P =
      (pbcAmbientCompleteKaroubiAssociator l Ω W k j).hom.app
          ((pbcAmbientCompleteKaroubiTransition l Ω W h).obj P) ≫
        (pbcAmbientCompleteKaroubiAssociator l Ω W h (k.trans j)).hom.app P) ∧
    (∀ P : pbcConstructibleCompleteKaroubiStage l Ω W E,
      (pbcConstructibleCompleteKaroubiTransition l Ω W j).map
          ((pbcConstructibleCompleteKaroubiAssociator l Ω W h k).hom.app P) ≫
        (pbcConstructibleCompleteKaroubiAssociator l Ω W (h.trans k) j).hom.app P =
      (pbcConstructibleCompleteKaroubiAssociator l Ω W k j).hom.app
          ((pbcConstructibleCompleteKaroubiTransition l Ω W h).obj P) ≫
        (pbcConstructibleCompleteKaroubiAssociator l Ω W h (k.trans j)).hom.app P) := by
  sorry

/-- The canonical ambient system on the finite-stage Karoubi categories.
Source: sketch32, lines 1291--1338
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcAmbientCompleteSystem : StageSystem
    (fun E : Padic.FiniteCoefficientFields l Ω ↦ pbcAmbientCompleteKaroubiStage l Ω W E) where
  T h := pbcAmbientCompleteKaroubiTransition l Ω W h
  assoc h k := pbcAmbientCompleteKaroubiAssociator l Ω W h k
  cocycle h k j P := (pbcCompleteKaroubi_cocycle l Ω W h k j).1 P

/-- The canonical constructible system on the finite-stage Karoubi categories.
Source: sketch32, lines 1291--1338
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcConstructibleCompleteSystem : StageSystem
    (fun E : Padic.FiniteCoefficientFields l Ω ↦
      pbcConstructibleCompleteKaroubiStage l Ω W E) where
  T h := pbcConstructibleCompleteKaroubiTransition l Ω W h
  assoc h k := pbcConstructibleCompleteKaroubiAssociator l Ω W h k
  cocycle h k j P := (pbcCompleteKaroubi_cocycle l Ω W h k j).2 P

/-- Identity transitions and repeated-field associators are normalized in both systems.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: raw transitions have literal identities. Karoubi extension preserves the
identity functor. The projector is the Karoubi identity, so sandwiching either
raw unitor gives the corresponding Karoubi unitor, including the zero projector. -/
theorem pbcCompleteSystem_units (h : E ≤ F) :
    (pbcAmbientCompleteSystem l Ω W).T (le_refl E) = 𝟭 _ ∧
    HEq ((pbcAmbientCompleteSystem l Ω W).assoc (le_refl E) h)
      (Functor.leftUnitor ((pbcAmbientCompleteSystem l Ω W).T h)) ∧
    HEq ((pbcAmbientCompleteSystem l Ω W).assoc h (le_refl F))
      (Functor.rightUnitor ((pbcAmbientCompleteSystem l Ω W).T h)) ∧
    (pbcConstructibleCompleteSystem l Ω W).T (le_refl E) = 𝟭 _ ∧
    HEq ((pbcConstructibleCompleteSystem l Ω W).assoc (le_refl E) h)
      (Functor.leftUnitor ((pbcConstructibleCompleteSystem l Ω W).T h)) ∧
    HEq ((pbcConstructibleCompleteSystem l Ω W).assoc h (le_refl F))
      (Functor.rightUnitor ((pbcConstructibleCompleteSystem l Ω W).T h)) := by
  sorry

/-- Scalar extension commutes with the raw full inclusion by the identity tensor map.
The heterogeneous equality records the canonical equality of the underlying tensor
objects; it does not permit any other comparison automorphism.
Source: sketch32, lines 1291--1311 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: before rationalization both composites are the same tensor object and map
in the complete full subcategory. The normalized unit branches use the same tensor
unit. Localizing the identity comparison gives existence. It fixes every object
component, so natural transformations and inverse equations give uniqueness. -/
theorem pbcCompleteRawInclusionComparison_exists (h : E ≤ F) :
    ∃! b : WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W ⋙
        pbcAmbientCompleteRawTransition l Ω W h ≅
      pbcScalarExtension l Ω W hDim.out hInv.out h ⋙
        WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω F) W,
      ∀ K : pbcConstructibleCompleteStage l Ω W E,
        HEq (b.hom.app K)
          (𝟙 ((pbcAmbientCompleteRawTransition l Ω W h).obj
            ((WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W).obj K))) := by
  sorry

/-- The identity-on-integral-tensor raw inclusion comparison.
Source: sketch32, lines 1291--1311 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcCompleteRawInclusionComparison (h : E ≤ F) :=
  (pbcCompleteRawInclusionComparison_exists l Ω W h).exists.choose

/-- The specified finite-stage inclusion comparison is the actual Karoubi extension
of the identity-on-integral-tensor raw comparison. Mathlib's map on natural
transformations sandwiches each component between the two images of the projector;
the inverse uses the reverse sandwich. The composition comparisons are identities
on the underlying object, projector and arrows.
Source: sketch32, lines 1291--1311 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcCompleteKaroubiInclusionComparison (h : E ≤ F) :
    pbcConstructibleCompleteInclusion l Ω W E ⋙
        pbcAmbientCompleteKaroubiTransition l Ω W h ≅
      pbcConstructibleCompleteKaroubiTransition l Ω W h ⋙
        pbcConstructibleCompleteInclusion l Ω W F :=
  (Idempotents.coefficientCompositionIso
    (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
    (pbcAmbientCompleteRawTransition l Ω W h)).symm ≪≫
      (Idempotents.functorExtension₂ _ _).mapIso (pbcCompleteRawInclusionComparison l Ω W h) ≪≫
    Idempotents.coefficientCompositionIso
      (pbcScalarExtension l Ω W hDim.out hInv.out h)
      (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω F) W)

/-- Re-express the fixed Karoubi comparison through the named canonical systems.
Source: sketch32, lines 1291--1311 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: unfold the two system constructors. Their transitions are exactly the
Karoubi transitions, so the specified comparison supplies existence. HEq fixes
the whole natural isomorphism, including its inverse, hence gives uniqueness. -/
theorem pbcCompleteInclusionComparison_exists (h : E ≤ F) :
    ∃! b : pbcConstructibleCompleteInclusion l Ω W E ⋙
        (pbcAmbientCompleteSystem l Ω W).T h ≅
      (pbcConstructibleCompleteSystem l Ω W).T h ⋙
        pbcConstructibleCompleteInclusion l Ω W F,
      HEq b (pbcCompleteKaroubiInclusionComparison l Ω W h) := by
  sorry

/-- The fixed finite-stage comparison, expressed through the canonical systems.
Source: sketch32, lines 1291--1311 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcCompleteInclusionComparison (h : E ≤ F) :=
  (pbcCompleteInclusionComparison_exists l Ω W h).exists.choose

/-- The comparison is a coherent family for common-stage descent.
Source: sketch32, lines 1291--1338 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: before extension the inclusion is identity on integral tensor constructions,
so its unit and tower equations are the tensor unit and balancing equations.
Localize those equations. Extend to projectors by the stated sandwiches; naturality
and idempotence reduce them to the raw equations. -/
theorem pbcCompleteInclusion_coherent (h : E ≤ F) (k : F ≤ G) :
    HEq (pbcCompleteInclusionComparison l Ω W (le_refl E))
      ((pbcConstructibleCompleteInclusion l Ω W E).rightUnitor ≪≫
        (pbcConstructibleCompleteInclusion l Ω W E).leftUnitor.symm) ∧
    (∀ P : pbcConstructibleCompleteKaroubiStage l Ω W E,
      ((pbcAmbientCompleteSystem l Ω W).T k).map
          ((pbcCompleteInclusionComparison l Ω W h).hom.app P) ≫
        (pbcCompleteInclusionComparison l Ω W k).hom.app
          (((pbcConstructibleCompleteSystem l Ω W).T h).obj P) ≫
        (pbcConstructibleCompleteInclusion l Ω W G).map
          (((pbcConstructibleCompleteSystem l Ω W).assoc h k).hom.app P) =
      ((pbcAmbientCompleteSystem l Ω W).assoc h k).hom.app
          ((pbcConstructibleCompleteInclusion l Ω W E).obj P) ≫
        (pbcCompleteInclusionComparison l Ω W (h.trans k)).hom.app P) := by
  sorry

/-- Karoubi tensor extension is additive on ambient stages.
Proof: its underlying map is the additive raw scalar-extension map by
pbcAmbientCompleteRaw_additive. Addition of Karoubi arrows is addition of
underlying arrows; faithfulness gives the additive equation.
Source: sketch32, lines 1291--1338
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[instance] theorem pbcAmbientCompleteTransition_additive (h : E ≤ F) :
    ((pbcAmbientCompleteSystem l Ω W).T h).Additive := by
  sorry

/-- Karoubi tensor extension is additive on constructible stages.
Proof: the underlying map is additive by the published
pbcScalarExtension_additive. Addition of Karoubi arrows is addition of their
underlying localized arrows; apply faithfulness.
Source: sketch32, lines 1291--1338
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[instance] theorem pbcConstructibleCompleteTransition_additive (h : E ≤ F) :
    ((pbcConstructibleCompleteSystem l Ω W).T h).Additive := by
  sorry

/-- Both finite-stage Karoubi categories have finite biproducts.
Source: sketch32, lines 1192--1207 and 1291--1338
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: the full complete integral category contains zero and finite sums: the
Koszul completion and its unit commute with finite sums. Constructible integral
objects are also closed under these sums, by their uniform bounds and compatible
etale origins. Raw localization keeps these sums, since tensoring the integral
biproduct equations preserves them. Mathlib's Karoubi biproduct construction
then gives biproducts for all finite-stage projectors. -/
theorem pbcCompleteStages_finiteBiproducts :
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      HasFiniteBiproducts (pbcAmbientCompleteKaroubiStage l Ω W E)) ∧
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      HasFiniteBiproducts (pbcConstructibleCompleteKaroubiStage l Ω W E)) := by
  sorry

/-- The ambient finite-stage biproducts, including the zero projector.
Source: sketch32, lines 1192--1207
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
instance pbcAmbientCompleteStage_biproducts (E : Padic.FiniteCoefficientFields l Ω) :
    HasFiniteBiproducts (pbcAmbientCompleteKaroubiStage l Ω W E) :=
  (pbcCompleteStages_finiteBiproducts l Ω W).1 E

/-- The constructible finite-stage biproducts, including the zero projector.
Source: sketch32, lines 1192--1207
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
instance pbcConstructibleCompleteStage_biproducts (E : Padic.FiniteCoefficientFields l Ω) :
    HasFiniteBiproducts (pbcConstructibleCompleteKaroubiStage l Ω W E) :=
  (pbcCompleteStages_finiteBiproducts l Ω W).2 E

/-- Pair category of the finite-stage ambient Karoubi categories, followed by outer Karoubi.
Source: sketch32, lines 1291--1338 and 1413--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcAmbientCompleteQbarCategory :=
  Idempotents.Karoubi (pbcAmbientCompleteSystem l Ω W).PairCategory

/-- Pair category of finite-stage constructible Karoubi objects, with the outer projector.
Source: sketch32, lines 1291--1338 and 1413--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcConstructibleCompleteQbarCategory :=
  Idempotents.Karoubi (pbcConstructibleCompleteSystem l Ω W).PairCategory

/-- Object formula of the common-stage constructible inclusion, retaining the inner projector.
Source: sketch32, lines 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
def pbcCompletePairInclusionObject
    (P : (pbcConstructibleCompleteSystem l Ω W).PairCategory) :
    (pbcAmbientCompleteSystem l Ω W).PairCategory :=
  ⟨P.stage, (pbcConstructibleCompleteInclusion l Ω W P.stage).obj P.obj⟩

/-- The canonical constructible inclusion on the existing common-stage quotient.
The dependency's representative formula conjugates by b at source and target.
Source: sketch32, lines 1291--1338 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcCompletePairInclusion :=
  StageSystem.coefficientPairFunctor
    (pbcConstructibleCompleteSystem l Ω W) (pbcAmbientCompleteSystem l Ω W)
    (pbcConstructibleCompleteInclusion l Ω W) (pbcCompleteInclusionComparison l Ω W)
    (fun h k P ↦ (pbcCompleteInclusion_coherent l Ω W h k).2 P)

/-- The descended inclusion preserves the common-stage addition laws.
Source: sketch32, lines 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: choose representatives for two arrows at one common stage. The finite-stage
inclusion and composition with fixed comparison arrows preserve addition. Apply
the representative formula and descend the resulting equality to the quotient. -/
@[instance] theorem pbcCompletePairInclusion_additive :
    (pbcCompletePairInclusion l Ω W).Additive := by
  sorry

/-- Ambient raw objects and arrows embed using the identity finite-stage projector.
Source: sketch32, lines 1192--1207
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcRawAmbientStageToComplete (E : Padic.FiniteCoefficientFields l Ω) :=
  Idempotents.toKaroubi (pbcAmbientCompleteStage l Ω W E)

/-- The raw finite-stage categories embed by identity projectors.
Source: sketch32, lines 1192--1207
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcRawConstructibleStageToComplete (E : Padic.FiniteCoefficientFields l Ω) :=
  Idempotents.toKaroubi (pbcConstructibleCompleteStage l Ω W E)

/-- The identity-projector comparison is the fixed Mathlib extension comparison.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: unfold the constructible system. Mathlib's comparison at the raw tensor
functor has exactly these endpoints, with underlying identity components and
inverse. HEq to this specified isomorphism fixes the entire datum uniquely. -/
theorem pbcRawStageToCompleteComparison_exists (h : E ≤ F) :
    ∃! c : pbcRawConstructibleStageToComplete l Ω W E ⋙
        (pbcConstructibleCompleteSystem l Ω W).T h ≅
      pbcScalarExtension l Ω W hDim.out hInv.out h ⋙
        pbcRawConstructibleStageToComplete l Ω W F,
      HEq c ((Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app
        (pbcScalarExtension l Ω W hDim.out hInv.out h)) := by
  sorry

/-- The canonical identity-projector scalar comparison, through the named system.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcRawStageToCompleteComparison (h : E ≤ F) :=
  (pbcRawStageToCompleteComparison_exists l Ω W h).exists.choose

/-- Raw pair objects enter with the identity finite-stage projector.
Source: sketch32, lines 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
def pbcRawPairToCompleteObject (P : pbcQbarCategory l Ω W) :
    (pbcConstructibleCompleteSystem l Ω W).PairCategory :=
  ⟨P.stage, (pbcRawConstructibleStageToComplete l Ω W P.stage).obj P.obj⟩

/-- The canonical identity-projector comparisons satisfy the descent tower equation.
Source: sketch32, lines 1291--1338 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: unfold the canonical systems and use Mathlib's identity-projector comparison.
Its components have underlying identity. Naturality and the projector identities
reduce the tower equation to the same balanced raw tensor associator on both
sides. Faithfulness of Karoubi underlying arrows yields the equation. -/
theorem pbcRawPairToComplete_coherent :
    StageSystem.pairFunctorCoherent (pbcScalarSystem l Ω W hDim.out hInv.out)
      (pbcConstructibleCompleteSystem l Ω W)
      (pbcRawConstructibleStageToComplete l Ω W) (pbcRawStageToCompleteComparison l Ω W) := by
  sorry

/-- The canonical raw-to-nested-pair inclusion on objects and representatives.
Source: sketch32, lines 1291--1338 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcRawPairToComplete :=
  StageSystem.coefficientPairFunctor (pbcScalarSystem l Ω W hDim.out hInv.out)
    (pbcConstructibleCompleteSystem l Ω W)
    (pbcRawConstructibleStageToComplete l Ω W) (pbcRawStageToCompleteComparison l Ω W)
    (pbcRawPairToComplete_coherent l Ω W)

/-- Embed the raw Qbar category using identity projectors at both completion steps.
Source: sketch32, lines 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
def pbcRawQbarToComplete : pbcQbarCategory l Ω W ⥤
    pbcConstructibleCompleteQbarCategory l Ω W :=
  pbcRawPairToComplete l Ω W ⋙ Idempotents.toKaroubi _

/-- The constructible-to-ambient functor on the full nested Karoubi categories.
Objects `((E,(K,p)),e)` are sent to `((E,(j K,j p)),J e)`; both projectors survive.
The finite-stage aliases, normalized tensor systems, quotient representatives and
this outer functor together render the coefficient categories in the node.
Source: sketch32, lines 1191--1228, 1291--1345 and 1412--1438
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
def pbcConstructibleCompleteQbarInclusion
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    [IsNoetherian W]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))] :
    pbcConstructibleCompleteQbarCategory l Ω W ⥤ pbcAmbientCompleteQbarCategory l Ω W :=
  (Idempotents.functorExtension₂ _ _).obj (pbcCompletePairInclusion l Ω W)

end AlgebraicGeometry.Scheme
