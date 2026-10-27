# WeilConjectures.SemilinearSections.OpenClosed localization data

## Reason

The main theorem needs three independent assembly lemmas about its existing data.
Keeping their type definitions in the theorem module would create an import cycle.
Move the existing definitions and already proved helper theorems verbatim to
Sheaf.Paper.SemilinearOpenClosedData, publicly re-exported from the original module.
Add ClosedData, containing exactly the existing closed-operation fields, so the
closed-operation lemma asserts a strict part of the argument. The main theorem
keeps its complete original signature and docstring.

## Old

All public declarations before semilinearOpenClosedComplexSequence lived in
lean/Sheaf/Paper/SemilinearOpenClosedComplexSequence.lean. Their complete original
text is reproduced below. Imports and namespace context are unchanged in meaning.

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.SemilinearSections.OpenClosed

/-- The existing small model at the coefficient universe of this statement.
Source: the small-site convention
(blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
instance (priority := 20000) baseSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _

/-- The same size convention for strict systems, with no equality of site universes.
Source: Zheng 4.1 (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
instance (priority := 20000) sequenceSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × T.ProEt) := essentiallySmallSelf.{0} _

/-- The canonical ring sheafification on the selected small pro-etale site.
Source: Stacks 03DA (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
instance (priority := 20000) ringSheafify (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  hasSheafifyEssentiallySmallSite _ _

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The inverse-image tower has the actual images of the original ring sheaves.
Source: Stacks 09A5 (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
abbrev inverseRings (B : ℕ → Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :
    ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  fun n ↦ (Scheme.proEtaleSheafInverseImage.{u, u + 2} f CommRingCat.{u + 1}).obj (B n)

/-- Adjacent maps are inverse images of the supplied adjacent maps.
Source: Stacks 09A5 (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
abbrev inverseMaps (B : ℕ → Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) :=
  fun n ↦ (Scheme.proEtaleSheafInverseImage.{u, u + 2} f CommRingCat.{u + 1}).map (τ n)

/-- Base change on the sequence site retains the horizontal index and its morphisms.
Source: Stacks 09A5; Zheng 4.1
(blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
abbrev siteMap := (𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)

/-- The product base-change functor is continuous for the vertical topology.
Source: Stacks 09A5; Zheng 4.1
(blueprint: lem-sp-semilinear-open-closed-complex-sequence).
Proof: the sheaf condition for a vertical cover is the sheaf condition at its fixed
index. Base change preserves the pro-etale covering condition at that index.
Horizontal naturality is retained by the identity functor on the index poset. -/
theorem siteMap_continuous : (siteMap f).IsContinuous
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (coefficientSequenceTopology (Scheme.ProEt.topology X)) := by
  have : RepresentablyFlat (Scheme.proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  have : RepresentablyFlat (siteMap f) := by
    constructor
    intro V
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence V.1 V.2 (𝟭 ℕ) (Scheme.proEtaleBaseChange f)).symm
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
  constructor
  intro V S hS
  change (S.functorPushforward (siteMap f)).functorPullback (Prod.sectR V.1 X.ProEt) ∈
    Scheme.ProEt.topology X ((Scheme.proEtaleBaseChange f).obj V.2)
  apply (Scheme.ProEt.topology X).superset_covering _
    ((Scheme.proEtaleBaseChangeCoverPreserving f).cover_preserve hS)
  intro W a ha
  obtain ⟨V', g, h, hg, rfl⟩ := ha
  exact ⟨(V.1, V'), Prod.mkHom (𝟙 V.1) g, Prod.mkHom (𝟙 V.1) h, hg, by
    ext <;> simp [siteMap]⟩

attribute [instance] siteMap_continuous

variable (B : ℕ → Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The sequence coefficient unit is natural both vertically and horizontally.
Source: Stacks 09A5, 03D6
(blueprint: lem-sp-semilinear-open-closed-complex-sequence).
Proof: vertical naturality is the naturality of each ring-sheaf unit. Horizontal
naturality is naturality of that unit in the ring sheaf, first for adjacent maps
and then for composites. The product presheaf restriction combines these two equations. -/
theorem unit_naturality {V W : (ℕ × Y.ProEt)ᵒᵖ} (a : V ⟶ W) :
    (ringPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) B τ).map a ≫
        ((Scheme.proEtaleSheafAdjunction.{u, u + 2} f CommRingCat.{u + 1}).unit.app
          (B W.unop.1)).hom.app (op W.unop.2) =
      ((Scheme.proEtaleSheafAdjunction.{u, u + 2} f CommRingCat.{u + 1}).unit.app
          (B V.unop.1)).hom.app (op V.unop.2) ≫
        (ringPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (inverseRings f B)
          (inverseMaps f B τ)).map ((siteMap f).op.map a) := by
  let η := (Scheme.proEtaleSheafAdjunction.{u, u + 2} f CommRingCat.{u + 1}).unit
  let δ : rings (Scheme.ProEt.topology Y) B τ ⟶
      rings (Scheme.ProEt.topology X) (inverseRings f B) (inverseMaps f B τ) ⋙
        Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1} :=
    NatTrans.ofOpSequence (fun n ↦ η.app (B n)) (by
      intro n
      dsimp only [rings, Functor.comp_map]
      simp only [Functor.ofOpSequence_map_homOfLE_succ]
      exact η.naturality (τ n))
  let ε := Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := Y.ProEt)).functor
    (Functor.uncurry.map
      (Functor.whiskerRight δ (sheafToPresheaf (Scheme.ProEt.topology Y)
        CommRingCat.{u + 1})))
  exact ε.naturality a

/-- The actual coefficient unit, given sectionwise by the level ring adjunction unit.
Source: Stacks 09A5, 03D6
(blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
def coefficientUnit : systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) B τ ⟶
    ((siteMap f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
        (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (inverseRings f B) (inverseMaps f B τ)) :=
  ⟨{ app V := ((Scheme.proEtaleSheafAdjunction.{u, u + 2} f CommRingCat.{u + 1}).unit.app
        (B V.unop.1)).hom.app (op V.unop.2)
     naturality {_ _} a := unit_naturality f B τ a }⟩

/-- Forget commutativity in that precise unit, retaining its section homomorphisms.
Source: Stacks 03D6 (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
def moduleUnit : ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) B τ) ⟶
    ((siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
        (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (inverseRings f B) (inverseMaps f B τ))) :=
  ⟨Functor.whiskerRight (coefficientUnit f B τ).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Ordinary direct image of strict systems, with all transition restrictions intact.
Source: Stacks 03D6, 09A5
(blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
def push : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (inverseRings f B) (inverseMaps f B τ) ⥤
    Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) B τ :=
  SheafOfModules.pushforward.{u + 1} (moduleUnit f B τ)

/-- The existing general-universe module pullback construction applies to this unit.
Source: Stacks 03D7 (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
instance pushRightAdjoint :
    (SheafOfModules.pushforward.{u + 1} (moduleUnit f B τ)).IsRightAdjoint :=
  SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, 0}
    (moduleUnit f B τ)

/-- The canonical module inverse image adjoint to the specified direct image.
Source: Stacks 03D6, 09A5
(blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
def pull : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) B τ ⥤
    Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (inverseRings f B) (inverseMaps f B τ) :=
  SheafOfModules.pullback.{u + 1} (moduleUnit f B τ)

/-- Its actual module adjunction, with the ordinary sheafification-unit transpose.
Source: Stacks 03D6 (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
def adjunction : pull f B τ ⊣ push f B τ :=
  SheafOfModules.pullbackPushforwardAdjunction (moduleUnit f B τ)

omit τ in
/-- The level unit used by the recorded ordinary module direct image.
Source: Stacks 03D6 (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
def levelUnit (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :
    (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
      ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
          ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) :=
  ⟨Functor.whiskerRight
    (Scheme.proEtaleRingDirectImageMap f R
      ((Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _)).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Existence of the ordinary level module inverse image in the site universes.
Source: Stacks 03D7 (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
instance levelRightAdjoint (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :
    (SheafOfModules.pushforward.{u + 1} (levelUnit f R)).IsRightAdjoint :=
  SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, 0}
    (levelUnit f R)

/-- Level module inverse image using the canonical sheafified module Kan extension.
Source: Stacks 03D6 (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
def levelPull (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :=
  SheafOfModules.pullback.{u + 1} (levelUnit f R)

/-- The level adjunction has the specified coefficient unit and its ordinary transpose.
Source: Stacks 03D6 (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
def levelAdjunction (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :
    levelPull f R ⊣ Scheme.proEtaleRingModuleDirectImage f R
      ((Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) :=
  SheafOfModules.pullbackPushforwardAdjunction (levelUnit f R)

section Localization

variable {T Z : Scheme.{u}} (i : Z ⟶ T) (U : T.ProEt)
  (A : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
  (a : ∀ n : ℕ, A (n + 1) ⟶ A n)

/-- A clause-by-clause presentation of the canonical strict-system localization sequence.
This packages functors and comparisons, rather than assuming any open-closed axiom.
Its existence, exactness and coefficient compatibility are the theorem below.
Source: Stacks 09AH, 09BM; blueprint operations.proof.md (2)
(blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
structure SequenceData where
  /-- The published localization of the ringed sequence site and its open adjunction. -/
  openPart : SequenceOpenOrdinary.{u + 1, u, 0} (Scheme.ProEt.topology T) U A a
  /-- Its output transitions are the prescribed extension/scalar-comparison composites. -/
  openTransitions : openPart.Transitions
  /-- Closed inverse image is additive. -/
  [pullAdditive : (pull i A a).Additive]
  /-- Closed inverse image is left exact. -/
  pullLimits : PreservesFiniteLimits (pull i A a)
  /-- Closed inverse image is right exact. -/
  pullColimits : PreservesFiniteColimits (pull i A a)
  /-- Closed direct image is additive. -/
  [pushAdditive : (push i A a).Additive]
  /-- Closed direct image is left exact. -/
  pushLimits : PreservesFiniteLimits (push i A a)
  /-- Closed direct image is right exact under the quasi-compact-complement hypothesis. -/
  pushColimits : PreservesFiniteColimits (push i A a)
  /-- The closed pushforward is levelwise the recorded ordinary ringed direct image. -/
  pushEvaluation : ∀ n : ℕ,
    push i A a ⋙ evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T) A a n ≅
      evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology Z)
        (inverseRings i A) (inverseMaps i A a) n ⋙
          Scheme.proEtaleRingModuleDirectImage i (A n) (inverseRings i A n) (Iso.refl _)
  /-- The direct-image evaluation comparison retains the actual additive sections. -/
  pushEvaluation_sections : ∀ (n : ℕ)
    (M : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology Z)
      (inverseRings i A) (inverseMaps i A a)) (V : T.ProEtᵒᵖ),
    HEq (fun x ↦ ((pushEvaluation n).hom.app M).val.app V x)
      (fun x : M.val.obj (op (n, (Scheme.proEtaleBaseChange i).obj V.unop)) ↦ x)
  /-- Inverse-image evaluation uses the actual ringed module pullback. -/
  pullEvaluation : ∀ n : ℕ,
    pull i A a ⋙ evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology Z)
        (inverseRings i A) (inverseMaps i A a) n ≅
      evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T) A a n ⋙ levelPull i (A n)
  /-- Identification with the dependency's small-model presentation of module inverse image. -/
  levelPresentation : ∀ n : ℕ,
    levelPull i (A n) ≅ Scheme.proEtaleModuleInverseImage i (A n)
  /-- Evaluation preserves the actual closed unit, fixing the inverse-image comparison. -/
  unitEvaluation : ∀ (n : ℕ)
    (M : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology T) A a),
    (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T) A a n).map
        ((adjunction i A a).unit.app M) ≫
      (pushEvaluation n).hom.app ((pull i A a).obj M) ≫
      (Scheme.proEtaleRingModuleDirectImage i (A n) (inverseRings i A n)
        (Iso.refl _)).map ((pullEvaluation n).hom.app M) =
    (levelAdjunction i (A n)).unit.app
      ((evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T) A a n).obj M)
  /-- The actual counit-unit complex is short exact in every integer degree.
  As the two maps are natural transformations of system functors, their termwise
  applications are chain maps, including all semilinear transition equations. -/
  complexSequence : ∀ C : CochainComplex
    (Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology T) A a) ℤ,
    Mono ((openPart.adjunction.mapHomologicalComplex (.up ℤ)).counit.app C) ∧
      Epi (((adjunction i A a).mapHomologicalComplex (.up ℤ)).unit.app C) ∧
      (ComposableArrows.mk₂
        ((openPart.adjunction.mapHomologicalComplex (.up ℤ)).counit.app C)
        (((adjunction i A a).mapHomologicalComplex (.up ℤ)).unit.app C)).Exact


end Localization

section ScalarMaps

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
  (A D : ℕ → Sheaf J CommRingCat.{u + 1})
  (a : ∀ n : ℕ, A (n + 1) ⟶ A n) (d : ∀ n : ℕ, D (n + 1) ⟶ D n)
  (φ : ∀ n : ℕ, A n ⟶ D n)
  (hφ : ∀ n : ℕ, φ (n + 1) ≫ d n = a n ≫ φ n)

/-- Restriction along the compatible ring-system map, with the recorded sectionwise map.
Source: Stacks 03CZ (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
abbrev scalar :=
  res.{u + 1, u, u + 1} (systemMap.{u + 1, u, u + 1} J A a D d φ hφ)

end ScalarMaps

section Coefficients

variable {T Z : Scheme.{u}} (i : Z ⟶ T) (U : T.ProEt)
  (A D : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
  (a : ∀ n : ℕ, A (n + 1) ⟶ A n) (d : ∀ n : ℕ, D (n + 1) ⟶ D n)
  (φ : ∀ n : ℕ, A n ⟶ D n)
  (hφ : ∀ n : ℕ, φ (n + 1) ≫ d n = a n ≫ φ n)

include hφ in
/-- Localization carries a compatible coefficient map to a compatible coefficient map.
Source: Stacks 04IE, 03CZ
(blueprint: lem-sp-semilinear-open-closed-complex-sequence).
Proof: apply the over-pullback functor to hφ at each index and use preservation of
composition. This is equality of the actual sectionwise ring maps. -/
theorem openMap_compatible (n : ℕ) :
    ((Scheme.ProEt.topology T).overPullback CommRingCat.{u + 1} U).map (φ (n + 1)) ≫
        openTowerMap.{u + 1, u, 0} (Scheme.ProEt.topology T) U D d n =
      openTowerMap.{u + 1, u, 0} (Scheme.ProEt.topology T) U A a n ≫
        ((Scheme.ProEt.topology T).overPullback CommRingCat.{u + 1} U).map (φ n) := by
  change ((Scheme.ProEt.topology T).overPullback CommRingCat.{u + 1} U).map
      (φ (n + 1)) ≫
    ((Scheme.ProEt.topology T).overPullback CommRingCat.{u + 1} U).map (d n) = _
  rw [← Functor.map_comp, hφ n, Functor.map_comp]

include hφ in
/-- Inverse image carries the given coefficient map to the inverse-image tower map.
Source: Stacks 09A5, 03CZ
(blueprint: lem-sp-semilinear-open-closed-complex-sequence).
Proof: apply ring inverse image to hφ, using functoriality on the two composites. -/
theorem inverseMap_compatible (n : ℕ) :
    (Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).map (φ (n + 1)) ≫
        inverseMaps i D d n =
      inverseMaps i A a n ≫
        (Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).map (φ n) := by
  change (Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).map
      (φ (n + 1)) ≫
    (Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).map (d n) = _
  rw [← Functor.map_comp, hφ n, Functor.map_comp]

/-- Scalar restriction on the actual localized coefficient tower.
Source: Stacks 03CZ (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
abbrev openScalar :=
  scalar (Scheme.ProEt.topology T |>.over U)
    (openTower.{u + 1, u, 0} (Scheme.ProEt.topology T) U A)
    (openTower.{u + 1, u, 0} (Scheme.ProEt.topology T) U D)
    (openTowerMap.{u + 1, u, 0} (Scheme.ProEt.topology T) U A a)
    (openTowerMap.{u + 1, u, 0} (Scheme.ProEt.topology T) U D d)
    (fun n ↦ ((Scheme.ProEt.topology T).overPullback CommRingCat.{u + 1} U).map (φ n))
    (openMap_compatible U A D a d φ hφ)

/-- Scalar restriction on the actual inverse-image coefficient tower.
Source: Stacks 03CZ (blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
abbrev closedScalar :=
  scalar (Scheme.ProEt.topology Z) (inverseRings i A) (inverseRings i D)
    (inverseMaps i A a) (inverseMaps i D d)
    (fun n ↦ (Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).map (φ n))
    (inverseMap_compatible i A D a d φ hφ)

/-- Canonical scalar comparisons for all four operations, including the actual arrows.
The open restriction and closed direct-image comparisons are section identities.
Their adjoint comparisons are fixed by the counit and unit equations, respectively.
Thus these comparisons do not replace either sequence map by an unrelated map.
Source: Stacks 03DI, 03CY, 03CZ, 09AH
(blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/
structure ScalarCompatibility (P : SequenceData i U A a) (Q : SequenceData i U D d) where
  /-- Restriction of scalars commutes with open restriction. -/
  openPull : scalar (Scheme.ProEt.topology T) A D a d φ hφ ⋙ P.openPart.L ≅
    Q.openPart.L ⋙ openScalar U A D a d φ hφ
  /-- Its underlying additive maps are the identity on the restricted sections. -/
  openPull_sections : ∀ (M : Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) D d) (V : (ℕ × Over U)ᵒᵖ),
    HEq (fun x ↦ ((openPull.hom.app M).val.app V) x)
      (fun x : M.val.obj (op (V.unop.1, V.unop.2.left)) ↦ x)
  /-- The corresponding adjoint comparison for the sheafified open extension. -/
  openPush : Q.openPart.Jfun ⋙ scalar (Scheme.ProEt.topology T) A D a d φ hφ ≅
    openScalar U A D a d φ hφ ⋙ P.openPart.Jfun
  /-- This comparison carries the actual open counit to the actual open counit. -/
  openCounit : ∀ M : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology T) D d,
    openPush.hom.app (Q.openPart.L.obj M) ≫
      P.openPart.Jfun.map (openPull.inv.app M) ≫
      P.openPart.adjunction.counit.app
        ((scalar (Scheme.ProEt.topology T) A D a d φ hφ).obj M) =
    (scalar (Scheme.ProEt.topology T) A D a d φ hφ).map
      (Q.openPart.adjunction.counit.app M)
  /-- Scalar restriction commutes with closed inverse image. -/
  closedPull : scalar (Scheme.ProEt.topology T) A D a d φ hφ ⋙ pull i A a ≅
    pull i D d ⋙ closedScalar i A D a d φ hφ
  /-- Closed direct image commutes with scalar restriction. -/
  closedPush : push i D d ⋙ scalar (Scheme.ProEt.topology T) A D a d φ hφ ≅
    closedScalar i A D a d φ hφ ⋙ push i A a
  /-- Its underlying additive maps are the identity on the same base-change sections. -/
  closedPush_sections : ∀ (M : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology Z)
      (inverseRings i D) (inverseMaps i D d)) (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (fun x ↦ ((closedPush.hom.app M).val.app V) x)
      (fun x : M.val.obj
        (op (V.unop.1, (Scheme.proEtaleBaseChange i).obj V.unop.2)) ↦ x)
  /-- This comparison carries the actual closed unit to the actual closed unit. -/
  closedUnit : ∀ M : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology T) D d,
    (scalar (Scheme.ProEt.topology T) A D a d φ hφ).map
        ((adjunction i D d).unit.app M) ≫
      closedPush.hom.app ((pull i D d).obj M) =
    (adjunction i A a).unit.app
        ((scalar (Scheme.ProEt.topology T) A D a d φ hφ).obj M) ≫
      (push i A a).map (closedPull.hom.app M)

end Coefficients

```

## New

The declarations above are verbatim in
lean/Sheaf/Paper/SemilinearOpenClosedData.lean, except their blueprint anchors now
point to def-sp-semilinear-open-closed-data. The original module publicly imports
this module and SequenceSiteOpenExtension, preserving its public API. The only
new record is ClosedData, whose fields are copied verbatim from SequenceData
from pullAdditive through unitEvaluation. SequenceData and ScalarCompatibility
are unchanged; no existing definition is strengthened or weakened. No data is
chosen from an unproved existence statement. The two local witnesses in the
main theorem are eliminated in a proposition, not used in a public definition.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SemilinearOpenClosedComplexSequence | H3 | Imports the extracted definitions; fills the existing theorem by three smaller statements and a proved degreewise assembly. |
| Sheaf.Paper.SemilinearClosedSystemPresentation | new, H3 delivery | Uses ClosedData only. |
| Sheaf.Paper.SemilinearOrdinaryLocalizationSequence | new, H3 delivery | Uses ClosedData and the actual open adjunction. |
| Sheaf.Paper.SemilinearLocalizationScalarCompatibility | new, H3 delivery | Uses the unchanged SequenceData and ScalarCompatibility. |

`python3 tools/downstream.py Sheaf.Paper.SemilinearOpenClosedComplexSequence
--uses SequenceData ScalarCompatibility` found zero downstream modules and only
the item's own declaration uses. No existing consumer needs adaptation, and no
forced adaptation or source-library edit is made. Pending DAG parents still
need the theorem and are preserved. The unit route is unchanged.

## Status

landed 20261025T123050-L-1828684 2026-10-25 (merge of deliver/H3/Sheaf.Paper.SemilinearOpenClosedComplexSequence)
