/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Geometric operations for varying constant coefficient rings

Source: Stacks Project, Tags 03DI, 03DJ, 07A6, 09AE and 0F7B;
Zheng, Construction 4.1 (blueprint: def-sp-varying-ring-operations).

Systems and their ordinary unbounded derived categories are the existing sequence-site
module categories. Direct image is actual continuous module pushforward. Its left adjoint,
and open extension, are selected by their universal properties; all compositors are
unit-preserving adjoint comparisons.

## Main definitions

- `Modules`, `Derived`: the existing semilinear categories.
- `push`, `pull`, `extension`, `P`, `G`, `J`: actual ordinary and derived operations.
- `modulePComp`, `gComp`, `pComp`, `jComp`: normalized composition.
- `evalG`, `evalP`, `evalJ`: canonical coefficient evaluation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- The small pro-etale site fits the coefficient universe, retaining Hom universe u.
Source: Stacks 098K (blueprint: def-sp-varying-ring-operations). -/
instance siteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The vertical sequence site has the same smallness bound.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance sequenceSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- Ring-valued sheafification with all site and value universes fixed explicitly.
Source: Stacks 00W1 (blueprint: def-sp-varying-ring-operations). -/
instance ringSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  HasSmallSiteSheafify.hasSheafify_of_essentiallySmall.{u + 2, u, u, u + 1}
    CommRingCat.{u + 1} (Scheme.ProEt.topology X)

/-- Constant coefficient sheaves, with arbitrary commutative rings.
Source: Stacks 00YV (blueprint: def-sp-varying-ring-operations). -/
abbrev coefficients (X : Scheme.{u}) (n : ℕ) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj (R n)

/-- The actual adjacent ring-sheaf maps.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def coefficientTransition (X : Scheme.{u}) (n : ℕ) :
    coefficients R X (n + 1) ⟶ coefficients R X n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2}
    (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (φ n)

/-- The already constructed module category on the vertical sequence site.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev Modules (X : Scheme.{u}) :=
  Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X)

/-- Its ordinary unbounded derived category, with no cartesianness condition.
Source: Stacks 05RU (blueprint: def-sp-varying-ring-operations). -/
abbrev Derived (X : Scheme.{u}) :=
  DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)

/-- The functor on sequence sites leaves the coefficient index unchanged.
Source: Stacks 09AE; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def baseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : ℕ × Y.ProEt ⥤ ℕ × X.ProEt :=
  (𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)

/-- Continuity on the vertical sequence topology.
Source: Stacks 09AE; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: the inverse image of a vertical covering sieve is the base change of its
covering slice. Pro-etale base change preserves covering families. The horizontal
coordinate is unchanged, so the vertical-slice criterion proves continuity. -/
theorem baseChange_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (baseChange f).IsContinuous (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := by
  have : RepresentablyFlat (Scheme.proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  have : RepresentablyFlat (baseChange f) := by
    constructor
    intro U
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence U.1 U.2 (𝟭 ℕ) (Scheme.proEtaleBaseChange f)).symm
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
  constructor
  intro U S hS
  change (S.functorPushforward (baseChange f)).functorPullback (Prod.sectR U.1 X.ProEt) ∈
    Scheme.ProEt.topology X ((Scheme.proEtaleBaseChange f).obj U.2)
  apply (Scheme.ProEt.topology X).superset_covering _
    ((Scheme.proEtaleBaseChangeCoverPreserving f).cover_preserve hS)
  intro V a ha
  obtain ⟨W, g, h, hg, rfl⟩ := ha
  exact ⟨(U.1, W), Prod.mkHom (𝟙 U.1) g, Prod.mkHom (𝟙 U.1) h, hg, by
    ext <;> simp [baseChange]⟩

attribute [instance] baseChange_continuous

/-- The coefficient structure map at a sequence-site object is the canonical map on
constant sections at that same index.
Source: Stacks 00YV, 09AE (blueprint: def-sp-varying-ring-operations). -/
def ringMapApp {X Y : Scheme.{u}} (f : X ⟶ Y) (U : (ℕ × Y.ProEt)ᵒᵖ) :
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj
        ((coefficients R Y U.unop.1).obj.obj (op U.unop.2)) ⟶
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj
        ((coefficients R X U.unop.1).obj.obj
          ((Scheme.proEtaleBaseChange f).op.obj (op U.unop.2))) :=
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1} (R U.unop.1)).hom.app
      (op U.unop.2))

private theorem constantMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
        Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} B =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    _ _) ((presheafToSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map
      ((Functor.const Y.ProEtᵒᵖ).map a) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun t ↦ t.app ((Scheme.proEtaleBaseChange f).op.obj U))
    ((toSheafification (Scheme.ProEt.topology X) CommRingCat.{u + 1}).naturality
      ((Functor.const X.ProEtᵒᵖ).map a))

/-- Naturality includes the horizontal, possibly nonflat, coefficient maps.
Source: Stacks 00YV; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: for vertical arrows use naturality of the constant-section map on the site;
for horizontal arrows use its naturality in the coefficient ring. Every product
arrow factors into these two arrows, giving the displayed naturality equation. -/
theorem ringMapApp_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : (ℕ × Y.ProEt)ᵒᵖ} (a : U ⟶ V) :
    (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) (coefficients R Y)
        (coefficientTransition R φ Y))).obj.map a ≫ ringMapApp R f V =
      ringMapApp R f U ≫
        (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
            (coefficientTransition R φ X))).obj.map ((baseChange f).op.map a) := by
  let δ : rings (Scheme.ProEt.topology Y) (coefficients R Y)
      (coefficientTransition R φ Y) ⟶
      rings (Scheme.ProEt.topology X) (coefficients R X)
        (coefficientTransition R φ X) ⋙
          Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1} :=
    NatTrans.ofOpSequence
      (fun n ↦ Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (R n))
      (by
        intro n
        dsimp only [rings, Functor.comp_map]
        simp only [Functor.ofOpSequence_map_homOfLE_succ]
        exact constantMap_naturality f (φ n))
  let ε := Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := Y.ProEt)).functor
    (Functor.uncurry.map
      (Functor.whiskerRight δ (sheafToPresheaf (Scheme.ProEt.topology Y)
        CommRingCat.{u + 1})))
  exact (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).congr_map (ε.naturality a)

/-- The real ring-sheaf map defining direct image on semilinear systems.
Source: Stacks 03DA; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def ringMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) (coefficients R Y)
          (coefficientTransition R φ Y)) ⟶
      ((baseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
            (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
              (coefficientTransition R φ X))) :=
  ⟨{ app := ringMapApp R f, naturality := fun _ _ a => ringMapApp_naturality R φ f a }⟩

/-- Direct image retains sections M_n(H ×_Y X) and their semilinear transitions.
Source: Stacks 03DA; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def push {X Y : Scheme.{u}} (f : X ⟶ Y) : Modules R φ X ⥤ Modules R φ Y :=
  SheafOfModules.pushforward (ringMap R φ f)

private abbrev modelTopology (X : Scheme.{u}) :=
  (AsSmall.down : AsSmall.{u + 1} (ℕ × X.ProEt) ⥤ ℕ × X.ProEt).inducedTopology
    (coefficientSequenceTopology (Scheme.ProEt.topology X))

private abbrev sequenceRing (X : Scheme.{u}) :=
  ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
      (coefficientTransition R φ X))

private theorem sequenceRing_map_vertical (X : Scheme.{u}) (n : ℕ)
    {U V : X.ProEt} (a : U ⟶ V) :
    (sequenceRing R φ X).obj.map (Prod.mkHom (𝟙 n) a).op =
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((coefficients R X n).obj.map a.op) := by
  change (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    (((rings (Scheme.ProEt.topology X) (coefficients R X)
      (coefficientTransition R φ X)).map (𝟙 (op n))).hom.app (op V) ≫
        (coefficients R X n).obj.map a.op) = _
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

private def sequenceModelEquivalence (X : Scheme.{u}) :
    SheafOfModules.{u + 1}
      (((AsSmall.down : AsSmall.{u + 1} (ℕ × X.ProEt) ⥤ ℕ × X.ProEt).sheafPushforwardContinuous
         RingCat.{u + 1} (modelTopology X)
          (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj (sequenceRing R φ X)) ≌
      Modules R φ X := by
  let A := sequenceRing R φ X
  let B := ((AsSmall.down : AsSmall.{u + 1} (ℕ × X.ProEt) ⥤ ℕ × X.ProEt).sheafPushforwardContinuous
     RingCat.{u + 1} (modelTopology X)
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj A
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := ℕ × X.ProEt)).functor.IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) (modelTopology X) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := ℕ × X.ProEt)).functor.IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := ℕ × X.ProEt)).inverse.inducedTopology
        (coefficientSequenceTopology (Scheme.ProEt.topology X))))
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := ℕ × X.ProEt)).inverse.IsContinuous
      (modelTopology X) (coefficientSequenceTopology (Scheme.ProEt.topology X)) := by
    change AsSmall.down.IsContinuous (modelTopology X)
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := ℕ × X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)

/-- Existence of inverse image as the left adjoint of the actual section functor.
Source: Stacks 03EK; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: form inverse image on the product site and extend scalars along ringMap.
Constant sheaves pull back to the same constants, compatibly with φ. Thus this
module pullback is the componentwise inverse image and has the usual adjunction. -/
theorem push_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (push R φ f).IsRightAdjoint := by
  let JX := coefficientSequenceTopology (Scheme.ProEt.topology X)
  let JY := coefficientSequenceTopology (Scheme.ProEt.topology Y)
  have : (AsSmall.up : ℕ × X.ProEt ⥤ AsSmall.{u + 1} (ℕ × X.ProEt)).IsContinuous
      JX (modelTopology X) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := ℕ × X.ProEt)).functor.IsContinuous
       JX ((AsSmall.equiv.{u, u + 1, u + 1} (C := ℕ × X.ProEt)).inverse.inducedTopology JX))
  let F : AsSmall.{u + 1} (ℕ × Y.ProEt) ⥤ AsSmall.{u + 1} (ℕ × X.ProEt) :=
    AsSmall.down ⋙ baseChange f ⋙ AsSmall.up
  have := Functor.isContinuous_comp (baseChange f)
    (AsSmall.up : ℕ × X.ProEt ⥤ AsSmall.{u + 1} (ℕ × X.ProEt))
    JY JX (modelTopology X)
  have : F.IsContinuous (modelTopology Y) (modelTopology X) :=
    Functor.isContinuous_comp AsSmall.down (baseChange f ⋙ AsSmall.up)
      (modelTopology Y) JY (modelTopology X)
  let SX := ((AsSmall.down : AsSmall.{u + 1} (ℕ × X.ProEt) ⥤ ℕ × X.ProEt).sheafPushforwardContinuous
     RingCat.{u + 1} (modelTopology X) JX).obj (sequenceRing R φ X)
  let SY := ((AsSmall.down : AsSmall.{u + 1} (ℕ × Y.ProEt) ⥤ ℕ × Y.ProEt).sheafPushforwardContinuous
     RingCat.{u + 1} (modelTopology Y) JY).obj (sequenceRing R φ Y)
  let a : SY ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
      (modelTopology Y) (modelTopology X)).obj SX :=
    ⟨Functor.whiskerLeft AsSmall.down.op (ringMap R φ f).hom⟩
  let eX := sequenceModelEquivalence R φ X
  let eY := sequenceModelEquivalence R φ Y
  let adj := eY.symm.toAdjunction.comp
    ((SheafOfModules.pullbackPushforwardAdjunction a).comp eX.toAdjunction)
  refine (adj.ofNatIsoRight ?_).isRightAdjoint
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    dsimp only [eX, eY, sequenceModelEquivalence]
    exact PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl)
  · intro M N b
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl


attribute [instance] push_isRightAdjoint

/-- Inverse image selected by its universal property, not by a noncanonical map.
Source: Stacks 03EK (blueprint: def-sp-varying-ring-operations). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) := (push R φ f).leftAdjoint

/-- The universal-property adjunction fixes every subsequent mate and compositor.
Source: Stacks 03EK (blueprint: def-sp-varying-ring-operations). -/
def moduleAdj {X Y : Scheme.{u}} (f : X ⟶ Y) : pull R φ f ⊣ push R φ f :=
  Adjunction.ofIsRightAdjoint _

/-- Inverse image is additive and exact on all systems.
Source: Zheng 4.1; Stacks 03EK (blueprint: def-sp-varying-ring-operations).
Proof: the left adjoint is canonically the componentwise abelian inverse image.
Kernels and sheafified cokernels are componentwise; inverse image preserves both.
Addition is inherited from abelian inverse image. No flatness of φ is used. -/
theorem pull_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pull R φ f).Additive ∧ PreservesFiniteLimits (pull R φ f) ∧
      PreservesFiniteColimits (pull R φ f) := by
  sorry

/-- Direct image is additive on all section modules.
Source: Stacks 03DA (blueprint: def-sp-varying-ring-operations).
Proof: continuous module pushforward preserves the underlying maps and their
pointwise sums. Extensionality on all sections gives additivity. -/
theorem push_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (push R φ f).Additive := by
  constructor
  intro M N f g
  ext U x
  rfl

attribute [instance] push_additive

/-- Additivity needed for the actual exact derived inverse image.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance pullAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) : (pull R φ f).Additive :=
  (pull_exact R φ f).1

/-- Left exactness of the actual inverse image.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance pullLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (pull R φ f) := (pull_exact R φ f).2.1

/-- Right exactness of the actual inverse image.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance pullColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pull R φ f) := (pull_exact R φ f).2.2

/-- K-injective resolutions on the actual ringed sequence site.
Source: Stacks 079P; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: the category is modules over systemRing on the small vertical sequence site.
Apply the recorded Grothendieck abelianness and K-injective resolution theorem to
that ringed site. This does not assert that evaluation preserves K-injectives. -/
theorem modules_kInjective (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (Modules R φ X) := by
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u,
        u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
      (coefficientTransition R φ X))).1
  infer_instance

attribute [instance] modules_kInjective

/-- Exact inverse image on the ordinary derived system category.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev G {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived R φ Y ⥤ Derived R φ X :=
  (pull R φ f).mapDerivedCategory

/-- Total right derived direct image, computed on the system category itself.
Source: Stacks 079P (blueprint: def-sp-varying-ring-operations). -/
abbrev P {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived R φ X ⥤ Derived R φ Y :=
  (push R φ f).rightDerivedFunctor

/-- The canonical derived adjunction is induced from the ordinary one.
Source: Stacks 07A6 (blueprint: def-sp-varying-ring-operations). -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : G R φ f ⊣ P R φ f :=
  (moduleAdj R φ f).mapDerivedCategoryRightDerivedAdjunction


private theorem constantMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : CommRingCat.{u + 1}) :
    Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A ≫
      (Scheme.proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) ≫
      (Functor.sheafPushforwardContinuousComp'
        (eFG := (MorphismProperty.Over.pullbackComp
          (P := @WeaklyEtale) (Q := ⊤) f g).symm)
        CommRingCat.{u + 1} (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y)
          (Scheme.ProEt.topology X)).hom.app (coefficients (fun _ ↦ A) X 0) =
      Scheme.proEtaleConstantDirectImageMap (f ≫ g) CommRingCat.{u + 1} A := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Z) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Z.ProEtᵒᵖ).obj A) _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  have hf := Equiv.apply_symm_apply
    ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj A)
      ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A)))
    (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  have hfU := congrArg (fun t ↦ t.app ((Scheme.proEtaleBaseChange g).op.obj U)) hf
  change (toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
      ((Scheme.proEtaleBaseChange g).op.obj U) ≫
    (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app
      ((Scheme.proEtaleBaseChange g).op.obj U) = _ at hfU
  change ((toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
      ((Scheme.proEtaleBaseChange g).op.obj U) ≫
    (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app
      ((Scheme.proEtaleBaseChange g).op.obj U)) ≫
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app
            U.unop).op = _
  rw [hfU]
  erw [Equiv.apply_symm_apply]
  have hn := (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
  change 𝟙 A ≫ _ = _ at hn
  rw [Category.id_comp] at hn
  exact hn.symm

/-- Ordinary direct-image composition is fixed on every section and coefficient index.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations).
Proof: restriction along the canonical fibre-product pasting isomorphism is linear,
natural in test objects, and compatible with every coefficient transition. Its
inverse is restriction along the inverse isomorphism. Sections determine uniqueness. -/
theorem modulePComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! d : push R φ f ⋙ push R φ g ≅ push R φ (f ≫ g),
      ∀ (N : Modules R φ X) (n : ℕ) (U : Z.ProEt)
        (x : ((push R φ f ⋙ push R φ g).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op (n, U)) x =
          N.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackComp f g).hom.app U)).op x := by
  have := Functor.isContinuous_comp (baseChange g) (baseChange f)
    (coefficientSequenceTopology (Scheme.ProEt.topology Z))
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
  let e : baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f :=
    NatIso.prod (Iso.refl (𝟭 ℕ)) (MorphismProperty.Over.pullbackComp f g)
  let a : sequenceRing R φ Z ⟶
      ((baseChange g ⋙ baseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Z))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj (sequenceRing R φ X) :=
    ringMap R φ g ≫ ((baseChange g).sheafPushforwardContinuous RingCat.{u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology Z))
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))).map (ringMap R φ f)
  have h : a ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Z))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).app (sequenceRing R φ X) =
      ringMap R φ (f ≫ g) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change ringMapApp R g U ≫
      ringMapApp R f (op (U.unop.1, (Scheme.proEtaleBaseChange g).obj U.unop.2)) ≫
        (sequenceRing R φ X).obj.map
          (Prod.mkHom (𝟙 U.unop.1)
            ((MorphismProperty.Over.pullbackComp f g).hom.app U.unop.2)).op = _
    rw [sequenceRing_map_vertical]
    exact (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).congr_map
      (congrArg (fun t ↦ t.hom.app (op U.unop.2))
        (constantMap_comp f g (R U.unop.1)))
  let d : push R φ f ⋙ push R φ g ≅ push R φ (f ≫ g) :=
    SheafOfModules.pushforwardComp (ringMap R φ g) (ringMap R φ f) ≪≫
      SheafOfModules.pushforwardNatIso a e ≪≫ SheafOfModules.pushforwardCongr h
  have hd : ∀ (N : Modules R φ X) (n : ℕ) (U : Z.ProEt)
      (x : ((push R φ f ⋙ push R φ g).obj N).val.obj (op (n, U))),
      (d.hom.app N).val.app (op (n, U)) x =
        N.val.map (Prod.mkHom (𝟙 n)
          ((MorphismProperty.Over.pullbackComp f g).hom.app U)).op x := by
    intros
    rfl
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (hd' N U.unop.1 U.unop.2 x).trans (hd N U.unop.1 U.unop.2 x).symm

/-- The section-normalized compositor for ordinary direct image.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def modulePComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (modulePComp_existsUnique R φ f g).choose

/-- Inverse-image composition is its unit-preserving conjugate.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def moduleGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull R φ (f ≫ g) ≅ pull R φ g ⋙ pull R φ f :=
  (Adjunction.leftAdjointCompIso (moduleAdj R φ g) (moduleAdj R φ f)
    (moduleAdj R φ (f ≫ g)) (modulePComp R φ f g)).symm

/-- Derived inverse-image composition is localized from the actual system comparison.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def gComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G R φ (f ≫ g) ≅ G R φ g ⋙ G R φ f :=
  Functor.mapDerivedCategoryNatIso (moduleGComp R φ f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Proper direct-image composition is the conjugate of inverse-image composition.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def pComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P R φ f ⋙ P R φ g ≅ P R φ (f ≫ g) :=
  conjugateIsoEquiv ((adj R φ g).comp (adj R φ f)) (adj R φ (f ≫ g)) (gComp R φ f g)

/-- The identity comparison for ordinary direct image is the pullback graph map.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations).
Proof: restriction along the graph of the identity base change is a linear isomorphism
at every index. The inverse graph gives its inverse. These maps commute with the
semilinear transitions, and the section formula determines them uniquely. -/
theorem modulePId_existsUnique (X : Scheme.{u}) :
    ∃! d : push R φ (𝟙 X) ≅ 𝟭 (Modules R φ X),
      ∀ (N : Modules R φ X) (n : ℕ) (U : X.ProEt)
        (x : ((push R φ (𝟙 X)).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op (n, U)) x =
          N.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U)).op x := by
  let e : baseChange (𝟙 X) ≅ 𝟭 (ℕ × X.ProEt) :=
    NatIso.prod (Iso.refl (𝟭 ℕ)) (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X)
  have h : ringMap R φ (𝟙 X) ≫
      (Functor.sheafPushforwardContinuousNatTrans e.inv RingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).app (sequenceRing R φ X) =
      𝟙 (sequenceRing R φ X) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have hc : Scheme.proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1}
          (R U.unop.1) ≫
        (Functor.sheafPushforwardContinuousId'
          (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) CommRingCat.{u + 1}
            (Scheme.ProEt.topology X)).hom.app (coefficients R X U.unop.1) =
        𝟙 (coefficients R X U.unop.1) := by
      apply ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv
         ((Functor.const X.ProEtᵒᵖ).obj (R U.unop.1)) _).injective
      rw [Adjunction.homEquiv_naturality_right]
      simp only [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
      apply NatTrans.ext
      funext V
      change (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (R U.unop.1))).app
          ((Scheme.proEtaleBaseChange (𝟙 X)).op.obj V) ≫
          (coefficients R X U.unop.1).obj.map
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).op = _
      have hn := (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (R U.unop.1))).naturality
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).op
      change 𝟙 (R U.unop.1) ≫ _ = _ at hn
      rw [Category.id_comp] at hn
      rw [Adjunction.homEquiv_unit]
      change _ = (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (R U.unop.1))).app V ≫ 𝟙 _
      rw [Category.comp_id]
      exact hn.symm
    change ringMapApp R (𝟙 X) U ≫
      (sequenceRing R φ X).obj.map
        (Prod.mkHom (𝟙 U.unop.1)
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U.unop.2)).op = _
    rw [sequenceRing_map_vertical]
    exact (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).congr_map
      (congrArg (fun t ↦ t.hom.app (op U.unop.2)) hc)
  let d : push R φ (𝟙 X) ≅ 𝟭 (Modules R φ X) :=
    SheafOfModules.pushforwardNatIso (ringMap R φ (𝟙 X)) e.symm ≪≫
      SheafOfModules.pushforwardCongr h ≪≫ SheafOfModules.pushforwardId _
  have hd : ∀ (N : Modules R φ X) (n : ℕ) (U : X.ProEt)
      (x : ((push R φ (𝟙 X)).obj N).val.obj (op (n, U))),
      (d.hom.app N).val.app (op (n, U)) x =
        N.val.map (Prod.mkHom (𝟙 n)
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U)).op x := by
    intros
    rfl
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (hd' N U.unop.1 U.unop.2 x).trans (hd N U.unop.1 U.unop.2 x).symm

/-- The uniquely normalized ordinary identity comparison.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations). -/
def modulePId (X : Scheme.{u}) := (modulePId_existsUnique R φ X).choose

/-- The inverse-image identity is localized from the adjoint identity comparison.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations). -/
def gId (X : Scheme.{u}) : G R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  Functor.mapDerivedCategoryNatIso
    (Adjunction.leftAdjointIdIso (moduleAdj R φ (𝟙 X)) (modulePId R φ X)) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The right-adjoint identity is fixed by the same unit normalization.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations). -/
def pId (X : Scheme.{u}) : P R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  (conjugateIsoEquiv Adjunction.id (adj R φ (𝟙 X)) (gId R φ X)).symm

/-- Open restriction has the extension-by-zero left adjoint.
Source: Stacks 03DI, 09AE (blueprint: def-sp-varying-ring-operations).
Proof: localization identifies the open pro-etale site with the slice site. On each
coefficient level use localizedSystemExtension and localizedSystemAdjunction. Their
direct-sum lift formula commutes with φ, so the adjunction assembles on the actual
sequence site. It identifies its right adjoint with pull along the open immersion. -/
theorem pull_isRightAdjoint {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (pull R φ j).IsRightAdjoint := by
  sorry

attribute [instance] pull_isRightAdjoint

/-- Open extension chosen by the localized module universal property.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
abbrev extension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (pull R φ j).leftAdjoint

/-- The actual ordinary open-extension adjunction.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
def moduleJAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    extension R φ j ⊣ pull R φ j := Adjunction.ofIsRightAdjoint _

/-- Exactness of extension by zero, including the empty open.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations).
Proof: the localized direct-sum extension has at most one lift at every test object.
Its underlying abelian sheaf is exact extension by zero. Sheafification is exact,
and componentwise kernels and cokernels give exactness on systems. The canonical
unit-preserving comparison with the chosen left adjoint transfers this assertion. -/
theorem extension_exact {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (extension R φ j).Additive ∧ PreservesFiniteLimits (extension R φ j) ∧
      PreservesFiniteColimits (extension R φ j) := by
  sorry

/-- Additivity of extension by zero.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
instance extensionAdditive {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (extension R φ j).Additive := (extension_exact R φ j).1

/-- Left exactness of extension by zero.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations). -/
instance extensionLimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (extension R φ j) := (extension_exact R φ j).2.1

/-- Right exactness of extension by zero.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations). -/
instance extensionColimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteColimits (extension R φ j) := (extension_exact R φ j).2.2

/-- Exact extension on the ordinary derived category of systems.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations). -/
abbrev J {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (extension R φ j).mapDerivedCategory

/-- The derived open adjunction retains the ordinary units and counits.
Source: Stacks 03DI, 07A6 (blueprint: def-sp-varying-ring-operations). -/
def jAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : J R φ j ⊣ G R φ j :=
  Adjunction.ofNatIsoRight ((moduleJAdj R φ j).mapDerivedCategoryRightDerivedAdjunction)
    (pull R φ j).rightDerivedFunctorIsoMapDerivedCategory

/-- Ordinary open composition has the inverse-image composition as its conjugate.
Source: Stacks 03DI, 0F7D (blueprint: def-sp-varying-ring-operations). -/
def moduleJComp {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    extension R φ i ⋙ extension R φ j ≅ extension R φ (i ≫ j) :=
  Adjunction.leftAdjointCompIso (moduleJAdj R φ i) (moduleJAdj R φ j)
    (moduleJAdj R φ (i ≫ j)) (moduleGComp R φ i j).symm

/-- Derived open composition is localized from that ordinary comparison.
Source: Stacks 0F7D (blueprint: def-sp-varying-ring-operations). -/
def jComp {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] : J R φ i ⋙ J R φ j ≅ J R φ (i ≫ j) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleJComp R φ i j)

/-- Identity extension with its canonical adjoint normalization.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
def jId (X : Scheme.{u}) : J R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  Adjunction.leftAdjointIdIso (jAdj R φ (𝟙 X)) (gId R φ X)


/-- Exact ordinary evaluation of a semilinear system.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev eval (X : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X) n

/-- Evaluation on the ordinary unbounded derived category.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev ev (X : Scheme.{u}) (n : ℕ) := (eval R φ X n).mapDerivedCategory

/-- Ordinary pushforward evaluation is identity on every section carrier.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: both sides have sections N_n(H ×_Y X), maps induced by the same restrictions,
and the same constant scalar map. The identity is linear and natural. Equality on
all sections proves uniqueness. -/
theorem moduleEvalP_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! d : push R φ f ⋙ eval R φ Y n ≅
        eval R φ X n ⋙ StrictTower.moduleDirectImage (R n) f,
      ∀ (N : Modules R φ X) (U : Y.ProEt)
        (x : ((push R φ f).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op U) x = x := by
  sorry

/-- The actual componentwise direct-image identification.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def moduleEvalP {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (moduleEvalP_existsUnique R φ f n).choose

/-- Inverse-image evaluation is uniquely fixed by the ordinary unit equation.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: the componentwise ordinary inverse-image adjunction identifies the left
adjoint with level inverse image. Its unit is the displayed system unit. The Hom
bijection forces the comparison uniquely, and inverse images of the same constant
rings make it invertible. This includes all semilinear transitions. -/
theorem moduleEvalG_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! d : pull R φ f ⋙ eval R φ X n ≅
        eval R φ Y n ⋙ StrictTower.modulePullback (R n) f,
      ∀ N : Modules R φ Y,
        (eval R φ Y n).map ((moduleAdj R φ f).unit.app N) ≫
          (moduleEvalP R φ f n).hom.app ((pull R φ f).obj N) ≫
          (StrictTower.moduleDirectImage (R n) f).map (d.hom.app N) =
        (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
          (coefficients R X n) (StrictTower.constantRingIso (R n) f)).unit.app
            ((eval R φ Y n).obj N) := by
  sorry

/-- The normalized ordinary pullback evaluation comparison.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def moduleEvalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (moduleEvalG_existsUnique R φ f n).choose

/-- Derived evaluation is localization of the actual ordinary comparison.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def evalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    G R φ f ⋙ ev R φ X n ≅
      ev R φ Y n ⋙ (StrictTower.modulePullback (R n) f).mapDerivedCategory :=
  letI : (StrictTower.modulePullback (R n) f).Additive :=
    StrictTower.modulePullback_additive (R n) f
  letI : PreservesFiniteLimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteLimits (R n) f
  letI : PreservesFiniteColimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteColimits (R n) f
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleEvalG R φ f n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The ordinary exact-level adjunction, derived with its original unit.
Source: Stacks 07A6 (blueprint: def-sp-varying-ring-operations). -/
def levelAdj {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
    (coefficients R X n)
      (StrictTower.constantRingIso (R n) f)).mapDerivedCategoryRightDerivedAdjunction

/-- Evaluation of total direct image is the canonical mate, before inversion.
Source: Zheng 4.1, Lemma 4.10 (blueprint: def-sp-varying-ring-operations). -/
def evalPMate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    P R φ f ⋙ ev R φ Y n ⟶
      ev R φ X n ⋙ (StrictTower.moduleDirectImage (R n) f).rightDerivedFunctor :=
  mateEquiv (adj R φ f) (levelAdj R f n) (evalG R φ f n).inv

/-- The canonical direct-image evaluation mate is invertible on all systems.
Source: Zheng 4.10; semilinear derived sections (blueprint: def-sp-varying-ring-operations).
Proof: apply the simultaneous-section direct-image evaluation of
lem-coef-semilinear-derived-sections. Its ordinary realization is the same identity
on sections and its derived adjunction is the canonical ordinary-derived one.
The unit normalization therefore identifies its comparison with evalPMate. No
assertion that evaluated K-injectives are K-injective is used. -/
theorem evalPMate_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (evalPMate R φ f n) := by
  sorry

/-- The normalized derived direct-image evaluation.
Source: Zheng 4.10 (blueprint: def-sp-varying-ring-operations). -/
def evalP {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  @asIso _ _ _ _ (evalPMate R φ f n) (evalPMate_isIso R φ f n)

/-- The exact-level open-extension adjunction.
Source: Stacks 03DI, 07A6 (blueprint: def-sp-varying-ring-operations). -/
def levelJAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  Adjunction.ofNatIsoRight
    ((StrictTower.moduleJAdj (R n) j).mapDerivedCategoryRightDerivedAdjunction)
      (StrictTower.modulePullback (R n) j).rightDerivedFunctorIsoMapDerivedCategory

/-- The open-extension evaluation comparison is fixed by the pullback comparison.
Source: Stacks 03DI; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def evalJInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    ev R φ U n ⋙ (StrictTower.moduleJ (R n) j).mapDerivedCategory ⟶
      J R φ j ⋙ ev R φ X n :=
  (mateEquiv (jAdj R φ j) (levelJAdj R j n)).symm (evalG R φ j n).hom

/-- The open-extension mate is the localization of the coefficientwise lift map.
Source: Stacks 03DI, 03DJ (blueprint: def-sp-varying-ring-operations).
Proof: in the localized direct-sum extension each lift keeps its label and section.
Evaluation at n commutes with this presheaf and with sheafification. The resulting
ordinary isomorphism descends termwise, and its adjoint comparison is moduleEvalG,
so the derived mate is evalJInv. -/
theorem evalJInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    IsIso (evalJInv R φ j n) := by
  sorry

/-- Derived open evaluation with its specified unit normalization.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
def evalJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  (@asIso _ _ _ _ (evalJInv R φ j n) (evalJInv_isIso R φ j n)).symm

end AlgebraicGeometry.ProEtale.VaryingRing
