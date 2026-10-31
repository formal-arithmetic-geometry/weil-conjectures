/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.CtfCoefficientStageSelectors
public import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionFormula
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
import WeilConjectures.SixFunctors.CtfStabilityDirectImages
import WeilConjectures.AlgebraicGeometry.CompactificationCoherenceCocycle
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The chosen finite-Tor restrictions at the four coefficient stages

Source: main-20261015, sec-six-functors, det-thm-sf-ctf-stability-adjunctions;
fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: det-thm-sf-ctf-stability-adjunctions).

All categories and operations below are the recorded ones. Restriction functors and
adjunctions are constructed using the full inclusions. No choice from an existence
theorem defines a functor or a morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u a b c d a₀ b₀ c₀ d₀
open CategoryTheory AlgebraicGeometry Opposite
namespace WeilConjectures



/-- Chosen closed data on the actual finite-Tor domain, together with preservation
proofs for the four specified functors. The tensor comparison identifies this closed
presentation with the recorded tensor; it does not supply a different tensor.
Source: all three restricted adjunctions
(blueprint: det-thm-sf-ctf-stability-adjunctions). -/
structure PodCtfAdjunctionData
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type a}
    [∀ X, Category.{b} (B X)] (O : SixFunctorPushStage D B)
    (P : ∀ X, ObjectProperty (B X))
    (J : ∀ X, ObjectProperty ((B X)ᵒᵖ × B X))
    (H : ∀ X, (J X).FullSubcategory ⥤ B X)
    (T : ∀ X, B X ⥤ (P X).FullSubcategory ⥤ B X)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) where
  pullDomain : ∀ K : (P Y).FullSubcategory, P X ((O.pull f).obj K.obj)
  directDomain : ∀ K : (P X).FullSubcategory, P Y ((O.direct f).obj K.obj)
  supportDomain : ∀ K : (P X).FullSubcategory, P Y ((O.support f c).obj K.obj)
  exceptionalDomain : ∀ K : (P Y).FullSubcategory, P X ((O.exceptional f c).obj K.obj)
  closedX : SixFunctorClosedDomain (P X) (J X) (H X)
  closedY : SixFunctorClosedDomain (P Y) (J Y) (H Y)
  tensorX : ∀ K : (P X).FullSubcategory,
    @MonoidalCategory.tensorLeft _ _ closedX.closed.monoidal K ⋙ (P X).ι ≅
      (T X).obj K.obj
  tensorY : ∀ K : (P Y).FullSubcategory,
    @MonoidalCategory.tensorLeft _ _ closedY.closed.monoidal K ⋙ (P Y).ι ≅
      (T Y).obj K.obj

namespace PodCtfAdjunctionData
variable {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type a}
  [∀ X, Category.{b} (B X)] {O : SixFunctorPushStage D B}
  {P : ∀ X, ObjectProperty (B X)} {J : ∀ X, ObjectProperty ((B X)ᵒᵖ × B X)}
  {H : ∀ X, (J X).FullSubcategory ⥤ B X}
  {T : ∀ X, B X ⥤ (P X).FullSubcategory ⥤ B X}
  {X Y : SixFunctorSpace D} {f : X ⟶ Y} {c : Compactification f.hom.left}
  (R : PodCtfAdjunctionData O P J H T f c)

/-- Restricted pullback, constructed on objects and arrows by full inclusion.
Source: adjunction (1) (blueprint: det-thm-sf-ctf-stability-adjunctions). -/
def pull := sixFunctorDomainChange (P Y) (P X) (O.pull f) R.pullDomain
/-- Restricted direct image, constructed on objects and arrows by full inclusion.
Source: adjunction (1) (blueprint: det-thm-sf-ctf-stability-adjunctions). -/
def direct := sixFunctorDomainChange (P X) (P Y) (O.direct f) R.directDomain
/-- Restricted compact support, with the original compactification.
Source: adjunction (3) (blueprint: det-thm-sf-ctf-stability-adjunctions). -/
def support := sixFunctorDomainChange (P X) (P Y) (O.support f c) R.supportDomain
/-- Restricted exceptional inverse image, with the original compactification.
Source: adjunction (3) (blueprint: det-thm-sf-ctf-stability-adjunctions). -/
def exceptional := sixFunctorDomainChange (P Y) (P X) (O.exceptional f c) R.exceptionalDomain

/-- The ordinary restricted adjunction, exactly the fully faithful restriction.
Source: adjunction (1) (blueprint: det-thm-sf-ctf-stability-adjunctions). -/
def ordinaryAdjunction : R.pull ⊣ R.direct :=
  (O.pullDirectAdjunction f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Iso.refl _) (Iso.refl _)

/-- The exceptional restricted adjunction, exactly the fully faithful restriction.
Source: adjunction (3) (blueprint: det-thm-sf-ctf-stability-adjunctions). -/
def exceptionalAdjunction : R.support ⊣ R.exceptional :=
  (O.exceptionalAdjunction f c).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Iso.refl _) (Iso.refl _)

/-- Left-factor tensor-Hom adjunction, using the closed presentation's signed symmetry.
Source: adjunction (2) and the convention in fix-lem-tensor-adjunction, Step 1
(blueprint: det-thm-sf-ctf-stability-adjunctions). -/
def tensorAdjunctionX (M : (P X).FullSubcategory) :=
  (R.closedX.closed.adjunction M).ofNatIsoLeft
    (@BraidedCategory.tensorLeftIsoTensorRight _ _ R.closedX.closed.monoidal
      R.closedX.symmetric.toBraidedCategory M).symm

/-- Left-factor tensor-Hom adjunction on the target's actual finite-Tor category.
Source: adjunction (2) and the convention in fix-lem-tensor-adjunction, Step 1
(blueprint: det-thm-sf-ctf-stability-adjunctions). -/
def tensorAdjunctionY (M : (P Y).FullSubcategory) :=
  (R.closedY.closed.adjunction M).ofNatIsoLeft
    (@BraidedCategory.tensorLeftIsoTensorRight _ _ R.closedY.closed.monoidal
      R.closedY.symmetric.toBraidedCategory M).symm
end PodCtfAdjunctionData


end WeilConjectures


namespace WeilConjectures
/-- Compatibility with an ambient adjunction means that full inclusions preserve
its Hom bijection, with the stated comparison isomorphisms. Source: the words
"as the restriction" in clauses (1)--(3)
(blueprint: det-thm-sf-ctf-stability-adjunctions). -/
def podCompatibleRestriction
    {A : Type a} {B : Type b} {A₀ : Type a₀} {B₀ : Type b₀}
    [Category.{c} A] [Category.{d} B] [Category.{c₀} A₀] [Category.{d₀} B₀]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (iA : A₀ ⥤ A) (iB : B₀ ⥤ B) : Prop :=
  ∃ (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ A₀)
    (α : F₀ ⋙ iB ≅ iA ⋙ F) (β : G₀ ⋙ iA ≅ iB ⋙ G) (adj₀ : F₀ ⊣ G₀),
    ∀ (K : A₀) (L : B₀) (h : F₀.obj K ⟶ L),
      iA.map (adj₀.homEquiv K L h) =
        adj.homEquiv (iA.obj K) (iB.obj L) (α.inv.app K ≫ iB.map h) ≫ β.inv.app L

private theorem compatible_of_fullyFaithful
    {A : Type a} {B : Type b} {A₀ : Type a₀} {B₀ : Type b₀}
    [Category.{c} A] [Category.{d} B] [Category.{c₀} A₀] [Category.{d₀} B₀]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (iA : A₀ ⥤ A) (iB : B₀ ⥤ B)
    (hA : iA.FullyFaithful) (hB : iB.FullyFaithful)
    (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ A₀)
    (α : F₀ ⋙ iB ≅ iA ⋙ F) (β : G₀ ⋙ iA ≅ iB ⋙ G) :
    podCompatibleRestriction adj iA iB := by
  refine ⟨F₀, G₀, α, β, adj.restrictFullyFaithful hA hB α.symm β.symm, ?_⟩
  intro K L h
  rw [Adjunction.restrictFullyFaithful_homEquiv_apply, hA.map_preimage]
  simp only [Iso.symm_hom, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private theorem compatible_of_preserves
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (P : ObjectProperty A) (Q : ObjectProperty B)
    (hF : ∀ K, P K → Q (F.obj K)) (hG : ∀ L, Q L → P (G.obj L)) :
    podCompatibleRestriction adj P.ι Q.ι := by
  exact compatible_of_fullyFaithful adj P.ι Q.ι P.fullyFaithfulι Q.fullyFaithfulι
    (Q.lift (P.ι ⋙ F) (fun K ↦ hF K.obj K.property))
    (P.lift (Q.ι ⋙ G) (fun L ↦ hG L.obj L.property)) (Iso.refl _) (Iso.refl _)

end WeilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme

/-- The original general admissible-coefficient restricted-adjunction statement.
Each clause includes the ambient Hom bijection, rather than bare existence of
an unrelated adjunction. Source: main-20261015,
det-thm-sf-ctf-stability-adjunctions, all three clauses
(blueprint: det-thm-sf-ctf-stability-adjunctions).

Proof plan: full inclusions and ObjectProperty.lift restrict the ambient functors
using det-thm-sf-ctf-stability-direct-images and
 det-thm-sf-ctf-stability-internal-hom. Apply Adjunction.restrictFullyFaithful;
its homEquiv formula proves podCompatibleRestriction. Transport tensor-Hom by
the signed symmetry to obtain right-factor tensor. For exceptional adjunctions,
use sk-prop-sf-existence at the direct-image preservation compactification and
transport to each boundary compactification by det-sf-comp-coherence-cocycle.
The fully faithful inclusion of Dctf in its localizing closure is the canonical
intersection inclusion ObjectProperty.ιOfLE, so the same restriction formula applies.
The lower shriek is the recorded localizingLowerShriek of def-sf-localizing-lower-shriek.
-/
theorem podGeneralCtfAdjunctions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    WeilConjectures.podCompatibleRestriction (derivedUpperStarLowerStarAdjunction Λ f)
      (constantModelBoundedConstructible Λ Y ⊓
        fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).ι
      (constantModelBoundedConstructible Λ X ⊓
        fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).ι ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ X,
      WeilConjectures.podCompatibleRestriction
        ((derivedTensorHomAdjunction Λ K.obj).ofNatIsoLeft
          (@BraidedCategory.tensorLeftIsoTensorRight _ _ _
            (_root_.DerivedCategory.braidedCategory' _) K.obj))
        (constantModelBoundedConstructible Λ X ⊓
          fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M).ι
        (constantModelBoundedConstructible Λ X ⊓
          fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M).ι) ∧
    (∀ c : Compactification.BoundaryCompactification f,
      ∃ (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
          ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
        (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
          (localizingClosureProEtale Λ X).FullSubcategory)
        (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G),
        WeilConjectures.podCompatibleRestriction adj
          (ObjectProperty.ιOfLE (fun K hK _P _hP hSP ↦ hSP K hK) :
            ConstantModelConstructibleFiniteTor Λ X ⥤
              (localizingClosureProEtale Λ X).FullSubcategory)
          (ObjectProperty.ιOfLE (fun K hK _P _hP hSP ↦ hSP K hK) :
            ConstantModelConstructibleFiniteTor Λ Y ⥤
              (localizingClosureProEtale Λ Y).FullSubcategory)) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated
    (Y ↘ Spec (.of k))
  obtain ⟨hpull, htensor, _, hdirect, hsupport, hexceptional⟩ :=
    constructibleFiniteTor_stability_direct_images (hcd := hcd) ℓ k Λ _hΛ f
  refine ⟨?_, ?_, ?_⟩
  · exact WeilConjectures.compatible_of_preserves
      (derivedUpperStarLowerStarAdjunction Λ f) _ _ hpull hdirect
  · intro K
    apply WeilConjectures.compatible_of_preserves
      ((derivedTensorHomAdjunction Λ K.obj).ofNatIsoLeft
        (@BraidedCategory.tensorLeftIsoTensorRight _ _ _
          (_root_.DerivedCategory.braidedCategory' _) K.obj))
    · intro M hM
      exact htensor M K.obj hM K.property
    · intro L hL
      exact (internalHom_stability (hcd := hcd) Λ ℓ k _hΛ K.obj L K.property hL).1
  · let c₀ := @HasCompactification.compactification X Y f
      (HasCompactification.of_isOver (S := Spec (.of k)) f)
    have hqc : QuasiCompact c₀.i :=
      (Compactification.quasiCompact_openImmersion_iff c₀).mpr inferInstance
    let b₀ : Compactification.BoundaryCompactification f := ⟨⟨c₀, hqc⟩⟩
    obtain ⟨h₀, _, _, _, _, _, _, G, _, _, _, adj₀, _⟩ :=
      exists_localizingExceptionalAdjoint (hcd := hcd) Λ ℓ k f b₀ _hΛ
    let P := constantModelBoundedConstructible Λ X ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K
    let Q := constantModelBoundedConstructible Λ Y ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K
    let iX : P.FullSubcategory ⥤ (localizingClosureProEtale Λ X).FullSubcategory :=
      ObjectProperty.ιOfLE (fun K hK _P _hP hSP ↦ hSP K hK)
    let iY : Q.FullSubcategory ⥤ (localizingClosureProEtale Λ Y).FullSubcategory :=
      ObjectProperty.ιOfLE (fun K hK _P _hP hSP ↦ hSP K hK)
    let F₀ : P.FullSubcategory ⥤ Q.FullSubcategory :=
      Q.lift (P.ι ⋙ rightDerivedLowerShriekOfCompactification Λ c₀)
        (fun K ↦ hsupport K.obj K.property)
    let G₀ : Q.FullSubcategory ⥤ P.FullSubcategory :=
      P.lift (iY ⋙ G ⋙ (localizingClosureProEtale Λ X).ι)
        (fun K ↦ hexceptional h₀ G adj₀ K.obj K.property)
    have hcoherence := compactification_coherence_cocycle Λ ℓ _hΛ k f
    obtain ⟨φ, _⟩ := hcoherence
    intro c
    obtain ⟨h, _, _, _⟩ := exists_localizingExceptionalAdjoint (hcd := hcd) Λ ℓ k f c _hΛ
    let e : localizingLowerShriek Λ c₀ h₀ ≅ localizingLowerShriek Λ c.obj.obj h :=
      ((localizingClosureProEtale Λ Y).fullyFaithfulι.whiskeringRight _).preimageIso
        (φ b₀ c)
    let adj := adj₀.ofNatIsoLeft e
    refine ⟨h, G, adj, ?_⟩
    exact WeilConjectures.compatible_of_fullyFaithful adj iX iY
      (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _)
      F₀ G₀ (Functor.isoWhiskerLeft iX e) (Iso.refl _)

end AlgebraicGeometry.ProEtale.CondensedRing
