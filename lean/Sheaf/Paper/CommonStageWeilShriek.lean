/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.Paper.WeilCompactSupportCohomology
public import Sheaf.Paper.CompactSupportCoefficientAction
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.SfRationalDirectImageAdjunction
import Sheaf.Paper.ProperSupportCoefficientAdjunction
import Sheaf.Paper.ProperSupportFiniteAdjunction
import Sheaf.Paper.ZlFrobeniusCompactSupportComparison
import Sheaf.Paper.ZlOpenWeilUnitEmptyFibre
import Sheaf.Paper.CompactSupportFiniteFieldIndependence
import Sheaf.Paper.CommonStagePullbackIdentity
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Compact support with canonical Frobenius comparison

Source: blueprint main-20261015, lem-zl-shriek-composition and
lem-fix-weil-operations; SGA 4, XVII, §5--6
(blueprint: def-zl-common-stage-weil-shriek).

Open extension and proper image are adjoints of the existing common-stage pullback.
Their Frobenius comparisons are specified mates of its normalized Frobenius square.
Their composite is identified naturally with the recorded compact-support action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

-- The inverse-square argument also used by the private Frobenius helper in
-- SfCommonStageDirectImage; no separatedness hypothesis is needed.
private theorem zlShriekFrobenius_isEquivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).IsEquivalence := by
  let := sfWeilPrimeInvertible D l hl X₀
  let e := D.geometricFrobenius X₀
  let X := (D.geometricFiber X₀).left
  have : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
    inferInstanceAs (LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact (D.geometricFiber X₀).hom :=
    inferInstanceAs (QuasiCompact
      (CategoryTheory.Limits.pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber X₀).hom
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber X₀).hom
  have : IsNoetherian X := ⟨⟩
  have : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n) :=
    ⟨AlgebraicGeometry.exists_topologicalKrullDim_le (D.geometricFiber X₀).hom⟩
  have : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x)) := ⟨fun x ↦ by
    apply isUnit_of_map_unit (IsLocalRing.residue (X.presheaf.stalk x))
    simpa only [map_natCast] using (isUnit_of_invertible (l : X.residueField x))⟩
  obtain ⟨S, hs, _⟩ := rationalCoefficientCategoryComparison l Ω D hl
  let unit : commonStageDerivedPullback l Ω (𝟙 X) ≅ 𝟭 _ :=
    eqToIso (congrArg₂ (fun hX hY ↦
      @commonStageDerivedPullback l _ Ω _ _ _ X X (𝟙 X) hX hY)
      (Subsingleton.elim (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
        (fun x ↦ fdResidueInvertible l X x))
      (Subsingleton.elim (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
        (fun x ↦ fdResidueInvertible l X x))) ≪≫
      (commonStageDerivedPullback_identity l Ω S hs X).some
  let c₁ : commonStageDerivedPullback l Ω e.hom ⋙
      commonStageDerivedPullback l Ω e.inv ≅ 𝟭 _ :=
    (zlPullComp l Ω e.inv e.hom).symm ≪≫
      eqToIso (congrArg (fun f ↦ commonStageDerivedPullback l Ω f) e.inv_hom_id) ≪≫ unit
  let c₂ : commonStageDerivedPullback l Ω e.inv ⋙
      commonStageDerivedPullback l Ω e.hom ≅ 𝟭 _ :=
    (zlPullComp l Ω e.hom e.inv).symm ≪≫
      eqToIso (congrArg (fun f ↦ commonStageDerivedPullback l Ω f) e.hom_inv_id) ≪≫ unit
  exact Functor.IsEquivalence.mk' (commonStageDerivedPullback l Ω e.inv) c₁.symm c₂

private theorem stagePullFamily_eq
    (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X))
    (hΦ : L.Φ = (fun E ↦ rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f))
    (hβ : ∀ (E F : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ F)
      (K : sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y),
      HEq ((L.β h).app K) (commonStagePullbackComparison l Ω f ⟨E, K⟩ F h)) :
    L.functor = commonStageDerivedPullback l Ω f := by
  apply (commonStageDerivedPullback_existsUnique l Ω f).unique
    (y₁ := L.functor)
  · rcases L with ⟨Φ, β, coh⟩
    dsimp only at hΦ
    subst Φ
    constructor
    · intro P
      rfl
    · intro P Q F hP hQ k
      apply heq_of_eq
      change StageSystem.PairCategory.mkHom
        (X := commonStagePullbackObject l Ω f P)
        (Y := commonStagePullbackObject l Ω f Q) F hP hQ
        ((β hP).hom.app P.obj ≫
          (rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
            f).map k ≫ (β hQ).inv.app Q.obj) = _
      have hp := congrArg Iso.hom (eq_of_heq (hβ P.stage F hP P.obj))
      have hq := congrArg Iso.inv (eq_of_heq (hβ Q.stage F hQ Q.obj))
      dsimp only [Iso.app_hom, Iso.app_inv] at hp hq
      rw [hp, hq]
  · exact (commonStageDerivedPullback_existsUnique l Ω
      f).exists.choose_spec


private instance properFiber {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (p : X₀ ⟶ Y₀) [IsProper p.left] : IsProper (zlFiberMap D p) :=
  MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) p inferInstance

private theorem recordedProperAdjunction
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (p : X₀ ⟶ Y₀) [IsProper p.left]
    (S : SfCompactSupportCoefficientAction l D.k (zlClosurePrimeUnit D l hl) Ω
      (Compactification.ofIsProper (zlFiberMap D p))) :
    Nonempty (zlPull D l hl Ω p ⊣ S.system.functor) := by
  let : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  let : ∀ x : (D.geometricFiber Y₀).left,
      Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl Y₀
  obtain ⟨L, _, hΦ, hβ, _⟩ :=
    sfRationalDirectImageAdjunctions D l hl Ω p
  have hf : ∀ E, Nonempty (L.Φ E ⊣ S.system.Φ E) := by
    intro E
    rw [congrFun hΦ E, S.finite_eq E]
    exact properSupportFiniteAdjunction D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) (zlFiberMap D p)
  let a₀ E := (hf E).some
  obtain ⟨e, hc⟩ := properSupportCoefficientAdjunction D l hl Ω
    (zlFiberMap D p) S L hΦ hβ a₀
  let a E := (a₀ E).ofNatIsoRight (e E)
  let η := DirectImageAdjunction.mateFamilyUnit L (fun E ↦ S.system.Φ E) a
    (fun h ↦ S.system.β h) hc
  let ε := DirectImageAdjunction.mateFamilyCounit L (fun E ↦ S.system.Φ E) a
    (fun h ↦ S.system.β h) hc
  have adj := descendStageAdjunction L
    (DirectImageAdjunction.mateFamily L (fun E ↦ S.system.Φ E) a
      (fun h ↦ S.system.β h) hc) a η ε (fun _ ↦ rfl) (fun _ ↦ rfl)
  change L.functor ⊣ S.system.functor at adj
  have hF := stagePullFamily_eq l Ω (zlFiberMap D p) L hΦ hβ
  rw [hF] at adj
  exact ⟨adj⟩

private theorem recordedSupportComposition
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [h.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (e : h = f ≫ g)
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification h)
    (Sf : SfCompactSupportCoefficientAction l D.k (zlClosurePrimeUnit D l hl) Ω cf)
    (Sg : SfCompactSupportCoefficientAction l D.k (zlClosurePrimeUnit D l hl) Ω cg)
    (Sh : SfCompactSupportCoefficientAction l D.k (zlClosurePrimeUnit D l hl) Ω ch) :
    Nonempty (Sf.system.functor ⋙ Sg.system.functor ≅ Sh.system.functor) := by
  subst h
  exact ⟨(sfFieldShriekCompositionQbar_existsUnique D l hl cf cg ch Ω
    Sf Sg Sh).exists.choose⟩

section Proper
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left]

/-- Proper inverse image has its constructible direct-image right adjoint.
Source: SGA 4, XVII, §5; blueprint lem-fix-weil-operations
(blueprint: def-zl-common-stage-weil-shriek).
Proof: proper direct image preserves bounded constructibility at every finite level.
Apply it to the coherent completed tower, rationalize, and descend through the
common-stage coefficient comparisons. The ordinary pullback/direct-image adjunction
restricts to the complete constructible categories and then localizes. Its Hom
bijections commute with finite coefficient extension; at a common finite field they
therefore give the adjunction on every common-stage Hom group. -/
theorem zlPull_proper_isLeftAdjoint : (zlPull D l hl Ω p₀).IsLeftAdjoint := by
  have _ : IsProper p₀.left := inferInstance
  exact sfModelPull_isLeftAdjoint D l hl Ω p₀

/-- Proper image selected by its adjunction to the recorded inverse image.
Source: SGA 4, XVII, §5 (blueprint: def-zl-common-stage-weil-shriek). -/
def zlCommonStageProperPush :=
  letI := zlPull_proper_isLeftAdjoint D l hl Ω p₀
  (zlPull D l hl Ω p₀).rightAdjoint

/-- The adjunction determining the proper image, including its unit and counit.
Source: SGA 4, XVII, §5 (blueprint: def-zl-common-stage-weil-shriek). -/
def zlCommonStageProperAdjunction :
    zlPull D l hl Ω p₀ ⊣ zlCommonStageProperPush D l hl Ω p₀ :=
  letI := zlPull_proper_isLeftAdjoint D l hl Ω p₀
  Adjunction.ofIsLeftAdjoint (zlPull D l hl Ω p₀)

/-- The proper Frobenius exchange is the specified counit mate of inverse-image exchange.
Source: blueprint lem-fix-weil-operations, first paragraph
(blueprint: def-zl-common-stage-weil-shriek). -/
def zlProperFrobeniusMap :
    zlCommonStageProperPush D l hl Ω p₀ ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ⟶
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙ zlCommonStageProperPush D l hl Ω p₀ :=
  (mateEquiv (zlCommonStageProperAdjunction D l hl Ω p₀)
    (zlCommonStageProperAdjunction D l hl Ω p₀)
    (TwoSquare.mk _ _ _ _ (zlFrobeniusSquare D l hl Ω p₀).inv)).natTrans

/-- The proper exchange for the geometric-Frobenius automorphism square is invertible.
Source: blueprint lem-fix-weil-operations, inverse automorphism squares
(blueprint: def-zl-common-stage-weil-shriek).
Proof: inverse image along geometric Frobenius is an equivalence, with inverse the
arithmetic-Frobenius pullback. Form the mate for its inverse square. The normalized
pullback composition identities identify both pasted squares with identity squares.
Mate pasting then makes their two composites identity transformations. Thus the
specified proper exchange, rather than an arbitrary comparison, is invertible. -/
theorem zlProperFrobeniusMap_isIso : IsIso (zlProperFrobeniusMap D l hl Ω p₀) := by
  let := zlShriekFrobenius_isEquivalence D l hl Ω X₀
  let := zlShriekFrobenius_isEquivalence D l hl Ω Y₀
  exact isIso_mateEquiv_of_isEquivalence _ _
    (TwoSquare.mk _ _ _ _ (zlFrobeniusSquare D l hl Ω p₀).inv)

/-- Proper Frobenius exchange with its actual mate as forward map.
Source: blueprint lem-fix-weil-operations (blueprint: def-zl-common-stage-weil-shriek). -/
def zlProperFrobenius :
    zlCommonStageProperPush D l hl Ω p₀ ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙ zlCommonStageProperPush D l hl Ω p₀ :=
  letI := zlProperFrobeniusMap_isIso D l hl Ω p₀
  asIso (zlProperFrobeniusMap D l hl Ω p₀)
end Proper

section Open
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left]

/-- Open inverse image has constructible extension by zero as its left adjoint.
Source: SGA 4, XVII, §5; blueprint lem-fix-weil-operations
(blueprint: def-zl-common-stage-weil-shriek).
Proof: the finite-type schemes are Noetherian, so the open immersion is quasi-compact.
Exact extension by zero preserves constructibility at every positive coefficient
level. Apply it to the completed tower and its quotient maps. The open adjunction
restricts to complete constructible inputs. Rational localization and the compatible
coefficient-extension units descend its Hom bijections to the common-stage category.
The resulting left adjoint is the usual open extension, on all objects and maps. -/
theorem zlPull_open_isRightAdjoint : (zlPull D l hl Ω j₀).IsRightAdjoint := by
  obtain ⟨I, R, h, hS⟩ := ZlOpenUnit.openWeilUnitAndEmptyFibre D l hl Y₀ X₀ j₀ Ω
  let := sfWeilPrimeInvertible D l hl X₀
  let := sfWeilPrimeInvertible D l hl Y₀
  have : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    zlGeometricFiber_finiteType D X₀
  have : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    zlGeometricFiber_quasiCompact D X₀
  have : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    zlGeometricFiber_finiteType D Y₀
  have : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    zlGeometricFiber_quasiCompact D Y₀
  have : (zlFiberMap D j₀).IsOver (Spec (.of D.k)) := zlFiberMap_isOver D j₀
  have : IsOpenImmersion (zlFiberMap D j₀) :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance
  have : IsLocallyNoetherian (D.geometricFiber Y₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((D.geometricFiber Y₀).left ↘ Spec (.of D.k))
  have : CompactSpace (D.geometricFiber Y₀).left :=
    QuasiCompact.compactSpace_of_compactSpace ((D.geometricFiber Y₀).left ↘ Spec (.of D.k))
  obtain ⟨S, _⟩ := sfCompactSupportFiniteFieldIndependence l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) Ω
    (Compactification.ofIsOpenImmersion (zlFiberMap D j₀))
  obtain ⟨Q, _⟩ := hS S
  exact Q.adj.isRightAdjoint

/-- Open extension selected by its adjunction to the recorded inverse image.
Source: SGA 4, XVII, §5 (blueprint: def-zl-common-stage-weil-shriek). -/
def zlCommonStageOpenShriek :=
  letI := zlPull_open_isRightAdjoint D l hl Ω j₀
  (zlPull D l hl Ω j₀).leftAdjoint

/-- The open adjunction determining extension by zero, including its unit and counit.
Source: SGA 4, XVII, §5 (blueprint: def-zl-common-stage-weil-shriek). -/
def zlCommonStageOpenAdjunction :
    zlCommonStageOpenShriek D l hl Ω j₀ ⊣ zlPull D l hl Ω j₀ :=
  letI := zlPull_open_isRightAdjoint D l hl Ω j₀
  Adjunction.ofIsRightAdjoint (zlPull D l hl Ω j₀)

/-- Inverse open Frobenius exchange is the left mate of the normalized pullback square.
Source: blueprint lem-fix-weil-operations, open extension paragraph
(blueprint: def-zl-common-stage-weil-shriek). -/
def zlOpenFrobeniusInverseMap :
    sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙ zlCommonStageOpenShriek D l hl Ω j₀ ⟶
      zlCommonStageOpenShriek D l hl Ω j₀ ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω :=
  ((mateEquiv (zlCommonStageOpenAdjunction D l hl Ω j₀)
    (zlCommonStageOpenAdjunction D l hl Ω j₀)).symm
    (TwoSquare.mk _ _ _ _ (zlFrobeniusSquare D l hl Ω j₀).hom)).natTrans

/-- The specified open mate is invertible for the geometric-Frobenius square.
Source: blueprint lem-fix-weil-operations, inverse automorphism squares
(blueprint: def-zl-common-stage-weil-shriek).
Proof: form the left mate for the inverse Frobenius square. Frobenius and its inverse
are scheme automorphisms, so their normalized pullback squares paste to identity.
The left-mate pasting identities identify both composites with the identity. Hence
this inverse open exchange is invertible on the whole common-stage category. -/
theorem zlOpenFrobeniusInverseMap_isIso :
    IsIso (zlOpenFrobeniusInverseMap D l hl Ω j₀) := by
  let := zlShriekFrobenius_isEquivalence D l hl Ω X₀
  let := zlShriekFrobenius_isEquivalence D l hl Ω Y₀
  exact isIso_inverseMate_of_equivalences _ _ (zlFrobeniusSquare D l hl Ω j₀)

/-- Open Frobenius exchange, inverse to the specified left mate.
Source: blueprint lem-fix-weil-operations (blueprint: def-zl-common-stage-weil-shriek). -/
def zlOpenFrobenius :
    zlCommonStageOpenShriek D l hl Ω j₀ ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙ zlCommonStageOpenShriek D l hl Ω j₀ :=
  letI := zlOpenFrobeniusInverseMap_isIso D l hl Ω j₀
  (asIso (zlOpenFrobeniusInverseMap D l hl Ω j₀)).symm
end Open

section CompactSupport
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left)

/-- Apply open extension first, then proper derived image, in the common-stage category.
Source: SGA 4, XVII, §5--6; blueprint lem-zl-shriek-composition
(blueprint: def-zl-common-stage-weil-shriek). -/
def zlCommonStageShriek :=
  letI : IsProper (zlCompactificationProper D f₀ c).left :=
    inferInstanceAs (IsProper c.g)
  zlCommonStageOpenShriek D l hl Ω (zlCompactificationOpen D f₀ c) ⋙
    zlCommonStageProperPush D l hl Ω (zlCompactificationProper D f₀ c)

/-- The composite proper/open Frobenius exchange, with canonical mate factors.
Source: blueprint lem-fix-weil-operations, compact-support paragraph
(blueprint: def-zl-common-stage-weil-shriek). -/
def zlShriekFrobenius :
    zlCommonStageShriek D l hl Ω f₀ c ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙ zlCommonStageShriek D l hl Ω f₀ c :=
  letI : IsProper (zlCompactificationProper D f₀ c).left :=
    inferInstanceAs (IsProper c.g)
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (zlProperFrobenius D l hl Ω (zlCompactificationProper D f₀ c)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (zlOpenFrobenius D l hl Ω (zlCompactificationOpen D f₀ c)) _ ≪≫
    Functor.associator _ _ _

/-- Compact support on the existing fixed pairs. Its structure is Ex! followed by Rf!(theta).
Source: blueprint lem-fix-weil-operations (blueprint: def-zl-common-stage-weil-shriek). -/
def zlComplexShriek :
    sfCommonStageWeilComplex D l hl X₀ Ω ⥤ sfCommonStageWeilComplex D l hl Y₀ Ω :=
  IsoAlgebra.mapOfNatIso (zlShriekFrobenius D l hl Ω f₀ c)

/-- The underlying operation naturally agrees with every normalized compact-support action.
Source: Bhatt--Scholze 6.7.6--6.7.7; SGA 4, XVII, §5--6
(blueprint: def-zl-common-stage-weil-shriek).
Proof: proper image and open extension in the recorded coefficient construction satisfy
adjunction with the normalized inverse image. Uniqueness of adjoints identifies them
naturally with the two chosen adjoints above, on every object and morphism. Their
composite is the completed proper/open construction. Its projection-normalized tower
realization gives the integral compact-support action; localizing and applying the
specified tensor-unit coefficient comparisons gives the common-stage action S. Compare
the geometric base change of c with cg through a common proper refinement. Proper base
change and open unit mates identify their composites naturally. Compose these maps to
obtain the claimed natural isomorphism, without a restriction on representatives. -/
theorem zlCommonStageShriek_recorded [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (cg : Compactification (zlFiberMap D f₀))
    (S : SfCompactSupportCoefficientAction
      (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
      (f := zlFiberMap D f₀) l D.k (zlClosurePrimeUnit D l hl) Ω cg) :
    Nonempty (zlCommonStageShriek D l hl Ω f₀ c ≅ S.system.functor) := by
  let M := zlCompactificationMiddle D f₀ c
  let j := zlCompactificationOpen D f₀ c
  let p := zlCompactificationProper D f₀ c
  let : IsProper p.left := inferInstanceAs (IsProper c.g)
  let : IsProper (zlFiberMap D p) := zlGeometricCompactification_isProper D f₀ c
  let : IsOpenImmersion (zlFiberMap D j) :=
    zlGeometricCompactification_isOpenImmersion D f₀ c
  obtain ⟨Sj, _⟩ := sfCompactSupportFiniteFieldIndependence l D.k
    (zlClosurePrimeUnit D l hl) Ω
    (Compactification.ofIsOpenImmersion (zlFiberMap D j))
  obtain ⟨Sp, _⟩ := sfCompactSupportFiniteFieldIndependence l D.k
    (zlClosurePrimeUnit D l hl) Ω
    (Compactification.ofIsProper (zlFiberMap D p))
  obtain ⟨_, _, _, hS⟩ := ZlOpenUnit.openWeilUnitAndEmptyFibre D l hl M X₀ j Ω
  obtain ⟨Q, _⟩ := hS Sj
  obtain ⟨ap⟩ := recordedProperAdjunction D l hl Ω p Sp
  let ej := (zlCommonStageOpenAdjunction D l hl Ω j).leftAdjointUniq Q.adj
  let ep := (zlCommonStageProperAdjunction D l hl Ω p).rightAdjointUniq ap
  obtain ⟨ec⟩ := recordedSupportComposition D l hl Ω
    (zlGeometricCompactification_comm D f₀ c)
    (Compactification.ofIsOpenImmersion (zlFiberMap D j))
    (Compactification.ofIsProper (zlFiberMap D p)) cg Sj Sp S
  exact ⟨Functor.isoWhiskerRight ej _ ≪≫ Functor.isoWhiskerLeft _ ep ≪≫ ec⟩
end CompactSupport

/-- Frobenius exchange for the iterated compact-support functor, in its actual order.
Source: blueprint lem-zl-shriek-composition, iterated Weil structure
(blueprint: def-zl-common-stage-weil-shriek). -/
def zlShriekCompositeFrobenius {X₀ Y₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (f₀ : X₀ ⟶ Y₀) (g₀ : Y₀ ⟶ Z₀)
    (cf : Compactification f₀.left) (cg : Compactification g₀.left) :
    (zlCommonStageShriek D l hl Ω f₀ cf ⋙ zlCommonStageShriek D l hl Ω g₀ cg) ⋙
        sfCommonStageWeilFrobeniusPullback D l hl Z₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙
        (zlCommonStageShriek D l hl Ω f₀ cf ⋙ zlCommonStageShriek D l hl Ω g₀ cg) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (zlShriekFrobenius D l hl Ω g₀ cg) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (zlShriekFrobenius D l hl Ω f₀ cf) _ ≪≫
    Functor.associator _ _ _

end WeilConjectures
