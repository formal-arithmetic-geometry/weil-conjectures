/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ConstructiblePullbackTExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Indization
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Opposites
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFullyFaithful
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.AlgebraicGeometry.CommonStageOpenHeartAdjunction
import WeilConjectures.AlgebraicGeometry.IsomorphismFieldTransport
import WeilConjectures.AlgebraicGeometry.CommonStagePullbackCompNaturality

/-! # Ambient equivariant ind-sheaves for the recorded common-stage Weil heart

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-l-dl-general-composition, lem-zl-composition-weight-bound.proof.md,
first paragraph; SGA 4, XVII, sheaf resolutions
(blueprint: def-zl-weil-ind-sheaf-category).

The underlying constructible heart is the existing common-stage heart. Ind-objects
are formed before taking Frobenius fixed pairs, retaining arbitrary Frobenius orbits.
The actual Weil heart embeds fully faithfully. All inverse-image comparisons are
normalized by the existing integral pullback composition and the Yoneda Kan unit.

## Main definitions

- `zlIndWeilHeart`.
- `zlWeilIndEmbedding`.
- `zlIndWeilPull`.
- `zlIndWeilPush`.
- `zlIndWeilOpenShriek`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The base-changed morphism, with the fixed closure of the finite field.
Source: blueprint composition proof, first paragraph
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlFiberMap {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- Pullback on geometric fibres, using exactly the recorded common-stage functor.
Source: blueprint composition proof, first paragraph
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlPull {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ (zlFiberMap D f₀)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y)

/-- The prescribed integral pullback composition, normalized by finite reductions.
Source: Stacks 099N(5), composition proof, first paragraph
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlIntegralPullComp (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (integralPullbackComposition l E).choose f g

/-- The literal integral-representative formula for common-stage pullback.
Source: blueprint rational and common-stage pullback prescription
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: expand commonStageDerivedPullback_existsUnique on objects, and then the
object clause of rationalDerivedPullback_existsUnique. Both identifications are
literal equalities; apply eqToIso. -/
theorem zlStagePull_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y) :
    (commonStageDerivedPullback l Ω f).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
          ((sfRationalConstructibleLocalization l _ Y).obj K)) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
        ((sfRationalConstructibleLocalization l _ X).obj
          ((constructibleIntegralPullback l _ f).obj K)) := by
  refine ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 _).trans ?_
  change (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
    ((rationalDerivedPullback l _ f).obj _) = _
  exact congrArg (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
    ((rationalDerivedPullback_existsUnique l _ f).exists.choose_spec.2.1 _)

/-- The object comparison is an equality comparison, never a chosen automorphism.
Source: blueprint common-stage pullback prescription
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlStagePullIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y) :=
  eqToIso (zlStagePull_eq l Ω f L K)



section CompositionProof
attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback
  constructibleIntegralPullback commonStagePullbackCompComponent
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence

/-- Descent of the normalized integral composition comparison.
Source: Stacks 099N(5); blueprint common-stage prescription
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: localize integralPullbackComposition, including its finite-reduction
normalization, on pure tensors. Its scalar compatibility descends this comparison
through the common-stage inclusions. The displayed equation specifies every
component, since every pair is an integral rationalized representative. Thus
naturality and uniqueness descend from the integral comparison, not from an
arbitrary natural isomorphism. -/
theorem zlPullComp_existsUnique {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! e : commonStageDerivedPullback l Ω (f ≫ g) ≅
        commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω f,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (K : sfIntegralConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Z),
        e.hom.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
            ((sfRationalConstructibleLocalization l _ Z).obj K)) ≫
          (commonStageDerivedPullback l Ω f).map (zlStagePullIso l Ω g L K).hom ≫
          (zlStagePullIso l Ω f L ((constructibleIntegralPullback l _ g).obj K)).hom =
        (zlStagePullIso l Ω (f ≫ g) L K).hom ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
            ((sfRationalConstructibleLocalization l _ X).map
              ((zlIntegralPullComp l _ f g).hom.app K)) := by
  let e : commonStageDerivedPullback l Ω (f ≫ g) ≅
      commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω f :=
    NatIso.ofComponents (F := commonStageDerivedPullback l Ω (f ≫ g))
      (G := commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω f)
      (commonStagePullbackCompComponent l Ω f g)
    (fun {_ _} a ↦ commonStagePullbackCompComponent_naturality l Ω f g a)
  have he (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Z) :
      e.hom.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
          ((sfRationalConstructibleLocalization l _ Z).obj K)) ≫
        (commonStageDerivedPullback l Ω f).map (zlStagePullIso l Ω g L K).hom ≫
        (zlStagePullIso l Ω f L ((constructibleIntegralPullback l _ g).obj K)).hom =
      (zlStagePullIso l Ω (f ≫ g) L K).hom ≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
          ((sfRationalConstructibleLocalization l _ X).map
            ((zlIntegralPullComp l _ f g).hom.app K)) := by
    apply eq_of_heq
    simp only [zlStagePullIso, eqToIso.hom, eqToHom_map, ← Category.assoc,
      comp_eqToHom_heq_iff, heq_eqToHom_comp_iff]
    dsimp only [zlIntegralPullComp]
    change HEq (commonStagePullbackCompComponent l Ω f g ⟨L, ⟨K⟩⟩).hom _
    exact commonStagePullbackCompComponent_heq.{u, v} l Ω f g ⟨L, ⟨K⟩⟩
  refine ⟨e, he, ?_⟩
  intro a ha
  apply Iso.ext
  apply NatTrans.ext
  funext P
  rcases P with ⟨L, ⟨K⟩⟩
  apply (cancel_mono
    ((commonStageDerivedPullback l Ω f).map (zlStagePullIso l Ω g L K).hom ≫
      (zlStagePullIso l Ω f L ((constructibleIntegralPullback l _ g).obj K)).hom)).1
  simpa only [Category.assoc, GeneralAlgebraicallyClosedCoefficients.inclusion,
    StageSystem.ι, sfRationalConstructibleLocalization, ScalarLocalization.localization]
    using (ha L K).trans (he L K).symm

end CompositionProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The uniquely normalized common-stage composition isomorphism.
Source: Stacks 099N(5), blueprint composition proof
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlPullComp {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (zlPullComp_existsUnique l Ω f g).exists.choose

/-- Geometric Frobenius is natural for a morphism defined over k₀.
Source: blueprint finite-field geometric fibre and composition proof
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: both maps are base changes of f₀ and the inverse q-power automorphism of
the chosen closure. Their equality follows from the pullback universal property;
semilinearity does not require either Frobenius to be k-linear. -/
theorem zlFrobenius_naturality {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (D.geometricFrobenius X₀).hom ≫ zlFiberMap D f₀ =
      zlFiberMap D f₀ ≫ (D.geometricFrobenius Y₀).hom := by
  apply pullback.hom_ext
  · simp [zlFiberMap, FiniteFieldDatum.geometricFrobenius,
      FiniteFieldDatum.galoisMap, Over.pullback_map_left, baseChangeMap, Category.assoc]
  · simp [zlFiberMap, FiniteFieldDatum.geometricFrobenius,
      FiniteFieldDatum.galoisMap, Over.pullback_map_left, baseChangeMap, Category.assoc]

/-- The canonical pullback square, composed from normalized composition comparisons.
Source: blueprint Frobenius equivariance of pullback
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlFrobeniusSquare {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    zlPull D l hl Ω f₀ ⋙ sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ⋙ zlPull D l hl Ω f₀ :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  (zlPullComp l Ω (D.geometricFrobenius X₀).hom (zlFiberMap D f₀)).symm ≪≫
    eqToIso (congrArg
      (fun f : (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left ↦
        commonStageDerivedPullback l Ω f) (zlFrobenius_naturality D f₀)) ≪≫
      zlPullComp l Ω (zlFiberMap D f₀) (D.geometricFrobenius Y₀).hom

/-- Pullback of a Weil heart object remains a Weil heart object.
Source: Bhatt--Scholze 6.8.11(3), blueprint composition proof
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: constructible_pullback_t_exact preserves both standard halves, hence their
intersection. IsoAlgebra.mapOfNatIso has the actual pulled-back carrier, so the
same heart condition proves the claim with its induced Frobenius structure. -/
theorem zlWeilPull_mem {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀)
    (K : sfCommonStageWeilSheaf D l hl Y₀ Ω) :
    sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
      (((IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f₀)).obj K.obj).carrier) := by
  let : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hc := (constructible_pullback_t_exact D l hl Ω (Classical.arbitrary _)
    (W := (D.geometricFiber X₀).left) (X := (D.geometricFiber Y₀).left)
    (zlFiberMap D f₀)).2
  dsimp only [ConstructibleCommonStagePullbackComparison] at hc
  have hX : constructiblePullbackResidueUnits D l hl (D.geometricFiber X₀).left =
      (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) := Subsingleton.elim _ _
  have hY : constructiblePullbackResidueUnits D l hl (D.geometricFiber Y₀).left =
      (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y) := Subsingleton.elim _ _
  rw [hX, hY] at hc
  obtain ⟨c⟩ := hc
  let A : sfCommonStageHeart l (D.geometricFiber Y₀).left Ω :=
    ⟨K.obj.carrier, K.property⟩
  have h : (c.heart.obj A).obj = (zlPull D l hl Ω f₀).obj A.obj :=
    congrArg (fun F : sfCommonStageHeart l (D.geometricFiber Y₀).left Ω ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left ↦
        F.obj A) c.heart_fac
  change sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
    ((zlPull D l hl Ω f₀).obj A.obj)
  have hp := (c.heart.obj A).property
  rw [← h]
  exact hp

/-- Canonical inverse image on the recorded Weil hearts; only the heart condition
is supplied by a theorem. The objects, morphisms and Frobenius actions are explicit.
Source: blueprint composition proof, first paragraph
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlWeilPull {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    sfCommonStageWeilSheaf D l hl Y₀ Ω ⥤ sfCommonStageWeilSheaf D l hl X₀ Ω :=
  ((sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω).inverseImage
    (sfCommonStageWeilForget D l hl X₀ Ω)).lift
      (((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω).inverseImage
        (sfCommonStageWeilForget D l hl Y₀ Ω)).ι ⋙
          IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f₀))
      (zlWeilPull_mem D l hl Ω f₀)

/-- Canonical pullback preserves the underlying constructible heart.
Source: Bhatt--Scholze 6.8.11(3), blueprint composition proof
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: apply constructible_pullback_t_exact to both standard halves. Their
intersection is precisely sfCommonStageHeartProperty. -/
theorem zlPull_mem {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀)
    (K : sfCommonStageHeart l (D.geometricFiber Y₀).left Ω) :
    sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
      ((zlPull D l hl Ω f₀).obj K.obj) := by
  let : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hc := (constructible_pullback_t_exact D l hl Ω (Classical.arbitrary _)
    (W := (D.geometricFiber X₀).left) (X := (D.geometricFiber Y₀).left)
    (zlFiberMap D f₀)).2
  dsimp only [ConstructibleCommonStagePullbackComparison] at hc
  have hX : constructiblePullbackResidueUnits D l hl (D.geometricFiber X₀).left =
      (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) := Subsingleton.elim _ _
  have hY : constructiblePullbackResidueUnits D l hl (D.geometricFiber Y₀).left =
      (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y) := Subsingleton.elim _ _
  rw [hX, hY] at hc
  obtain ⟨c⟩ := hc
  have h : (c.heart.obj K).obj = (zlPull D l hl Ω f₀).obj K.obj :=
    congrArg (fun F : sfCommonStageHeart l (D.geometricFiber Y₀).left Ω ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left ↦
        F.obj K) c.heart_fac
  change sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
    ((zlPull D l hl Ω f₀).obj K.obj)
  have hp := (c.heart.obj K).property
  rw [← h]
  exact hp

/-- The actual underlying heart inverse image.
Source: blueprint composition proof
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlHeartPull {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :=
  (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω).lift
    ((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω).ι ⋙
      zlPull D l hl Ω f₀) (zlPull_mem D l hl Ω f₀)

/-- Frobenius preserves the underlying heart.
Source: blueprint composition proof; Bhatt--Scholze 6.8.11(3)
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: apply t-exactness of isomorphism inverse image to geometric Frobenius.
The same argument for the inverse proves it is a heart equivalence. -/
theorem zlHeartFrobenius_mem (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : sfCommonStageHeart l (D.geometricFiber X₀).left Ω) :
    sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
      ((sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj K.obj) := by
  let : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hc := (constructible_pullback_t_exact D l hl Ω (Classical.arbitrary _)
    (W := (D.geometricFiber X₀).left) (X := (D.geometricFiber X₀).left)
    (D.geometricFrobenius X₀).hom).2
  dsimp only [ConstructibleCommonStagePullbackComparison] at hc
  have hX : constructiblePullbackResidueUnits D l hl (D.geometricFiber X₀).left =
      (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) := Subsingleton.elim _ _
  rw [hX] at hc
  obtain ⟨c⟩ := hc
  have h : (c.heart.obj K).obj = (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj K.obj :=
    congrArg (fun F : sfCommonStageHeart l (D.geometricFiber X₀).left Ω ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left ↦
        F.obj K) c.heart_fac
  change sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
    ((sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj K.obj)
  have hp := (c.heart.obj K).property
  rw [← h]
  exact hp

/-- Geometric Frobenius restricted to the actual underlying heart.
Source: blueprint composition proof
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlHeartFrobenius (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :=
  (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω).lift
    ((sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω).ι ⋙
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
    (zlHeartFrobenius_mem D l hl Ω X₀)

private theorem zlHeartPull_exact {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    PreservesFiniteLimits (zlHeartPull D l hl Ω f₀) ∧
      PreservesFiniteColimits (zlHeartPull D l hl Ω f₀) := by
  let : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hc := (constructible_pullback_t_exact D l hl Ω (Classical.arbitrary _)
    (W := (D.geometricFiber X₀).left) (X := (D.geometricFiber Y₀).left)
    (zlFiberMap D f₀)).2
  dsimp only [ConstructibleCommonStagePullbackComparison] at hc
  have hX : constructiblePullbackResidueUnits D l hl (D.geometricFiber X₀).left =
      (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) := Subsingleton.elim _ _
  have hY : constructiblePullbackResidueUnits D l hl (D.geometricFiber Y₀).left =
      (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y) := Subsingleton.elim _ _
  rw [hX, hY] at hc
  obtain ⟨c⟩ := hc
  let P := sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
  let e : c.heart ≅ zlHeartPull D l hl Ω f₀ :=
    (Functor.FullyFaithful.ofFullyFaithful P.ι).whiskeringRight _ |>.preimageIso
      (eqToIso c.heart_fac)
  let := c.heart_limits
  let := c.heart_colimits
  exact ⟨preservesFiniteLimits_of_natIso e, preservesFiniteColimits_of_natIso e⟩

private theorem zlHeartFrobenius_exact (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    PreservesFiniteLimits (zlHeartFrobenius D l hl Ω X₀) ∧
      PreservesFiniteColimits (zlHeartFrobenius D l hl Ω X₀) := by
  let : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hc := (constructible_pullback_t_exact D l hl Ω (Classical.arbitrary _)
    (W := (D.geometricFiber X₀).left) (X := (D.geometricFiber X₀).left)
    (D.geometricFrobenius X₀).hom).2
  dsimp only [ConstructibleCommonStagePullbackComparison] at hc
  have hX : constructiblePullbackResidueUnits D l hl (D.geometricFiber X₀).left =
      (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) := Subsingleton.elim _ _
  rw [hX] at hc
  obtain ⟨c⟩ := hc
  let P := sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
  let e : c.heart ≅ zlHeartFrobenius D l hl Ω X₀ :=
    (Functor.FullyFaithful.ofFullyFaithful P.ι).whiskeringRight _ |>.preimageIso
      (eqToIso c.heart_fac)
  let := c.heart_limits
  let := c.heart_colimits
  exact ⟨preservesFiniteLimits_of_natIso e, preservesFiniteColimits_of_natIso e⟩

/-- The unique heart lift of the normalized pullback square.
Source: blueprint composition proof, Frobenius equivariance
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: all four functors preserve the heart. Full faithfulness of its inclusion
lifts zlFrobeniusSquare and its inverse, proving existence, naturality and uniqueness. -/
theorem zlHeartSquare_existsUnique {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    ∃! e : zlHeartPull D l hl Ω f₀ ⋙ zlHeartFrobenius D l hl Ω X₀ ≅
        zlHeartFrobenius D l hl Ω Y₀ ⋙ zlHeartPull D l hl Ω f₀,
      ∀ K, (e.hom.app K).hom = (zlFrobeniusSquare D l hl Ω f₀).hom.app K.obj := by
  let e : zlHeartPull D l hl Ω f₀ ⋙ zlHeartFrobenius D l hl Ω X₀ ≅
      zlHeartFrobenius D l hl Ω Y₀ ⋙ zlHeartPull D l hl Ω f₀ :=
    NatIso.ofComponents (fun K ↦ (sfCommonStageHeartProperty l
      (D.geometricFiber X₀).left Ω).isoMk
        ((zlFrobeniusSquare D l hl Ω f₀).app K.obj))
      (fun a ↦ ObjectProperty.hom_ext _
        ((zlFrobeniusSquare D l hl Ω f₀).hom.naturality a.hom))
  refine ⟨e, fun _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact he' K

/-- The canonical heart square, with its specified underlying arrow.
Source: blueprint composition proof, Frobenius equivariance
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlHeartSquare {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :=
  (zlHeartSquare_existsUnique D l hl Ω f₀).exists.choose

/-- A small presentation of the underlying heart; the independent universes are retained.
Source: blueprint common-stage coefficient convention
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlSmallHeart (_hl : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :=
  AsSmall.{0} (sfCommonStageHeart l (D.geometricFiber X₀).left Ω)

/-- The inherited small category structure, with no change of Hom sets beyond ULift.
Source: blueprint common-stage size convention
(blueprint: def-zl-weil-ind-sheaf-category). -/
instance zlSmallHeartCategory (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    SmallCategory (zlSmallHeart D l Ω hl X₀) :=
  inferInstanceAs (SmallCategory
    (AsSmall.{0} (sfCommonStageHeart l (D.geometricFiber X₀).left Ω)))

/-- The small presentation is abelian.
Source: blueprint constructible-heart convention
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: sfCommonStageHeart_properties identifies the underlying heart with the heart
of the standard bounded t-structure and supplies its abelian structure. Transfer
this structure along AsSmall.equiv. The finite-type geometric fibre has its
inherited structure over D.k; no extra hypothesis is imposed. -/
theorem zlSmallHeart_abelian (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    Nonempty (Abelian (zlSmallHeart D l Ω hl X₀)) := by
  let : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let := (sfCommonStageHeart_properties l (D.geometricFiber X₀).left Ω D hl).2.2.some
  exact ⟨inferInstanceAs (Abelian (AsSmall.{0}
    (sfCommonStageHeart l (D.geometricFiber X₀).left Ω)))⟩

/-- The canonical abelian structure on the small heart presentation.
Source: blueprint constructible-heart convention
(blueprint: def-zl-weil-ind-sheaf-category). -/
instance zlSmallHeartAbelian (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    Abelian (zlSmallHeart D l Ω hl X₀) :=
  (zlSmallHeart_abelian D l hl Ω X₀).some

/-- Pullback in the small presentation of the underlying heart.
Source: blueprint common-stage coefficient convention
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlSmallPull {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    zlSmallHeart D l Ω hl Y₀ ⥤ zlSmallHeart D l Ω hl X₀ :=
  AsSmall.down ⋙ zlHeartPull D l hl Ω f₀ ⋙ AsSmall.up

/-- Frobenius in the small presentation of the underlying heart.
Source: blueprint common-stage coefficient convention
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlSmallFrobenius (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    zlSmallHeart D l Ω hl X₀ ⥤ zlSmallHeart D l Ω hl X₀ :=
  AsSmall.down ⋙ zlHeartFrobenius D l hl Ω X₀ ⋙ AsSmall.up

section IndExtension
attribute [-instance] Functor.hasLeftKanExtension_of_preserves
attribute [-instance] Functor.hasPointwiseLeftKanExtension_of_preserves
attribute [-instance] Functor.PreservesLeftKanExtension.preserves

universe w
variable {C B : Type w} [SmallCategory C] [SmallCategory B]
  [Abelian C] [Abelian B]

/-- The ind-extension of an exact heart functor is a Kan extension along Yoneda.
Source: SGA 4, XVII, sheaf resolutions; blueprint compact-support construction
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: the ind-category of a small abelian category is cocomplete. Small comma
colimits construct the Kan extension. On ind-presentations it is the filtered
colimit of the given functor. The universal cocones determine its comparison. -/
@[instance]
theorem zlIndMap_hasLeftKanExtension (F : C ⥤ B) :
    Functor.HasLeftKanExtension (Ind.yoneda (C := C)) (F ⋙ Ind.yoneda) := by
  have hc : Nonempty (Abelian C) := ⟨inferInstance⟩
  have hb : Nonempty (Abelian B) := ⟨inferInstance⟩
  obtain ⟨_⟩ := hc
  obtain ⟨_⟩ := hb
  infer_instance

/-- The canonical ind-extension, including its Kan universal property.
Source: SGA 4, XVII, sheaf resolutions
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlIndMap (F : C ⥤ B) : Ind C ⥤ Ind B :=
  letI := zlIndMap_hasLeftKanExtension F
  Functor.leftKanExtension (Ind.yoneda (C := C)) (F ⋙ Ind.yoneda)

/-- The unit at representable objects is invertible.
Source: SGA 4, XVII, sheaf resolutions
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: Yoneda is fully faithful, so its comma category at a representable has a
terminal presentation. Its colimit is the original functor value. Thus every
component of the Kan unit is invertible. -/
theorem zlIndMap_unit_isIso (F : C ⥤ B) :
    IsIso (Functor.leftKanExtensionUnit (Ind.yoneda (C := C)) (F ⋙ Ind.yoneda)) := by
  exact (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    (Functor.leftKanExtension (Ind.yoneda (C := C)) (F ⋙ Ind.yoneda))
    (Functor.leftKanExtensionUnit (Ind.yoneda (C := C)) (F ⋙ Ind.yoneda))).isIso_hom

/-- The comparison with Yoneda is the inverse of the actual Kan unit.
Source: SGA 4, XVII, sheaf resolutions
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlIndMapIso (F : C ⥤ B) : Ind.yoneda ⋙ zlIndMap F ≅ F ⋙ Ind.yoneda :=
  letI := zlIndMap_hasLeftKanExtension F
  letI := zlIndMap_unit_isIso F
  (asIso (Functor.leftKanExtensionUnit (Ind.yoneda (C := C))
    (F ⋙ Ind.yoneda))).symm

private instance zlPresheafLanLeftAdjoint (F : C ⥤ B) : (F.op.lan (H := Type w)).IsLeftAdjoint :=
  (F.op.lanAdjunction (Type w)).isLeftAdjoint

omit [Abelian C] in
private theorem zlIndInclusion_lke :
    (Ind.inclusion C).IsLeftKanExtension Ind.yonedaCompInclusion.inv := by
  apply Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExtension
    (E := Functor.LeftExtension.mk (Ind.inclusion C) Ind.yonedaCompInclusion.inv)
  intro X
  let E := ((CostructuredArrow.post Ind.yoneda (Ind.inclusion C) X).asEquivalence.trans
    (CostructuredArrow.mapNatIso Ind.yonedaCompInclusion))
  exact IsColimit.ofIsoColimit
    ((Presheaf.isColimitTautologicalCocone ((Ind.inclusion C).obj X)).whiskerEquivalence E)
    (Cocone.ext (Iso.refl _) (by intro j; rfl))

omit [Abelian B] in
private theorem zlIndInclusion_preserves (F : C ⥤ B) :
    (Ind.inclusion B).PreservesLeftKanExtension (F ⋙ Ind.yoneda) Ind.yoneda := by
  apply Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise

private def zlYonedaULiftIso : yoneda (C := C) ≅ uliftYoneda.{w} :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Equiv.ulift.symm.toIso))

private def zlPresheafLanIso (F : C ⥤ B) :
    yoneda ⋙ F.op.lan ≅ F ⋙ yoneda :=
  Functor.isoWhiskerRight zlYonedaULiftIso F.op.lan ≪≫
    (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{w} F).symm ≪≫
    Functor.isoWhiskerLeft F zlYonedaULiftIso.symm

omit [Abelian B] in
private theorem zlIndPresheaf_lke (F : C ⥤ B) :
    (Ind.inclusion C ⋙ F.op.lan).IsLeftKanExtension
      ((zlPresheafLanIso F).inv ≫ Functor.whiskerRight Ind.yonedaCompInclusion.inv F.op.lan ≫
        (Functor.associator _ _ _).hom) := by
  let := zlIndInclusion_lke (C := C)
  let : F.op.lan.PreservesLeftKanExtension yoneda Ind.yoneda :=
    Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise _ _ _
  have h := Functor.PreservesLeftKanExtension.preserves (G := F.op.lan)
    (Ind.inclusion C) Ind.yonedaCompInclusion.inv
  exact (Functor.isLeftKanExtension_iff_of_iso₂ _ _
    (zlPresheafLanIso F) (Iso.refl _) (by simp)).mp h

private theorem zlIndPresheaf_iso (F : C ⥤ B) :
    Nonempty (Functor.leftKanExtension Ind.yoneda (F ⋙ Ind.yoneda) ⋙ Ind.inclusion B ≅
      Ind.inclusion C ⋙ F.op.lan) := by
  let zlIndMap := Functor.leftKanExtension Ind.yoneda (F ⋙ Ind.yoneda)
  let α := Functor.leftKanExtensionUnit Ind.yoneda (F ⋙ Ind.yoneda)
  let := zlIndInclusion_preserves F
  let := Functor.PreservesLeftKanExtension.preserves (G := Ind.inclusion B) zlIndMap α
  let := zlIndPresheaf_lke F
  exact ⟨Functor.leftKanExtensionUniqueOfIso (zlIndMap ⋙ Ind.inclusion B)
    (Functor.whiskerRight α (Ind.inclusion B) ≫ (Functor.associator _ _ _).hom)
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerLeft F Ind.yonedaCompInclusion)
    (Ind.inclusion C ⋙ F.op.lan)
    ((zlPresheafLanIso F).inv ≫ Functor.whiskerRight Ind.yonedaCompInclusion.inv F.op.lan ≫
      (Functor.associator _ _ _).hom)⟩

private theorem zlIndMap_filtered (F : C ⥤ B) :
    PreservesFilteredColimitsOfSize.{w, w}
      (Functor.leftKanExtension Ind.yoneda (F ⋙ Ind.yoneda)) := by
  let zlIndMap := Functor.leftKanExtension Ind.yoneda (F ⋙ Ind.yoneda)
  obtain ⟨e⟩ := zlIndPresheaf_iso F
  let : PreservesFilteredColimitsOfSize.{w, w} (zlIndMap ⋙ Ind.inclusion B) :=
    ⟨fun _ _ _ ↦ preservesColimitsOfShape_of_natIso e.symm⟩
  exact ⟨fun _ _ _ ↦ preservesColimitsOfShape_of_reflects_of_preserves zlIndMap (Ind.inclusion B)⟩

private theorem zlIndMap_limits (F : C ⥤ B) [PreservesFiniteLimits F] :
    PreservesFiniteLimits (Functor.leftKanExtension Ind.yoneda (F ⋙ Ind.yoneda)) := by
  let zlIndMap := Functor.leftKanExtension Ind.yoneda (F ⋙ Ind.yoneda)
  obtain ⟨e⟩ := zlIndPresheaf_iso F
  let : PreservesFiniteLimits (zlIndMap ⋙ Ind.inclusion B) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves zlIndMap (Ind.inclusion B)


private theorem zlIndMap_lke (F : C ⥤ B) : (zlIndMap F).IsLeftKanExtension (zlIndMapIso F).inv := by
  change (Functor.leftKanExtension Ind.yoneda (F ⋙ Ind.yoneda)).IsLeftKanExtension
    (Functor.leftKanExtensionUnit Ind.yoneda (F ⋙ Ind.yoneda))
  infer_instance

attribute [local irreducible] zlIndMap zlIndMapIso

private def zlIndCompositeIso (L : C ⥤ B) (G : B ⥤ B) :
    Ind.yoneda ⋙ (zlIndMap L ⋙ zlIndMap G) ≅ (L ⋙ G) ⋙ Ind.yoneda :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (zlIndMapIso L) (zlIndMap G) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L (zlIndMapIso G) ≪≫
    (Functor.associator _ _ _).symm

private theorem zlIndComposite_lke (L : C ⥤ B) (G : B ⥤ B) :
    (zlIndMap L ⋙ zlIndMap G).IsLeftKanExtension (zlIndCompositeIso L G).inv := by
  let : PreservesFilteredColimitsOfSize.{w,w} (zlIndMap G) := by
    simpa only [zlIndMap] using zlIndMap_filtered G
  let : (zlIndMap L).IsLeftKanExtension (zlIndMapIso L).inv := zlIndMap_lke L
  let : (zlIndMap G).PreservesLeftKanExtension (L ⋙ Ind.yoneda) Ind.yoneda :=
    Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise _ _ _
  have h := Functor.PreservesLeftKanExtension.preserves
    (G := zlIndMap G) (zlIndMap L) (zlIndMapIso L).inv
  exact (Functor.isLeftKanExtension_iff_of_iso₂ _ _
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L (zlIndMapIso G) ≪≫
      (Functor.associator _ _ _).symm) (Iso.refl _) (by ext A; simp [zlIndCompositeIso])).mp h

private def zlIndCompositeIso' (F : C ⥤ C) (L : C ⥤ B) :
    Ind.yoneda ⋙ (zlIndMap F ⋙ zlIndMap L) ≅ (F ⋙ L) ⋙ Ind.yoneda :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (zlIndMapIso F) (zlIndMap L) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (zlIndMapIso L) ≪≫
    (Functor.associator _ _ _).symm

private theorem zlIndComposite_lke' (F : C ⥤ C) (L : C ⥤ B) :
    (zlIndMap F ⋙ zlIndMap L).IsLeftKanExtension (zlIndCompositeIso' F L).inv := by
  let : PreservesFilteredColimitsOfSize.{w,w} (zlIndMap L) := by
    simpa only [zlIndMap] using zlIndMap_filtered L
  let : (zlIndMap F).IsLeftKanExtension (zlIndMapIso F).inv := zlIndMap_lke F
  let : (zlIndMap L).PreservesLeftKanExtension (F ⋙ Ind.yoneda) Ind.yoneda :=
    Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise _ _ _
  have h := Functor.PreservesLeftKanExtension.preserves
    (G := zlIndMap L) (zlIndMap F) (zlIndMapIso F).inv
  exact (Functor.isLeftKanExtension_iff_of_iso₂ _ _
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (zlIndMapIso L) ≪≫
      (Functor.associator _ _ _).symm) (Iso.refl _) (by ext A; simp [zlIndCompositeIso'])).mp h


/-- A square descends uniquely to ind-objects with its given representable components.
Source: SGA 4, XVII, sheaf resolutions; blueprint Frobenius equivariance
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: ind-extension preserves filtered colimits. Every object is a filtered
colimit of representables. Extend the given square by the colimit universal
property; its inverse extends in the same way. The displayed equation fixes all
representable components, hence all components and their naturality uniquely. -/
theorem zlIndSquare_existsUnique (L : C ⥤ B) (F : C ⥤ C) (G : B ⥤ B)
    (e : L ⋙ G ≅ F ⋙ L) :
    ∃! c : zlIndMap L ⋙ zlIndMap G ≅ zlIndMap F ⋙ zlIndMap L,
      ∀ A : C,
        c.hom.app (Ind.yoneda.obj A) ≫
            (zlIndMap L).map ((zlIndMapIso F).hom.app A) ≫
            (zlIndMapIso L).hom.app (F.obj A) =
          (zlIndMap G).map ((zlIndMapIso L).hom.app A) ≫
            (zlIndMapIso G).hom.app (L.obj A) ≫ Ind.yoneda.map (e.hom.app A) := by
  let := zlIndComposite_lke L G
  let := zlIndComposite_lke' F L
  let c := Functor.leftKanExtensionUniqueOfIso (zlIndMap L ⋙ zlIndMap G) (zlIndCompositeIso L G).inv
    (Functor.isoWhiskerRight e Ind.yoneda) (zlIndMap F ⋙ zlIndMap L) (zlIndCompositeIso' F L).inv
  have hc : (zlIndCompositeIso L G).inv ≫ Functor.whiskerLeft Ind.yoneda c.hom =
      (Functor.isoWhiskerRight e Ind.yoneda).hom ≫ (zlIndCompositeIso' F L).inv := by
    apply Functor.descOfIsLeftKanExtension_fac
  have hc' : Functor.whiskerLeft Ind.yoneda c.hom ≫ (zlIndCompositeIso' F L).hom =
      (zlIndCompositeIso L G).hom ≫ (Functor.isoWhiskerRight e Ind.yoneda).hom := by
    calc
      _ = (zlIndCompositeIso L G).hom ≫ ((zlIndCompositeIso L G).inv ≫
          Functor.whiskerLeft Ind.yoneda c.hom) ≫ (zlIndCompositeIso' F L).hom := by simp
      _ = _ := by rw [hc]; simp
  refine ⟨c, ?_, ?_⟩
  · intro A
    simpa [zlIndCompositeIso, zlIndCompositeIso'] using NatTrans.congr_app hc' A
  · intro d hd
    apply Iso.ext
    apply Functor.hom_ext_of_isLeftKanExtension
      (zlIndMap L ⋙ zlIndMap G) (zlIndCompositeIso L G).inv
    apply (cancel_mono (zlIndCompositeIso' F L).hom).mp
    rw [Category.assoc, Category.assoc]
    congr 1
    apply NatTrans.ext
    funext A
    have hcA : c.hom.app (Ind.yoneda.obj A) ≫
        (zlIndMap L).map ((zlIndMapIso F).hom.app A) ≫ (zlIndMapIso L).hom.app (F.obj A) =
        (zlIndMap G).map ((zlIndMapIso L).hom.app A) ≫
          (zlIndMapIso G).hom.app (L.obj A) ≫ Ind.yoneda.map (e.hom.app A) := by
      simpa [zlIndCompositeIso, zlIndCompositeIso'] using NatTrans.congr_app hc' A
    simpa [zlIndCompositeIso, zlIndCompositeIso'] using (hd A).trans hcA.symm


/-- The ind-square with its normalized Yoneda components.
Source: blueprint Frobenius equivariance
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlIndSquare (L : C ⥤ B) (F : C ⥤ C) (G : B ⥤ B) (e : L ⋙ G ≅ F ⋙ L) :=
  (zlIndSquare_existsUnique L F G e).exists.choose

private theorem zlIndMap_left (F : C ⥤ B) [PreservesFiniteColimits F] :
    (zlIndMap F).IsLeftAdjoint := by
  let P : Ind B ⥤ Cᵒᵖ ⥤ Type w :=
    Ind.inclusion B ⋙ (Functor.whiskeringLeft _ _ _).obj F.op
  have hp (X : Ind B) : IsIndObject (P.obj X) := by
    let : PreservesFiniteLimits ((Ind.inclusion B).obj X) :=
      (isIndObject_iff_preservesFiniteLimits _).mp (Ind.isIndObject_inclusion_obj X)
    apply (isIndObject_iff_preservesFiniteLimits _).mpr
    change PreservesFiniteLimits (F.op ⋙ (Ind.inclusion B).obj X)
    let := preservesFiniteLimits_op F
    infer_instance
  let Q := ObjectProperty.lift IsIndObject P hp
  let R := Q ⋙ (Ind.equivalence C).inverse
  let r : R ⋙ Ind.inclusion C ≅ P :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Q
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Ind.equivalence C).counitIso (ObjectProperty.ι _) ≪≫
        Functor.leftUnitor _) ≪≫ ObjectProperty.liftCompιIso _ P hp
  obtain ⟨e⟩ := zlIndPresheaf_iso F
  let adj := (F.op.lanAdjunction (Type w)).restrictFullyFaithful
    (Ind.inclusion.fullyFaithful (C := C)) (Ind.inclusion.fullyFaithful (C := B))
    (by simpa only [zlIndMap] using e.symm) r.symm
  simpa only [zlIndMap] using adj.isLeftAdjoint

private theorem zlIndMap_equiv (F : C ⥤ B) [F.IsEquivalence] :
    (zlIndMap F).IsEquivalence := by
  let T := F.op.lan (H := Type w)
  let : T.IsEquivalence :=
    (F.op.lanAdjunction (Type w)).isEquivalence_left_of_isEquivalence_right
  obtain ⟨e⟩ := zlIndPresheaf_iso F
  let e' : zlIndMap F ⋙ Ind.inclusion B ≅ Ind.inclusion C ⋙ T := by
    simpa only [zlIndMap] using e
  let : (zlIndMap F).Full := Functor.Full.of_comp_faithful_iso e'
  let : (zlIndMap F).Faithful := Functor.Faithful.of_comp_iso e'
  let : (zlIndMap F).EssSurj := ⟨fun X ↦ by
    let Q := F.op ⋙ (Ind.inclusion B).obj X
    have hp : IsIndObject Q := by
      let : PreservesFiniteLimits ((Ind.inclusion B).obj X) :=
        (isIndObject_iff_preservesFiniteLimits _).mp (Ind.isIndObject_inclusion_obj X)
      apply (isIndObject_iff_preservesFiniteLimits _).mpr
      change PreservesFiniteLimits (F.op ⋙ (Ind.inclusion B).obj X)
      infer_instance
    let A := (Ind.equivalence C).inverse.obj ⟨Q, hp⟩
    let r : (Ind.inclusion C).obj A ≅ Q :=
      (ObjectProperty.ι _).mapIso ((Ind.equivalence C).counitIso.app ⟨Q, hp⟩)
    refine ⟨A, ⟨(Ind.inclusion.fullyFaithful (C := B)).preimageIso ?_⟩⟩
    exact e'.app A ≪≫ T.mapIso r ≪≫
      asIso ((F.op.lanAdjunction (Type w)).counit.app ((Ind.inclusion B).obj X))⟩
  exact {}

private theorem zlIndMap_colimits (F : C ⥤ B) [PreservesFiniteColimits F] :
    PreservesFiniteColimits (zlIndMap F) := by
  let := zlIndMap_left F
  infer_instance

private def zlIndMap_adjunction {F : C ⥤ B} {G : B ⥤ C} (a : F ⊣ G) : zlIndMap F ⊣ zlIndMap G := by
  let eF := Classical.choice (zlIndPresheaf_iso F)
  let eG := Classical.choice (zlIndPresheaf_iso G)
  let e : G.op.lan (H := Type w) ≅
      (Functor.whiskeringLeft _ _ (Type w)).obj F.op :=
    Adjunction.leftAdjointUniq (G.op.lanAdjunction (Type w)) (a.op.whiskerLeft (Type w))
  exact (F.op.lanAdjunction (Type w)).restrictFullyFaithful
    (Ind.inclusion.fullyFaithful (C := C)) (Ind.inclusion.fullyFaithful (C := B))
    (by simpa only [zlIndMap] using eF.symm)
    (by simpa only [zlIndMap] using (eG ≪≫ Functor.isoWhiskerLeft (Ind.inclusion B) e).symm)


end IndExtension

attribute [instance] Functor.hasLeftKanExtension_of_preserves
attribute [instance] Functor.hasPointwiseLeftKanExtension_of_preserves
attribute [instance] Functor.PreservesLeftKanExtension.preserves
attribute [local irreducible] zlIndMap zlIndMapIso

/-- The small presentation of the canonical Frobenius square.
Source: blueprint Frobenius equivariance
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: whisker zlHeartSquare with AsSmall.down and AsSmall.up, and insert the
unit and counit of their equivalence. Their underlying maps are identities,
so this gives exactly the same normalized square. -/
theorem zlSmallSquare_existsUnique {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    ∃! e : zlSmallPull D l hl Ω f₀ ⋙ zlSmallFrobenius D l hl Ω X₀ ≅
        zlSmallFrobenius D l hl Ω Y₀ ⋙ zlSmallPull D l hl Ω f₀,
      ∀ K, (e.hom.app K).down.hom =
        (zlFrobeniusSquare D l hl Ω f₀).hom.app (AsSmall.down.obj K).obj := by
  let e : zlSmallPull D l hl Ω f₀ ⋙ zlSmallFrobenius D l hl Ω X₀ ≅
      zlSmallFrobenius D l hl Ω Y₀ ⋙ zlSmallPull D l hl Ω f₀ :=
    NatIso.ofComponents (fun K ↦
      AsSmall.up.mapIso ((sfCommonStageHeartProperty l
        (D.geometricFiber X₀).left Ω).isoMk
          ((zlFrobeniusSquare D l hl Ω f₀).app (AsSmall.down.obj K).obj)))
      (fun a ↦ by
        apply ULift.ext
        apply ObjectProperty.hom_ext
        exact (zlFrobeniusSquare D l hl Ω f₀).hom.naturality
          (AsSmall.down.map a).hom)
  refine ⟨e, fun _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ULift.ext
  apply ObjectProperty.hom_ext
  exact he' K

/-- The normalized small-presentation square.
Source: blueprint Frobenius equivariance
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlSmallSquare {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :=
  (zlSmallSquare_existsUnique D l hl Ω f₀).exists.choose

/-- All equivariant ind-sheaves, rather than ind-objects of finite-rank Weil sheaves.
This retains arbitrary Frobenius orbits, so the free equivariant object exists.
Source: SGA 4, XVII, sheaf resolutions; blueprint fixed-pair convention
(blueprint: def-zl-weil-ind-sheaf-category). -/
abbrev zlIndWeilHeart (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :=
  IsoAlgebra (zlIndMap (zlSmallFrobenius D l hl Ω X₀))

section FrobeniusEquivalence
attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback

private theorem zlHeartFrobenius_equiv (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (zlHeartFrobenius D l hl Ω X₀).IsEquivalence := by
  let : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let g := (D.geometricFrobenius X₀).hom
  let I := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := I
  obtain ⟨iX, iY, hc⟩ := isomorphismFieldTransport D l hl Ω g
  have hiX : iX = I := Subsingleton.elim _ _
  have hiY : iY = I := Subsingleton.elim _ _
  subst iX
  subst iY
  obtain ⟨hX, hY, _, _, S, R, _, ⟨c⟩, ⟨d⟩⟩ := hc
  let F := sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω
  let : F.IsEquivalence := c.equivalence
  have hcH := (constructible_pullback_t_exact D l hl Ω (Classical.arbitrary _)
    (W := (D.geometricFiber X₀).left) (X := (D.geometricFiber X₀).left) (inv g)).2
  dsimp only [ConstructibleCommonStagePullbackComparison] at hcH
  have hI : constructiblePullbackResidueUnits D l hl (D.geometricFiber X₀).left = I :=
    Subsingleton.elim _ _
  rw [hI] at hcH
  obtain ⟨H⟩ := hcH
  let P := sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
  let e : commonStageDerivedPullback l Ω (inv g) ⋙ F ≅ 𝟭 _ := by
    have de := d.epsilon
    change commonStageDerivedPullback l Ω (inv g) ⋙
      commonStageDerivedPullback l Ω (inv (inv g)) ≅ 𝟭 _ at de
    rw [CategoryTheory.IsIso.inv_inv] at de
    exact de
  let : (zlHeartFrobenius D l hl Ω X₀).Full := by
    change (P.lift (P.ι ⋙ F) _).Full
    infer_instance
  let : (zlHeartFrobenius D l hl Ω X₀).Faithful := by
    change (P.lift (P.ι ⋙ F) _).Faithful
    infer_instance
  let : (zlHeartFrobenius D l hl Ω X₀).EssSurj := ⟨fun K ↦ by
    refine ⟨H.heart.obj K, ⟨P.isoMk ?_⟩⟩
    exact F.mapIso ((eqToIso H.heart_fac).app K) ≪≫ e.app K.obj⟩
  exact {}

end FrobeniusEquivalence

/-- Frobenius remains an exact autoequivalence after ind-extension.
Source: blueprint fixed-pair convention; SGA 4, XVII, sheaf resolutions
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: geometric Frobenius and its inverse are exact on the underlying heart.
Extend their inverse equivalence, its unit and its counit by filtered colimits.
Exactness follows from exactness of filtered colimits. This proves all clauses. -/
theorem zlIndFrobenius_exact (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (zlIndMap (zlSmallFrobenius D l hl Ω X₀)).Additive ∧
      PreservesFiniteLimits (zlIndMap (zlSmallFrobenius D l hl Ω X₀)) ∧
      PreservesFiniteColimits (zlIndMap (zlSmallFrobenius D l hl Ω X₀)) ∧
      (zlIndMap (zlSmallFrobenius D l hl Ω X₀)).IsEquivalence := by
  let : (zlHeartFrobenius D l hl Ω X₀).IsEquivalence :=
    zlHeartFrobenius_equiv D l hl Ω X₀
  let eX : sfCommonStageHeart l (D.geometricFiber X₀).left Ω ≌
      zlSmallHeart D l Ω hl X₀ := AsSmall.equiv
  let : (zlSmallFrobenius D l hl Ω X₀).IsEquivalence := by
    change (eX.inverse ⋙ zlHeartFrobenius D l hl Ω X₀ ⋙ eX.functor).IsEquivalence
    infer_instance
  let := zlIndMap_equiv (zlSmallFrobenius D l hl Ω X₀)
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance,
    inferInstance, inferInstance⟩

/-- The ambient equivariant ind-category is Grothendieck abelian.
Source: blueprint fixed-pair convention; SGA 4, XVII, sheaf resolutions
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: the underlying ind-category is Grothendieck abelian. Apply the exact
fixed-pair construction to the autoequivalence in zlIndFrobenius_exact.
Equivariant sums of all Frobenius iterates give the left adjoint to forgetting;
it is exact. The generator and exact filtered colimits lift to fixed pairs. -/
theorem zlIndWeilHeart_grothendieck (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    Nonempty (Abelian (zlIndWeilHeart D l hl Ω X₀)) ∧
      (∀ a : Abelian (zlIndWeilHeart D l hl Ω X₀),
        @IsGrothendieckAbelian.{max (u + 2) v} _ _ a) := by
  obtain ⟨hadd, hlim, hcolim, hequiv⟩ := zlIndFrobenius_exact D l hl Ω X₀
  let := hadd
  let := hlim
  let := hcolim
  let := hequiv
  let a₀ : Abelian (zlIndWeilHeart D l hl Ω X₀) := inferInstance
  have h : @IsGrothendieckAbelian.{max (u + 2) v} _ _ a₀ :=
    IsoAlgebra.isGrothendieckAbelian (zlIndMap (zlSmallFrobenius D l hl Ω X₀))
  refine ⟨⟨a₀⟩, fun a₁ ↦ ?_⟩
  exact @IsGrothendieckAbelian.of_equivalence _ _ _ _ a₀ a₁ h
    (CategoryTheory.Equivalence.refl)

/-- The canonical abelian structure on equivariant ind-sheaves.
Source: blueprint fixed-pair convention
(blueprint: def-zl-weil-ind-sheaf-category). -/
instance zlIndWeilHeartAbelian (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    Abelian (zlIndWeilHeart D l hl Ω X₀) :=
  (zlIndWeilHeart_grothendieck D l hl Ω X₀).1.some

/-- Grothendieck structure, hence enough injectives, on equivariant ind-sheaves.
Source: blueprint fixed-pair convention
(blueprint: def-zl-weil-ind-sheaf-category). -/
instance zlIndWeilHeartGrothendieck (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    IsGrothendieckAbelian.{max (u + 2) v} (zlIndWeilHeart D l hl Ω X₀) :=
  (zlIndWeilHeart_grothendieck D l hl Ω X₀).2 inferInstance

private def zlWeilSmallPairsModel (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
    IsoAlgebra (zlSmallFrobenius D l hl Ω X₀) :=
  { obj := fun K ↦ IsoAlgebra.mk ⟨⟨K.obj.carrier, K.property⟩⟩
      { hom := ⟨ObjectProperty.homMk K.obj.str.hom⟩
        inv := ⟨ObjectProperty.homMk K.obj.str.inv⟩
        hom_inv_id := by
          apply ULift.ext
          apply ObjectProperty.hom_ext
          exact K.obj.str.hom_inv_id
        inv_hom_id := by
          apply ULift.ext
          apply ObjectProperty.hom_ext
          exact K.obj.str.inv_hom_id }
    map := fun a ↦ ObjectProperty.homMk
      { f := ⟨ObjectProperty.homMk a.hom.hom.f⟩
        h := by
          apply ULift.ext
          apply ObjectProperty.hom_ext
          exact a.hom.hom.h }
    map_id := fun _ ↦ by
      apply ObjectProperty.hom_ext
      apply Algebra.Hom.ext
      apply ULift.ext
      apply ObjectProperty.hom_ext
      rfl
    map_comp := fun _ _ ↦ by
      apply ObjectProperty.hom_ext
      apply Algebra.Hom.ext
      apply ULift.ext
      apply ObjectProperty.hom_ext
      rfl }

private def zlWeilSmallPairsModelFullyFaithful (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (zlWeilSmallPairsModel D l hl Ω X₀).FullyFaithful :=
  { preimage := fun g ↦ ObjectProperty.homMk (ObjectProperty.homMk
        { f := g.hom.f.down.hom
          h := congrArg (fun f ↦ f.down.hom) g.hom.h })
    map_preimage := fun g ↦ by
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        apply ULift.ext
        apply ObjectProperty.hom_ext
        rfl
    preimage_map := fun a ↦ by
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        rfl }

/-- The actual common-stage Weil heart is abelian.
Source: blueprint composition proof, abelian fixed-pair category
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: geometric Frobenius is an exact autoequivalence of the constructible heart
by constructible_pullback_t_exact and isomorphism inverse image. Form kernels and
cokernels in that heart. Exactness transports their universal properties and hence
induces invertible Frobenius structures. The same properties give the equivariant
arrows and their universal properties. Images and coimages agree after forgetting,
so the fixed-pair heart is abelian. No triangulation of fixed pairs is asserted. -/
theorem zlWeilHeart_abelian (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    Nonempty (Abelian (sfCommonStageWeilSheaf D l hl X₀ Ω)) := by
  obtain ⟨hlim, hcolim⟩ := zlHeartFrobenius_exact D l hl Ω X₀
  let := hlim
  let := hcolim
  let H := sfCommonStageHeart l (D.geometricFiber X₀).left Ω
  let e : H ≌ zlSmallHeart D l Ω hl X₀ := AsSmall.equiv
  let : PreservesFiniteLimits (zlSmallFrobenius D l hl Ω X₀) :=
    inferInstanceAs (PreservesFiniteLimits (e.inverse ⋙
      zlHeartFrobenius D l hl Ω X₀ ⋙ e.functor))
  let : PreservesFiniteColimits (zlSmallFrobenius D l hl Ω X₀) :=
    inferInstanceAs (PreservesFiniteColimits (e.inverse ⋙
      zlHeartFrobenius D l hl Ω X₀ ⋙ e.functor))
  let : (zlSmallFrobenius D l hl Ω X₀).Additive :=
    Functor.additive_of_preserves_binary_products _
  let F := zlWeilSmallPairsModel D l hl Ω X₀
  let ff := zlWeilSmallPairsModelFullyFaithful D l hl Ω X₀
  let := ff.full
  let := ff.faithful
  let : F.EssSurj := ⟨fun K ↦ by
    let a : sfCommonStageWeilSheaf D l hl X₀ Ω :=
      ⟨IsoAlgebra.mk (AsSmall.down.obj K.carrier).obj
        { hom := K.str.hom.down.hom
          inv := K.str.inv.down.hom
          hom_inv_id := congrArg (fun f ↦ f.down.hom) K.str.hom_inv_id
          inv_hom_id := congrArg (fun f ↦ f.down.hom) K.str.inv_hom_id },
        (AsSmall.down.obj K.carrier).property⟩
    refine ⟨a, ⟨?_⟩⟩
    exact (Algebra.IsIsoStr _).isoMk
      (Algebra.isoMk (Iso.refl _) (by
        change (zlSmallFrobenius D l hl Ω X₀).map (𝟙 K.carrier) ≫ _ = _ ≫ 𝟙 _
        rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
        apply ULift.ext
        apply ObjectProperty.hom_ext
        rfl))⟩
  let : F.IsEquivalence := {}
  let := Preadditive.ofFullyFaithful ff
  let : HasFiniteLimits (sfCommonStageWeilSheaf D l hl X₀ Ω) :=
    ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence F⟩
  exact ⟨abelianOfEquivalence F⟩

/-- The abelian structure on the recorded category, without changing its arrows.
Source: blueprint composition proof, abelian fixed-pair category
(blueprint: def-zl-weil-ind-sheaf-category). -/
instance zlWeilHeartAbelian (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    Abelian (sfCommonStageWeilSheaf D l hl X₀ Ω) :=
  (zlWeilHeart_abelian D l hl Ω X₀).some

/-- Passage to the small presentation with literally the same carrier and Weil arrow.
Source: blueprint fixed-pair convention
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: lift the carrier and structure isomorphism through the full heart inclusion
and AsSmall.up. Lift each equivariant map in the same way. Full faithfulness
proves its equivariance, functor laws and uniqueness with the displayed formulas. -/
theorem zlWeilSmallPairs_existsUnique (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    ∃! F : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
        IsoAlgebra (zlSmallFrobenius D l hl Ω X₀),
      (∀ K, (F.obj K).carrier =
        (⟨⟨K.obj.carrier, K.property⟩⟩ : zlSmallHeart D l Ω hl X₀)) ∧
      (∀ K, HEq (F.obj K).str.hom.down.hom K.obj.str.hom) ∧
      ∀ (K L : sfCommonStageWeilSheaf D l hl X₀ Ω) (a : K ⟶ L),
        HEq (F.map a).hom.f.down.hom a.hom.hom.f := by
  let F := zlWeilSmallPairsModel D l hl Ω X₀
  refine ⟨F, ⟨fun _ ↦ rfl, fun _ ↦ HEq.rfl, fun _ _ _ ↦ HEq.rfl⟩, ?_⟩
  intro F' hF'
  have obj_ext (A B : IsoAlgebra (zlSmallFrobenius D l hl Ω X₀))
      (h : A.carrier = B.carrier)
      (hs : HEq A.str.hom.down.hom B.str.hom.down.hom) : A = B := by
    rcases A with ⟨⟨a, sa⟩, ha⟩
    rcases B with ⟨⟨b, sb⟩, hb⟩
    change a = b at h
    cases h
    have hstr : sa = sb := by
      apply ULift.ext
      apply ObjectProperty.hom_ext
      exact eq_of_heq hs
    cases hstr
    rfl
  have ho : ∀ K, F'.obj K = F.obj K := fun K ↦
    obj_ext (F'.obj K) (F.obj K) (hF'.1 K) (hF'.2.1 K)
  apply CategoryTheory.Functor.hext ho
  intro K L a
  have hom_ext {A B A' B' : IsoAlgebra (zlSmallFrobenius D l hl Ω X₀)}
      (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
      (h : HEq f.hom.f.down.hom g.hom.f.down.hom) : HEq f g := by
    cases hA
    cases hB
    apply heq_of_eq
    apply ObjectProperty.hom_ext
    apply Algebra.Hom.ext
    apply ULift.ext
    apply ObjectProperty.hom_ext
    exact eq_of_heq h
  exact hom_ext (ho K) (ho L) (F'.map a) (F.map a) (hF'.2.2 K L a)

/-- The literal small-presentation functor, with no changed Weil action.
Source: blueprint fixed-pair convention
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlWeilSmallPairs (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :=
  (zlWeilSmallPairs_existsUnique D l hl Ω X₀).exists.choose

/-- The fully faithful embedding into all equivariant ind-sheaves. Its Frobenius
comparison is the inverse of the Yoneda Kan unit.
Source: blueprint fixed-pair convention
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlWeilIndEmbedding (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    sfCommonStageWeilSheaf D l hl X₀ Ω ⥤ zlIndWeilHeart D l hl Ω X₀ :=
  zlWeilSmallPairs D l hl Ω X₀ ⋙
    IsoAlgebra.mapOfNatIso (zlIndMapIso (zlSmallFrobenius D l hl Ω X₀))

/-- Canonical inverse image on all equivariant ind-sheaves.
Source: blueprint Frobenius equivariance; SGA 4, XVII, sheaf resolutions
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlIndWeilPull {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    zlIndWeilHeart D l hl Ω Y₀ ⥤ zlIndWeilHeart D l hl Ω X₀ :=
  IsoAlgebra.mapOfNatIso (zlIndSquare (zlSmallPull D l hl Ω f₀)
    (zlSmallFrobenius D l hl Ω Y₀) (zlSmallFrobenius D l hl Ω X₀)
    (zlSmallSquare D l hl Ω f₀))

/-- Inverse image has a direct-image right adjoint.
Source: SGA 4, XVII, compact-support construction
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: exact heart inverse image extends to an exact colimit-preserving functor
on the ind-categories. Its Frobenius square has invertible mates, so the ordinary
right adjoint lifts to fixed pairs. The mate unit and counit give the adjunction
on equivariant Hom sets and determine its Weil action uniquely. -/
theorem zlIndWeilPull_isLeftAdjoint {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (zlIndWeilPull D l hl Ω f₀).IsLeftAdjoint := by
  obtain ⟨hlim, hcolim⟩ := zlHeartPull_exact D l hl Ω f₀
  let := hlim
  let := hcolim
  let eY : sfCommonStageHeart l (D.geometricFiber Y₀).left Ω ≌
      zlSmallHeart D l Ω hl Y₀ := AsSmall.equiv
  let eX : sfCommonStageHeart l (D.geometricFiber X₀).left Ω ≌
      zlSmallHeart D l Ω hl X₀ := AsSmall.equiv
  let : PreservesFiniteColimits (zlSmallPull D l hl Ω f₀) :=
    inferInstanceAs (PreservesFiniteColimits
      (eY.inverse ⋙ zlHeartPull D l hl Ω f₀ ⋙ eX.functor))
  let := zlIndMap_left (zlSmallPull D l hl Ω f₀)
  obtain ⟨hYadd, hYlim, hYcolim, hYeq⟩ := zlIndFrobenius_exact D l hl Ω Y₀
  obtain ⟨hXadd, hXlim, hXcolim, hXeq⟩ := zlIndFrobenius_exact D l hl Ω X₀
  let := hYeq
  let := hXeq
  let adj := Adjunction.ofIsLeftAdjoint (zlIndMap (zlSmallPull D l hl Ω f₀))
  let e := zlIndSquare (zlSmallPull D l hl Ω f₀)
    (zlSmallFrobenius D l hl Ω Y₀) (zlSmallFrobenius D l hl Ω X₀)
    (zlSmallSquare D l hl Ω f₀)
  exact (IsoAlgebra.mapOfNatIsoAdjunction adj e (IsoAlgebra.mateIso adj e)
    (IsoAlgebra.mateEquiv_natTrans_eq_mateIso_hom adj e)).isLeftAdjoint

/-- Ordinary direct image, determined by its adjunction with the prescribed inverse image.
Source: SGA 4, XVII, compact-support construction
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlIndWeilPush {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :=
  letI := zlIndWeilPull_isLeftAdjoint D l hl Ω f₀
  (zlIndWeilPull D l hl Ω f₀).rightAdjoint

/-- Ordinary direct image is additive.
Source: SGA 4, XVII, compact-support construction
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: it preserves finite products, which are biproducts in an abelian category.
The biproduct formula for addition therefore proves additivity. -/
@[instance]
theorem zlIndWeilPush_additive {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (zlIndWeilPush D l hl Ω f₀).Additive := by
  let := zlIndWeilPull_isLeftAdjoint D l hl Ω f₀
  change (zlIndWeilPull D l hl Ω f₀).rightAdjoint.Additive
  exact Functor.additive_of_preserves_binary_products _

private theorem zlHeartPull_openAdjunction {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (j₀ : X₀ ⟶ Y₀)
    [IsOpenImmersion j₀.left] :
    ∃ J : sfCommonStageHeart l (D.geometricFiber X₀).left Ω ⥤
        sfCommonStageHeart l (D.geometricFiber Y₀).left Ω,
      PreservesFiniteLimits J ∧ PreservesFiniteColimits J ∧
        Nonempty (J ⊣ zlHeartPull D l hl Ω j₀) := by
  let : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let : IsOpenImmersion (zlFiberMap D j₀) := by
    have hmap : zlFiberMap D j₀ = pullback.map X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) Y₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
        j₀.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext <;> simp [zlFiberMap, Over.pullback]
    rw [hmap]
    infer_instance
  let : (zlFiberMap D j₀).IsOver (Spec (.of D.k)) := ⟨by
    exact ((Over.pullback (Spec.map
      (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).w⟩
  exact commonStageOpenHeartAdjunction D l hl Ω
    (U := (D.geometricFiber X₀).left) (T := (D.geometricFiber Y₀).left)
    (zlFiberMap D j₀)
    (zlHeartPull D l hl Ω j₀) rfl

private theorem zlIndWeilOpen_exactAdjunction {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (j₀ : X₀ ⟶ Y₀)
    [IsOpenImmersion j₀.left] :
    ∃ J : zlIndWeilHeart D l hl Ω X₀ ⥤ zlIndWeilHeart D l hl Ω Y₀,
      PreservesFiniteLimits J ∧ PreservesFiniteColimits J ∧
        Nonempty (J ⊣ zlIndWeilPull D l hl Ω j₀) := by
  obtain ⟨J, hlim, hcolim, ⟨a⟩⟩ := zlHeartPull_openAdjunction D l hl Ω j₀
  let := hlim
  let := hcolim
  let eY : sfCommonStageHeart l (D.geometricFiber Y₀).left Ω ≌
      zlSmallHeart D l Ω hl Y₀ := AsSmall.equiv
  let eX : sfCommonStageHeart l (D.geometricFiber X₀).left Ω ≌
      zlSmallHeart D l Ω hl X₀ := AsSmall.equiv
  let L := eX.inverse ⋙ J ⋙ eY.functor
  let adj : L ⊣ zlSmallPull D l hl Ω j₀ :=
    eX.symm.toAdjunction.comp (a.comp eY.toAdjunction)
  let adjI := zlIndMap_adjunction adj
  let : PreservesFiniteLimits (zlIndMap L) := by
    simpa only [zlIndMap] using zlIndMap_limits L
  let : PreservesColimits (zlIndMap L) := adjI.leftAdjoint_preservesColimits
  let : PreservesFiniteColimits (zlIndMap L) := inferInstance
  obtain ⟨hYadd, hYlim, hYcolim, hYeq⟩ := zlIndFrobenius_exact D l hl Ω Y₀
  obtain ⟨hXadd, hXlim, hXcolim, hXeq⟩ := zlIndFrobenius_exact D l hl Ω X₀
  let := hYadd
  let := hYlim
  let := hYcolim
  let := hYeq
  let := hXadd
  let := hXlim
  let := hXcolim
  let := hXeq
  let e := zlIndSquare (zlSmallPull D l hl Ω j₀)
    (zlSmallFrobenius D l hl Ω Y₀) (zlSmallFrobenius D l hl Ω X₀)
    (zlSmallSquare D l hl Ω j₀)
  let m := ((mateEquiv adjI adjI).symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans
  let : IsIso m := isIso_inverseMate_of_equivalences adjI adjI e
  let eL := (asIso m).symm
  have h : (mateEquiv adjI adjI (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = e.hom := by
    exact congrArg TwoSquare.natTrans ((mateEquiv adjI adjI).apply_symm_apply
      (TwoSquare.mk _ _ _ _ e.hom))
  exact ⟨IsoAlgebra.mapOfNatIso eL, inferInstance, inferInstance,
    ⟨IsoAlgebra.mapOfNatIsoAdjunction adjI eL e h⟩⟩

/-- Open inverse image has exact extension by zero as its left adjoint.
Source: SGA 4, XVII, compact-support construction
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: exact open extension preserves constructibility and extends by filtered
colimits. Its Frobenius comparison is the invertible mate of the normalized
pullback square. Mate pasting makes its unit and counit equivariant, giving
an adjunction on all fixed pairs, not just those with finite Frobenius orbit. -/
theorem zlIndWeilPull_isRightAdjoint {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (j₀ : X₀ ⟶ Y₀)
    [IsOpenImmersion j₀.left] :
    (zlIndWeilPull D l hl Ω j₀).IsRightAdjoint := by
  obtain ⟨J, _, _, ⟨a⟩⟩ := zlIndWeilOpen_exactAdjunction D l hl Ω j₀
  exact a.isRightAdjoint

/-- Exact open extension by zero, determined by its adjunction.
Source: SGA 4, XVII, compact-support construction
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlIndWeilOpenShriek {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (j₀ : X₀ ⟶ Y₀)
    [IsOpenImmersion j₀.left] :=
  letI := zlIndWeilPull_isRightAdjoint D l hl Ω j₀
  (zlIndWeilPull D l hl Ω j₀).leftAdjoint
/-- The canonical ambient inverse image is exact.
Source: Bhatt--Scholze 6.8.11(3); blueprint Frobenius equivariance
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: underlying heart inverse image is exact by constructible_pullback_t_exact.
Its ind-extension is exact because filtered colimits are exact and finite diagrams
admit simultaneous filtered presentations. The exact Frobenius autoequivalences
make kernels and cokernels in fixed pairs be computed on carriers. Thus the
lifted functor preserves finite limits and finite colimits, and is additive. -/
theorem zlIndWeilPull_exact {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (zlIndWeilPull D l hl Ω f₀).Additive ∧
      PreservesFiniteLimits (zlIndWeilPull D l hl Ω f₀) ∧
      PreservesFiniteColimits (zlIndWeilPull D l hl Ω f₀) := by
  obtain ⟨hlim, hcolim⟩ := zlHeartPull_exact D l hl Ω f₀
  let := hlim
  let := hcolim
  let eY : sfCommonStageHeart l (D.geometricFiber Y₀).left Ω ≌
      zlSmallHeart D l Ω hl Y₀ := AsSmall.equiv
  let eX : sfCommonStageHeart l (D.geometricFiber X₀).left Ω ≌
      zlSmallHeart D l Ω hl X₀ := AsSmall.equiv
  let : PreservesFiniteLimits (zlSmallPull D l hl Ω f₀) :=
    inferInstanceAs (PreservesFiniteLimits
      (eY.inverse ⋙ zlHeartPull D l hl Ω f₀ ⋙ eX.functor))
  let : PreservesFiniteColimits (zlSmallPull D l hl Ω f₀) :=
    inferInstanceAs (PreservesFiniteColimits
      (eY.inverse ⋙ zlHeartPull D l hl Ω f₀ ⋙ eX.functor))
  let : PreservesFiniteLimits (zlIndMap (zlSmallPull D l hl Ω f₀)) := by
    simpa only [zlIndMap] using zlIndMap_limits (zlSmallPull D l hl Ω f₀)
  let := zlIndMap_colimits (zlSmallPull D l hl Ω f₀)
  have hpair : PreservesFiniteLimits (zlIndWeilPull D l hl Ω f₀) ∧
      PreservesFiniteColimits (zlIndWeilPull D l hl Ω f₀) := by
    obtain ⟨hYadd, hYlim, hYcolim, hYeq⟩ := zlIndFrobenius_exact D l hl Ω Y₀
    obtain ⟨hXadd, hXlim, hXcolim, hXeq⟩ := zlIndFrobenius_exact D l hl Ω X₀
    let := hYadd
    let := hYlim
    let := hYcolim
    let := hXadd
    let := hXlim
    let := hXcolim
    let : PreservesFiniteLimits (zlIndWeilPull D l hl Ω f₀) := by
      unfold zlIndWeilPull
      infer_instance
    let : PreservesFiniteColimits (zlIndWeilPull D l hl Ω f₀) := by
      unfold zlIndWeilPull
      infer_instance
    exact ⟨inferInstance, inferInstance⟩
  let := hpair.1
  let := hpair.2
  exact ⟨Functor.additive_of_preserves_binary_products _, hpair⟩

/-- The adjoint open extension is exact.
Source: SGA 4, XVII, extension by zero; blueprint compact-support construction
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: on underlying constructible sheaves the left adjoint is actual extension
by zero, which is exact. Extend by filtered colimits and use exactness of these
colimits. The mate comparison identifies the extension's induced Weil action
with that of the chosen adjoint, by uniqueness of adjoints. Exactness is
preserved by this comparison and is detected by forgetting the Weil action. -/
theorem zlIndWeilOpenShriek_exact {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (j₀ : X₀ ⟶ Y₀)
    [IsOpenImmersion j₀.left] :
    (zlIndWeilOpenShriek D l hl Ω j₀).Additive ∧
      PreservesFiniteLimits (zlIndWeilOpenShriek D l hl Ω j₀) ∧
      PreservesFiniteColimits (zlIndWeilOpenShriek D l hl Ω j₀) := by
  obtain ⟨J, hlim, hcolim, ⟨a⟩⟩ := zlIndWeilOpen_exactAdjunction D l hl Ω j₀
  let := hlim
  let := hcolim
  let := zlIndWeilPull_isRightAdjoint D l hl Ω j₀
  let e : J ≅ zlIndWeilOpenShriek D l hl Ω j₀ :=
    Adjunction.leftAdjointUniq a (Adjunction.ofIsRightAdjoint _)
  let : PreservesFiniteLimits (zlIndWeilOpenShriek D l hl Ω j₀) :=
    preservesFiniteLimits_of_natIso e
  let : PreservesFiniteColimits (zlIndWeilOpenShriek D l hl Ω j₀) :=
    preservesFiniteColimits_of_natIso e
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- The representing embedding is fully faithful, including Weil structures.
Source: blueprint fixed-pair and constructible-heart conventions
(blueprint: def-zl-weil-ind-sheaf-category).
Proof: the full heart inclusion and AsSmall equivalence are fully faithful.
Yoneda is fully faithful, and its normalized Frobenius comparison is invertible.
An underlying map between the represented objects is equivariant exactly when
its unique preimage is, since Yoneda is faithful. This proves both clauses. -/
theorem zlWeilIndEmbedding_full_faithful (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (zlWeilIndEmbedding D l hl Ω X₀).Full ∧
      (zlWeilIndEmbedding D l hl Ω X₀).Faithful := by
  let F := zlWeilSmallPairsModel D l hl Ω X₀
  have hF : zlWeilSmallPairs D l hl Ω X₀ = F :=
    (zlWeilSmallPairs_existsUnique D l hl Ω X₀).unique
      (zlWeilSmallPairs_existsUnique D l hl Ω X₀).exists.choose_spec
      ⟨fun _ ↦ rfl, fun _ ↦ HEq.rfl, fun _ _ _ ↦ HEq.rfl⟩
  let ff : F.FullyFaithful :=
    { preimage := fun g ↦ ObjectProperty.homMk (ObjectProperty.homMk
        { f := g.hom.f.down.hom
          h := congrArg (fun f ↦ f.down.hom) g.hom.h })
      map_preimage := fun g ↦ by
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        apply ULift.ext
        apply ObjectProperty.hom_ext
        rfl
      preimage_map := fun a ↦ by
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        rfl }
  let gg := IsoAlgebra.fullyFaithfulMapOfNatIso
    (zlIndMapIso (zlSmallFrobenius D l hl Ω X₀))
    (Functor.FullyFaithful.ofFullyFaithful Ind.yoneda)
  change (zlWeilSmallPairs D l hl Ω X₀ ⋙ _).Full ∧
    (zlWeilSmallPairs D l hl Ω X₀ ⋙ _).Faithful
  rw [hF]
  exact ⟨(ff.comp gg).full, (ff.comp gg).faithful⟩

end WeilConjectures
