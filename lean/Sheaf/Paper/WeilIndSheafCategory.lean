/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.ConstructiblePullbackTExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Indization
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra

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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The abelian structure on the recorded category, without changing its arrows.
Source: blueprint composition proof, abelian fixed-pair category
(blueprint: def-zl-weil-ind-sheaf-category). -/
instance zlWeilHeartAbelian (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    Abelian (sfCommonStageWeilSheaf D l hl X₀ Ω) :=
  (zlWeilHeart_abelian D l hl Ω X₀).some

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
  sorry

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
  sorry

/-- Geometric Frobenius restricted to the actual underlying heart.
Source: blueprint composition proof
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlHeartFrobenius (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :=
  (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω).lift
    ((sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω).ι ⋙
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
    (zlHeartFrobenius_mem D l hl Ω X₀)

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The comparison with Yoneda is the inverse of the actual Kan unit.
Source: SGA 4, XVII, sheaf resolutions
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlIndMapIso (F : C ⥤ B) : Ind.yoneda ⋙ zlIndMap F ≅ F ⋙ Ind.yoneda :=
  letI := zlIndMap_hasLeftKanExtension F
  letI := zlIndMap_unit_isIso F
  (asIso (Functor.leftKanExtensionUnit (Ind.yoneda (C := C))
    (F ⋙ Ind.yoneda))).symm

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
  sorry

/-- The ind-square with its normalized Yoneda components.
Source: blueprint Frobenius equivariance
(blueprint: def-zl-weil-ind-sheaf-category). -/
def zlIndSquare (L : C ⥤ B) (F : C ⥤ C) (G : B ⥤ B) (e : L ⋙ G ≅ F ⋙ L) :=
  (zlIndSquare_existsUnique L F G e).exists.choose

end IndExtension

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry


end WeilConjectures
