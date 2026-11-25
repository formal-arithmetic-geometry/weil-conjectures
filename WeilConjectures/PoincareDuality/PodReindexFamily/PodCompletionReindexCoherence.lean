/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso

/-! # Coherence of the specified ordinary reindexing comparisons

We define a family `PodReindexFamily` of normalized ordinary reindexing comparisons along
isomorphisms of schemes, together with the identity, composition and tensor coherence
conditions it may satisfy. All equations refer to the family's own reduction, limit and
tensor maps.

## Main definitions

* `PodReindexFamily`: a family of normalized reindexing data on all isomorphisms.
* `PodReindexFamily.Relabelling`, `PodReindexFamily.Identity`,
  `PodReindexFamily.Composition`, `PodReindexFamily.TensorConstraints`: coherence conditions.

## Implementation details

A single family of choices is fixed, so that the identity and composition laws compare the
same data rather than unrelated existence statements.

## References

* [Stacks Project, Tag 015F](https://stacks.math.columbia.edu/tag/015F)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0941](https://stacks.math.columbia.edu/tag/0941)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- A family of normalized reindexing data: completion and completed tensor comparisons on
every isomorphism, together with identity and composition relabellings. -/
structure PodReindexFamily where
  /-- Ambient comparisons on every isomorphism. -/
  completion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)], PodCompletionReindex l E f
  /-- Completed tensor comparison on that same ambient datum. -/
  tensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)],
    PodCompletedTensorReindex l E f (completion f)
  /-- Identity relabelling before localization. -/
  identity : ∀ W : Scheme.{u}, isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _
  /-- Relabelling compositor before localization. -/
  composition : ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
    [IsIso h] [IsIso f], isoReductionIntegralInverse l E (h ≫ f) ≅
      isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h

namespace PodReindexFamily
variable (A : PodReindexFamily l E)

/-- The derived identity comparison obtained by localizing the identity relabelling. -/
def identityDerived (W : Scheme.{u}) : podOrdinaryReindex l E (𝟙 W) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (A.identity W) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The derived composition comparison obtained by localizing the relabelling compositor. -/
def compositionDerived {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
    [IsIso h] [IsIso f] : podOrdinaryReindex l E (h ≫ f) ≅
      podOrdinaryReindex l E f ⋙ podOrdinaryReindex l E h :=
  Functor.mapDerivedCategoryNatIso (A.composition h f) ≪≫
    (Functor.mapDerivedCategoryCompIso (isoReductionIntegralInverse l E f)
      (isoReductionIntegralInverse l E h)).symm

/-- Ordinary reindexing restricted to the complete constructible full subcategories. -/
def constructible {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)] :
    sfIntegralConstructibleCategory l E W ⥤ sfIntegralConstructibleCategory l E V :=
  (sfIntegralConstructible l E V).lift
    ((sfIntegralConstructible l E W).ι ⋙ podOrdinaryReindex l E f)
    (A.tensor f).constructible

/-- The identity and composition relabellings act on local sections by the canonical
restriction maps. -/
def Relabelling : Prop :=
  (∀ (W : Scheme.{u}) (M : scalarReductionSource l E W) (U : W.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))),
    ((A.identity W).hom.app M).val.app (op U) x =
      M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
        (𝟙 W) rfl).hom.app U).op x) ∧
  (∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    (M : scalarReductionSource l E V) (U : Z.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))),
    ((A.composition h f).hom.app M).val.app (op U) x =
      M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op x)

/-- The identity comparisons are compatible with the reduction, limit and tensor maps. -/
def Identity : Prop :=
  ∀ (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)],
  (∀ K : DerivedCategory (scalarReductionSource l E W),
    (A.completion (𝟙 W)).reduction.hom.app K ≫
        (podReindexCalculus l E W).reduction.map ((A.identityDerived l E W).hom.app K) =
      (integralComparisonSystemUnit l E W).hom.app
        ((podReindexCalculus l E W).reduction.obj K)) ∧
  (∀ N : coefficientSequenceDerived l E W,
    (A.completion (𝟙 W)).limit.hom.app N ≫
        (coefficientSequenceLimit l E W).map ((integralComparisonSystemUnit l E W).hom.app N) =
      (A.identityDerived l E W).hom.app ((coefficientSequenceLimit l E W).obj N)) ∧
  (∀ M N : sfIntegralConstructibleCategory l E W,
    ((A.tensor (𝟙 W)).tensor M N).hom ≫ (integralCompletedTensor l E W).map
        (Prod.mkHom ((A.identityDerived l E W).hom.app M.obj)
          ((A.identityDerived l E W).hom.app N.obj)) =
      (A.identityDerived l E W).hom.app ((integralCompletedTensor l E W).obj (M.obj,N.obj)))

/-- Successive relabelling commutes with reduction, total limit and completed tensor,
using the strict-system compositor and the section-normalized ordinary compositor. -/
def Composition : Prop :=
  ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)],
  (∀ K : DerivedCategory (scalarReductionSource l E V),
    (integralComparisonSystemComposition l E h f).hom.app
        ((podReindexCalculus l E V).reduction.obj K) ≫
      (integralComparisonDerivedSequencePullback l E h).map
        ((A.completion f).reduction.hom.app K) ≫
      (A.completion h).reduction.hom.app ((podOrdinaryReindex l E f).obj K) =
    (A.completion (h ≫ f)).reduction.hom.app K ≫
      (podReindexCalculus l E Z).reduction.map
        ((A.compositionDerived l E h f).hom.app K)) ∧
  (∀ N : coefficientSequenceDerived l E V,
    (A.compositionDerived l E h f).hom.app ((coefficientSequenceLimit l E V).obj N) ≫
      (podOrdinaryReindex l E h).map ((A.completion f).limit.hom.app N) ≫
      (A.completion h).limit.hom.app ((integralComparisonDerivedSequencePullback l E f).obj N) =
    (A.completion (h ≫ f)).limit.hom.app N ≫
      (coefficientSequenceLimit l E Z).map
        ((integralComparisonSystemComposition l E h f).hom.app N)) ∧
  (∀ M N : sfIntegralConstructibleCategory l E V,
    (A.compositionDerived l E h f).hom.app
        ((integralCompletedTensor l E V).obj (M.obj,N.obj)) ≫
      (podOrdinaryReindex l E h).map ((A.tensor f).tensor M N).hom ≫
      ((A.tensor h).tensor ((A.constructible l E f).obj M)
        ((A.constructible l E f).obj N)).hom =
    ((A.tensor (h ≫ f)).tensor M N).hom ≫ (integralCompletedTensor l E Z).map
      (Prod.mkHom ((A.compositionDerived l E h f).hom.app M.obj)
        ((A.compositionDerived l E h f).hom.app N.obj)))

/-- Associativity and Koszul symmetry for this family's own tensor comparison. -/
def TensorConstraints {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)] : Prop :=
  (∀ M N P : sfIntegralConstructibleCategory l E W,
    (podOrdinaryReindex l E f).map (pullbackTensorIntegralAssociator l E W M N P).hom.hom ≫
      ((A.tensor f).tensor M ((constructibleIntegralTensor l E W).obj (N,P))).hom ≫
      (integralCompletedTensor l E V).map
        (Prod.mkHom (𝟙 _) ((A.tensor f).tensor N P).hom) =
    ((A.tensor f).tensor ((constructibleIntegralTensor l E W).obj (M,N)) P).hom ≫
      (integralCompletedTensor l E V).map
        (Prod.mkHom ((A.tensor f).tensor M N).hom (𝟙 _)) ≫
      (pullbackTensorIntegralAssociator l E V ((A.constructible l E f).obj M)
        ((A.constructible l E f).obj N) ((A.constructible l E f).obj P)).hom.hom) ∧
  (∀ M N : sfIntegralConstructibleCategory l E W,
    (podOrdinaryReindex l E f).map (pullbackTensorIntegralBraiding l E W M N).hom.hom ≫
      ((A.tensor f).tensor N M).hom =
    ((A.tensor f).tensor M N).hom ≫
      (pullbackTensorIntegralBraiding l E V ((A.constructible l E f).obj M)
        ((A.constructible l E f).obj N)).hom.hom) ∧
  (∃ ε : (podOrdinaryReindex l E f).obj (pullbackTensorIntegralUnit l E W).obj ≅
      (pullbackTensorIntegralUnit l E V).obj,
    ∀ M : sfIntegralConstructibleCategory l E W,
    (((A.tensor f).tensor (pullbackTensorIntegralUnit l E W) M).hom ≫
      (integralCompletedTensor l E V).map (Prod.mkHom ε.hom (𝟙 _)) ≫
      (pullbackTensorIntegralLeftUnitor l E V ((A.constructible l E f).obj M)).hom.hom =
      (podOrdinaryReindex l E f).map (pullbackTensorIntegralLeftUnitor l E W M).hom.hom) ∧
    (((A.tensor f).tensor M (pullbackTensorIntegralUnit l E W)).hom ≫
      (integralCompletedTensor l E V).map (Prod.mkHom (𝟙 _) ε.hom) ≫
      (pullbackTensorIntegralRightUnitor l E V ((A.constructible l E f).obj M)).hom.hom =
      (podOrdinaryReindex l E f).map (pullbackTensorIntegralRightUnitor l E W M).hom.hom))

end PodReindexFamily

end WeilConjectures
