/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.SecSmoothPurity.ModuleTensorGenerators
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Algebra.Homology.CochainTensorModelRigidity
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Canonical derived section pairings under adapted resolutions

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 4.1(1);
Stacks Project, Tags 06YU and 0FPT
(blueprint: lem-zl-derived-section-pairing-coherence).

The normalization is imposed on every flat-term K-flat pair, even when its
sections have not been shown K-flat. Only the resolutions in the hypothesis
must have K-flat sections. The monoidal comparison is unique with this normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w z

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures

namespace CategoryTheory.DerivedSectionPairing

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u}) (W : Cᵒᵖ)

/-- The existing module evaluation functor, with the actual section-ring action.
Source: HRS Lemma 4.1(1), Stacks 03DA
(blueprint: lem-zl-derived-section-pairing-coherence). -/
abbrev evaluation : RingedTensorModules.{c, v, u} J R ⥤
    ModuleCat.{max c v u} (R.obj.obj W) :=
  SheafOfModules.evaluation.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R) W

/-- Additivity of actual module evaluation, inherited from the two forgetful functors.
Source: Stacks 03DA (blueprint: lem-zl-derived-section-pairing-coherence). -/
instance evaluation_additive : (evaluation.{c, v, u} J R W).Additive :=
  inferInstanceAs ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ W).Additive)

/-- Termwise application of the existing evaluation functor to unbounded complexes.
Source: Stacks 06YU (blueprint: lem-zl-derived-section-pairing-coherence). -/
abbrev onComplexes := (evaluation.{c, v, u} J R W).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ordinary total section pairing, as a natural chain isomorphism.
Source: HRS Lemma 4.1(1), Stacks 06YN
(blueprint: lem-zl-derived-section-pairing-coherence). -/
abbrev TotalPairing :=
  ((onComplexes.{c, v, u} J R W).prod (onComplexes.{c, v, u} J R W)) ⋙
      MonoidalCategory.tensor (CochainComplex (ModuleCat.{max c v u} (R.obj.obj W)) ℤ) ≅
    coefficientTotalTensor.{u, c, v} J R ⋙ onComplexes.{c, v, u} J R W

/-- On each direct-sum summand the pairing is the actual sheafified tensor of sections.
The two complexes use the signed total differential, and the pairing is a chain map.
Source: Stacks 06YN, HRS Lemma 4.1(1)
(blueprint: lem-zl-derived-section-pairing-coherence). -/
def TotalPairingFormula (b : TotalPairing.{c, v, u} J R W) : Prop :=
  ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (p q n : ℤ) (h : p + q = n)
    (x : (P.X p).val.obj W) (y : (Q.X q).val.obj W),
    ((b.hom.app (P, Q)).f n)
      ((CochainComplex.ιMapBifunctor
        ((onComplexes.{c, v, u} J R W).obj P) ((onComplexes.{c, v, u} J R W).obj Q)
        (curriedTensor (ModuleCat.{max c v u} (R.obj.obj W))) p q n h)
          (x ⊗ₜ[R.obj.obj W] y)) =
      coefficientTensorGenerator.{u, c, v} J R P Q p q n h W x y

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]
  [HasDerivedCategory.{z} (ModuleCat.{max c v u} (R.obj.obj W))]
  [PreservesFiniteLimits (evaluation.{c, v, u} J R W)]
  [PreservesFiniteColimits (evaluation.{c, v, u} J R W)]

/-- Strong monoidal data on the actual termwise localized section functor.
Naturality, associativity and both unit equations are the fields of `CoreMonoidal`.
Source: Stacks 0FPT (blueprint: lem-zl-derived-section-pairing-coherence). -/
abbrev Comparison
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R)) :=
  @Functor.CoreMonoidal
    (DerivedCategory (RingedTensorModules.{c, v, u} J R)) _ S.monoidal
    (DerivedCategory (ModuleCat.{max c v u} (R.obj.obj W))) _ _
    (evaluation.{c, v, u} J R W).mapDerivedCategory.{w, z}

/-- The normalization square, including the canonical derived-to-ordinary target map.
It quantifies over every flat-term K-flat pair, without assuming its evaluation K-flat.
Source: Stacks 06YU, HRS Lemma 4.1(1)
(blueprint: lem-zl-derived-section-pairing-coherence). -/
def Normalization
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (b : TotalPairing.{c, v, u} J R W) (m : Comparison.{c, v, u, w, z} J R W S) : Prop :=
  ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
    (∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X p)) →
    (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X q)) →
    (((evaluation.{c, v, u} J R W).mapDerivedCategoryFactors.{w, z}.hom.app P) ⊗ₘ
      ((evaluation.{c, v, u} J R W).mapDerivedCategoryFactors.{w, z}.hom.app Q)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((onComplexes.{c, v, u} J R W).obj P) ((onComplexes.{c, v, u} J R W).obj Q) ≫
        DerivedCategory.Q.map (b.hom.app (P, Q)) =
      ((@Functor.CoreMonoidal.μIso _ _ S.monoidal _ _ _ _ m)
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        (evaluation.{c, v, u} J R W).mapDerivedCategory.{w, z}.map ((T.iso J R S P Q hP hQ).inv) ≫
        (evaluation.{c, v, u} J R W).mapDerivedCategoryFactors.{w, z}.hom.app
          ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q))

/-- The comparison preserves the prescribed Koszul braidings on arbitrary derived objects.
Source: Stacks 0FPT (blueprint: lem-zl-derived-section-pairing-coherence). -/
def Symmetry
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (m : Comparison.{c, v, u, w, z} J R W S) : Prop :=
  ∀ K L : DerivedCategory (RingedTensorModules.{c, v, u} J R),
    ((@Functor.CoreMonoidal.μIso _ _ S.monoidal _ _ _ _ m) K L).hom ≫
      (evaluation.{c, v, u} J R W).mapDerivedCategory.{w, z}.map
        ((β.toBraidedCategory.braiding K L).hom) =
      (DerivedMonoidal.braiding' DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat.{max c v u} (R.obj.obj W)) (.up ℤ))
        ((evaluation.{c, v, u} J R W).mapDerivedCategory.{w, z}.obj K)
        ((evaluation.{c, v, u} J R W).mapDerivedCategory.{w, z}.obj L)).hom ≫
          ((@Functor.CoreMonoidal.μIso _ _ S.monoidal _ _ _ _ m) L K).hom

/-- The derived unit is the localization of the identity on the section ring in degree zero.
The scalar equation specifies the ordinary chain comparison uniquely, including zero rings.
Source: Stacks 06YU and 0FPT (blueprint: lem-zl-derived-section-pairing-coherence). -/
def UnitNormalization
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (H : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (m : Comparison.{c, v, u, w, z} J R W S) : Prop :=
  ∃ e : (𝟙_ (CochainComplex (ModuleCat.{max c v u} (R.obj.obj W)) ℤ)) ≅
      (onComplexes.{c, v, u} J R W).obj (ringedTensorUnitComplex.{c, v, u} J R),
    (∀ a : R.obj.obj W,
      (e.hom.f 0) ((HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
        (ModuleCat.of (R.obj.obj W) (R.obj.obj W))).inv a) =
      ringedTensorUnitSection.{c, v, u} J R W a) ∧
    (@Functor.CoreMonoidal.εIso _ _ S.monoidal _ _ _ _ m).hom ≫
      (evaluation.{c, v, u} J R W).mapDerivedCategory.{w, z}.map H.unitIso.hom ≫
        (evaluation.{c, v, u} J R W).mapDerivedCategoryFactors.{w, z}.hom.app
          (ringedTensorUnitComplex.{c, v, u} J R) =
      Functor.LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map e.hom

/-- The actual section pairings descend uniquely to the coherent strong symmetric monoidal
comparison on ordinary unbounded derived categories. The ordinary comparison is also a
chain isomorphism for arbitrary complexes, without flatness or boundedness assumptions.

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 4.1(1);
Stacks Project, Tags 06YU and 0FPT
(blueprint: lem-zl-derived-section-pairing-coherence).

Proof:
1. In each total degree sum the ordinary section tensor isomorphisms, then use evaluation's
   coproduct comparison. Naturality with respect to both differentials and additivity
   identify d_P tensor 1 + (-1)^p 1 tensor d_Q on both sides. This gives b and its summand
   formula for all complexes, including complexes unbounded in both directions.
2. Exact evaluation preserves cohomology and quasi-isomorphisms. Localize termwise using
   lem-weil-pbc-localization-universal-property. The two-variable fully faithful restriction
   in lem-sf-cochain-tensor-model-rigidity applies to flat-term K-flat cochain models.
3. On these models compose the target native lax tensorator, Q(b), and the source K-flat
   model comparison, inserting mapDerivedCategoryFactors. Fullness extends this to all
   derived morphisms and faithfulness proves normalized uniqueness. This construction
   does not require the evaluations of every K-flat model to be K-flat.
4. For each input choose the adapted resolution in the hypothesis. Its evaluated complex
   is K-flat, so the target lax tensorator is invertible by lem-sf-ringed-derived-native-tensor
   (over the point site). All other factors are isomorphisms. Naturality transports this
   to every derived input, independently of the chosen resolutions.
5. For triples, lem-pur-kflat-total-tensor-model makes iterated flat-term K-flat models
   available. The native localization associator square reduces coherence to unsigned
   reassociation of the ordinary (p,q,r) summands. Their signed differentials agree.
   Naturality transports the equation to all triples.
6. On (p,q) the two symmetry routes have the same (-1)^(pq) sign. For the degree-zero unit,
   both unit equations are scalar multiplication and the section unit is the identity.
   The prescribed constraints of lem-sf-ringed-derived-closed-symmetric-monoidal and native
   localization preserve these equalities. They give Symmetry and UnitNormalization and
   the associativity and both unitality fields of the unique CoreMonoidal comparison. -/
theorem derived_section_pairing_coherence
    [PreservesColimitsOfSize.{max c v u, max c v u} (evaluation.{c, v, u} J R W)]
    (ordinary : (evaluation.{c, v, u} J R W).CoreMonoidal)
    (_hpair : ∀ (M N : RingedTensorModules.{c, v, u} J R)
      (x : M.val.obj W) (y : N.val.obj W),
      (ordinary.μIso M N).hom (x ⊗ₜ[R.obj.obj W] y) =
        CochainPullback.moduleTmul M N W x y)
    (_hunit : ordinary.εIso.hom = 𝟙 _)
    (_hsym : ∀ M N : RingedTensorModules.{c, v, u} J R,
      (ordinary.μIso M N).hom ≫ (evaluation.{c, v, u} J R W).map (β_ M N).hom =
        (β_ ((evaluation.{c, v, u} J R W).obj M) ((evaluation.{c, v, u} J R W).obj N)).hom ≫
          (ordinary.μIso N M).hom)
    (_hadapted : ∀ K : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ,
      ∃ (P : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) (f : P ⟶ K),
        QuasiIso f ∧ CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∧
        (∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X p)) ∧
        (HomologicalComplex.quasiIso (ModuleCat.{max c v u} (R.obj.obj W)) (.up ℤ)).kFlat
          ((onComplexes.{c, v, u} J R W).obj P))
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (H : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β) :
    ∃ b : TotalPairing.{c, v, u} J R W, TotalPairingFormula.{c, v, u} J R W b ∧
      ∃! m : Comparison.{c, v, u, w, z} J R W S,
        Normalization.{c, v, u, w, z} J R W S T b m ∧ Symmetry.{c, v, u, w, z} J R W S β m ∧
          UnitNormalization.{c, v, u, w, z} J R W S T β H m := by
  sorry

end CategoryTheory.DerivedSectionPairing
