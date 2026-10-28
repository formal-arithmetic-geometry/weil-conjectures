/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.SfPreservationClass
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Paper.ProEtaleConstructibleOrigin
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.CompactSupportProjectionFormula
import Sheaf.Paper.FixProjectionCompactificationComparison
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution

/-! # Independence of the presentation of the exceptional tensor map

Source: latest blueprint, sec-smooth-purity/sk-thm-smooth-purity,
prop-pur-smooth-purity-naturality-cover.proof.md, second paragraph
(blueprint: lem-pur-tensor-map-presentation-independent).

All tensor sources are written in etale-origin coordinates, as in the recorded
finite-coefficient cohomological smoothness definition. Applying the canonical
monoidal and pullback comparison identifies these sources with Lf* K tensor omega.
The realization below uses the retained witness and the specified class Hom bijection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The ordinary right adjoint at the specified compactification, without an opaque
HasCompactification choice. Source: latest blueprint, tensor-formula canonicity
(blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationEtaleRight (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).rightAdjoint

/-- The specified ordinary adjunction. Source: latest blueprint, tensor-formula canonicity
(blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationEtaleAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣
      tensorPresentationEtaleRight A c :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  Adjunction.ofIsLeftAdjoint _

/-- The canonical comparison of ordinary right adjoints, induced by the existing
compact-support comparison, with its counit normalization. Source: latest blueprint,
tensor-formula canonicity (blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationRightIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f) :
    tensorPresentationEtaleRight A c ≅ tensorPresentationEtaleRight A d :=
  (tensorPresentationEtaleAdjunction A c).rightAdjointUniq
    ((tensorPresentationEtaleAdjunction A d).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekOfCompactificationIso A c d).symm)

/-- Symmetry with the monoidal structure retained before specializing the coefficients.
Source: latest blueprint, the first arrow of the tensor transpose
(blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationSymmetry (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    ((Etale.derivedTensor B X).obj M).obj N ≅
      ((Etale.derivedTensor B X).obj N).obj M :=
  letI := Etale.derivedBraidedCategory B X
  β_ M N

/-- The actual inverse projection arrow at c. Its invertibility is the published
finite-coefficient projection formula, not an additional assumption.
Source: latest blueprint, the second arrow of the tensor transpose
(blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationInverseProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  letI : HasCompactification f := ⟨⟨c⟩⟩
  @inv _ _ _ _
    (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K)
    ((Etale.hasProjectionFormulaOfCompactification_iff A c M K).mpr
      (Etale.hasProjectionFormula_of_finite A f M K))

/-- The source Lf* K tensor omega_c in ordinary etale coordinates.
Source: latest blueprint, tensor-formula canonicity
(blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationSource (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj
      ((tensorPresentationEtaleRight A c).obj (𝟙_ _))

/-- Symmetry, inverse projection, counit at the coefficient unit, and left unitor.
This is the arrow to be transposed, with no arbitrary map as input.
Source: latest blueprint, tensor-formula canonicity
(blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationCounitArrow (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (tensorPresentationSymmetry (ModuleCat.{u + 1} A) X
        ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)
        ((tensorPresentationEtaleRight A c).obj (𝟙_ _))).hom ≫
    tensorPresentationInverseProjection A c ((tensorPresentationEtaleRight A c).obj (𝟙_ _)) K ≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).map
      ((tensorPresentationEtaleAdjunction A c).counit.app (𝟙_ _))).app K ≫
    (Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y K).hom

/-- The unit-normalized identification of the transported exceptional value on nu* K
with nu* of the ordinary value at K. Source: latest blueprint, comparison-class adjunction
(blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationTargetIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  letI := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) Y K.obj K.property
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
    ((tensorPresentationEtaleRight A c).mapIso
      (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app K.obj)).symm)

/-- The actual class transpose with a retained etale-origin witness for the tensor source.
The comparison at that source is followed by comparison pullback of the inverse-projection
and counit composite, then the class Hom bijection and its unit normalization.
Source: latest blueprint, tensor-formula canonicity
(blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationRealization (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hH : _root_.DerivedCategory.TStructure.t.plus (tensorPresentationSource A c K.obj))
    (W : Scheme.FixedEtaleOriginWitness X A
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj
        ⟨tensorPresentationSource A c K.obj, hH⟩)) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  specifiedExceptionalHomEquiv A c _ W
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus.obj K)
      ((fixedCompactSupportComparisonIso A c).hom.app
          ⟨tensorPresentationSource A c K.obj, hH⟩ ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
          (tensorPresentationCounitArrow A c K.obj)) ≫
    (tensorPresentationTargetIso A c K).hom

/-- Change of the tensor source induced by the canonical right-adjoint comparison.
Source: latest blueprint, tensor-formula canonicity
(blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationSourceIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).mapIso
      ((tensorPresentationRightIso A c d).app (𝟙_ _))

/-- Comparison with the fixed compactification used by the specified constructible functor.
Source: latest blueprint, agreement with def-pur-co-smoothness, clause 2
(blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationSpecifiedIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [HasCompactification f]
    (c : Compactification f) :
    tensorPresentationEtaleRight A c ≅ Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f :=
  (tensorPresentationEtaleAdjunction A c).rightAdjointUniq
    ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIso A c).symm)

/-- The specified theta, with the source ordered as pullback tensor omega, in exactly
those comparison coordinates used by finiteComparedTensorClause. Source: latest blueprint,
def-pur-co-smoothness, clause 2 (blueprint: lem-pur-tensor-map-presentation-independent). -/
def tensorPresentationSpecifiedMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
    ((tensorPresentationSymmetry (ModuleCat.{u + 1} A) X
        ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)
        (Etale.dualizingComplex (ModuleCat.{u + 1} A) f)).hom ≫
      Etale.dualizingComplexTensorMap A f K)

/-- The realization on the finite-type purity domain. Compactness of the target is
supplied by its finite-type structure morphism, rather than assumed separately.
Source: latest blueprint, tensor-formula canonicity
(blueprint: lem-pur-tensor-map-presentation-independent). -/
def purityTensorPresentationRealization (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [Y.Over (Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (hH : _root_.DerivedCategory.TStructure.t.plus
      (tensorPresentationSource P.Coefficient c K.obj))
    (W : Scheme.FixedEtaleOriginWitness X P.Coefficient
      ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj
        ⟨tensorPresentationSource P.Coefficient c K.obj, hH⟩)) :=
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  tensorPresentationRealization P.Coefficient c K hH W

/-- Presentation independence of the specified tensor map, including every etale-origin
witness, identity and cocycle laws, and agreement with the fixed constructible theta.
Source: latest blueprint, sec-smooth-purity/sk-thm-smooth-purity,
prop-pur-smooth-purity-naturality-cover.proof.md, second paragraph
(blueprint: lem-pur-tensor-map-presentation-independent).

Proof:
1. Pullback preserves finite Tor amplitude. Exceptional preservation gives bounded
constructibility of omega_c and G_c K. Tensor closure gives bounded constructibility
of the displayed source, hence a bounded-below etale origin, for every c. Finite-type
compactifications have finite-dimensional proper parts. Thus every Hom bijection used
here is in the comparison class of thm-sf-ambient-adjoint-class.
2. Transpose the canonical right comparison through those Hom bijections. Their
compactification compatibility gives the counit identity epsilon_c rho inverse =
epsilon_d F_d(b). Witness independence gives the same identity for any retained witness.
3. Apply the compactification comparison square for projection, invert the projection
maps on the bounded finite-Tor domain, and use naturality in omega along b at the unit.
This gives the square for the inverse projection arrows.
4. Prepend symmetry and append counit tensor identity and the unitor. Naturality of
symmetry and unitor, the square in step 3 and the counit identity in step 2 identify
the two arrows to be transposed.
5. Naturality in the source of the class Hom bijections transposes that square to
theta_c followed by b_K = (identity tensor b_unit) followed by theta_d. Changing either
origin witness fixes this same arrow, since the Hom chain is witness independent.
6. The right comparisons obey identity and cocycle by uniqueness of adjoints and
compact-support coherence. Tensor functoriality gives the same laws for the source
comparisons. Pasting the squares in step 5 gives the corresponding laws for these
maps. Set d to the compactification defining the recorded constructible functor:
its defining transpose is precisely dualizingComplexTensorMap, with the source
symmetry inserted as in def-pur-co-smoothness. This proves agreement with that theta.
No unbounded pro-etale adjunction is used. -/
theorem tensorMap_presentation_independent
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (_hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Y
      ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K.obj)) :
    ∃ hH : ∀ c : Compactification f, _root_.DerivedCategory.TStructure.t.plus
        (tensorPresentationSource P.Coefficient c K.obj),
      (∀ (c c' : Compactification f)
        (W : Scheme.FixedEtaleOriginWitness X P.Coefficient
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj
            ⟨tensorPresentationSource P.Coefficient c K.obj, hH c⟩))
        (W' : Scheme.FixedEtaleOriginWitness X P.Coefficient
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj
            ⟨tensorPresentationSource P.Coefficient c' K.obj, hH c'⟩)),
        purityTensorPresentationRealization P c K (hH c) W ≫
            (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
              ((tensorPresentationRightIso P.Coefficient c c').hom.app K.obj) =
          (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
              (tensorPresentationSourceIso P.Coefficient c c' K.obj).hom ≫
            purityTensorPresentationRealization P c' K (hH c') W') ∧
      (∀ (c : Compactification f)
        (W W' : Scheme.FixedEtaleOriginWitness X P.Coefficient
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj
            ⟨tensorPresentationSource P.Coefficient c K.obj, hH c⟩)),
        purityTensorPresentationRealization P c K (hH c) W =
          purityTensorPresentationRealization P c K (hH c) W') ∧
      (∀ c : Compactification f,
        tensorPresentationRightIso P.Coefficient c c = Iso.refl _ ∧
        tensorPresentationSourceIso P.Coefficient c c K.obj = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification f,
        tensorPresentationRightIso P.Coefficient c₁ c₃ =
          tensorPresentationRightIso P.Coefficient c₁ c₂ ≪≫
            tensorPresentationRightIso P.Coefficient c₂ c₃ ∧
        tensorPresentationSourceIso P.Coefficient c₁ c₃ K.obj =
          tensorPresentationSourceIso P.Coefficient c₁ c₂ K.obj ≪≫
            tensorPresentationSourceIso P.Coefficient c₂ c₃ K.obj) ∧
      (∀ (hc : HasCompactification f) (c : Compactification f)
        (W : Scheme.FixedEtaleOriginWitness X P.Coefficient
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj
            ⟨tensorPresentationSource P.Coefficient c K.obj, hH c⟩)),
        purityTensorPresentationRealization P c K (hH c) W ≫
            (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
              ((@tensorPresentationSpecifiedIso.{u} P.Coefficient _ _ X Y f _ hc c).hom.app
                K.obj) =
          (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
              (((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj
                ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
                  K.obj)).map
                ((@tensorPresentationSpecifiedIso.{u} P.Coefficient _ _ X Y f _ hc c).hom.app
                  (𝟙_ _))) ≫
            @tensorPresentationSpecifiedMap.{u} P.Coefficient _ _ X Y f hc K.obj) := by
  sorry

end AlgebraicGeometry.ProEtale
