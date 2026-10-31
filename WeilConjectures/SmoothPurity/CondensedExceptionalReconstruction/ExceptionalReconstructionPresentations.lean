/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointComparisons
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemTransport
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleTowerBrownAdjunction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.ClopenStrictSystemComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealization
import WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.FilteredCondensedRepresentingPair
import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import WeilConjectures.CategoryTheory.Derived.DerivedMorphismPresheaf
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible

/-! # Condensed exceptional inverse image from an ordinary coefficient system

Source: current blueprint sec-smooth-purity, sk-prop-sp-integral-adjunction,
sk-prop-sp-rational, sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical;
WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperShriek.lean,
`boundedConstructibleUpperShriekOfCompactification` and its specifying adjunction.
(blueprint: def-pur-exceptional-reconstruction-presentations).

The coefficient field is the canonical universe lift of Q_l. All systems below are
objects of ordinary derived categories of strict varying-coefficient module sheaves.
The helper records package the constructions and clauses of this node. In particular
no ambient unbounded pro-etale exceptional right adjoint is assumed or constructed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance high] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleLevelDerived
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived
attribute [local instance high] CategoryTheory.Functor.preservesZeroMorphisms_of_additive
attribute [local instance high] AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_additive
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_limits
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_colimits
  SheafOfModules.CoefficientSystemOrdinaryImage.systemInverseAdditive
  SheafOfModules.CoefficientSystemOrdinaryImage.inverseAdditive
  WeilConjectures.PurityFiniteSetting.ClopenSequenceRealizationData.ordinaryAdditive
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local irreducible] CategoryTheory.mateEquiv CategoryTheory.conjugateEquiv
attribute [local irreducible] DerivedCategory.Q
  CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible]   AlgebraicGeometry.ProEtale.SemilinearProperOpen.R
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.adj
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.rightAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactification
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedExceptionalReconstruction
open CondensedERealization CompactSupportCondensedRealization PurityFiniteSetting

/-- The canonical universe lift of Q_l, with its unchanged scalar algebra.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-presentations). -/
abbrev Field (l : ℕ) [Fact l.Prime] := ULift.{u} (Padic l)

/-- The transported normed-field structure on the canonical lift of Q_l.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-presentations). -/
instance fieldNormed (l : ℕ) [Fact l.Prime] : NormedField (Field.{u} l) :=
  { (inferInstance : _root_.Field (Field.{u} l)),
    (inferInstance : NormedCommRing (Field.{u} l)) with
    dist_eq x y := dist_eq_norm_neg_add x.down y.down
    norm_mul x y := norm_mul x.down y.down }

/-- The degree-one Q_l extension structure on its canonical universe lift.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-presentations). -/
instance fieldFinite (l : ℕ) [Fact l.Prime] : FiniteDimensional ℚ_[l] (Field.{u} l) :=
  (ULift.moduleEquiv (R := ℚ_[l]) (M := ℚ_[l])).symm.finiteDimensional

variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The recorded bounded constructible category for the finite-subfield-valued closure ring.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-presentations). -/
abbrev Omega (T : Scheme.{u}) :=
  BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) T)

/-- The canonical scalar embedding of the lifted Q_l into its fixed algebraic closure.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-presentations). -/
def embedding : Field.{u} l →ₐ[ℚ_[l]] PadicAlgCl l :=
  (IsScalarTower.toAlgHom ℚ_[l] ℚ_[l] (PadicAlgCl l)).comp
    (ULift.algEquiv : Field.{u} l ≃ₐ[ℚ_[l]] ℚ_[l]).toAlgHom

variable (D : CondensedERealization.Data l (Field.{u} l) k)

/-- U_T is raw rationalization, the recorded scalar-extension realization J_T, then
derived extension to the finite-subfield-valued condensed closure coefficient.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-presentations). -/
def realization (T : Base k) : Integral l (Field.{u} l) T.scheme ⥤ Omega l T.scheme :=
  pbcRationalization T.scheme (pbcIntegralDatum l (Field.{u} l)) (pbcUniformizer l (Field.{u} l)) ⋙
    (D.atObject T).realization.functor ⋙
      ObjectProperty.lift (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme))
        ((boundedConstructible (Coefficient (Field.{u} l) T.scheme)).ι ⋙
          omegaScalar l (Field.{u} l) (embedding l) T.scheme)
        (fun K ↦ omegaScalar_preserves l (Field.{u} l) (embedding l) T.scheme K)

open AlgebraicGeometry.ProEtale.SemilinearProperOpen

/-- Apply the specified ordinary square termwise to complexes, with both composites
written separately. This keeps the presentation normalization explicit without unfolding
coefficient rings during elaboration.
Source: current blueprint sk-prop-sp-integral-adjunction, ordinary localization.
(blueprint: def-pur-exceptional-reconstruction-presentations). -/
def complexSquare
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {E : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} E]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms C] [HasZeroMorphisms E]
    (F : A ⥤ B) (G : B ⥤ E) (H : A ⥤ C) (I : C ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [H.PreservesZeroMorphisms] [I.PreservesZeroMorphisms]
    (e : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (I.mapHomologicalComplex (.up ℤ)).obj ((H.mapHomologicalComplex (.up ℤ)).obj K) where
  f i := e.hom.app (K.X i)
  comm' i j _ := (e.hom.naturality (K.d i j)).symm

/-- The localization square expressed abstractly, so the four fixed factorization
isomorphisms can be checked without repeatedly expanding the coefficient categories.
Source: current blueprint sk-prop-sp-integral-adjunction, ordinary localization.
(blueprint: def-pur-exceptional-reconstruction-presentations). -/
def localizationSquare
    {A B C E A' B' C' E' : Type u₁}
    [Category.{v₁} A] [Category.{v₁} B] [Category.{v₁} C] [Category.{v₁} E]
    [Category.{v₂} A'] [Category.{v₂} B'] [Category.{v₂} C'] [Category.{v₂} E']
    (QA : A ⥤ A') (QB : B ⥤ B') (QC : C ⥤ C') (QE : E ⥤ E')
    (F : A ⥤ B) (G : B ⥤ E) (H : A ⥤ C) (I : C ⥤ E)
    (F' : A' ⥤ B') (G' : B' ⥤ E') (H' : A' ⥤ C') (I' : C' ⥤ E')
    (f : QA ⋙ F' ≅ F ⋙ QB) (g : QB ⋙ G' ≅ G ⋙ QE)
    (h : QA ⋙ H' ≅ H ⋙ QC) (i : QC ⋙ I' ≅ I ⋙ QE)
    (e : ∀ K : A, G.obj (F.obj K) ⟶ I.obj (H.obj K))
    (e' : F' ⋙ G' ≅ H' ⋙ I') : Prop :=
  ∀ K : A, e'.hom.app (QA.obj K) ≫ I'.map (h.hom.app K) ≫ i.hom.app (H.obj K) =
    G'.map (f.hom.app K) ≫ g.hom.app (F.obj K) ≫ QE.map (e K)

/-- Paste the specified proper and open presentation comparisons.
Source: current blueprint sk-prop-sp-integral-adjunction, proper/open localization.
(blueprint: def-pur-exceptional-reconstruction-presentations). -/
def pasteComparisons
    {A B C A' B' C' : Type u₁}
    [Category.{v₁} A] [Category.{v₁} B] [Category.{v₁} C]
    [Category.{v₁} A'] [Category.{v₁} B'] [Category.{v₁} C']
    (j : A ⥤ B) (g : B ⥤ C) (eX : A ⥤ A') (eZ : B ⥤ B') (eY : C ⥤ C')
    {j' : A' ⥤ B'} {g' : B' ⥤ C'}
    (proper : g ⋙ eY ≅ eZ ⋙ g') (openComparison : j ⋙ eZ ≅ eX ⋙ j') :
    (j ⋙ g) ⋙ eY ≅ eX ⋙ (j' ⋙ g') :=
  Functor.associator j g eY ≪≫ Functor.isoWhiskerLeft j proper ≪≫
    (Functor.associator j eZ g').symm ≪≫
    Functor.isoWhiskerRight openComparison g' ≪≫ Functor.associator eX j' g'

/-- Normalization on complex representatives of the strict-system presentation comparison.
The equation fixes the derived inverse-image comparison by ordinary localization.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: def-pur-exceptional-reconstruction-presentations). -/
def SequenceLocalization {T S : Scheme.{u}} (g : T ⟶ S)
    (PT : ExceptionalProEvaluation T (clopenSystemRing l (Field.{u} l))
      (clopenSystemUniformizer l (Field.{u} l)))
    (PS : ExceptionalProEvaluation S (clopenSystemRing l (Field.{u} l))
      (clopenSystemUniformizer l (Field.{u} l)))
    (O : ExceptionalProOrdinaryImage (clopenSystemRing l (Field.{u} l))
      (clopenSystemUniformizer l (Field.{u} l)) g)
    (I : SheafOfModules.CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology T)
      _ _ _ _ _ O PS PT)
    (ST : ClopenSequenceRealization l (Field.{u} l) T)
    (SS : ClopenSequenceRealization l (Field.{u} l) S)
    (ordinaryPull : SS.ordinary.functor ⋙
      pull (quotientRings l (Field.{u} l)) (quotientMaps l (Field.{u} l)) g ≅
        O.inverse ⋙ ST.ordinary.functor)
    (derivedPull : SS.derived.functor ⋙
      P (quotientRings l (Field.{u} l)) (quotientMaps l (Field.{u} l)) g ≅
        I.system.inverse ⋙ ST.derived.functor) : Prop :=
  letI := SemilinearProperOpen.pull_additive (quotientRings l (Field.{u} l))
    (quotientMaps l (Field.{u} l)) g
  letI := SS.ordinaryAdditive
  letI := ST.ordinaryAdditive
  letI := O.systemInverseAdditive
  localizationSquare
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (SS.ordinary.functor.mapHomologicalComplex (.up ℤ))
    ((pull (quotientRings l (Field.{u} l)) (quotientMaps l (Field.{u} l))
      g).mapHomologicalComplex (.up ℤ))
    (O.inverse.mapHomologicalComplex (.up ℤ))
    (ST.ordinary.functor.mapHomologicalComplex (.up ℤ))
    SS.derived.functor (P (quotientRings l (Field.{u} l))
      (quotientMaps l (Field.{u} l)) g) I.system.inverse ST.derived.functor
    SS.factors
    ((pull (quotientRings l (Field.{u} l)) (quotientMaps l (Field.{u} l))
      g).mapDerivedCategoryFactors)
    I.system.inverseFactors ST.factors
    (complexSquare SS.ordinary.functor
      (pull (quotientRings l (Field.{u} l)) (quotientMaps l (Field.{u} l)) g)
      O.inverse ST.ordinary.functor ordinaryPull) derivedPull

/-- Graph of a section map across definitionally equivalent coefficient presentations.
The heterogeneous input equality records the same section without forcing Lean to expand
all sheafification constructions during elaboration.
Source: current blueprint sk-prop-sp-integral-adjunction, section normalization.
(blueprint: def-pur-exceptional-reconstruction-presentations). -/
def sectionValue {A B : Type u₁} (F : A → B)
    {C E : Type u₁} (x : C) (y : E) : Prop :=
  ∃ a : A, HEq a x ∧ HEq (F a) y

end WeilConjectures.CondensedExceptionalReconstruction
