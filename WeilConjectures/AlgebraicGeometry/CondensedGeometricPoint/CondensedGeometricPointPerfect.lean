/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldComplexCohomologySplitting
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectScalarChangeModel
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteStrictPerfectHom
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # Perfect scalar complexes at a condensed geometric point

Source: current blueprint, sec-six-functors/sk-lem-finite, geometric-point statement
and first proof paragraph (blueprint: lem-sf-condensed-geometric-point-perfect).

## Main definitions

- `fiber`: derived singleton evaluation after the canonical condensed-point equivalence.
- `restricted`: restriction of this fixed functor to the two specified full subcategories.
- `Statement`: exact symmetric monoidal equivalence, with the canonical closed comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGeometricPoint

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

/-- The ambient, unbounded derived category over the actual pulled-back ring object.
Source: blueprint sk-lem-finite (blueprint: lem-sf-condensed-geometric-point-perfect). -/
abbrev Complexes := DerivedCategory
  (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
    (condensedRingObj Λ (Spec (.of k))))

/-- The object property whose full subcategory is the recorded
`ConstantModelConstructibleFiniteTor Λ (Spec k)`; this just exposes its defining property.
Source: blueprint sk-lem-finite (blueprint: lem-sf-condensed-geometric-point-perfect). -/
abbrev ctf : ObjectProperty (Complexes Λ k) :=
  constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
    _root_.DerivedCategory.finiteTorAmplitude _

/-- The full perfect subcategory uses the recorded bounded finite projective predicate,
with exactly the scalar ring Λ(*), rather than the ring of all continuous Qbar functions.
Source: blueprint sk-lem-finite (blueprint: lem-sf-condensed-geometric-point-perfect). -/
abbrev perfect : ObjectProperty
    (DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) :=
  _root_.DerivedCategory.IsPerfectRingComplex

/-- The fixed fibre functor. The inverse here is the inverse of the actual point pullback,
not a supplied equivalence with scalar modules. After this exact transport we use the
recorded right derived singleton evaluation. In particular its codomain is unbounded D(Λ(*)).
Source: blueprint sk-lem-finite, first proof paragraph; HRS Lemma 4.1
(blueprint: lem-sf-condensed-geometric-point-perfect). -/
def fiber : Complexes Λ k ⥤
    DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) :=
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  letI := Functor.additive_of_preserves_binary_products e.inverse
  e.inverse.mapDerivedCategory ⋙
    CondensedRing.Evaluation.G (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})

/-- Restrict the fixed derived evaluation, once its values have been proved perfect.
The proof argument only certifies membership; all objects and arrows are those of `fiber`.
Source: blueprint sk-lem-finite (blueprint: lem-sf-condensed-geometric-point-perfect). -/
def restricted (h : ∀ K : (ctf Λ k).FullSubcategory,
    perfect Λ ((fiber Λ k).obj K.obj)) :
    (ctf Λ k).FullSubcategory ⥤ (perfect Λ).FullSubcategory :=
  (perfect Λ).lift ((ctf Λ k).ι ⋙ fiber Λ k) h

/-- The detailed comparison claim, for the monoidal and triangulated structures inherited
from the ambient relative derived tensor and distinguished triangles. The standard
`ihomComparison` is the transpose of the tensorator followed by mapped evaluation; its
naturality includes both variables. Its displayed equation retains the actual evaluation.
The inherited braidings are the K-flat derived Koszul braidings. The single structure `m`
is braided, and its underlying monoidal structure is the one used by the internal-Hom
comparison, its evaluation equation and the unit comparison.
Source: blueprint sk-lem-finite, first proof paragraph; Stacks 08JH and 08JJ
(blueprint: lem-sf-condensed-geometric-point-perfect). -/
def RestrictedComparison
    [ObjectProperty.IsMonoidal (ctf Λ k)] [ObjectProperty.IsMonoidal (perfect Λ)]
    [ObjectProperty.IsMonoidalClosed (ctf Λ k)]
    [ObjectProperty.IsMonoidalClosed (perfect Λ)]
    [(ctf Λ k).IsTriangulated] [(perfect Λ).IsTriangulated]
    (h : ∀ K : (ctf Λ k).FullSubcategory, perfect Λ ((fiber Λ k).obj K.obj)) : Prop :=
  letI := _root_.DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))
  letI := _root_.DerivedCategory.braidedCategory'
    (ModuleCat.{u + 1} (condensedScalarRing Λ))
  ∃ m : (restricted Λ k h).Braided,
    letI : (restricted Λ k h).Monoidal := m.toMonoidal
    (restricted Λ k h).IsEquivalence ∧
    (∃ s : (restricted Λ k h).CommShift ℤ,
      letI := s
      (restricted Λ k h).IsTriangulated) ∧
    (∀ C D : (ctf Λ k).FullSubcategory,
      IsIso ((Functor.LaxMonoidal.ihomComparison (restricted Λ k h) C).natTrans.app D)) ∧
    (∀ C D : (ctf Λ k).FullSubcategory,
      (restricted Λ k h).obj C ◁
          (Functor.LaxMonoidal.ihomComparison (restricted Λ k h) C).natTrans.app D ≫
          (ihom.ev ((restricted Λ k h).obj C)).app ((restricted Λ k h).obj D) =
        Functor.LaxMonoidal.μ (restricted Λ k h) C ((ihom C).obj D) ≫
          (restricted Λ k h).map ((ihom.ev C).app D)) ∧
    (∀ C : (ctf Λ k).FullSubcategory,
      Nonempty ((restricted Λ k h).obj ((ihom C).obj (𝟙_ _)) ≅
        (ihom ((restricted Λ k h).obj C)).obj (𝟙_ _)))

omit Λ k in
/-- The discrete condensed ring of the actual quotient by the uniformizer ideal to power
`n`. This specializes the recorded continuous-map construction with the discrete topology;
it does not substitute the different quotient by a power of the rational prime.
Source: blueprint sk-lem-finite and sk-def-sfb-admissible-coefficients
(blueprint: lem-sf-condensed-geometric-point-perfect). -/
def residueRingSheaf (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E) (n : ℕ) :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  let A := PadicAlgCl.integers ℓ E ⧸ (Ideal.span ({π} : Set _)) ^ n
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  Profinite.continuousMapRingSheaf A

omit Λ k in
/-- The underlying abelian sheaf of `residueRingSheaf`, carrying the canonical ring-object
structure furnished by `sheafCompose`.
Source: blueprint sk-lem-finite, discrete coefficient case
(blueprint: lem-sf-condensed-geometric-point-perfect). -/
abbrev residueRingObj (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E) (n : ℕ) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (residueRingSheaf ℓ E π n)

omit Λ k in
omit Λ in
end AlgebraicGeometry.ProEtale.CondensedGeometricPoint
