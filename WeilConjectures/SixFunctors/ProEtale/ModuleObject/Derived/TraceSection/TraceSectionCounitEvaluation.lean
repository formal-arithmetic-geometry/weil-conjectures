/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfRfShriekPreservation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompCompositionWitnesses
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceSection.TraceFiniteProjectionIsomorphism
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceFiniteCtfModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceSection.TraceFiniteCoefficientPrimary
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Evaluation along a section

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/
lem-trf-trace-class-diagonal-pairing.proof.md, Step 3(d), with Step 3(a).
(blueprint: lem-trf-section-counit-evaluation).

The auxiliary definitions construct the coefficient stage, the left-factor inverse
projection, the compact-support section comparison and its adjunction conjugate,
and the three arrows l, V and theta of the section calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceSection

/-- Structure-map finite type in the bundled separated finite-type category.
Source: Step 3(d) (blueprint: lem-trf-section-counit-evaluation). -/
instance structureFiniteType (k : Type u) [Field k] (T : SepFinType k) :
    LocallyOfFiniteType (T.obj.left ↘ Spec (.of k)) := by
  change LocallyOfFiniteType T.obj.hom
  infer_instance

/-- Structure-map quasi-compactness in the bundled finite-type category.
Source: Step 3(d) (blueprint: lem-trf-section-counit-evaluation). -/
instance structureQuasiCompact (k : Type u) [Field k] (T : SepFinType k) :
    QuasiCompact (T.obj.left ↘ Spec (.of k)) := by
  change QuasiCompact T.obj.hom
  infer_instance

/-- Structure-map separatedness in the bundled category.
Source: Step 3(d) (blueprint: lem-trf-section-counit-evaluation). -/
instance structureSeparated (k : Type u) [Field k] (T : SepFinType k) :
    IsSeparated (T.obj.left ↘ Spec (.of k)) := by
  change IsSeparated T.obj.hom
  infer_instance

/-- Separatedness of a composite in the bundled category.
Source: Step 3(a) (blueprint: lem-trf-section-counit-evaluation). -/
instance compSeparated (k : Type u) [Field k] {T U V : SepFinType k}
    (a : T ⟶ U) (b : U ⟶ V) [IsSeparated a.hom.left] [IsSeparated b.hom.left] :
    IsSeparated (a ≫ b).hom.left := by
  change IsSeparated (a.hom.left ≫ b.hom.left)
  infer_instance

/-- Finite type of a composite in the bundled category.
Source: Step 3(a) (blueprint: lem-trf-section-counit-evaluation). -/
instance compFiniteType (k : Type u) [Field k] {T U V : SepFinType k}
    (a : T ⟶ U) (b : U ⟶ V)
    [LocallyOfFiniteType a.hom.left] [LocallyOfFiniteType b.hom.left] :
    LocallyOfFiniteType (a ≫ b).hom.left := by
  change LocallyOfFiniteType (a.hom.left ≫ b.hom.left)
  infer_instance

/-- Quasi-compactness of a composite in the bundled category.
Source: Step 3(a) (blueprint: lem-trf-section-counit-evaluation). -/
instance compQuasiCompact (k : Type u) [Field k] {T U V : SepFinType k}
    (a : T ⟶ U) (b : U ⟶ V) [QuasiCompact a.hom.left] [QuasiCompact b.hom.left] :
    QuasiCompact (a ≫ b).hom.left := by
  change QuasiCompact (a.hom.left ≫ b.hom.left)
  infer_instance

/-- Bundled finite-type schemes over a field are Noetherian; this is not a hypothesis.
Source: finite-type schemes in Step 3(d) (blueprint: lem-trf-section-counit-evaluation). -/
instance schemeNoetherian (k : Type u) [Field k] (T : SepFinType k) :
    IsNoetherian T.obj.left := by
  let : CompactSpace T.obj.left := QuasiCompact.compactSpace_of_compactSpace T.obj.hom
  let : IsLocallyNoetherian T.obj.left := LocallyOfFiniteType.isLocallyNoetherian T.obj.hom
  exact ⟨⟩

/-- Algebraic closedness already specified by the finite-field datum.
Source: coefficient conventions (blueprint: lem-trf-section-counit-evaluation). -/
instance closureAlgClosed (D : WeilConjectures.FiniteFieldDatum.{u}) :
    IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀

/-- The geometric finite-field datum has its specified positive characteristic.
Source: coefficient conventions (blueprint: lem-trf-section-counit-evaluation). -/
instance closureCharP (D : WeilConjectures.FiniteFieldDatum.{u}) : CharP D.k D.p := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have hc : Fintype.card D.k₀ = D.q := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (hc.trans D.cardinality_eq)
  exact charP_of_injective_algebraMap' D.k₀ D.p

/-- Primality of the characteristic follows from the specified prime.
Source: coefficient conventions (blueprint: lem-trf-section-counit-evaluation). -/
instance closureCharPrime (D : WeilConjectures.FiniteFieldDatum.{u}) :
    Fact (ringChar D.k).Prime := ⟨by rw [ringChar.eq D.k D.p]; exact D.prime⟩

/-- Invertibility convention for the supplied finite-coefficient functors.
Source: coefficient conventions (blueprint: lem-trf-section-counit-evaluation). -/
instance closureCharDifferent (ell : ℕ) (D : WeilConjectures.FiniteFieldDatum.{u})
    [Fact (ell ≠ D.p)] : Fact (ringChar D.k ≠ ell) := ⟨by
  rw [ringChar.eq D.k D.p]
  exact (Fact.out : ell ≠ D.p).symm⟩

section Geometry
variable (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
  [Fact (ell ≠ D.p)]
  (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
  [DiscreteTopology A] [IsTopologicalRing A]
  (hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0)

/-- The recorded finite discrete condensed coefficient object.
Source: Step 3(d) (blueprint: lem-trf-section-counit-evaluation). -/
abbrev coefficient := Profinite.continuousMapRingObj.{u} A

/-- Inverse left-factor projection, using the two canonical signed symmetries.
Source: Step 3(d) (blueprint: lem-trf-section-counit-evaluation). -/
def projection {X Y : SepFinType D.k} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (B : ConstantModelConstructibleFiniteTor (coefficient A) Y.obj.left)
    (M : ConstantModelConstructibleFiniteTor (coefficient A) X.obj.left) :
    (lower ell D A hA f).obj (tensor ell D A hA X ((pull ell D A hA f).obj B) M) ≅
      tensor ell D A hA Y B ((lower ell D A hA f).obj M) := by
  letI := _root_.DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology X.obj.left) Ab.{u + 1})
      (condensedRingObj (coefficient A) X.obj.left))
  letI := _root_.DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology Y.obj.left) Ab.{u + 1})
      (condensedRingObj (coefficient A) Y.obj.left))
  let c := (AlgebraicGeometry.compactificationOverField D.k f.hom.left).obj.obj
  letI := finiteProjectionIsomorphism ell D A hA f c ⟨M.obj, M.property.1⟩ B
  exact (ObjectProperty.fullyFaithfulι _).preimageIso
    ((rightDerivedLowerShriekOfCompactification (coefficient A) c).mapIso
        (β_ ((pull ell D A hA f).obj B).obj M.obj) ≪≫
      (asIso (exceptionalProjectionMorphismOfCompactification
        (coefficient A) c M.obj B.obj)).symm ≪≫
      β_ ((lower ell D A hA f).obj M).obj B.obj)

/-- Transport the supplied compact-support model along an equality of morphisms.
Source: Step 3(a) (blueprint: lem-trf-section-counit-evaluation). -/
def lowerCongr {X Y : SepFinType D.k} {f g : X ⟶ Y}
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (h : f = g) : lower ell D A hA f ≅ lower ell D A hA g := by
  subst g
  exact Iso.refl _

/-- Pullback along f then its section, with the native compositor and identity comparison.
Source: Step 3(d) (blueprint: lem-trf-section-counit-evaluation). -/
def pullSection {X Y : SepFinType D.k} (f : Y ⟶ X) (j : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated j.hom.left] [LocallyOfFiniteType j.hom.left] [QuasiCompact j.hom.left]
    (h : j ≫ f = 𝟙 X) : pull ell D A hA f ⋙ pull ell D A hA j ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (ObjectProperty.ι _)
      ((leftDerivedUpperStarComp (coefficient A) j.hom.left f.hom.left).symm ≪≫
        eqToIso (congrArg (fun g ↦ moduleObjectDerivedPullback (coefficient A) g)
          (congrArg (fun a ↦ a.hom.left) h)) ≪≫
        leftDerivedUpperStarId (coefficient A) X.obj.left))

/-- The arrow V, transposed along the specified exceptional adjunction of f.
Source: Step 3(d) (blueprint: lem-trf-section-counit-evaluation). -/
def pairingLift {X Y : SepFinType D.k} (f : Y ⟶ X)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (B K W : ConstantModelConstructibleFiniteTor (coefficient A) X.obj.left)
    (v : tensor ell D A hA X B K ⟶ W) :
    tensor ell D A hA Y ((pull ell D A hA f).obj B)
      ((upper ell D A hA f).obj K) ⟶ (upper ell D A hA f).obj W :=
  (adj ell D A hA f).homEquiv _ W
    ((projection ell D A hA f B ((upper ell D A hA f).obj K)).hom ≫
      (⟨𝟙 B.obj ⊗ₘ ((adj ell D A hA f).counit.app K).hom⟩ :
        tensor ell D A hA X B ((lower ell D A hA f).obj ((upper ell D A hA f).obj K)) ⟶
          tensor ell D A hA X B K) ≫ v)

/-- Theta is inverse left-factor projection for j after the inverse section pullback map.
Source: Step 3(d) (blueprint: lem-trf-section-counit-evaluation). -/
def theta {X Y : SepFinType D.k} (f : Y ⟶ X) (j : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated j.hom.left] [LocallyOfFiniteType j.hom.left] [QuasiCompact j.hom.left]
    (h : j ≫ f = 𝟙 X)
    (B K : ConstantModelConstructibleFiniteTor (coefficient A) X.obj.left) :
    (lower ell D A hA j).obj (tensor ell D A hA X B K) ≅
      tensor ell D A hA Y ((pull ell D A hA f).obj B) ((lower ell D A hA j).obj K) :=
  (lower ell D A hA j).mapIso
    ((ObjectProperty.fullyFaithfulι _).preimageIso
      (X := tensor ell D A hA X B K)
      (Y := tensor ell D A hA X ((pull ell D A hA j).obj ((pull ell D A hA f).obj B)) K)
      (tensorIso ((ObjectProperty.ι _).mapIso
        ((pullSection ell D A hA f j h).app B)).symm (Iso.refl K.obj))) ≪≫
    projection ell D A hA j ((pull ell D A hA f).obj B) K

end Geometry

end AlgebraicGeometry.ProEtale.CondensedRing.TraceSection
