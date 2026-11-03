/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariant
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalConeMap
public import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDncFamily
public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.AlgebraicGeometry.SectionReesNoetherianGeometry.SectionReesNoetherianGeometry
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfLocallyClosedPerfectGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection

/-!
# Condensed deformation-to-the-normal-cone section invariant

This module states the condensed interface for `sk-thm-dnc`.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`
(blueprint: sk-thm-dnc).

Main declarations: `dncSectionBaseChangeMap` constructs the native mate;
`dncCanonicalTheta` and `dncCanonicalEta` specialize it to the two fibres;
`DncNormalizedComparison` and `dncSectionInvariant_condensed_statement` give the full statement.
The theorem proof is postponed and follows the twelve proof steps in its docstring.
The fibre maps below are expressed using the derived pullback functors and the
normal-cone pullback square, so that the statement does not replace the geometric
objects by arbitrary isomorphic objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing


/-- Finite-type schemes over a field are Noetherian; used only for unit membership.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof step 1 (blueprint: sk-thm-dnc). -/
local instance dncBaseNoetherian {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom

section
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  (hcd : BaseFieldFiniteCD ell k) (ha : IsLocalizingAdmissibleCoefficient ell Λ)
  {B V B' V' : Over (Spec (.of k))}
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  (g : V ⟶ B) [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
  (g' : V' ⟶ B') [IsSeparated g'.left] [LocallyOfFiniteType g'.left]
  [QuasiCompact g'.left] (b : B' ⟶ B) (v : V' ⟶ V)
  (sq : IsPullback v.left g'.left g.left b.left)

end

/-- The geometric finite-field datum has prime characteristic.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
fixed purity conventions (blueprint: sk-thm-dnc). -/
local instance dncPrimeCharacteristic (D : WeilConjectures.FiniteFieldDatum.{u}) :
    Fact (ringChar D.k).Prime := by
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩

/-- The coefficient prime differs from the geometric base characteristic.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
fixed purity conventions (blueprint: sk-thm-dnc).
Proof: the cardinality of D.k₀ gives characteristic D.p; its injective algebra map
into the algebraic closure gives CharP D.k D.p. Hence ringChar D.k = D.p, and
hell.symm is the required inequality. Only this proposition-only typing fact is
postponed, with no chosen object or morphism. -/
theorem dncCharacteristicNe (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) (hell : ell ≠ D.p) : Fact (ringChar D.k ≠ ell) := by
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ⟨by rw [ringChar.eq D.k D.p]; exact Ne.symm hell⟩

section
variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
    (Padic.coefficientExtensionRing ell (DiagonalCoefficients.bottomField ell).1 n))))
  {B V B' V' : Over (Spec (.of D.k))}
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  (g : V ⟶ B) [Smooth g.left] [IsSeparated g.left]
  [LocallyOfFiniteType g.left] [QuasiCompact g.left]
  (g' : V' ⟶ B') [Smooth g'.left] [IsSeparated g'.left]
  [LocallyOfFiniteType g'.left] [QuasiCompact g'.left]
  (b : B' ⟶ B) (v : V' ⟶ V)
  (sq : IsPullback v.left g'.left g.left b.left)

end

/-- The normal-cone object used by the zero-fibre clause.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncNormalOver
    (D : WeilConjectures.FiniteFieldDatum.{u}) {B V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) : Over (Spec (.of D.k)) :=
  Over.mk (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)

/-- The actual normal-cone zero section, as a morphism over the finite field.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncNormalSection
    (D : WeilConjectures.FiniteFieldDatum.{u}) {B V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) (hs : s ≫ g = 𝟙 B) :
    B ⟶ dncNormalOver D g s :=
  Over.homMk (Scheme.Hom.normalConeZeroSection s.left) (by
    change Scheme.Hom.normalConeZeroSection s.left ≫
      (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom) = B.hom
    rw [← Category.assoc,
      Scheme.Hom.normalConeZeroSection_normalConeProj (congrArg (fun f => f.left) hs),
      Category.id_comp])

/-- The actual normal-cone projection, as a morphism over the finite field.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncNormalProjection
    (D : WeilConjectures.FiniteFieldDatum.{u}) {B V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) : dncNormalOver D g s ⟶ B :=
  Over.homMk (Scheme.Hom.normalConeProj g.left s.left) (by rfl)

/-- The affine-line base map induced by a morphism of bases.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncBaseChangeMap
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' : Over (Spec (.of D.k))} (b : B' ⟶ B) :
    condensedDncBase D B' ⟶ condensedDncBase D B :=
  Over.homMk (AffineSpace.map (ULift.{u} (Fin 1)) b.left) (by
    change AffineSpace.map (ULift.{u} (Fin 1)) b.left ≫
      ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom) =
      (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left) ≫ B'.hom
    rw [← Category.assoc, AffineSpace.map_over]
    rw [Category.assoc, b.w])

/-- The geometric facts used to type the condensed normal-cone invariant.

Proof: apply smooth base-change stability to the normal-cone pullback square; inherit
separatedness, finite type, and quasi-compactness from the original pair, and use the
normal-cone relative-dimension calculation.  The section equation `hs` identifies the
zero section with the pullback centre.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`.
(blueprint: sk-thm-dnc). -/
theorem dncNormalGeometryFacts
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g.left s.left) ∧
    IsSeparated (Scheme.Hom.normalConeProj g.left s.left) ∧
    LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left) ∧
    QuasiCompact (Scheme.Hom.normalConeProj g.left s.left) := by
  have hsg : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f ↦ f.left) hs
  letI := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g.left s.left hsg
  letI := SmoothOfRelativeDimension.smooth d
    (Scheme.Hom.deformationSpaceProj g.left s.left)
  have sq := Scheme.Hom.isPullback_normalConeToDeformationSpace g.left s.left
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  exact ⟨MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) sq inferInstance,
    MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance,
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance,
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance⟩

/-- The condensed module on the normal cone obtained from the actual normal-cone
projection and zero section. This is the normal-cone object in the statement.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md.
(blueprint: sk-thm-dnc). -/
noncomputable def dncNormalSectionInvariant
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
        (Padic.coefficientExtensionRing ell E n))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left)) := by
  letI : IsNoetherian B.left := isNoetherian_of_locallyOfFiniteType B.hom
  have hsg : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f => f.left) hs
  have hf := dncNormalGeometryFacts D d g s hs
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g.left s.left) := hf.1
  letI : Smooth (Scheme.Hom.normalConeProj g.left s.left) :=
    SmoothOfRelativeDimension.smooth d _
  letI : IsSeparated (Scheme.Hom.normalConeProj g.left s.left) := hf.2.1
  letI : LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.1
  letI : QuasiCompact (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.2
  letI : IsSeparated ((dncNormalOver D g s).hom) := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : LocallyOfFiniteType ((dncNormalOver D g s).hom) := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : QuasiCompact ((dncNormalOver D g s).hom) := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : IsClosedImmersion (dncNormalSection D g s hs).left := by
    change IsClosedImmersion (Scheme.Hom.normalConeZeroSection s.left)
    infer_instance
  letI : Smooth (dncNormalProjection D g s).left := by
    change Smooth (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : IsSeparated (dncNormalProjection D g s).left := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : LocallyOfFiniteType (dncNormalProjection D g s).left := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : QuasiCompact (dncNormalProjection D g s).left := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  exact sectionInvariant D ell hell E n hn Λ hcoeff B (dncNormalOver D g s)
    (dncNormalProjection D g s) (dncNormalSection D g s hs) (by
      apply Over.OverMorphism.ext
      exact Scheme.Hom.normalConeZeroSection_normalConeProj hsg)


/-- Canonical base-change identification at `t=1`, built from the condensed
upper-star composition and identity isomorphisms.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncOneBaseIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] {B : Over (Spec (.of k))}
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left))) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).obj
      ((moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj C) ≅ C := by
  let c := (leftDerivedUpperStarComp Λ (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)
    (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).app C
  let i := (leftDerivedUpperStarId Λ B.left).app C
  exact c.symm ≪≫ eqToIso (by rw [AffineSpace.oneSection_comp_over]) ≪≫ i

/-- Canonical base-change identification at `t=0`.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncZeroBaseIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] {B : Over (Spec (.of k))}
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left))) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)).obj
      ((moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj C) ≅ C := by
  let c := (leftDerivedUpperStarComp Λ (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)
    (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).app C
  let i := (leftDerivedUpperStarId Λ B.left).app C
  exact c.symm ≪≫ eqToIso (by rw [AffineSpace.zeroSection_comp_over]) ≪≫ i

/-- A pulled section pair over the fibre product V times_B B'.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
structure DncPulledPair
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B) where
  V' : Over (Spec (.of D.k))
  g' : V' ⟶ B'
  s' : B' ⟶ V'

/-- The canonical lift of the pulled-back section through the fibre product.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
noncomputable def dncPullbackLift
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B)
    (hs : s ≫ g = 𝟙 B) : B'.left ⟶ pullback g.left b.left :=
  pullback.lift (b.left ≫ s.left) (𝟙 B'.left) (by
    calc
      (b.left ≫ s.left) ≫ g.left = b.left ≫ (s.left ≫ g.left) := Category.assoc _ _ _
      _ = b.left ≫ 𝟙 B.left := congrArg (fun f => b.left ≫ f) (congrArg (fun f => f.left) hs)
      _ = 𝟙 B'.left ≫ b.left := by simp)

/-- The actual pullback pair used for arbitrary base change.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPair
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B)
    (hs : s ≫ g = 𝟙 B) : DncPulledPair D g s b where
  V' := Over.mk (pullback.fst g.left b.left ≫ V.hom)
  g' := Over.homMk (pullback.snd g.left b.left) (by
    change pullback.snd g.left b.left ≫ B'.hom =
      pullback.fst g.left b.left ≫ V.hom
    rw [← g.w, ← Category.assoc, pullback.condition, Category.assoc, b.w])
  s' := Over.homMk (dncPullbackLift D g s b hs) (by
    change dncPullbackLift D g s b hs ≫
      (pullback.fst g.left b.left ≫ V.hom) = B'.hom
    rw [dncPullbackLift, ← Category.assoc, pullback.lift_fst, Category.assoc, s.w, b.w])

/-- The pulled section is a section of the pulled morphism.

Proof: expand `dncPulledPair` and `dncPullbackLift`; use `pullback.lift_snd`,
`pullback.lift_fst`, the original equation `hs`, and extensionality in `Over` to
obtain the displayed retraction.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`.
(blueprint: sk-thm-dnc). -/
theorem dncPulledPair_section_retraction
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B)
    (hs : s ≫ g = 𝟙 B) :
    (dncPulledPair D g s b hs).s' ≫ (dncPulledPair D g s b hs).g' = 𝟙 B' := by
  apply Over.OverMorphism.ext
  change dncPullbackLift D g s b hs ≫ pullback.snd g.left b.left = 𝟙 B'.left
  exact pullback.lift_snd _ _ _

/-- The canonical pullback pair inherits the geometric hypotheses needed by the
recorded DNC and section-invariant definitions.  The conclusion refers to the
actual `dncPulledPair`, so no arbitrary record can provide these instances.

Proof: apply smooth and closed-immersion base change to the displayed fibre
product and use `dncPulledPair_section_retraction`.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
theorem dncPulledPairGeometryFacts
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    SmoothOfRelativeDimension d (dncPulledPair D g s b hs).g'.left ∧
    IsSeparated (dncPulledPair D g s b hs).g'.left ∧
    LocallyOfFiniteType (dncPulledPair D g s b hs).g'.left ∧
    QuasiCompact (dncPulledPair D g s b hs).g'.left ∧
    IsSeparated (dncPulledPair D g s b hs).V'.hom ∧
    LocallyOfFiniteType (dncPulledPair D g s b hs).V'.hom ∧
    QuasiCompact (dncPulledPair D g s b hs).V'.hom ∧
    IsClosedImmersion (dncPulledPair D g s b hs).s'.left := by
  change SmoothOfRelativeDimension d (pullback.snd g.left b.left) ∧
    IsSeparated (pullback.snd g.left b.left) ∧
    LocallyOfFiniteType (pullback.snd g.left b.left) ∧
    QuasiCompact (pullback.snd g.left b.left) ∧
    IsSeparated (pullback.fst g.left b.left ≫ V.hom) ∧
    LocallyOfFiniteType (pullback.fst g.left b.left ≫ V.hom) ∧
    QuasiCompact (pullback.fst g.left b.left ≫ V.hom) ∧
    IsClosedImmersion (dncPullbackLift D g s b hs)
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have hdim : SmoothOfRelativeDimension d (pullback.snd g.left b.left) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (IsPullback.of_hasPullback g.left b.left) inferInstance
  have w : pullback.fst g.left b.left ≫ V.hom =
      pullback.snd g.left b.left ≫ B'.hom := by
    rw [← g.w, ← Category.assoc, pullback.condition, Category.assoc, b.w]
  have hsec : IsClosedImmersion
      (dncPullbackLift D g s b hs ≫ pullback.snd g.left b.left) := by
    rw [dncPullbackLift, pullback.lift_snd]
    infer_instance
  refine ⟨hdim, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_,
    IsClosedImmersion.of_comp _ (pullback.snd g.left b.left)⟩
  all_goals rw [w]; infer_instance

/-- The actual DNC family attached to the canonical pulled pair, using its own
Rees construction and section invariant.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-dnc-section-family (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairFamily
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    let pair := dncPulledPair D g s b hs
    let H := dncPulledPairGeometryFacts D d g s hs b
    letI := H.1
    letI := SmoothOfRelativeDimension.smooth d pair.g'.left
    letI := H.2.1
    letI := H.2.2.1
    letI := H.2.2.2.1
    letI := H.2.2.2.2.1
    letI := H.2.2.2.2.2.1
    letI := H.2.2.2.2.2.2.1
    letI := H.2.2.2.2.2.2.2
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (condensedDncBase D B').left) Ab.{u + 1})
      (condensedRingObj Λ (condensedDncBase D B').left)) := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact condensedDncFamily D B' pair.V' pair.g' pair.s' ell hell
    (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
    (Or.inl hcoeff) d hpair

/-- The section invariant of the pulled pair, with the actual pulled section.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-section-invariant (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairSectionInvariant
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B'.left) Ab.{u + 1})
      (condensedRingObj Λ B'.left)) := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact sectionInvariant D ell hell
    (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
    (Or.inl hcoeff) B' pair.V' pair.g' pair.s' hpair

/-- The actual normal-cone invariant for the pulled pair.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-normal-bundle (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairNormalInvariant
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B'.left) Ab.{u + 1})
      (condensedRingObj Λ B'.left)) := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact dncNormalSectionInvariant D ell hell
    (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
    (Or.inl hcoeff) B' pair.V' d pair.g' pair.s' hpair

/-- The functorial associated-graded map of normal cones, induced coefficientwise
by the map of section ideals, with the same ideal-containment proof as the Rees map.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
def dncNormalPairMap {S S' X X' : Scheme.{u}} (s : S ⟶ X) (s' : S' ⟶ X')
    [IsClosedImmersion s] [IsClosedImmersion s'] (v : X' ⟶ X) (b : S' ⟶ S)
    (w : s' ≫ v = b ≫ s) : s'.ker.normalCone ⟶ s.ker.normalCone :=
  Scheme.IdealSheafData.normalConeMap v s.ker s'.ker fun {U' U} hU ↦
    (s.ker.ideal_map_appLE_le_ideal_comap v ⟨U.1, U.2⟩ ⟨U'.1, U'.2⟩ hU).trans
      (Scheme.IdealSheafData.le_def.mp
        (Scheme.Modules.closedImmersion_conormal_functorial s' s v b w).1 ⟨U'.1, U'.2⟩)

/-- The fixed Rees and associated-graded maps form Cartesian squares and respect
the augmentation and zero sections. Proof: use the coefficientwise Rees base-change
calculation in centred smooth coordinates and pass to the quotient by t at zero;
the augmentation kills each degree-one coordinate. No map is selected by this theorem.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
theorem dncPulledPairSquares
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  let φ := SectionReesBaseChange.pairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left (by
    change dncPullbackLift D g s b hs ≫ pullback.fst g.left b.left = _
    simp only [dncPullbackLift, pullback.lift_fst])
  let ν := dncNormalPairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left (by
    change dncPullbackLift D g s b hs ≫ pullback.fst g.left b.left = _
    simp only [dncPullbackLift, pullback.lift_fst])
  IsPullback φ (Scheme.Hom.deformationSpaceProj pair.g'.left pair.s'.left)
    (Scheme.Hom.deformationSpaceProj g.left s.left) (dncBaseChangeMap D b).left ∧
  pair.s'.left.deformationSpaceSection ≫ φ =
    (dncBaseChangeMap D b).left ≫ s.left.deformationSpaceSection ∧
  IsPullback ν (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
    (Scheme.Hom.normalConeProj g.left s.left) b.left ∧
  Scheme.Hom.normalConeZeroSection pair.s'.left ≫ ν =
    b.left ≫ Scheme.Hom.normalConeZeroSection s.left := by
  let pair := dncPulledPair D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  have hsg : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f ↦ f.left) hs
  have w : pair.s'.left ≫ pullback.fst g.left b.left = b.left ≫ s.left :=
    pullback.lift_fst _ _ _
  let φ := SectionReesBaseChange.pairMap s.left pair.s'.left
    (pullback.fst g.left b.left) b.left w
  let ν := dncNormalPairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left w
  change IsPullback φ (Scheme.Hom.deformationSpaceProj pair.g'.left pair.s'.left)
      (Scheme.Hom.deformationSpaceProj g.left s.left) (dncBaseChangeMap D b).left ∧
    pair.s'.left.deformationSpaceSection ≫ φ =
      (dncBaseChangeMap D b).left ≫ s.left.deformationSpaceSection ∧
    IsPullback ν (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
      (Scheme.Hom.normalConeProj g.left s.left) b.left ∧
    Scheme.Hom.normalConeZeroSection pair.s'.left ≫ ν =
      b.left ≫ Scheme.Hom.normalConeZeroSection s.left
  obtain ⟨s', hc, w', he, hp, hcompat, _, ν', hν', hpν⟩ :=
    SectionReesBaseChange.base_change d g.left s.left hsg b.left
  have he' : s' = pair.s'.left := he
  clear he
  subst s'
  have htotal : IsPullback φ
      (Scheme.Hom.deformationSpaceProj pair.g'.left pair.s'.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left))
      (Scheme.Hom.deformationSpaceProj g.left s.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)) b.left := by
    simpa only [φ, pair, dncPulledPair, Over.homMk_left,
      Scheme.Hom.deformationSpaceProj,
      Scheme.IdealSheafData.deformationSpaceProj_over',
      Scheme.IdealSheafData.deformationSpaceProj] using hp
  have hq := IsPullback.of_bot htotal hcompat.1 (AffineSpace.isPullback_map b.left)
  letI : IsClosedImmersion s.left.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g.left s.left).flip inferInstance
  have hν : ν' = ν := by
    apply (cancel_mono s.left.ker.normalConeToDeformationSpace).mp
    exact hν'.trans
      (Scheme.IdealSheafData.normalConeMap_normalConeToDeformationSpace _ _ _ _).symm
  rw [hν] at hpν
  obtain ⟨μ, _, _, hμ, _, hzero, _⟩ := hcompat.2.2.2
  have hμν : μ = ν := by
    apply (cancel_mono s.left.ker.normalConeToDeformationSpace).mp
    exact hμ.trans
      (Scheme.IdealSheafData.normalConeMap_normalConeToDeformationSpace _ _ _ _).symm
  exact ⟨hq, hcompat.2.1, hpν, hμν ▸ hzero⟩

/-- Pullback along the affine-line square, from the two composition isomorphisms
and the actual equation AffineSpace.map_over.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
noncomputable def dncLinePullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] {B B' : Over (Spec (.of k))} (b : B' ⟶ B)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left))) :
    (moduleObjectDerivedPullback Λ (AffineSpace.map (ULift.{u} (Fin 1)) b.left)).obj
      ((moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj C) ≅
    (moduleObjectDerivedPullback Λ
      (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left)).obj
      ((moduleObjectDerivedPullback Λ b.left).obj C) :=
  ((leftDerivedUpperStarComp Λ (AffineSpace.map (ULift.{u} (Fin 1)) b.left)
    (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).app C).symm ≪≫
  eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C)
    (AffineSpace.map_over (n := ULift.{u} (Fin 1)) b.left)) ≪≫
  (leftDerivedUpperStarComp Λ
    (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left) b.left).app C

/-- A native coefficient-module sheaf is a finite locally constant line if its
underlying additive sheaf is that of a locally constant sheaf with regular rank-one
models over the fixed ring `Z/ell^n`. For this finite quotient, every additive map
is automatically linear: multiplication by a scalar is integer multiplication.
The underlying-sheaf isomorphism below ties the locally constant sheaf to `M`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 7 (blueprint: sk-thm-dnc). -/
noncomputable def dncLisseRankOneModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ell n : ℕ) (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  let A := ZMod (ell ^ n)
  ∃ L : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1, 0} A)))),
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X A
      (fun P ↦ Nonempty (P ≅ ModuleCat.of (ULift.{u + 1, 0} A)
        (ULift.{u + 1, 0} A))) L ∧
    Nonempty ((Mod.forget (condensedRingObj Λ X)).obj M ≅
      (SheafOfModules.toSheaf _).obj L)

end AlgebraicGeometry.ProEtale.CondensedRing
