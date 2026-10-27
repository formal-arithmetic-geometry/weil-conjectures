/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import Sheaf.TraceFormula.TwoTermPerfectDeterminant
public import Sheaf.RingTheory.CompletionKaehlerDifferentialComparison
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.FieldTheory.Perfect
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.TraceFormula.CompletedJacobianDifferentials
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Mathlib.RingTheory.Ideal.GoingDown
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Etale.Kaehler
import WeilConjectures.RingTheory.KaehlerDifferentialsPolynomialExtension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import WeilConjectures.RingTheory.RegularSequenceConormal
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Completed algebraic and continuous formal conormal determinants

Source: Stacks, Duality, Tags 0E9Y and 0E9Z; Cotangent, Tag 08SL;
Perfect Complexes, Tags 0FJX and 0FJY. This is the auxiliary completion comparison
specified by the DAG, not a claim of base change of the base scheme.
(blueprint: lem-trf-completed-conormal-determinant-comparison).

The presentation structures retain their actual quotient maps and regular equations.
Conormal modules are Mathlib's `Algebra.Extension.Cotangent`, not free replacements.
The determinant condition is the existing exact-cone condition of algebraic adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u v w

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A regular local polynomial presentation, with its rational centre and equations.
Source: Stacks, 08SL and 0E9Z
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
structure CompletedConormalAlgebraicPresentation (k A : Type u)
    [Field k] [CommRing A] [Algebra k A] (d : ℕ) where
  m : ℕ
  q : Ideal (MvPolynomial (Fin m) k)
  maximal : q.IsMaximal
  rational : Nonempty ((MvPolynomial (Fin m) k ⧸ q) ≃ₐ[k] k)
  quotient : letI := maximal; Localization.AtPrime q →ₐ[k] A
  surjective : Function.Surjective quotient
  codimension : d ≤ m
  equations : letI := maximal; Fin (m - d) → Localization.AtPrime q
  regular : letI := maximal
    RingTheory.Sequence.IsRegular (Localization.AtPrime q) (List.ofFn equations)
  kernel : RingHom.ker quotient = Ideal.span (Set.range equations)

attribute [instance] CompletedConormalAlgebraicPresentation.maximal

/-- The actual extension `P → A` of an algebraic presentation.
Source: Stacks, 08SL (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalAlgebraicPresentation.extension
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] {d : ℕ}
    (P : CompletedConormalAlgebraicPresentation k A d) : Algebra.Extension k A :=
  Algebra.Extension.ofSurjective P.quotient P.surjective

/-- A continuous local regular formal presentation, including its specified equations.
Continuity is for the variable-adic topology and the indicated maximal-ideal topology.
Source: Stacks, 0C52 and 08SL
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
structure CompletedConormalFormalPresentation (k R : Type u)
    [Field k] [CommRing R] [Algebra k R] (a : Ideal R) (d : ℕ) where
  n : ℕ
  c : ℕ
  rank_eq : c + d = n
  quotient : MvPowerSeries (Fin n) k →ₐ[k] R
  surjective : Function.Surjective quotient
  local_hom : IsLocalHom quotient.toRingHom
  continuous : @Continuous _ _
    (@MvPowerSeries.WithPiTopology.instTopologicalSpace (Fin n) k ⊤)
    a.adicTopology quotient
  equations : Fin c → MvPowerSeries (Fin n) k
  in_variables : ∀ j, equations j ∈
    Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k))
  regular : RingTheory.Sequence.IsRegular (MvPowerSeries (Fin n) k) (List.ofFn equations)
  kernel : RingHom.ker quotient = Ideal.span (Set.range equations)

/-- The actual formal extension `T → R`.
Source: Stacks, 08SL (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalFormalPresentation.extension
    {k R : Type u} [Field k] [CommRing R] [Algebra k R] {a : Ideal R} {d : ℕ}
    (T : CompletedConormalFormalPresentation k R a d) : Algebra.Extension k R :=
  Algebra.Extension.ofSurjective T.quotient T.surjective

/-- A two-term affine conormal model; the terms are retained as modules, without bases.
Source: Stacks, 08SL and 0FJX
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
structure CompletedConormalModel (R : Type u) [CommRing R] where
  neg : ModuleCat.{u} R
  pos : ModuleCat.{u} R
  differential : neg ⟶ pos
  a : ℕ
  b : ℕ

/-- Scalar extension of the actual algebraic conormal complex.
Source: Stacks, 08SL (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalAlgebraicPresentation.model
    {k A R : Type u} [Field k] [CommRing A] [CommRing R]
    [Algebra k A] [Algebra A R] {d : ℕ}
    (P : CompletedConormalAlgebraicPresentation k A d) : CompletedConormalModel R where
  neg := ModuleCat.of R (R ⊗[A] P.extension.Cotangent)
  pos := ModuleCat.of R (R ⊗[A] P.extension.CotangentSpace)
  differential := ModuleCat.ofHom (LinearMap.baseChange R P.extension.cotangentComplex)
  a := P.m - d
  b := P.m

/-- The formal model with its continuous conormal differential.
Source: Stacks, 08SL, continuous version
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalFormalPresentation.model
    {k R : Type u} [Field k] [CommRing R] [Algebra k R] {a : Ideal R} {d : ℕ}
    (T : CompletedConormalFormalPresentation k R a d)
    (δ : T.extension.Cotangent →ₗ[R] (Fin T.n → R)) : CompletedConormalModel R where
  neg := ModuleCat.of R T.extension.Cotangent
  pos := ModuleCat.of R (Fin T.n → R)
  differential := ModuleCat.ofHom δ
  a := T.c
  b := T.n

/-- The affine two-term complex in precisely degrees minus one and zero.
Source: Stacks, 08SL (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalModel.complex {R : Type u} [CommRing R]
    (C : CompletedConormalModel R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  HomologicalComplex.double C.differential (c := ComplexShape.up ℤ)
    (i₀ := -1) (i₁ := 0) (by decide)

/-- The actual associated quasi-coherent complex on the affine spectrum.
Source: Stacks, 08SL (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalModel.sheafComplex {R : Type u} [CommRing R]
    (C : CompletedConormalModel R) :=
  letI : (tilde.functor (CommRingCat.of R)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ tilde.map_zero⟩
  ((tilde.functor (CommRingCat.of R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C.complex

/-- The conormal determinant line, with the negative exterior factor dualized first.
Source: Stacks, 0FJX (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalModel.line {R : Type u} [CommRing R]
    (C : CompletedConormalModel R) : (Spec (CommRingCat.of R)).Modules :=
  flatLCITwoTermLine (Spec (CommRingCat.of R))
    ((tilde.functor (CommRingCat.of R)).obj C.neg)
    ((tilde.functor (CommRingCat.of R)).obj C.pos) C.a C.b

/-- The canonical section of a tilde module determined by a module element.
Source: Stacks, affine module/sheaf dictionary and 08SL
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def completedConormalSection {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (x : M) :=
  ((tilde.toTildeΓNatIso (R := CommRingCat.of R)).app M).hom x

/-- A chain map with its degree-minus-one and degree-zero maps written in the given terms.
Source: Stacks, 08SL (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
structure CompletedConormalMap {R : Type u} [CommRing R]
    (C D : CompletedConormalModel R) where
  neg : C.neg ⟶ D.neg
  pos : C.pos ⟶ D.pos
  chain : C.complex ⟶ D.complex
  neg_eq : chain.f (-1) =
    (HomologicalComplex.doubleXIso₀ C.differential (by decide)).hom ≫ neg ≫
      (HomologicalComplex.doubleXIso₀ D.differential (by decide)).inv
  pos_eq : chain.f 0 =
    (HomologicalComplex.doubleXIso₁ C.differential (by decide) (by decide)).hom ≫ pos ≫
      (HomologicalComplex.doubleXIso₁ D.differential (by decide) (by decide)).inv

/-- The induced morphism between the actual associated quasi-coherent complexes.
Source: Stacks, 08SL (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalMap.sheafMap {R : Type u} [CommRing R]
    {C D : CompletedConormalModel R} (f : CompletedConormalMap C D) :=
  letI : (tilde.functor (CommRingCat.of R)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ tilde.map_zero⟩
  ((tilde.functor (CommRingCat.of R)).mapHomologicalComplex (ComplexShape.up ℤ)).map f.chain

/-- The actual derived isomorphism induced by a conormal quasi-isomorphism.
Source: Stacks, 08SL and 0FJX
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalMap.derivedIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))]
    {C D : CompletedConormalModel R} (f : CompletedConormalMap C D)
    (hf : QuasiIso f.sheafMap) :
    DerivedCategory.Q.obj C.sheafComplex ≅ DerivedCategory.Q.obj D.sheafComplex :=
  letI := hf
  asIso (DerivedCategory.Q.map f.sheafMap)

/-- The determinant of a chain comparison, using the recorded exact-cone normalization.
Source: Stacks, 0FJX and 0FJY
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalMap.IsDeterminant {R : Type u} [CommRing R]
    {C D : CompletedConormalModel R} (f : CompletedConormalMap C D)
    (e : C.line ≅ D.line) : Prop :=
  ∃ hr : C.a + D.b = D.a + C.b,
    IsFlatLCIDeterminantComparison
      ((tilde.functor (CommRingCat.of R)).obj C.neg)
      ((tilde.functor (CommRingCat.of R)).obj D.neg)
      ((tilde.functor (CommRingCat.of R)).obj C.pos)
      ((tilde.functor (CommRingCat.of R)).obj D.pos) C.a D.a C.b D.b hr
      ((tilde.functor (CommRingCat.of R)).map C.differential)
      ((tilde.functor (CommRingCat.of R)).map D.differential)
      ((tilde.functor (CommRingCat.of R)).map f.neg)
      ((tilde.functor (CommRingCat.of R)).map f.pos) e

/-- The local lifting condition, without treating an arbitrary map as a lift.
Source: Stacks, 0C52 (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def IsCompletedConormalLift
    {k A R : Type u} [Field k] [CommRing A] [CommRing R]
    [Algebra k A] [Algebra A R] [Algebra k R] [IsScalarTower k A R] {d : ℕ}
    (P : CompletedConormalAlgebraicPresentation k A d)
    {a : Ideal R} (T : CompletedConormalFormalPresentation k R a d)
    (α : Localization.AtPrime P.q →ₐ[k] MvPowerSeries (Fin T.n) k) : Prop :=
  IsLocalHom α.toRingHom ∧
    T.quotient.comp α = (IsScalarTower.toAlgHom k A R).comp P.quotient

/-- The chain map of a lift is specified on every relation and every universal differential.
Source: Stacks, 08SL, polynomial/localization chain rule and 0C52
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def IsCompletedConormalLiftMap
    {k A R : Type u} [Field k] [CommRing A] [CommRing R]
    [Algebra k A] [Algebra A R] [Algebra k R] [IsScalarTower k A R] {d : ℕ}
    (P : CompletedConormalAlgebraicPresentation k A d)
    {a : Ideal R} (T : CompletedConormalFormalPresentation k R a d)
    (δ : T.extension.Cotangent →ₗ[R] (Fin T.n → R))
    (α : Localization.AtPrime P.q →ₐ[k] MvPowerSeries (Fin T.n) k)
    (f : CompletedConormalMap (P.model (R := R)) (T.model δ)) : Prop :=
  (∀ h : P.extension.ker, ∃ h' : T.extension.ker,
    h'.val = α h.val ∧
    f.neg (1 ⊗ₜ[A] Algebra.Extension.Cotangent.mk h) =
      Algebra.Extension.Cotangent.mk h') ∧
  (∀ x : P.extension.Ring,
    f.pos (1 ⊗ₜ[A] ((1 : A) ⊗ₜ[P.extension.Ring]
      KaehlerDifferential.D k P.extension.Ring x)) =
        fun i ↦ T.quotient (MvPowerSeries.pderiv k i (α x)))

/-- The source adjunction module on the affine algebraic scheme.
Its extension to the local ring is the stalk `K_A`, so extension to the completion is
canonically `K_A ⊗_A R` by tensor associativity.
Source: Stacks, 0E9Z (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
abbrev completedConormalAdjunctionSections
    {k S : Type u} [Field k] [CommRing S] [Algebra k S] {d : ℕ}
    (J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) d) :=
  (moduleSpecΓFunctor (R := CommRingCat.of S)).obj
    (J.line (FlatLCIBaseChange.identity (Spec.map (CommRingCat.ofHom (algebraMap k S)))))

/-- Generic points at which the algebraic smooth identification is required.
The map from the local ring has minimal-prime kernel; its image lies in a smooth open.
Source: Stacks, 0E9Z (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def IsCompletedConormalGeneric
    {k S A L : Type u} [Field k] [CommRing S] [CommRing A] [Field L]
    [Algebra k S] [Algebra S A] [Algebra S L] [Algebra A L]
    [IsScalarTower S A L] : Prop :=
  RingHom.ker (algebraMap A L) ∈ minimalPrimes A ∧
    ∃ (U : (Spec (CommRingCat.of S)).Opens)
      (h : Spec (CommRingCat.of L) ⟶ U.toScheme),
      Smooth (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S))) ∧
      h ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap S L))

/-- Normalization of the generic algebraic map by the recorded smooth-locus comparison.
The derivation of functions on the affine smooth neighbourhood is fixed on all restrictions
of elements of `S`; the localization rule then fixes it on every regular function there.
Source: Stacks, 0E9Y and 0E9Z
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def IsCompletedConormalSmoothComparison
    {k S A L : Type u} [Field k] [CommRing S] [CommRing A] [Field L]
    [Algebra k S] [Algebra S A] [Algebra k A] [IsScalarTower k S A]
    [Algebra S L] [Algebra A L] [IsScalarTower S A L] {d : ℕ}
    (J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) d)
    (γ : completedConormalAdjunctionSections J →
      ⋀[L]^d (L ⊗[A] KaehlerDifferential k A)) : Prop :=
  ∃ (U : (Spec (CommRingCat.of S)).Opens), IsAffine U.toScheme ∧
    Nonempty (FlatLCIPresentation
      (Spec.map (CommRingCat.ofHom (algebraMap k S))) d U) ∧
    ∃ (h : Spec (CommRingCat.of L) ⟶ U.toScheme),
      h ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap S L)) ∧
      Smooth (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S))) ∧
      ∃ e : (Scheme.Modules.tensorPullback U.ι).obj
          (J.line (FlatLCIBaseChange.identity
            (Spec.map (CommRingCat.ofHom (algebraMap k S))))) ≅
        Scheme.Modules.exteriorSheaf
          (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S))).relativeDifferentials d,
        J.IsSmoothComparison (FlatLCIBaseChange.identity
          (Spec.map (CommRingCat.ofHom (algebraMap k S)))) U e ∧
        ∃ (D : Γ(U.toScheme, ⊤) →+ (L ⊗[A] KaehlerDifferential k A))
          (ρ : Γ(Scheme.Modules.exteriorSheaf
            (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S))).relativeDifferentials d,
              ⊤) →+ ⋀[L]^d (L ⊗[A] KaehlerDifferential k A)),
          (∀ a b : Γ(U.toScheme, ⊤), D (a * b) =
            ((Scheme.ΓSpecIso (CommRingCat.of L)).hom (h.appTop a)) • D b +
            ((Scheme.ΓSpecIso (CommRingCat.of L)).hom (h.appTop b)) • D a) ∧
          (∀ s : S, D (U.ι.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) =
            (1 : L) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap S A s)) ∧
          (∀ (a : Γ(U.toScheme, ⊤)) (b : Fin d → Γ(U.toScheme, ⊤)),
            ρ (a • Scheme.Modules.exteriorSheafSection
              (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S))).relativeDifferentials
                d ⊤ (fun i ↦ (Scheme.Hom.relativeDifferentialsDerivation
                  (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)))).d
                  (X := op ⊤) (b i))) =
              ((Scheme.ΓSpecIso (CommRingCat.of L)).hom (h.appTop a)) •
                exteriorPower.ιMulti L d (fun i ↦ D (b i))) ∧
          ∀ s : completedConormalAdjunctionSections J,
            γ s = ρ (e.hom.app ⊤ (Scheme.Modules.tensorPullbackSection U.ι
              (J.line (FlatLCIBaseChange.identity
                (Spec.map (CommRingCat.ofHom (algebraMap k S))))) ⊤ s))

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- The formal conormal differential and augmentation, characterized on all relations
and all coordinate vectors. The source basis consists of the specified equation classes.
Source: Stacks, 08SL, 0C52, and 0E9Y
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
structure CompletedConormalFormalData
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
    {d : ℕ}
    (T : CompletedConormalFormalPresentation k (Algebra.LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))) d)
    (D : Derivation k (Algebra.LocalCompletion A) (Algebra.CompletedDifferentials k A)) where
  differential : T.extension.Cotangent →ₗ[Algebra.LocalCompletion A]
    (Fin T.n → Algebra.LocalCompletion A)
  differential_eq : ∀ h : T.extension.ker,
    differential (Algebra.Extension.Cotangent.mk h) =
      fun i ↦ T.quotient (MvPowerSeries.pderiv k i h.val)
  augmentation : (Fin T.n → Algebra.LocalCompletion A) →ₗ[Algebra.LocalCompletion A]
    Algebra.CompletedDifferentials k A
  augmentation_eq : ∀ i, augmentation (Pi.single i 1) = D (T.quotient (MvPowerSeries.X i))
  injective : Function.Injective differential
  exact : Function.Exact differential augmentation
  surjective : Function.Surjective augmentation
  basis : Module.Basis (Fin T.c) (Algebra.LocalCompletion A) T.extension.Cotangent
  basis_eq : ∀ j, ∃ h : T.extension.ker, h.val = T.equations j ∧
    basis j = Algebra.Extension.Cotangent.mk h

/-- The algebraic augmentation after completion is the scalar extension of the universal
cokernel projection; it is not a chosen map onto an isomorphic module.
Source: Stacks, 08SL and 00RU
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalAlgebraicPresentation.augmentation
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A] {d : ℕ}
    (P : CompletedConormalAlgebraicPresentation k A d) :=
  LinearMap.baseChange (Algebra.LocalCompletion A) P.extension.toKaehler

/-- An ambient continuous change of regular formal presentation over the identity of `R`.
Source: Stacks, 0C52 and 0FJY
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
structure CompletedConormalFormalMap
    {k R : Type u} [Field k] [CommRing R] [Algebra k R] {a : Ideal R} {d : ℕ}
    (T U : CompletedConormalFormalPresentation k R a d) where
  hom : MvPowerSeries (Fin T.n) k →ₐ[k] MvPowerSeries (Fin U.n) k
  over_identity : U.quotient.comp hom = T.quotient
  continuous : @Continuous _ _
    (@MvPowerSeries.WithPiTopology.instTopologicalSpace (Fin T.n) k ⊤)
    (@MvPowerSeries.WithPiTopology.instTopologicalSpace (Fin U.n) k ⊤) hom

/-- The actual chain map induced by a formal presentation change.
Source: Stacks, 0C52, series chain rule, and 0FJY
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def IsCompletedConormalFormalMap
    {k R : Type u} [Field k] [CommRing R] [Algebra k R] {a : Ideal R} {d : ℕ}
    {T U : CompletedConormalFormalPresentation k R a d}
    (δT : T.extension.Cotangent →ₗ[R] (Fin T.n → R))
    (δU : U.extension.Cotangent →ₗ[R] (Fin U.n → R))
    (h : CompletedConormalFormalMap T U)
    (f : CompletedConormalMap (T.model δT) (U.model δU)) : Prop :=
  (∀ r : T.extension.ker, ∃ r' : U.extension.ker,
    r'.val = h.hom r.val ∧ f.neg (Algebra.Extension.Cotangent.mk r) =
      Algebra.Extension.Cotangent.mk r') ∧
  ∀ i : Fin T.n, f.pos (Pi.single i 1) =
    fun j ↦ U.quotient (MvPowerSeries.pderiv k j (h.hom (MvPowerSeries.X i)))

/-- The generic formal augmentation, with coefficients extended to the given field.
Source: Stacks, 0E9Y and 0C52
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalFormalData.genericAugmentation
    {k A L : Type u} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
    [Field L] [Algebra A L] [Algebra (Algebra.LocalCompletion A) L]
    [IsScalarTower A (Algebra.LocalCompletion A) L] {d : ℕ}
    {T : CompletedConormalFormalPresentation k (Algebra.LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))) d}
    {D : Derivation k (Algebra.LocalCompletion A) (Algebra.CompletedDifferentials k A)}
    (F : CompletedConormalFormalData T D) :
    (Fin T.n → L) →ₗ[L] (L ⊗[A] KaehlerDifferential k A) :=
  Fintype.linearCombination L (fun i ↦
    TensorProduct.map
      (IsScalarTower.toAlgHom A (Algebra.LocalCompletion A) L).toLinearMap
      (LinearMap.id : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A)
      (F.augmentation (Pi.single i 1)))

/-- The field-valued Jacobian on the relation basis.
Source: Stacks, 0E9Y and 08SL
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalFormalPresentation.genericJacobian
    {k R L : Type u} [Field k] [CommRing R] [Algebra k R]
    [Field L] [Algebra R L] {a : Ideal R} {d : ℕ}
    (T : CompletedConormalFormalPresentation k R a d) : (Fin T.c → L) →ₗ[L] (Fin T.n → L) :=
  Fintype.linearCombination L (fun j i ↦
    algebraMap R L (T.quotient (MvPowerSeries.pderiv k i (T.equations j))))

/-- The specified ordered-wedge normalization of the determinant isomorphism.
The coefficient determinant is exactly the top wedge of relation images followed by
quotient lifts, in the standard coordinate basis. The dual relation wedge evaluates to one.
Source: Stacks, 0E9Y (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def IsCompletedConormalGenericDeterminant
    {k A L : Type u} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
    [Field L] [Algebra A L] [Algebra (Algebra.LocalCompletion A) L]
    [IsScalarTower A (Algebra.LocalCompletion A) L] {d : ℕ}
    {T : CompletedConormalFormalPresentation k (Algebra.LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))) d}
    {D : Derivation k (Algebra.LocalCompletion A) (Algebra.CompletedDifferentials k A)}
    (F : CompletedConormalFormalData T D)
    (δ : (⋀[L]^d (L ⊗[A] KaehlerDifferential k A)) ≃ₗ[L]
      L ⊗[Algebra.LocalCompletion A]
        (moduleSpecΓFunctor (R := CommRingCat.of (Algebra.LocalCompletion A))).obj
          (T.model F.differential).line) : Prop :=
  ∀ (α : Γ(SheafOfModules.homObj
      (R := (Spec (CommRingCat.of (Algebra.LocalCompletion A))).sheaf)
      (Scheme.Modules.exteriorSheaf
        ((tilde.functor (CommRingCat.of (Algebra.LocalCompletion A))).obj
          (ModuleCat.of (Algebra.LocalCompletion A) T.extension.Cotangent)) T.c)
      (SheafOfModules.unit (Spec (CommRingCat.of (Algebra.LocalCompletion A))).ringCatSheaf),
        ⊤)),
    α.app (op (Over.mk (𝟙 (⊤ : (Spec (CommRingCat.of (Algebra.LocalCompletion A))).Opens))))
      (Scheme.Modules.exteriorSheafSection _ T.c ⊤ (fun j ↦
        completedConormalSection (ModuleCat.of (Algebra.LocalCompletion A)
          T.extension.Cotangent) (F.basis j))) =
        (1 : Γ(Spec (CommRingCat.of (Algebra.LocalCompletion A)), ⊤)) →
    ∀ (v : Fin d → L ⊗[A] KaehlerDifferential k A) (l : Fin d → (Fin T.n → L)),
      (∀ i, F.genericAugmentation (l i) = v i) →
      δ (exteriorPower.ιMulti L d v) =
        (Matrix.det (fun i j : Fin T.n ↦
          Fin.append
            (fun r : Fin T.c ↦ algebraMap (Algebra.LocalCompletion A) L
              (T.quotient (MvPowerSeries.pderiv k i (T.equations r))))
            (fun r : Fin d ↦ l r i) (Fin.cast T.rank_eq.symm j))) •
          ((1 : L) ⊗ₜ[Algebra.LocalCompletion A]
            @id ((moduleSpecΓFunctor
              (R := CommRingCat.of (Algebra.LocalCompletion A))).obj
                (T.model F.differential).line)
            (Scheme.Modules.tmulSection (X := Spec (CommRingCat.of (Algebra.LocalCompletion A)))
              (N := Scheme.Modules.exteriorSheaf
                ((tilde.functor (CommRingCat.of (Algebra.LocalCompletion A))).obj
                  (ModuleCat.of (Algebra.LocalCompletion A)
                    (Fin T.n → Algebra.LocalCompletion A))) T.n)
              α (Scheme.Modules.exteriorSheafSection _ T.n ⊤ (fun i ↦
                completedConormalSection
                  (ModuleCat.of (Algebra.LocalCompletion A) (Fin T.n → Algebra.LocalCompletion A))
                  (Pi.single i 1)))))

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- The completed stalk of the actual algebraic adjunction line, in the affine dictionary.
Source: Stacks, 0E9Z (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
abbrev completedConormalSource
    {k S A : Type u} [Field k] [CommRing S] [CommRing A]
    [Algebra k S] [Algebra S A] [IsLocalRing A] {d : ℕ}
    (J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) d) :=
  ModuleCat.of (Algebra.LocalCompletion A)
    (Algebra.LocalCompletion A ⊗[S] completedConormalAdjunctionSections J)

/-- The actual maps induced by an algebraic presentation change, after scalar extension.
Source: Stacks, 08SL and 0FJY
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def IsCompletedConormalAlgebraicMap
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A] {d : ℕ}
    (P Q : CompletedConormalAlgebraicPresentation k A d)
    (β : Localization.AtPrime P.q →ₐ[k] Localization.AtPrime Q.q)
    (f : CompletedConormalMap (P.model (R := Algebra.LocalCompletion A))
      (Q.model (R := Algebra.LocalCompletion A))) : Prop :=
  (∀ h : P.extension.ker, ∃ h' : Q.extension.ker,
    h'.val = β h.val ∧
    f.neg (1 ⊗ₜ[A] Algebra.Extension.Cotangent.mk h) =
      1 ⊗ₜ[A] Algebra.Extension.Cotangent.mk h') ∧
  ∀ x : P.extension.Ring,
    f.pos (1 ⊗ₜ[A] ((1 : A) ⊗ₜ[P.extension.Ring]
      KaehlerDifferential.D k P.extension.Ring x)) =
        1 ⊗ₜ[A] ((1 : A) ⊗ₜ[Q.extension.Ring]
          KaehlerDifferential.D k Q.extension.Ring (β x))

/-- The full comparison system: actual conormal complexes, lift maps, their derived classes,
normalized determinants, and every generic-field normalization. Fields carrying equations
are conditions on the actual constructed objects, not replacement assumptions in the theorem.
Source: Stacks, 08SL, 0C52, 0E9Y, 0E9Z, 0FJX and 0FJY
(blueprint: lem-trf-completed-conormal-determinant-comparison). -/
structure CompletedConormalDeterminantComparison
    {k S A : Type u} [Field k] [CommRing S] [CommRing A] [IsLocalRing A]
    [Algebra k S] [Algebra S A] [Algebra k A] [IsScalarTower k S A]
    [∀ X : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {d : ℕ}
    (J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) d) where
  derivation : Derivation k (Algebra.LocalCompletion A) (Algebra.CompletedDifferentials k A)
  extension : Algebra.IsCompletedDifferentialExtension k A derivation
  formal : ∀ T : CompletedConormalFormalPresentation k (Algebra.LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))) d,
    CompletedConormalFormalData T derivation
  comparison : ∀ T : CompletedConormalFormalPresentation k (Algebra.LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))) d,
    (tilde.functor (CommRingCat.of (Algebra.LocalCompletion A))).obj
      (completedConormalSource (A := A) J) ≅ (T.model (formal T).differential).line
  algebraic : ∀ P : CompletedConormalAlgebraicPresentation k A d,
    (tilde.functor (CommRingCat.of (Algebra.LocalCompletion A))).obj
      (completedConormalSource (A := A) J) ≅ (P.model (R := Algebra.LocalCompletion A)).line
  algebraic_exact : ∀ P : CompletedConormalAlgebraicPresentation k A d,
    Function.Injective (P.model (R := Algebra.LocalCompletion A)).differential ∧
      Function.Exact (P.model (R := Algebra.LocalCompletion A)).differential P.augmentation ∧
      Function.Surjective P.augmentation
  algebraic_bases : ∀ P : CompletedConormalAlgebraicPresentation k A d,
    Nonempty (Module.Basis (Fin (P.m - d)) (Algebra.LocalCompletion A)
      (P.model (R := Algebra.LocalCompletion A)).neg) ∧
    Nonempty (Module.Basis (Fin P.m) (Algebra.LocalCompletion A)
      (P.model (R := Algebra.LocalCompletion A)).pos)
  lifts : ∀ (P : CompletedConormalAlgebraicPresentation k A d)
    (T : CompletedConormalFormalPresentation k (Algebra.LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))) d),
    ∃ α, IsCompletedConormalLift P T α
  lift_maps : ∀ (P : CompletedConormalAlgebraicPresentation k A d)
    (T : CompletedConormalFormalPresentation k (Algebra.LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))) d)
    (α : Localization.AtPrime P.q →ₐ[k] MvPowerSeries (Fin T.n) k),
    IsCompletedConormalLift P T α →
    ∃ f : CompletedConormalMap (P.model (R := Algebra.LocalCompletion A))
        (T.model (formal T).differential),
      IsCompletedConormalLiftMap P T (formal T).differential α f ∧
      QuasiIso f.sheafMap ∧
      (formal T).augmentation.comp f.pos.hom = P.augmentation ∧
      f.IsDeterminant ((algebraic P).symm ≪≫ comparison T)
  lift_independent : ∀ (P : CompletedConormalAlgebraicPresentation k A d)
    (T : CompletedConormalFormalPresentation k (Algebra.LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))) d)
    (α β : Localization.AtPrime P.q →ₐ[k] MvPowerSeries (Fin T.n) k)
    (f g : CompletedConormalMap (P.model (R := Algebra.LocalCompletion A))
      (T.model (formal T).differential)),
    IsCompletedConormalLift P T α → IsCompletedConormalLift P T β →
    IsCompletedConormalLiftMap P T (formal T).differential α f →
    IsCompletedConormalLiftMap P T (formal T).differential β g →
      DerivedCategory.Q.map f.sheafMap = DerivedCategory.Q.map g.sheafMap
  algebraic_changes : ∀ (P Q : CompletedConormalAlgebraicPresentation k A d)
    (β : Localization.AtPrime P.q →ₐ[k] Localization.AtPrime Q.q),
    IsLocalHom β.toRingHom → Q.quotient.comp β = P.quotient →
    ∃ f : CompletedConormalMap (P.model (R := Algebra.LocalCompletion A))
        (Q.model (R := Algebra.LocalCompletion A)),
      IsCompletedConormalAlgebraicMap P Q β f ∧ QuasiIso f.sheafMap ∧
      f.IsDeterminant ((algebraic P).symm ≪≫ algebraic Q)
  formal_changes : ∀ (T U : CompletedConormalFormalPresentation k (Algebra.LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))) d)
    (h : CompletedConormalFormalMap T U),
    ∃ f : CompletedConormalMap (T.model (formal T).differential)
        (U.model (formal U).differential),
      IsCompletedConormalFormalMap (formal T).differential (formal U).differential h f ∧
      QuasiIso f.sheafMap ∧
      (formal U).augmentation.comp f.pos.hom = (formal T).augmentation ∧
      f.IsDeterminant ((comparison T).symm ≪≫ comparison U)
  generic : ∀ (L : Type u) [Field L] [Algebra A L] [Algebra S L]
    [Algebra (Algebra.LocalCompletion A) L] [IsScalarTower S A L]
    [IsScalarTower A (Algebra.LocalCompletion A) L],
    IsCompletedConormalGeneric (k := k) (S := S) (A := A) (L := L) →
    ∃ γ : (L ⊗[S] completedConormalAdjunctionSections J) ≃ₗ[L]
        ⋀[L]^d (L ⊗[A] KaehlerDifferential k A),
      IsCompletedConormalSmoothComparison J
        (fun s ↦ γ ((1 : L) ⊗ₜ[S] s)) ∧
      ∀ T : CompletedConormalFormalPresentation k (Algebra.LocalCompletion A)
          ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))) d,
        Function.Injective (T.genericJacobian (L := L)) ∧
        Function.Exact (T.genericJacobian (L := L)) ((formal T).genericAugmentation (L := L)) ∧
        Function.Surjective ((formal T).genericAugmentation (L := L)) ∧
        ∃ δ : (⋀[L]^d (L ⊗[A] KaehlerDifferential k A)) ≃ₗ[L]
            L ⊗[Algebra.LocalCompletion A]
              (moduleSpecΓFunctor (R := CommRingCat.of (Algebra.LocalCompletion A))).obj
                (T.model (formal T).differential).line,
          IsCompletedConormalGenericDeterminant (formal T) δ ∧
          ∀ s : completedConormalAdjunctionSections J,
            δ (γ ((1 : L) ⊗ₜ[S] s)) =
              LinearMap.baseChange L
                ((moduleSpecΓFunctor (R := CommRingCat.of (Algebra.LocalCompletion A))).map
                  (comparison T).hom).hom
                ((1 : L) ⊗ₜ[Algebra.LocalCompletion A]
                  completedConormalSection (completedConormalSource (A := A) J)
                    ((1 : Algebra.LocalCompletion A) ⊗ₜ[S] s))

/-- The comparison for any two formal presentations is obtained through their common
completed algebraic source. These actual isomorphisms compose for every three presentations.
Source: Stacks, 0FJY (blueprint: lem-trf-completed-conormal-determinant-comparison). -/
def CompletedConormalDeterminantComparison.formalComparison
    {k S A : Type u} [Field k] [CommRing S] [CommRing A] [IsLocalRing A]
    [Algebra k S] [Algebra S A] [Algebra k A] [IsScalarTower k S A]
    [∀ X : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))] {d : ℕ}
    {J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) d}
    (F : CompletedConormalDeterminantComparison (A := A) J)
    (T U : CompletedConormalFormalPresentation k (Algebra.LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))) d) :
    (T.model (F.formal T).differential).line ≅ (U.model (F.formal U).differential).line :=
  (F.comparison T).symm ≪≫ F.comparison U

/-- Completed algebraic and continuous formal conormal determinants, with their prescribed
normalization and all presentation comparisons. The comparison is on the completion of the
stalk of the algebraic line, rather than a base change of the base scheme.

Source: Stacks, 08SL, 0C52, 0E9Y, 0E9Z, 0FJX and 0FJY; the auxiliary completion comparison
and its eleven-step proof in the DAG
(blueprint: lem-trf-completed-conormal-determinant-comparison).

Proof (the complete DAG proof plan):
1. The finite-type Noetherian theorem applied over the field k, followed by Noetherianity of
   localization and completion, makes S,A,R Noetherian. The local completion map A→R is faithfully
   flat. Put N=Ω¹_{A/k} and M_R=N⊗_A R. The regular-sequence conormal-basis theorem gives
   I/I²≃A^{m-d} and J/J²≃R^c, with the stated equation classes as bases. Polynomial differentials
   followed by localization give Ω¹_{P/k}⊗_P A≃A^m on du_i. Thus both displayed complexes have
   finite free terms. N is finitely generated: its generators are the images of du_i.
   Inputs: lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian, lem-
   weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-faithfully-flat, lem-weil-
   pbc-regular-sequence-conormal-free, lem-weil-pbc-kahler-differentials-polynomial-extension,
   lem-weil-pbc-kahler-differentials-localization.
2. The cokernel of the algebraic conormal map is N: a P-linear map Ω¹_{P/k}→V for an A-module V
   factors through that cokernel exactly when the corresponding k-derivation of P vanishes on I,
   exactly when it descends to A. This is precisely the universal property of N. Tensor right
   exactness identifies the cokernel after tensoring with R with M_R, with du_i↦d(u_i mod I)⊗1.
   Apply the completed-Jacobian theorem to the given formal presentation, with residue field F=k
   and section the structural k→R: F/k is finite separable, the map is continuous and surjective,
   and all g_j lie in (z). It supplies the unique continuous extension d̂:R→M_R and the cokernel
   isomorphism for C_T, sending e_i to d̂(z_i). Denote the two augmentation maps to M_R[0] by
   q_P,q_T.
   Inputs: def-weil-pbc-kahler-differentials, lem-weil-pbc-tensor-right-exact, lem-trf-completed-
   jacobian-differentials, lem-trf-completion-kahler-differential-comparison.
3. The finite-type algebra S is finitely presented over the Noetherian field k. For each field
   extension k'/k, the perfect-field reduced-tensor theorem makes S⊗_k k' reduced, so Spec S is
   geometrically reduced. The dense-smooth-open theorem applies and puts every generic point in
   the smooth locus: an open dense subset meets each component away from the other finitely many
   components and therefore contains its generic point. Pure dimension d and the equidimensional-
   open dimension theorem give local topological dimension d on Spec S. The smooth-differentials
   rank theorem and localization of differentials now give dim_{A_a}(N⊗_A A_a)=d for each minimal
   prime a of A. Here A_a is the generic field of the corresponding reduced component. By Step 2
   the algebraic conormal map over that field has cokernel of dimension d. Its domain and codomain
   have dimensions m-d and m, so rank-nullity makes it injective.
   Inputs: lem-weil-pbc-finite-type-noetherian-finite-presentation, lem-weil-pbc-noetherian-
   finitely-many-minimal-primes, lem-weil-pbc-perfect-reduced-tensor, lem-pur-geometrically-
   reduced-dense-smooth-open, lem-sbc-equidimensional-open-local-dimension, lem-weil-pbc-smooth-
   differentials-free-rank-fibre-dimension, lem-weil-pbc-kahler-differentials-localization, lem-
   weil-pbc-minimal-prime-reduced-localization-field.
4. Let p be a minimal prime of R. Flat going-down for A→R shows that its contraction a to A is
   minimal: otherwise a strictly smaller prime of A would lift to a prime strictly below p. Since
   A is reduced (a localization of S), A_a is a field by the minimal-prime localization theorem;
   the same theorem makes F_p=R_p a field because R is reduced. The local map A_a→F_p is an
   extension of fields. The algebraic exact vector-space sequence of Step 3 therefore remains
   exact over F_p, and dim_{F_p}(M_R⊗_R F_p)=d. Tensor right exactness applied to Step 2
   identifies both base-changed cokernels with this vector space.
   Inputs: lem-sc-flat-going-down, lem-weil-pbc-minimal-prime-reduced-localization-field, lem-
   weil-pbc-tensor-right-exact.
5. Over each F_p the formal differential has domain dimension c, codomain dimension n and cokernel
   dimension d=n-c; rank-nullity gives zero kernel. The algebraic differential also has zero
   kernel over F_p by Step 4. The total-fractions theorem gives Q(R)≃∏_p R_p. The map R→Q(R) is
   injective: if a/1=0, some nonzerodivisor s satisfies sa=0, hence a=0. Coordinatewise, the same
   is true for every finite free R-module. Therefore a vector in the kernel of either
   differential, zero in every F_p by the preceding calculations, is zero in its free source over
   R. Both q_P and q_T are now quasi-isomorphisms: the only remaining cohomology is their already
   identified degree-zero cokernel M_R.
   Inputs: lem-weil-pbc-reduced-noetherian-total-ring-fractions.
6. To construct a local lift α:P→T, lift each u_i mod I to an element of T; its residue is the
   prescribed k-value of u_i. Every polynomial outside the rational maximal ideal q then evaluates
   to a power series with nonzero constant term, which is a unit (its inverse is its constant
   inverse times a geometric series). Thus evaluation extends to P. Reducing to the residue field
   proves α is local, and its composite with T→R is the given P→R. Because α(I)⊆J and α(I²)⊆J²,
   [h]↦[α(h)] defines the degree -1 map; the differential formula defines degree zero. Formal
   differentiation is a derivation, and differentiating polynomials and inverses proves the chain
   rule, hence f_α:C_P⊗R→C_T is a chain map.
   Inputs: def-weil-pbc-multivariate-power-series, def-weil-pbc-kahler-differentials.
7. The finite-module tensor/completion theorem identifies M_R with the adic completion of N, and
   module-completion completeness makes it separated; the image of (z) is the maximal ideal of R,
   so these are also the (z)-adic powers. For any series h∈T, truncate modulo (z)^b. Termwise
   derivatives of the tail lie in (z)^{b-1}; both the universal continuous derivation on R and the
   formal derivative expression therefore converge to the same element of M_R, since they agree on
   polynomials. This gives d̂(h mod J)=∑_i (∂h/∂z_i mod J)d̂(z_i). In particular q_T f_α=q_P on
   each du_i and hence on the complex. In D(R), where the augmentations of Step 5 are invertible,
   f_α=q_T^{-1}q_P. It is a quasi-isomorphism and its derived class is independent of α.
   Inputs: lem-weil-pbc-completion-finite-module-tensor, lem-weil-pbc-module-completion-complete,
   lem-trf-completion-kahler-differential-comparison, def-pc-derived-category.
8. The adjunction-line theorem identifies K_A in the chosen algebraic chart with
   (Λ^{m-d}(I/I²))^∨⊗Λ^m(Ω¹_{P/k}⊗_P A). Applying the two-term determinant functor to the
   isomorphism f_α=q_T^{-1}q_P and its scalar-extension comparison gives Φ_T:K_A⊗_A
   R≃(Λ^c(J/J²))^∨⊗Λ^n R^n=λ_T. This uses completion of the algebraic modules and the actual
   conormal map, rather than any claim that completion is a change of the base scheme. Lift-
   independence follows immediately from Step 7 and functoriality of the determinant.
   Inputs: lem-trf-flat-lci-canonical-adjunction, lem-trf-two-term-perfect-determinant.
9. Let θ:R→L satisfy the stated generic-smooth hypothesis. Smooth differentials have rank the
   local fibre dimension, here d; localization identifies their fibre with Ω¹_{A/k}⊗_A κ(a) at the
   specified generic point a. Its further extension to L consequently has dimension d. Tensor
   right exactness makes this vector space M the cokernel of both C_P⊗L and C_T⊗L. For the
   algebraic map the source and target dimensions are m-d,m; for the formal map they are c,n with
   n-c=d. Rank-nullity makes both left maps injective. Thus both sequences are short exact even
   though R→L need not be flat. The two augmentations after tensoring with L are quasi-
   isomorphisms, and the equality (q_T⊗L)(f_α⊗L)=q_P⊗L is the tensor of the chain-map equality
   from Step 7.
   Inputs: lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension, lem-weil-pbc-kahler-
   differentials-localization, lem-weil-pbc-tensor-right-exact.
10. For the short exact sequence of Step 9 choose its relation basis a_j=[g_j] and any lifts ṽ_i
   of a basis v_i of M. The vectors d̂g_1,…,d̂g_c,ṽ_1,…,ṽ_d form a basis of L^n. Changing a lift
   by a relation vector adds a wedge with c+1 relation vectors, hence zero; changing the relation
   basis multiplies its dual top wedge and its image top wedge by inverse determinants. The
   resulting δ_T is therefore precisely the displayed well-defined determinant isomorphism. In
   this split basis the augmentation is the projection [L^c→L^c⊕M]→M[0]. The determinant
   construction cancels the identical relation factors by evaluation, so det(q_T⊗L)=δ_T^{-1}. The
   same calculation for P gives det(q_P⊗L)=γ_A, by the adjunction theorem's smooth-locus
   identification (relations precede quotient lifts in both formulas). Functoriality and scalar-
   extension compatibility now yield δ_T^{-1}(Φ_T⊗L)=γ_A.
   Inputs: lem-trf-two-term-perfect-determinant, lem-trf-flat-lci-canonical-adjunction.
11. For a continuous map between two regular formal presentations inducing 1_R, apply the series
   chain rule of Step 7 to its coordinate images. Its conormal chain map h satisfies q_{T'}h=q_T,
   hence h=q_{T'}^{-1}q_T in D(R). Thus for three such presentations the comparisons compose by
   cancellation; determinant functoriality gives det(h)Φ_T=Φ_{T'}. Algebraic presentation changes
   likewise commute with the differential augmentations. To compare their source identifications
   with the fixed K_A, use Step 10 at every L=R_p, p minimal: Step 4 ensures these are allowed
   generic-smooth fields. The canonical algebraic adjunction transitions agree with γ_A there, so
   the two candidate line maps agree at every R_p. Their difference is zero: after trivializing
   the lines on the local ring R it is a scalar, detected by the injection R→∏_p R_p established
   in Step 5. Hence the comparisons respect all algebraic presentation changes as well, and their
   cocycle law holds over R. This also proves the normalization for every choice of presentations.
   Inputs: lem-trf-two-term-perfect-determinant, lem-trf-flat-lci-canonical-adjunction, lem-weil-
   pbc-reduced-noetherian-total-ring-fractions.
-/
theorem exists_completedConormalDeterminantComparison
    {k S : Type u} [Field k] [PerfectField k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [_root_.IsReduced S]
    [∀ X : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (d : ℕ) (hpure : (Spec (CommRingCat.of S)).IsPureDimension d)
    (hlci : Algebra.IsLocalCompleteIntersection k S)
    (p : Ideal S) [p.IsMaximal]
    (hresidue : Nonempty ((S ⧸ p) ≃ₐ[k] k))
    [_root_.IsReduced (Algebra.LocalCompletion (Localization.AtPrime p))]
    (J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) d)
    (hJ : J.IsNormalized) :
    Nonempty (CompletedConormalDeterminantComparison
      (A := Localization.AtPrime p) J) := by
  sorry

end AlgebraicGeometry
