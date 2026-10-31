/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.LinearAlgebra.TwoTermCofactorNaturality
public import WeilConjectures.AlgebraicGeometry.LciCotangentPresentation
public import WeilConjectures.TraceFormula.CanonicalTwoTermPerfectDeterminant
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.RingTheory.KoszulConormalComparison
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import Mathlib.RingTheory.Etale.Kaehler

/-! # Affine conormal realization and the augmented Jacobian

Source: Stacks Project, Duality, Tag 0E9Y; Cotangent Complex, Tags 08RB, 08SJ, 08SL
and 08T3; More on Algebra, Tag 0FJM; Perfect Complexes, Tags 0FJX and 0FJY
(blueprint: lem-sfb-affine-conormal-jacobian-realization).

The chart variable ranges over every affine open immersion into the quotient spectrum.
It includes the identity and algebra isomorphisms. Thus restriction is not restricted to
principal opens. All objects are the recorded conormal, cotangent and determinant objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option genInjectivity false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Algebra.CotangentResolution
open scoped TensorProduct ChangeOfRings

namespace Algebra.AffineConormal

/-- The polynomial ring in one more variable than relations.
Source: Stacks, Tag 0E9Y (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
abbrev PolynomialRing (R : Type u) [CommRing R] (c : ℕ) := MvPolynomial (Fin (c + 1)) R

/-- The ideal of the specified ordered equations.
Source: Stacks, Tags 08SJ, 0E9Y
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def ideal {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → PolynomialRing R c) :=
  Ideal.span (Set.range f)

/-- The presented quotient, with its actual quotient algebra structure.
Source: Stacks, Tag 08SJ (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
abbrev QuotientRing {R : Type u} [CommRing R] {c : ℕ}
    (f : Fin c → PolynomialRing R c) := PolynomialRing R c ⧸ ideal f

/-- The structure arrow of the quotient algebra.
Source: Stacks, Tag 08RB (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def arrow {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → PolynomialRing R c) :
    Arrow CommRingCat.{u} :=
  Arrow.mk (CommRingCat.ofHom (algebraMap R (QuotientRing f)))

/-- The actual polynomial presentation used by the recorded naive comparison.
Source: Stacks, Tags 08RB and 08SJ
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def presentation {R : Type u} [CommRing R] {c : ℕ}
    (f : Fin c → PolynomialRing R c) : Naive.Presentation (arrow f) where
  ring := CommRingCat.of (PolynomialRing R c)
  base := CommRingCat.ofHom (algebraMap R (PolynomialRing R c))
  augmentation := CommRingCat.ofHom (Ideal.Quotient.mk (ideal f))
  triangle := rfl
  surjective := Ideal.Quotient.mk_surjective

/-- The recorded conormal differential, without an injectivity hypothesis.
Source: Stacks, Tags 08RB, 08SJ
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def complex {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → PolynomialRing R c) :
    Module.TwoTermComplex.{u, u} (QuotientRing f) :=
  ⟨Naive.conormal (presentation f), Naive.differentials (presentation f),
    Naive.differential (presentation f)⟩

/-- Extension of the displayed two-term complex to an affine chart.
Source: Stacks, Tags 08T3, 0E9Y
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def chartComplex {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → PolynomialRing R c)
    (A : CommRingCat.{u}) [Algebra R A] (φ : QuotientRing f →ₐ[R] A) :
    Module.TwoTermComplex.{u, u} A :=
  ⟨(ModuleCat.extendScalars φ.toRingHom).obj (complex f).neg,
    (ModuleCat.extendScalars φ.toRingHom).obj (complex f).zero,
    (ModuleCat.extendScalars φ.toRingHom).map (complex f).differential⟩

/-- A generator of the conormal module `I/I²`.
Source: Stacks, Tag 062I (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def relation {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → PolynomialRing R c)
    (i : Fin c) : (ideal f).Cotangent :=
  (ideal f).toCotangent ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩

/-- The universal ambient coordinate differential in the recorded conormal model.
Source: Stacks, Tag 00RX (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def dx {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → PolynomialRing R c)
    (j : Fin (c + 1)) : (complex f).zero :=
  Naive.tensorGenerator (presentation f) 1 (MvPolynomial.X j)

/-- The canonical scalar-extension unit, used to state all comparison normalizations.
Source: Stacks, Tag 01I9 (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def unit {B A : Type u} [CommRing B] [CommRing A] (φ : B →+* A)
    (M : ModuleCat.{u} B) (x : M) : (ModuleCat.extendScalars φ).obj M :=
  (ModuleCat.extendRestrictScalarsAdj φ).unit.app M x

/-- The top dual wedge: the determinant of the ordered coordinate functionals.
Source: Stacks, Tag 0E9Y (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def topDual {B : Type u} [CommRing B] {M : Type u} [AddCommGroup M] [Module B M]
    {n : ℕ} (b : Module.Basis (Fin n) B M) : Module.Dual B (⋀[B]^n M) :=
  exteriorPower.alternatingMapToDual B M n b.coord

/-- The relation-first augmented Jacobian, before reduction modulo the equations.
Source: Stacks, Tag 0E9Y (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def augmentedJacobian {R : Type u} [CommRing R] {c : ℕ}
    (f : Fin c → PolynomialRing R c) (a : PolynomialRing R c) : PolynomialRing R c :=
  Matrix.det (fun i j : Fin (c + 1) ↦ MvPolynomial.pderiv j
    (Fin.snoc (α := fun _ : Fin (c + 1) ↦ PolynomialRing R c) f a i))

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The ring square from the original quotient to the affine chart.
Source: Stacks, Tag 08QL (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def chartSquare {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → PolynomialRing R c)
    (A : CommRingCat.{u}) [Algebra R A] (φ : QuotientRing f →ₐ[R] A) :
    arrow f ⟶ Arrow.mk (CommRingCat.ofHom (algebraMap R A)) :=
  Arrow.homMk' (𝟙 _) (CommRingCat.ofHom φ.toRingHom)
    (CommRingCat.hom_ext φ.comp_algebraMap.symm)

/-- The intrinsic chart cotangent complex, using the recorded standard resolution.
Source: Stacks, Tags 08PN, 08T3
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def intrinsic (C : Coherence.{u}) (R : Type u) [CommRing R]
    (A : CommRingCat.{u}) [Algebra R A] :=
  cotangentComplex C (Arrow.mk (CommRingCat.ofHom (algebraMap R A)))

/-- A realization on an arbitrary affine open chart, retaining all normalizations.
Source: Stacks, Tags 0E9Y, 08RB, 08SJ and 08T3
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
structure Chart {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → PolynomialRing R c)
    (C : Coherence.{u}) (κ : Naive.Comparison C)
    (A : CommRingCat.{u}) [Algebra R A] (φ : QuotientRing f →ₐ[R] A) where
  conormalIso : (complex f).neg ≃ₗ[QuotientRing f] (ideal f).Cotangent
  conormal_formula : ∀ (z : RingHom.ker (presentation f).augmentation.hom)
    (hz : z.val ∈ ideal f), conormalIso (Naive.kernelClass (presentation f) z) =
      (ideal f).toCotangent ⟨z.val, hz⟩
  conormalBasis : Module.Basis (Fin c) (QuotientRing f) (ideal f).Cotangent
  conormalBasis_formula : ∀ i, conormalBasis i = relation f i
  ambientBasis : Module.Basis (Fin (c + 1)) (QuotientRing f) (complex f).zero
  ambientBasis_formula : ∀ j, ambientBasis j = dx f j
  negBasis : Module.Basis (Fin c) A (chartComplex f A φ).neg
  negBasis_formula : ∀ i, negBasis i =
    unit φ.toRingHom (complex f).neg (conormalIso.symm (relation f i))
  zeroBasis : Module.Basis (Fin (c + 1)) A (chartComplex f A φ).zero
  zeroBasis_formula : ∀ j, zeroBasis j = unit φ.toRingHom (complex f).zero (dx f j)
  jacobian : ∀ i, (chartComplex f A φ).differential.hom (negBasis i) =
    ∑ j, φ (Ideal.Quotient.mk (ideal f) (MvPolynomial.pderiv j (f i))) • zeroBasis j
  omega : (chartComplex f A φ).cofactorCokernel ≃ₗ[A] Ω[A⁄R]
  omega_formula : ∀ j,
    omega ((LinearMap.range (chartComplex f A φ).differential.hom).mkQ (zeroBasis j)) =
      KaehlerDifferential.D R A (φ (Ideal.Quotient.mk (ideal f) (MvPolynomial.X j)))
  cofactor : Module.TwoTermCofactorPresentation (chartComplex f A φ) c
  trivialization : (chartComplex f A φ).cofactorLine c ≃ₗ[A] A
  orientation : trivialization
    (topDual negBasis ⊗ₜ[A] exteriorPower.ιMulti A (c + 1) zeroBasis) = 1
  polynomial : Naive.IsLocalizedPolynomial (presentation f)
  naiveIso : (complex f).cofactorComplex ≅ Naive.complex (presentation f)
  naive_negative : naiveIso.hom.f (-1) ≫ (Naive.conormalIso (presentation f)).hom =
    (HomologicalComplex.doubleXIso₀ (complex f).differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).hom
  naive_zero : naiveIso.hom.f 0 ≫ (Naive.differentialsIso (presentation f)).hom =
    (HomologicalComplex.doubleXIso₁ (complex f).differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).hom
  standardChange :
    ((ModuleCat.extendScalars φ.toRingHom).mapHomologicalComplex (.up ℤ)).obj
      (CotangentPresentation.ringComplex C (arrow f)) ⟶
    CotangentPresentation.ringComplex C
      (Arrow.mk (CommRingCat.ofHom (algebraMap R A)))
  standardChange_formula : ∀ (i : ℤ)
    (x : (CotangentPresentation.ringComplex C (arrow f)).X i),
    standardChange.f i (unit φ.toRingHom _ x) =
      (C.differentialMap (C.standardMap (chartSquare f A φ))).map.f i x
  cotangentIso : DerivedCategory.Q.obj (chartComplex f A φ).cofactorComplex ≅ intrinsic C R A
  extendedDouble :
    ((ModuleCat.extendScalars φ.toRingHom).mapHomologicalComplex (.up ℤ)).obj
      (complex f).cofactorComplex ≅ (chartComplex f A φ).cofactorComplex
  extended_negative : extendedDouble.hom.f (-1) ≫
    (HomologicalComplex.doubleXIso₀ (chartComplex f A φ).differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).hom =
    (ModuleCat.extendScalars φ.toRingHom).map
      (HomologicalComplex.doubleXIso₀ (complex f).differential
        (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).hom
  extended_zero : extendedDouble.hom.f 0 ≫
    (HomologicalComplex.doubleXIso₁ (chartComplex f A φ).differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).hom =
    (ModuleCat.extendScalars φ.toRingHom).map
      (HomologicalComplex.doubleXIso₁ (complex f).differential
        (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).hom
  cotangent_normalization : ∀ a : Naive.PresentationMap (𝟙 _)
    (Naive.standardPresentation C (arrow f)) (presentation f),
    DerivedCategory.Q.map standardChange ≫ cotangentIso.inv =
      DerivedCategory.Q.map
        (((ModuleCat.extendScalars φ.toRingHom).mapHomologicalComplex (.up ℤ)).map
          (κ.projection (presentation f) polynomial a ≫ naiveIso.inv) ≫ extendedDouble.hom)



/-- The differential-valued cofactor on the actual Kähler module.
Source: Stacks, Tag 0E9Y (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def Chart.w {R : Type u} [CommRing R] {c : ℕ} {f : Fin c → PolynomialRing R c}
    {C : Coherence.{u}} {κ : Naive.Comparison C} {A : CommRingCat.{u}} [Algebra R A]
    {φ : QuotientRing f →ₐ[R] A} (H : Chart f C κ A φ) :
    Ω[A⁄R] →ₗ[A] (chartComplex f A φ).cofactorLine c :=
  H.cofactor.map.comp H.omega.symm.toLinearMap

/-- The tilde model on the quotient spectrum, with finite freeness stated separately.
Source: Stacks, Tags 0FJX, 08T3
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def sheafModel {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → PolynomialRing R c)
    (A : CommRingCat.{u}) [Algebra R A] (φ : QuotientRing f →ₐ[R] A)
    (hn : (tilde (chartComplex f A φ).neg).IsFiniteLocallyFreeOfRank c)
    (hz : (tilde (chartComplex f A φ).zero).IsFiniteLocallyFreeOfRank (c + 1)) :
    TwoTermDeterminantModel (Spec A) :=
  ⟨tilde (chartComplex f A φ).neg, tilde (chartComplex f A φ).zero,
    tilde.map (chartComplex f A φ).differential, c, c + 1, hn, hz⟩

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The canonical affine sheaf determinant comparison, specified on its ordered generator.
The target is the tilde standard-resolution complex, hence the intrinsic affine cotangent
complex of the recorded cotangent-presentation theorem. Its inverse is fixed by a chain
representative of the already normalized ring comparison. No arbitrary derived isomorphism
or arbitrary trivialization is used.
Source: Stacks, Tags 08T3, 0FJX and 0FJY
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
structure DeterminantChart {R : Type u} [CommRing R] {c : ℕ}
    {f : Fin c → PolynomialRing R c} {C : Coherence.{u}} {κ : Naive.Comparison C}
    {A : CommRingCat.{u}} [Algebra R A] {φ : QuotientRing f →ₐ[R] A}
    (H : Chart f C κ A φ) where
  neg_free : (tilde (chartComplex f A φ).neg).IsFiniteLocallyFreeOfRank c
  zero_free : (tilde (chartComplex f A φ).zero).IsFiniteLocallyFreeOfRank (c + 1)
  doubleIso : (CotangentPresentation.tildeComplexFunctor A).obj
    (chartComplex f A φ).cofactorComplex ≅ (sheafModel f A φ neg_free zero_free).complex
  negative : doubleIso.hom.f (-1) ≫
    (HomologicalComplex.doubleXIso₀ (sheafModel f A φ neg_free zero_free).differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).hom =
    tilde.map (HomologicalComplex.doubleXIso₀ (chartComplex f A φ).differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).hom
  zero : doubleIso.hom.f 0 ≫
    (HomologicalComplex.doubleXIso₁ (sheafModel f A φ neg_free zero_free).differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).hom =
    tilde.map (HomologicalComplex.doubleXIso₁ (chartComplex f A φ).differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).hom
  ringProjection : CotangentPresentation.ringComplex C
    (Arrow.mk (CommRingCat.ofHom (algebraMap R A))) ⟶ (chartComplex f A φ).cofactorComplex
  ringProjection_formula : DerivedCategory.Q.map ringProjection = H.cotangentIso.inv
  intrinsicIso : DerivedCategory.Q.obj (sheafModel f A φ neg_free zero_free).complex ≅
    DerivedCategory.Q.obj ((CotangentPresentation.tildeComplexFunctor A).obj
      (CotangentPresentation.ringComplex C
        (Arrow.mk (CommRingCat.ofHom (algebraMap R A)))))
  intrinsic_normalization : intrinsicIso.inv = DerivedCategory.Q.map
    ((CotangentPresentation.tildeComplexFunctor A).map ringProjection ≫ doubleIso.hom)
  dualGenerator : Γ(Scheme.Modules.dual
    (Scheme.Modules.exteriorSheaf (tilde (chartComplex f A φ).neg) c), ⊤)
  dual_normalization : dualGenerator.app (op (Over.mk (𝟙 (⊤ : (Spec A).Opens))))
    (Scheme.Modules.exteriorSheafSection (tilde (chartComplex f A φ).neg) c ⊤
      (fun i ↦ tilde.toOpen (chartComplex f A φ).neg ⊤ (H.negBasis i))) = (1 : Γ(Spec A, ⊤))
  lineIso : tilde (ModuleCat.of A ((chartComplex f A φ).cofactorLine c)) ≅
    (sheafModel f A φ neg_free zero_free).line
  line_normalization : lineIso.hom.app ⊤
    (tilde.toOpen (ModuleCat.of A ((chartComplex f A φ).cofactorLine c)) ⊤
      (topDual H.negBasis ⊗ₜ[A] exteriorPower.ιMulti A (c + 1) H.zeroBasis)) =
    Scheme.Modules.tmulSection (X := Spec A)
      (M := Scheme.Modules.dual
        (Scheme.Modules.exteriorSheaf (tilde (chartComplex f A φ).neg) c))
      (N := Scheme.Modules.exteriorSheaf (tilde (chartComplex f A φ).zero) (c + 1))
      dualGenerator
      (Scheme.Modules.exteriorSheafSection (tilde (chartComplex f A φ).zero) (c + 1) ⊤
        (fun j ↦ tilde.toOpen (chartComplex f A φ).zero ⊤ (H.zeroBasis j)))

/-- The specified comparison from the affine exterior determinant to the intrinsic one.
It uses exactly the functor and model isomorphisms recorded by the determinant dependency.
Source: Stacks, Tags 0FJX and 0FJY
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def DeterminantChart.comparison {R : Type u} [CommRing R] {c : ℕ}
    {f : Fin c → PolynomialRing R c} {C : Coherence.{u}} {κ : Naive.Comparison C}
    {A : CommRingCat.{u}} [Algebra R A] {φ : QuotientRing f →ₐ[R] A}
    {H : Chart f C κ A φ} (J : DeterminantChart H)
    (T : TwoTermPerfectDeterminantData.{u, w})
    (hL : isTwoTermPerfect (Spec A) (DerivedCategory.Q.obj
      ((CotangentPresentation.tildeComplexFunctor A).obj
        (CotangentPresentation.ringComplex C
          (Arrow.mk (CommRingCat.ofHom (algebraMap R A))))))) :
    tilde (ModuleCat.of A ((chartComplex f A φ).cofactorLine c)) ≅
      twoTermDeterminantValue (T.functor (Spec A)) _ hL :=
  J.lineIso ≪≫ (T.modelIso (sheafModel f A φ J.neg_free J.zero_free)).symm ≪≫
    twoTermDeterminantIso (T.functor (Spec A))
      (T.model_mem (sheafModel f A φ J.neg_free J.zero_free)) hL J.intrinsicIso



/-- The wedge formula for every conormal basis and every lift, together with uniqueness
using just the indicated basis. The universal quantifier on bases is basis independence;
the cokernel argument is lift independence.
Source: Stacks, Tag 0E9Y (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def Chart.Formula {R : Type u} [CommRing R] {c : ℕ} {f : Fin c → PolynomialRing R c}
    {C : Coherence.{u}} {κ : Naive.Comparison C} {A : CommRingCat.{u}} [Algebra R A]
    {φ : QuotientRing f →ₐ[R] A} (H : Chart f C κ A φ) : Prop :=
  (∀ (b : Module.Basis (Fin c) A (chartComplex f A φ).neg)
    (v : (chartComplex f A φ).zero),
    H.w (H.omega ((LinearMap.range (chartComplex f A φ).differential.hom).mkQ v)) =
      topDual b ⊗ₜ[A] exteriorPower.ιMulti A (c + 1)
        (Fin.snoc (α := fun _ : Fin (c + 1) ↦ (chartComplex f A φ).zero)
          (fun i ↦ (chartComplex f A φ).differential.hom (b i)) v)) ∧
  (∀ w' : Ω[A⁄R] →ₗ[A] (chartComplex f A φ).cofactorLine c,
    (∀ v : (chartComplex f A φ).zero,
      w' (H.omega ((LinearMap.range (chartComplex f A φ).differential.hom).mkQ v)) =
        topDual H.negBasis ⊗ₜ[A] exteriorPower.ιMulti A (c + 1)
          (Fin.snoc (α := fun _ : Fin (c + 1) ↦ (chartComplex f A φ).zero)
            (fun i ↦ (chartComplex f A φ).differential.hom (H.negBasis i)) v)) →
    w' = H.w)

/-- Comparison between two presentations on the same affine algebra. The derived
isomorphism goes through the same intrinsic cotangent complex, and the determinant
is precisely the good-diagram, kernel-first determinant of the recorded dependency.
The equation on cokernels says its H⁰ map is the identity on intrinsic differentials.
Source: Stacks, Tags 0E9Y, 0FJM and 08QL
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def Chart.Transport {R : Type u} [CommRing R] {c c' : ℕ}
    {f : Fin c → PolynomialRing R c} {f' : Fin c' → PolynomialRing R c'}
    {C : Coherence.{u}} {κ : Naive.Comparison C} {A : CommRingCat.{u}} [Algebra R A]
    {φ : QuotientRing f →ₐ[R] A} {φ' : QuotientRing f' →ₐ[R] A}
    (H : Chart f C κ A φ) (H' : Chart f' C κ A φ') : Prop :=
  letI := Module.Finite.of_basis H.negBasis
  letI := Module.Finite.of_basis H.zeroBasis
  letI := Module.Projective.of_basis H.negBasis
  letI := Module.Projective.of_basis H.zeroBasis
  letI := Module.Finite.of_basis H'.negBasis
  letI := Module.Finite.of_basis H'.zeroBasis
  letI := Module.Projective.of_basis H'.negBasis
  letI := Module.Projective.of_basis H'.zeroBasis
  Nonempty (Module.TwoTermCofactorGoodDiagram (chartComplex f A φ) (chartComplex f' A φ')
    (H.cotangentIso ≪≫ H'.cotangentIso.symm)) ∧
  ∀ d : Module.TwoTermCofactorGoodDiagram (chartComplex f A φ) (chartComplex f' A φ')
    (H.cotangentIso ≪≫ H'.cotangentIso.symm),
    (∀ x : d.middle.zero,
      H.omega ((LinearMap.range (chartComplex f A φ).differential.hom).mkQ
        (d.left.zero.hom x)) =
      H'.omega ((LinearMap.range (chartComplex f' A φ').differential.hom).mkQ
        (d.right.zero.hom x))) ∧
    (d.determinant H.cofactor H'.cofactor).toLinearMap.comp H.w = H'.w

/-- The actual square of structure maps associated to a map of R-algebras.
Source: Stacks, Tag 08QL (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def algebraSquare {R : Type u} [CommRing R] {A A' : CommRingCat.{u}}
    [Algebra R A] [Algebra R A'] (ψ : A →ₐ[R] A') :
    Arrow.mk (CommRingCat.ofHom (algebraMap R A)) ⟶
      Arrow.mk (CommRingCat.ofHom (algebraMap R A')) :=
  Arrow.homMk' (𝟙 _) (CommRingCat.ofHom ψ.toRingHom)
    (CommRingCat.hom_ext ψ.comp_algebraMap.symm)

/-- The normalized map of chart complexes under restriction. Its two nonzero components
send the transported ordered frames to the corresponding frames. The derived equation
uses the standard-resolution map of the actual ring square.
Source: Stacks, Tags 08QL and 08T3
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
structure Chart.Restriction {R : Type u} [CommRing R] {c : ℕ}
    {f : Fin c → PolynomialRing R c} {C : Coherence.{u}} {κ : Naive.Comparison C}
    {A A' : CommRingCat.{u}} [Algebra R A] [Algebra R A']
    {φ : QuotientRing f →ₐ[R] A} {φ' : QuotientRing f →ₐ[R] A'}
    (H : Chart f C κ A φ) (H' : Chart f C κ A' φ') (ψ : A →ₐ[R] A') where
  map : (chartComplex f A φ).cofactorComplex ⟶
    ((ModuleCat.restrictScalars ψ.toRingHom).mapHomologicalComplex (.up ℤ)).obj
      (chartComplex f A' φ').cofactorComplex
  negative : ∀ i,
    (HomologicalComplex.doubleXIso₀ (chartComplex f A' φ').differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).hom
      (map.f (-1) ((HomologicalComplex.doubleXIso₀ (chartComplex f A φ).differential
        (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).inv (H.negBasis i))) = H'.negBasis i
  zero : ∀ j,
    (HomologicalComplex.doubleXIso₁ (chartComplex f A' φ').differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).hom
      (map.f 0 ((HomologicalComplex.doubleXIso₁ (chartComplex f A φ).differential
        (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).inv
          (H.zeroBasis j))) = H'.zeroBasis j
  intrinsic : H.cotangentIso.hom ≫ cotangentMap C (algebraSquare ψ) =
    DerivedCategory.Q.map map ≫
      (ModuleCat.restrictScalars ψ.toRingHom).mapDerivedCategoryFactors.inv.app
        (chartComplex f A' φ').cofactorComplex ≫
      (ModuleCat.restrictScalars ψ.toRingHom).mapDerivedCategory.map H'.cotangentIso.hom
  cofactor : ∀ a : A, H'.w (KaehlerDifferential.D R A' (ψ a)) =
    H'.trivialization.symm (ψ (H.trivialization (H.w (KaehlerDifferential.D R A a))))

/-- The determinant pullback map on the actual affine exterior lines, obtained solely
from the recorded determinant functor's model and pullback comparisons.
Source: Stacks, Tag 0FJY (blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def DeterminantChart.pullbackComparison {R : Type u} [CommRing R] {c : ℕ}
    {f : Fin c → PolynomialRing R c} {C : Coherence.{u}} {κ : Naive.Comparison C}
    {A A' : CommRingCat.{u}} [Algebra R A] [Algebra R A']
    {φ : QuotientRing f →ₐ[R] A} {φ' : QuotientRing f →ₐ[R] A'}
    {H : Chart f C κ A φ} {H' : Chart f C κ A' φ'}
    (J : DeterminantChart H) (J' : DeterminantChart H') (ψ : A →ₐ[R] A')
    (e : (derivedPullback (Spec.map (CommRingCat.ofHom ψ.toRingHom))).obj
      (DerivedCategory.Q.obj (sheafModel f A φ J.neg_free J.zero_free).complex) ≅
        DerivedCategory.Q.obj (sheafModel f A' φ' J'.neg_free J'.zero_free).complex)
    (T : TwoTermPerfectDeterminantData.{u, w}) :
    (Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom ψ.toRingHom))).obj
      (tilde (ModuleCat.of A ((chartComplex f A φ).cofactorLine c))) ⟶
        tilde (ModuleCat.of A' ((chartComplex f A' φ').cofactorLine c)) :=
  (Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom ψ.toRingHom))).map
      J.lineIso.hom ≫
    (Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom ψ.toRingHom))).map
      (T.modelIso (sheafModel f A φ J.neg_free J.zero_free)).inv ≫
    (T.pullbackIso (Spec.map (CommRingCat.ofHom ψ.toRingHom)) _
      (T.model_mem (sheafModel f A φ J.neg_free J.zero_free))).hom ≫
    (twoTermDeterminantIso (T.functor (Spec A'))
      (T.pullback_mem (Spec.map (CommRingCat.ofHom ψ.toRingHom)) _
        (T.model_mem (sheafModel f A φ J.neg_free J.zero_free)))
      (T.model_mem (sheafModel f A' φ' J'.neg_free J'.zero_free)) e).hom ≫
    (T.modelIso (sheafModel f A' φ' J'.neg_free J'.zero_free)).hom ≫ J'.lineIso.inv

/-- Restriction of the determinant identification. The termwise maps are fixed on the
actual pulled-back frames; the derived comparison uses the recorded K-flat counit.
For every canonical determinant functor, its pullback comparison transports the ordered
line generator to the ordered line generator. The equation is on the true inverse-image
open, with the actual restriction map, and includes the identity and empty affine chart.
Source: Stacks, Tags 08T3, 0FJX and 0FJY
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
structure DeterminantChart.Restriction {R : Type u} [CommRing R] {c : ℕ}
    {f : Fin c → PolynomialRing R c} {C : Coherence.{u}} {κ : Naive.Comparison C}
    {A A' : CommRingCat.{u}} [Algebra R A] [Algebra R A']
    {φ : QuotientRing f →ₐ[R] A} {φ' : QuotientRing f →ₐ[R] A'}
    {H : Chart f C κ A φ} {H' : Chart f C κ A' φ'}
    (J : DeterminantChart H) (J' : DeterminantChart H') (ψ : A →ₐ[R] A') where
  chain : CotangentPresentation.pullbackComplex
    (Spec.map (CommRingCat.ofHom ψ.toRingHom))
    (sheafModel f A φ J.neg_free J.zero_free).complex ⟶
      (sheafModel f A' φ' J'.neg_free J'.zero_free).complex
  derived : (derivedPullback (Spec.map (CommRingCat.ofHom ψ.toRingHom))).obj
    (DerivedCategory.Q.obj (sheafModel f A φ J.neg_free J.zero_free).complex) ≅
      DerivedCategory.Q.obj (sheafModel f A' φ' J'.neg_free J'.zero_free).complex
  normalization : derived.hom = CotangentPresentation.pullbackCounit
    (Spec.map (CommRingCat.ofHom ψ.toRingHom))
    (sheafModel f A φ J.neg_free J.zero_free).complex ≫ DerivedCategory.Q.map chain
  negative : ∀ i,
    ((sheafModel f A φ J.neg_free J.zero_free).pullbackNegativeMap
      (Spec.map (CommRingCat.ofHom ψ.toRingHom))
      (sheafModel f A' φ' J'.neg_free J'.zero_free) chain).app
        ((Spec.map (CommRingCat.ofHom ψ.toRingHom)) ⁻¹ᵁ ⊤)
      (Scheme.Modules.tensorPullbackSection (Spec.map (CommRingCat.ofHom ψ.toRingHom))
        (tilde (chartComplex f A φ).neg) ⊤
          (tilde.toOpen (chartComplex f A φ).neg ⊤ (H.negBasis i))) =
    (tilde (chartComplex f A' φ').neg).presheaf.map (homOfLE le_top).op
      (tilde.toOpen (chartComplex f A' φ').neg ⊤ (H'.negBasis i))
  zero : ∀ j,
    ((sheafModel f A φ J.neg_free J.zero_free).pullbackZeroMap
      (Spec.map (CommRingCat.ofHom ψ.toRingHom))
      (sheafModel f A' φ' J'.neg_free J'.zero_free) chain).app
        ((Spec.map (CommRingCat.ofHom ψ.toRingHom)) ⁻¹ᵁ ⊤)
      (Scheme.Modules.tensorPullbackSection (Spec.map (CommRingCat.ofHom ψ.toRingHom))
        (tilde (chartComplex f A φ).zero) ⊤
          (tilde.toOpen (chartComplex f A φ).zero ⊤ (H.zeroBasis j))) =
    (tilde (chartComplex f A' φ').zero).presheaf.map (homOfLE le_top).op
      (tilde.toOpen (chartComplex f A' φ').zero ⊤ (H'.zeroBasis j))
  determinant : ∀ (T : TwoTermPerfectDeterminantData.{u, w}), T.IsCanonical →
    (J.pullbackComparison J' ψ derived T).app
        ((Spec.map (CommRingCat.ofHom ψ.toRingHom)) ⁻¹ᵁ ⊤)
      (Scheme.Modules.tensorPullbackSection (Spec.map (CommRingCat.ofHom ψ.toRingHom))
        (tilde (ModuleCat.of A ((chartComplex f A φ).cofactorLine c))) ⊤
        (tilde.toOpen (ModuleCat.of A ((chartComplex f A φ).cofactorLine c)) ⊤
          (topDual H.negBasis ⊗ₜ[A] exteriorPower.ιMulti A (c + 1) H.zeroBasis))) =
    (tilde (ModuleCat.of A' ((chartComplex f A' φ').cofactorLine c))).presheaf.map
      (homOfLE le_top).op
      (tilde.toOpen (ModuleCat.of A' ((chartComplex f A' φ').cofactorLine c)) ⊤
        (topDual H'.negBasis ⊗ₜ[A'] exteriorPower.ιMulti A' (c + 1) H'.zeroBasis))

/-- The corresponding shifted Koszul orientation, expressed through the already recorded
ordered contraction convention. Its dual generator differs by the sign depending only
on the number of relations; consequently the associated scalar trivialization differs
by that same sign. This compares actual normalized Koszul comparisons, not arbitrary maps.
Source: Stacks, Duality, Tag 0BQZ, ordered contractions; Tag 0E9Y, ordered wedge
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
def KoszulOrientation {R : Type u} [CommRing R] {c : ℕ}
    (f : Fin c → PolynomialRing R c) : Prop :=
  ∀ (b : Module.Basis (Fin c) (QuotientRing f) (ideal f).Cotangent)
    (_hb : ∀ i, b i = relation f i)
    (q : ExteriorAlgebra.koszulDualComplex (PolynomialRing R c) c f ⟶
      (HomologicalComplex.single (ModuleCat (PolynomialRing R c)) (ComplexShape.up ℕ) c).obj
        (ExteriorAlgebra.koszulNormalDeterminant (PolynomialRing R c) (ideal f) c))
    (_hq : ExteriorAlgebra.IsKoszulConormalComparison
      (PolynomialRing R c) (ideal f) c f rfl q)
    (x : (ExteriorAlgebra.koszulComplex (PolynomialRing R c) c f).X c ⟶
      ModuleCat.of (PolynomialRing R c) (PolynomialRing R c))
    (_hx : x.hom (exteriorPower.ιMulti (PolynomialRing R c) c
      (fun i ↦ Finsupp.single i 1)) = 1),
    exteriorPower.pairingDual (QuotientRing f) (ideal f).Cotangent c
      (ExteriorAlgebra.koszulComparisonValue (PolynomialRing R c) (ideal f) c f q x) =
      (-1 : QuotientRing f) ^ (c * (c - 1) / 2) • topDual b

/-- All affine charts of all regular polynomial presentations, with a single compatible
choice of their normalized realization data. The chart hypothesis is exactly an open
immersion, so the empty affine, nonprincipal affine opens, identity and isomorphisms
are included. There is no smoothness, reducedness or characteristic hypothesis.
Source: Stacks, Tags 0E9Y, 08SJ, 08SL and 08T3
(blueprint: lem-sfb-affine-conormal-jacobian-realization). -/
structure Realization (R : Type u) [CommRing R] (C : Coherence.{u})
    (κ : Naive.Comparison C) where
  chart : ∀ (c : ℕ) (f : Fin c → PolynomialRing R c)
    (_hr : RingTheory.Sequence.IsRegular (PolynomialRing R c) (List.ofFn f))
    (A : CommRingCat.{u}) [Algebra R A] (φ : QuotientRing f →ₐ[R] A)
    (_ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))), Chart f C κ A φ
  formula : ∀ (c : ℕ) (f : Fin c → PolynomialRing R c)
    (hr : RingTheory.Sequence.IsRegular (PolynomialRing R c) (List.ofFn f))
    (A : CommRingCat.{u}) [Algebra R A] (φ : QuotientRing f →ₐ[R] A)
    (ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))),
    (chart c f hr A φ ho).Formula
  jacobian : ∀ (c : ℕ) (f : Fin c → PolynomialRing R c)
    (hr : RingTheory.Sequence.IsRegular (PolynomialRing R c) (List.ofFn f))
    (A : CommRingCat.{u}) [Algebra R A] (φ : QuotientRing f →ₐ[R] A)
    (ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)))
    (a : PolynomialRing R c),
    (chart c f hr A φ ho).trivialization ((chart c f hr A φ ho).w
      (KaehlerDifferential.D R A (φ (Ideal.Quotient.mk (ideal f) a)))) =
        φ (Ideal.Quotient.mk (ideal f) (augmentedJacobian f a))
  determinantChart : ∀ (c : ℕ) (f : Fin c → PolynomialRing R c)
    (hr : RingTheory.Sequence.IsRegular (PolynomialRing R c) (List.ofFn f))
    (A : CommRingCat.{u}) [Algebra R A] (φ : QuotientRing f →ₐ[R] A)
    (ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))),
    DeterminantChart (chart c f hr A φ ho)
  perfect : ∀ (c : ℕ) (f : Fin c → PolynomialRing R c)
    (_hr : RingTheory.Sequence.IsRegular (PolynomialRing R c) (List.ofFn f))
    (A : CommRingCat.{u}) [Algebra R A] (φ : QuotientRing f →ₐ[R] A)
    (_ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))),
    isTwoTermPerfect (Spec A) (DerivedCategory.Q.obj
        ((CotangentPresentation.tildeComplexFunctor A).obj
          (CotangentPresentation.ringComplex C
            (Arrow.mk (CommRingCat.ofHom (algebraMap R A))))))
  restriction : ∀ (c : ℕ) (f : Fin c → PolynomialRing R c)
    (hr : RingTheory.Sequence.IsRegular (PolynomialRing R c) (List.ofFn f))
    (A A' : CommRingCat.{u}) [Algebra R A] [Algebra R A']
    (φ : QuotientRing f →ₐ[R] A) (φ' : QuotientRing f →ₐ[R] A')
    (ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)))
    (ho' : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ'.toRingHom)))
    (ψ : A →ₐ[R] A') (_hψ : ψ.comp φ = φ'),
    Nonempty ((chart c f hr A φ ho).Restriction (chart c f hr A' φ' ho') ψ)
  determinant_restriction : ∀ (c : ℕ) (f : Fin c → PolynomialRing R c)
    (hr : RingTheory.Sequence.IsRegular (PolynomialRing R c) (List.ofFn f))
    (A A' : CommRingCat.{u}) [Algebra R A] [Algebra R A']
    (φ : QuotientRing f →ₐ[R] A) (φ' : QuotientRing f →ₐ[R] A')
    (ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)))
    (ho' : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ'.toRingHom)))
    (ψ : A →ₐ[R] A') (_hψ : ψ.comp φ = φ'),
    Nonempty ((determinantChart c f hr A φ ho).Restriction
      (determinantChart c f hr A' φ' ho') ψ)
  transport : ∀ (c c' : ℕ) (f : Fin c → PolynomialRing R c)
    (f' : Fin c' → PolynomialRing R c')
    (hr : RingTheory.Sequence.IsRegular (PolynomialRing R c) (List.ofFn f))
    (hr' : RingTheory.Sequence.IsRegular (PolynomialRing R c') (List.ofFn f'))
    (A : CommRingCat.{u}) [Algebra R A]
    (φ : QuotientRing f →ₐ[R] A) (φ' : QuotientRing f' →ₐ[R] A)
    (ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)))
    (ho' : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ'.toRingHom))),
    (chart c f hr A φ ho).Transport (chart c' f' hr' A φ' ho')
  koszul_orientation : ∀ (c : ℕ) (f : Fin c → PolynomialRing R c)
    (_hr : RingTheory.Sequence.IsRegular (PolynomialRing R c) (List.ofFn f)),
    KoszulOrientation f
  empty_relations : ∀ (f : Fin 0 → PolynomialRing R 0)
    (hr : RingTheory.Sequence.IsRegular (PolynomialRing R 0) (List.ofFn f))
    (A : CommRingCat.{u}) [Algebra R A] (φ : QuotientRing f →ₐ[R] A)
    (ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))),
    (chart 0 f hr A φ ho).w (KaehlerDifferential.D R A
      (φ (Ideal.Quotient.mk (ideal f) (MvPolynomial.X 0)))) =
    topDual (chart 0 f hr A φ ho).negBasis ⊗ₜ[A]
      exteriorPower.ιMulti A 1 (chart 0 f hr A φ ho).zeroBasis

/-- The affine conormal model, canonical intrinsic and determinant comparisons, unique
cofactor map and augmented Jacobian formula, coherently on all affine open charts and
under all isomorphisms of presented algebras.
Source: Stacks, Duality, Tag 0E9Y; Cotangent Complex, Tags 08RB, 08SJ, 08SL and 08T3;
More on Algebra, Tag 0FJM; Perfect Complexes, Tags 0FJX and 0FJY
(blueprint: lem-sfb-affine-conormal-jacobian-realization).

Proof:
1. Regular sequences are Koszul-regular (lem-weil-pbc-regular-sequence-koszul-regular).
The conormal-basis theorem lem-sc-koszul-conormal-basis gives the indicated basis of I/I².
The polynomial Kähler basis gives the ambient coordinate frame and Jacobian differential.
2. Jacobi--Zariski exactness gives the canonical cokernel isomorphism with Ω, sending dx_j
to d(x_j mod I). Polynomial differentiation lifts da to its partial-derivative vector.
No injectivity of the conormal differential is used.
3. The canonical comparison of lem-trf-lci-cotangent-presentation identifies this two-term
complex with the intrinsic cotangent complex. Its normalization is the projection of
lem-trf-lci-naive-cotangent-model. The determinant functor of
lem-trf-two-term-perfect-determinant gives exactly the dual-first exterior line, with its
canonical model, evaluation and pullback comparisons. The affine tilde comparisons carry
these to the sheafified standard-resolution complex.
4. Apply lem-sfb-two-term-cofactor-naturality. Alternation kills repeated relation vectors,
so changing a lift by an image changes nothing. A change of conormal basis multiplies the
relation wedge by det(g) and its dual by the inverse, hence cancels. Surjectivity onto the
cokernel proves uniqueness of the descended map.
5. The top ordered wedges give the normalized trivialization. Expanding the relation-first
wedge followed by the partial-derivative vector gives the permutation determinant. Reduction
modulo I preserves this sum, so the value is the augmented Jacobian.
6. Kähler localization and lem-sfb-cofactor-local-descent give the formula on principal opens.
Principal opens cover every affine open, and sheaf uniqueness on their intersections gives
compatibility on all affine opens. The intrinsic and determinant comparisons restrict by
their recorded normalization and pullback laws.
7. For an isomorphism of presented R-algebras lift the coordinate images to the other
polynomial presentation. Naive comparison naturality identifies H⁰ with the Kähler map.
Standard-resolution coherence identifies the intrinsic complexes; the good-diagram theorem
identifies their determinants and gives cofactor naturality. On literally transported frames
the normalized trivializations transport as well; different frames use the determinant
comparison, without equating unrelated scalar trivializations.
8. The ordering is relation-first and kernel-first. The corresponding shifted Koszul
normalization permutes only the fixed-rank blocks and introduces suspension signs depending
only on c. For c=0 both relation wedges are empty, the conormal module is zero, and the
formula sends dx_0 to dx_0; the augmented determinant is the one-by-one partial derivative.
-/
theorem exists_affineConormalJacobianRealization (R : Type u) [CommRing R]
    (C : Coherence.{u}) (κ : Naive.Comparison C) : Nonempty (Realization.{u, w} R C κ) := by
  sorry

end Algebra.AffineConormal
