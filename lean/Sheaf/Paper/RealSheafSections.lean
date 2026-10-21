/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Paper.EtaleWeilFundamentalRepresentation
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
import Sheaf.Paper.EtaleWeilSheafEquivalence
import Sheaf.Paper.RealSheavesSetup
import Sheaf.AlgebraicGeometry.PureDimension
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Curve
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.Paper.LisseIntegralSmallCoefficients
import Sheaf.Paper.GaloisLisseRepresentations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Paper.LisseAdicFiberFunctors
import Sheaf.Paper.LisseModuleSheaves
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.RepresentationTheory.LAdic
import WeilConjectures.GroupTheory.WeilGroup
import Sheaf.Paper.DenseOpenPiOneSurjective

/-!
# Ordinary etale adic sections and geometric invariants

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-p-real-sections,
Proposition p-real-sections (blueprint: p-real-sections).

Sections are inverse limits of finite-level etale sections, followed by rationalization
and coefficient extension. Evaluation uses finite-level germs. The Frobenius is uniquely
specified by the actual etale descent isomorphism, on every geometric stalk.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open FiniteEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {Y : Scheme.{u}}
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]

/-- Ordinary sections of the integral system on an etale object: its actual inverse
limit of section modules. Source: Weil II (1.1.1) b), p-real-sections proof, Step 3
(blueprint: p-real-sections). -/
def etaleIntegralSectionsAt (F : LisseIntegralSheaf l E Y) (V : Y.Etale) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) :=
  limit (F.obj ⋙ sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op V))

/-- Evaluation is the unique inverse-limit map with the actual finite-level germs
as its projections. Source: p-real-sections proof, Steps 3 and 5
(blueprint: p-real-sections).
Proof: finite-level germ maps are natural in the coefficient transitions. They
therefore give a cone from the limit of sections to the stalk diagram. Apply the
limit universal property. Its projection equations prove uniqueness. -/
theorem etaleIntegralEvaluation_exists (F : LisseIntegralSheaf l E Y) (V : Y.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (a : (pointSmallEtale t).fiber.obj V) :
    ∃! e : etaleIntegralSectionsAt l E F V ⟶ lisseIntegralFiber l E Y t F,
      ∀ n : ℕ,
        e ≫ limit.π (F.obj ⋙ (pointSmallEtale t).ulift.{u + 1}.sheafFiber) (op n) =
          limit.π (F.obj ⋙ sheafToPresheaf _ _ ⋙
            (CategoryTheory.evaluation _ _).obj (op V)) (op n) ≫
            (pointSmallEtale t).ulift.{u + 1}.toPresheafFiber V ⟨a⟩
              (F.obj.obj (op n)).obj := by
  sorry

/-- The uniquely determined ordinary evaluation map.
Source: p-real-sections proof, Step 5 (blueprint: p-real-sections). -/
def etaleIntegralEvaluation (F : LisseIntegralSheaf l E Y) (V : Y.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (a : (pointSmallEtale t).fiber.obj V) :
    etaleIntegralSectionsAt l E F V ⟶ lisseIntegralFiber l E Y t F :=
  (etaleIntegralEvaluation_exists l E F V t a).exists.choose

variable (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]

/-- Ordinary algebraic-coefficient sections, formed at the coefficient pair already
carried by the etale sheaf. This definition contains no representation or invariants.
Source: Weil II (1.1.1) b)--d), p-real-sections proof, Step 3
(blueprint: p-real-sections). -/
def etaleAlgebraicSectionsAt (F : LisseAlgebraicSheaf l Y Q) (V : Y.Etale) :
    ModuleCat.{u + 1} Q :=
  (ModuleCat.extendScalars (algebraMap (lisseAlgebraicPair l Y Q F).base.val Q)).obj
    ((ModuleCat.extendScalars
      (algebraMap (Padic.coefficientExtensionIntegers l
        (lisseAlgebraicPair l Y Q F).base.val) (lisseAlgebraicPair l Y Q F).base.val)).obj
      (etaleIntegralSectionsAt l (lisseAlgebraicPair l Y Q F).base.val
        (lisseCoefficientPairModel l Y Q (lisseAlgebraicPair l Y Q F)).integral V))

/-- Evaluation after the same two scalar extensions as the actual etale fibre.
Source: p-real-sections proof, Steps 3 and 5 (blueprint: p-real-sections). -/
def etaleAlgebraicEvaluation (F : LisseAlgebraicSheaf l Y Q) (V : Y.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (a : (pointSmallEtale t).fiber.obj V) :
    etaleAlgebraicSectionsAt l Q F V ⟶ lisseAlgebraicFiber l Y Q t F :=
  (ModuleCat.extendScalars (algebraMap (lisseAlgebraicPair l Y Q F).base.val Q)).map
    ((ModuleCat.extendScalars
      (algebraMap (Padic.coefficientExtensionIntegers l
        (lisseAlgebraicPair l Y Q F).base.val) (lisseAlgebraicPair l Y Q F).base.val)).map
      (etaleIntegralEvaluation l (lisseAlgebraicPair l Y Q F).base.val
        (lisseCoefficientPairModel l Y Q (lisseAlgebraicPair l Y Q F)).integral V t a))

/-- Frobenius on ordinary sections is uniquely characterized by pulling back a
section and applying the etale Weil descent datum. The two lifts select the same
open before and after Frobenius. Source: p-real-sections proof, Step 6
(blueprint: p-real-sections).
Proof: at a common finite coefficient field, pull back finite-level sections along
h and then apply the finite-stage morphism representing the descent isomorphism.
Pass to compatible inverse limits, invert the uniformizer and extend coefficients.
The finite germ formula gives the displayed equation; apply the inverse descent
isomorphism and h^-1 for the inverse. A section vanishing at all geometric points
is zero at every finite level, so these equations determine the map uniquely. -/
theorem etaleSectionsFrobenius_exists (h : Y ≅ Y) (V : Y.Etale)
    [IsOpenImmersion V.hom]
    (stable : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y),
      Nonempty ((pointSmallEtale t).fiber.obj V) ↔
        Nonempty ((pointSmallEtale (t ≫ h.hom)).fiber.obj V))
    (F : EtaleLisseWeilSheaf l Q h) :
    ∃! σ : etaleAlgebraicSectionsAt l Q F.carrier V ≃ₗ[Q]
        etaleAlgebraicSectionsAt l Q F.carrier V,
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y)
        (a : (pointSmallEtale t).fiber.obj V)
        (b : (pointSmallEtale (t ≫ h.hom)).fiber.obj V)
        (s : etaleAlgebraicSectionsAt l Q F.carrier V),
        etaleAlgebraicEvaluation l Q F.carrier V t a (σ s) =
          etaleAlgebraicFiberMap l Q t F.str.hom
            ((lisseAlgebraicAutomorphismFiberIso h l Q t F.carrier).inv
              (etaleAlgebraicEvaluation l Q F.carrier V (t ≫ h.hom) b s)) := by
  sorry

/-- The uniquely specified actual Frobenius on ordinary sections.
Source: p-real-sections proof, Step 6 (blueprint: p-real-sections). -/
def etaleSectionsFrobenius (h : Y ≅ Y) (V : Y.Etale) [IsOpenImmersion V.hom]
    (stable : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y),
      Nonempty ((pointSmallEtale t).fiber.obj V) ↔
        Nonempty ((pointSmallEtale (t ≫ h.hom)).fiber.obj V))
    (F : EtaleLisseWeilSheaf l Q h) :
    etaleAlgebraicSectionsAt l Q F.carrier V ≃ₗ[Q]
      etaleAlgebraicSectionsAt l Q F.carrier V :=
  (etaleSectionsFrobenius_exists l Q h V stable F).exists.choose

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.WeilGroup
open Scheme Scheme.FiniteEtale

/-- The geometric standing curve is Noetherian and separated, and the coefficient
prime is invertible there. These are consequences of the standing arithmetic curve
hypotheses, supplied as proof data rather than additional assumptions of the theorem.
Source: p-real-sections proof, Steps 1 and 2 (blueprint: p-real-sections).
Proof: finite type and quasi-compactness survive field base change. The algebraic
closure is Noetherian, so the geometric curve is Noetherian. Separatedness survives
base change. Every residue field is an algebra over K of the same characteristic;
the prime different from that characteristic is nonzero, hence invertible. -/
theorem sectionsGeometricCurve_properties {K : Type u} [Field K] [Finite K]
    {C : Scheme.{u}} [C.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))] :
    IsNoetherian (C ↘ Spec (.of K)).geometricFiber ∧
      (C ↘ Spec (.of K)).geometricFiber.IsSeparated ∧
      ∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar K ≠ l)]
        (x : (C ↘ Spec (.of K)).geometricFiber),
        Nonempty (Invertible (l : (C ↘ Spec (.of K)).geometricFiber.residueField x)) := by
  sorry

/-- Noetherianity supplied by the standing curve hypotheses.
Source: p-real-sections proof, Step 1 (blueprint: p-real-sections). -/
instance sectionsGeometricCurve_noetherian {K : Type u} [Field K] [Finite K]
    {C : Scheme.{u}} [C.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))] :
    IsNoetherian (C ↘ Spec (.of K)).geometricFiber :=
  (sectionsGeometricCurve_properties (C := C)).1

/-- Separatedness supplied by the standing curve hypotheses.
Source: p-real-sections proof, Step 1 (blueprint: p-real-sections). -/
instance sectionsGeometricCurve_separated {K : Type u} [Field K] [Finite K]
    {C : Scheme.{u}} [C.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))] :
    (C ↘ Spec (.of K)).geometricFiber.IsSeparated :=
  (sectionsGeometricCurve_properties (C := C)).2.1

/-- The coefficient prime is a unit on the geometric curve.
Source: p-real-sections proof, Step 2 (blueprint: p-real-sections). -/
instance sectionsGeometricCurve_invertible {K : Type u} [Field K] [Finite K]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
    {C : Scheme.{u}} [C.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))]
    (x : (C ↘ Spec (.of K)).geometricFiber) :
    Invertible (l : (C ↘ Spec (.of K)).geometricFiber.residueField x) :=
  Classical.choice ((sectionsGeometricCurve_properties (C := C)).2.2 l x)

/-- The actual geometric etale open. Source: p-real-sections, U=U_0 times k
(blueprint: p-real-sections). -/
abbrev sectionsGeometricOpen {K : Type u} [Field K] {C U : Scheme.{u}}
    [C.Over (Spec (.of K))] [U.Over (Spec (.of K))]
    (j : U ⟶ C) [j.IsOver (Spec (.of K))] [IsOpenImmersion j] :
    (C ↘ Spec (.of K)).geometricFiber.Etale :=
  Scheme.Etale.mk (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (.of K))))

/-- The recorded geometric-base-change open-immersion instance, exposed through
the etale-object wrapper. Source: p-real-sections, the geometric open
(blueprint: p-real-sections). -/
instance sectionsGeometricOpen_isOpenImmersion {K : Type u} [Field K]
    {C U : Scheme.{u}} [C.Over (Spec (.of K))] [U.Over (Spec (.of K))]
    (j : U ⟶ C) [j.IsOver (Spec (.of K))] [IsOpenImmersion j] :
    IsOpenImmersion (sectionsGeometricOpen (K := K) j).hom :=
  inferInstanceAs (IsOpenImmersion
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (.of K)))))

/-- An arithmetic open is stable under geometric Galois Frobenius.
Source: p-real-sections proof, Step 6 (blueprint: p-real-sections).
Proof: the geometric base-change map commutes with id times geometric Frobenius.
Compose each lift with Frobenius on U for one implication and its inverse for the
other. Their composites are identity lifts. -/
theorem sectionsGeometricOpen_stable {K : Type u} [Field K] [Finite K]
    {C U : Scheme.{u}} [C.Over (Spec (.of K))] [U.Over (Spec (.of K))]
    (j : U ⟶ C) [j.IsOver (Spec (.of K))] [IsOpenImmersion j] :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ (C ↘ Spec (.of K)).geometricFiber),
      Nonempty ((pointSmallEtale t).fiber.obj (sectionsGeometricOpen (K := K) j)) ↔
        Nonempty ((pointSmallEtale
          (t ≫ (C ↘ Spec (.of K)).geometricGaloisFrobenius.hom)).fiber.obj
            (sectionsGeometricOpen (K := K) j)) := by
  sorry

/-- Ordinary etale adic sections on a nonempty arithmetic open are the geometric
invariants of the actual etale Weil fundamental representation, by evaluation,
compatibly with residual Frobenius. Source: blueprint main-20261015, p-real-sections
(blueprint: p-real-sections).

Proof plan, following the node's six steps:
1. Base change of the standing smooth finite-type separated geometrically connected
curve gives a connected smooth geometric curve of dimension one, using the recorded
base-change, dimension and sobriety dependencies.
2. Smooth-connected-curve local rings and smooth-normality make the curve integral,
Noetherian and normal. The nonempty open is connected and dense. Base-change image
surjectivity also makes the arithmetic open dense. The coefficient prime is invertible.
3. Finite-level ordinary sections equal maps from the rank-one coefficient sheaf,
by multiplication by a section and evaluation at 1. Take compatible inverse limits,
rationalize and extend the finite coefficient field, as in def-pod-lisse-l-adic-sheaves.
4. Apply cor-galois-lisse-representations to the underlying etale lisse sheaves on
this connected open. Its unit is trivial and its action is the geometric restriction
of def-wf-fundamental-representation, by the finite-cover germ normalization.
5. Evaluation at 1 identifies equivariant maps from the trivial representation with
invariants, with inverse v mapping a to a times v. The resulting map is precisely
the actual finite-level germ map, limit, coefficient extension and path transport below.
6. Dense-open Weil-group surjectivity lifts the selected degree-one element. Its
conjugation preserves the degree kernel, so it acts invertibly on invariants. On
sections, etaleSectionsFrobenius is pullback followed by descent; its stalk formula
is exactly the degree-one operator of etaleFundamentalRep. Evaluation is equivariant.
Two lifts differ by a geometric element and hence have the same action on invariants. -/
theorem ordinarySections_eq_geometricInvariants
    {K : Type u} [Field K] [Finite K] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar K ≠ l)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    {C U : Scheme.{u}} [C.Over (Spec (.of K))] [U.Over (Spec (.of K))]
    [IsCurve (C ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
    [GeometricallyConnected (C ↘ Spec (.of K))] [IsCurve (U ↘ Spec (.of K))]
    (j : U ⟶ C) [j.IsOver (Spec (.of K))] [IsOpenImmersion j] [Nonempty U]
    (W : WeilGroup (C ↘ Spec (.of K))) (WU : WeilGroup (U ↘ Spec (.of K)))
    (R : Restriction j WU W) (B : BasePointData W) (D : WeilMonodromyData B)
    (F : EtaleLisseWeilSheaf l Q (C ↘ Spec (.of K)).geometricGaloisFrobenius)
    (t : Spec (.of (AlgebraicClosure K)) ⟶ (U ↘ Spec (.of K)).geometricFiber)
    (τ : fiber (t ≫ Scheme.Hom.geometricFiberMap j (comp_over j (Spec (.of K)))) ≅
      fiber B.t) :
    ∃ e : etaleAlgebraicSectionsAt l Q F.carrier (sectionsGeometricOpen (K := K) j) ≃ₗ[Q]
        Representation.invariants
          (((etaleFundamentalRep l Q (C ↘ Spec (.of K)).geometricGaloisFrobenius B.t
            D.degreeDatum D.toEtale F).comp R.restrict).comp WU.geometric.subtype),
      (∀ s, (e s : lisseAlgebraicFiber l (C ↘ Spec (.of K)).geometricFiber Q B.t F.carrier) =
        etaleAlgebraicPath l Q F.carrier τ
          (etaleAlgebraicEvaluation l Q F.carrier (sectionsGeometricOpen (K := K) j) _
            (Over.homMk t) s)) ∧
      ∀ s, (e (etaleSectionsFrobenius l Q
          (C ↘ Spec (.of K)).geometricGaloisFrobenius (sectionsGeometricOpen (K := K) j)
          (sectionsGeometricOpen_stable (K := K) j) F s) :
          lisseAlgebraicFiber l (C ↘ Spec (.of K)).geometricFiber Q B.t F.carrier) =
        etaleFundamentalRep l Q (C ↘ Spec (.of K)).geometricGaloisFrobenius B.t
          D.degreeDatum D.toEtale F D.frobLift (e s) := by
  sorry

end AlgebraicGeometry.WeilGroup
