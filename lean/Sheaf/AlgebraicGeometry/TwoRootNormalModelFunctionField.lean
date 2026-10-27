/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.TraceFormula.LocalDimensionFormula
import WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Function field of a normal two-root chart model

Source: Stacks Project, Tags 0358, 01RV, 01RW and 035I; the explicit two-root
fraction-field and integral-closure calculation in the DAG proof.
(blueprint: lem-sfb-two-root-normal-model-function-field)

The Boolean chart index is false for C (coordinate x, roots a,b), and true for A
(coordinate y, roots v,u). Compatible coordinates over base affines are encoded by
sections on the full inverse images of the two standard opens: their restrictions
are automatically compatible, and conversely the assumed compatible coordinates
glue uniquely to these sections. A surjective polynomial evaluation with the given
kernel is precisely the displayed quotient presentation, with its prescribed
coefficient and coordinate maps. All function-field identifications use germs.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.TwoRootNormalModel

/-- The standard x- or y-open of P1 over U, with false denoting x.
Source: Stacks 01NG, standard projective charts.
(blueprint: lem-sfb-two-root-normal-model-function-field) -/
abbrev standard (U : Scheme.{u}) (i : Bool) :
    (ProjectiveSpace (ULift.{u} Bool) U).Opens :=
  ProjectiveSpace.standardOpen (ULift.{u} Bool) U ⟨i⟩

/-- The standard chart above a base open V.
Source: Stacks 01NG, the base-changed standard charts.
(blueprint: lem-sfb-two-root-normal-model-function-field) -/
def targetChart (U : Scheme.{u}) (V : U.Opens) (i : Bool) :
    (ProjectiveSpace (ULift.{u} Bool) U).Opens :=
  standard U i ⊓ (ProjectiveSpace (ULift.{u} Bool) U ↘ U) ⁻¹ᵁ V

/-- The inverse-image affine chart of the given cover.
Source: Stacks 035I, affine-local normalization; the displayed two-root charts.
(blueprint: lem-sfb-two-root-normal-model-function-field) -/
def sourceChart {U Y : Scheme.{u}}
    (q : Y ⟶ ProjectiveSpace (ULift.{u} Bool) U) (V : U.Opens) (i : Bool) : Y.Opens :=
  q ⁻¹ᵁ targetChart U V i

/-- Restriction of one of the two given root coordinates to a base open.
Source: the compatible chart presentations in the DAG statement, Stacks 01RV.
(blueprint: lem-sfb-two-root-normal-model-function-field) -/
def rootOn {U Y : Scheme.{u}}
    (q : Y ⟶ ProjectiveSpace (ULift.{u} Bool) U) (V : U.Opens) (i : Bool)
    (t : Γ(Y, q ⁻¹ᵁ standard U i)) : Γ(Y, sourceChart q V i) :=
  Y.presheaf.map (homOfLE (q.preimage_mono inf_le_left)).op t

/-- The polynomial ideal of the two-root presentation. Variables are (x,a,b) on C
and (y,v,u) on A; thus the A equations are v^n=y and u^n=1-y.
Source: the displayed chart equations in the DAG statement, Stacks 01RV.
(blueprint: lem-sfb-two-root-normal-model-function-field) -/
def relations (R : Type u) [CommRing R] (n : ℕ) (i : Bool) :
    Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {MvPolynomial.X 1 ^ n - MvPolynomial.X 0,
    MvPolynomial.X 2 ^ n -
      (if i then 1 - MvPolynomial.X 0 else MvPolynomial.X 0 - 1)}

/-- The prescribed presentation map, with structural coefficients, the pulled-back
standard projective coordinate, and the two given root sections.
Source: the two-root chart presentations in the DAG statement, Stacks 01NG and 01RV.
(blueprint: lem-sfb-two-root-normal-model-function-field) -/
def presentation {U Y : Scheme.{u}}
    (q : Y ⟶ ProjectiveSpace (ULift.{u} Bool) U) (V : U.Opens) (i : Bool)
    (r s : ∀ j : Bool, Γ(Y, q ⁻¹ᵁ standard U j)) :
    MvPolynomial (Fin 3) Γ(U, V) →+* Γ(Y, sourceChart q V i) :=
  MvPolynomial.eval₂Hom
    ((q ≫ ProjectiveSpace (ULift.{u} Bool) U ↘ U).appLE V (sourceChart q V i)
      (fun _z hz ↦ hz.2)).hom
    ![q.appLE (standard U i) (sourceChart q V i) (q.preimage_mono inf_le_left)
        (ProjectiveSpace.coordRatio (ULift.{u} Bool) U ⟨i⟩ ⟨!i⟩),
      rootOn q V i (r i), rootOn q V i (s i)]

/-- Restrict a C-coordinate to the intersection with the A-chart.
Source: the overlap substitutions in the DAG statement, Stacks 01NG.
(blueprint: lem-sfb-two-root-normal-model-function-field) -/
def onOverlapC {U Y : Scheme.{u}}
    (q : Y ⟶ ProjectiveSpace (ULift.{u} Bool) U)
    (t : Γ(Y, q ⁻¹ᵁ standard U false)) :
    Γ(Y, q ⁻¹ᵁ (standard U false ⊓ standard U true)) :=
  Y.presheaf.map (homOfLE (q.preimage_mono inf_le_left)).op t

/-- Restrict an A-coordinate to the intersection with the C-chart.
Source: the overlap substitutions in the DAG statement, Stacks 01NG.
(blueprint: lem-sfb-two-root-normal-model-function-field) -/
def onOverlapA {U Y : Scheme.{u}}
    (q : Y ⟶ ProjectiveSpace (ULift.{u} Bool) U)
    (t : Γ(Y, q ⁻¹ᵁ standard U true)) :
    Γ(Y, q ⁻¹ᵁ (standard U false ⊓ standard U true)) :=
  Y.presheaf.map (homOfLE (q.preimage_mono inf_le_right)).op t

/-- A normal integral finite two-root model has the specified function field and is
exactly the normalization of P1 in it, on both charts and globally.
Source: Stacks 0358, 01RV, 01RW and 035I; the DAG's explicit two-root argument.
(blueprint: lem-sfb-two-root-normal-model-function-field)

Proof, following the six DAG steps:
1. The standard chart theorem (lem-weil-pbc-projective-space-standard-charts) gives
   domain charts R[x], R[y] (lem-weil-pbc-polynomial-ring-domain). Charts over any
   two nonempty base affines meet above a common nonempty affine refinement, also
   on the principal open where x is invertible. They form a reduced irreducible
   nonempty cover, so P is integral (def-pc-integral-scheme).
2. Apply lem-sc-integral-function-field-affine-fraction on one nonempty base affine
   and its x-chart. Clearing coefficient denominators identifies Frac R[x] with
   K(x), preserving structural constants and the standard coordinate. Surjectivity
   makes q dominant; def-sfb-dominant-function-field-map is its generic-stalk map.
3. The nonempty source C-chart has fraction field k(Y) by the same affine-fraction
   lemma. Its root-coordinate germs satisfy a^n=x and b^n=x-1. Every fraction in
   its presented ring belongs to K(x)(a,b), and the converse inclusion is immediate.
   Restriction compatibility identifies these germs over all base affines.
4. The subalgebra K(x)[a,b] is spanned by a^i b^j for i,j<n, by reducing powers
   with the two monic equations. It is a domain, hence a field by
   lem-weil-pbc-finite-dimensional-domain-is-field. It is therefore k(Y), proving
   finiteness without asserting independence of these monomials.
5. The base and source are locally Noetherian by pqf-lem-locnoeth-lft, finite type
   over the field and the chart presentations. Apply
   lem-sbc-normal-sections-finite-product on each affine source chart. Its domain
   property forces the finite product to have exactly one factor, giving integral
   closedness; the affine-fraction theorem gives its fraction field k(Y).
6. Apply lem-sfb-finite-normal-cover-normalization, or its affine argument: the
   source ring S is integral over the target chart ring B; an element of k(Y)
   integral over B is integral over S, hence lies in S. Thus S is exactly the
   integral closure. These equalities use the canonical germs and commute with
   restrictions, so glue to the P-isomorphism with normalization. The given
   v*a=1 and u*a=b give v=a^-1 and u=b/a; y=x^-1 is the standard projective
   coordinate relation. No condition on characteristic, roots of unity, primality
   of n or normality of U is used.
-/
theorem functionField_and_normalization
    (k₀ : Type u) [Field k₀] (U Y : Scheme.{u}) [IsIntegral U] [IsIntegral Y]
    (p : U ⟶ Spec (.of k₀)) [LocallyOfFiniteType p] [QuasiCompact p]
    (n : ℕ) (hn : 1 ≤ n)
    (q : Y ⟶ ProjectiveSpace (ULift.{u} Bool) U) [IsFinite q] [Surjective q]
    (hnormal : ∀ z : Y, IsDomain (Y.presheaf.stalk z) ∧
      IsIntegrallyClosed (Y.presheaf.stalk z))
    (r s : ∀ i : Bool, Γ(Y, q ⁻¹ᵁ standard U i))
    (hcharts : ∀ (V : U.affineOpens) (i : Bool),
      IsAffineOpen (sourceChart q V.1 i) ∧
      Function.Surjective (presentation q V.1 i r s) ∧
      RingHom.ker (presentation q V.1 i r s) = relations Γ(U, V.1) n i)
    (hv : onOverlapA q (r true) * onOverlapC q (r false) = 1)
    (hu : onOverlapA q (s true) * onOverlapC q (r false) = onOverlapC q (s false)) :
    ∃ (_ : IsIntegral (ProjectiveSpace (ULift.{u} Bool) U))
      (_ : Nonempty (standard U false)) (_ : Nonempty (q ⁻¹ᵁ standard U false))
      (e : RatFunc U.functionField ≃+*
        (ProjectiveSpace (ULift.{u} Bool) U).functionField)
      (_ : Algebra (ProjectiveSpace (ULift.{u} Bool) U).functionField Y.functionField),
      e RatFunc.X = (ProjectiveSpace (ULift.{u} Bool) U).germToFunctionField _
        (ProjectiveSpace.coordRatio (ULift.{u} Bool) U ⟨false⟩ ⟨true⟩) ∧
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          (ProjectiveSpace (ULift.{u} Bool) U).fromSpecFunctionField ≫
            ProjectiveSpace (ULift.{u} Bool) U ↘ U =
        Spec.map (CommRingCat.ofHom (algebraMap U.functionField (RatFunc U.functionField))) ≫
          U.fromSpecFunctionField ∧
      Spec.map (CommRingCat.ofHom (algebraMap
          (ProjectiveSpace (ULift.{u} Bool) U).functionField Y.functionField)) ≫
            (ProjectiveSpace (ULift.{u} Bool) U).fromSpecFunctionField =
        Y.fromSpecFunctionField ≫ q ∧
      FiniteDimensional (ProjectiveSpace (ULift.{u} Bool) U).functionField Y.functionField ∧
      (∃ a b : Y.functionField,
        a = Y.germToFunctionField _ (r false) ∧
        b = Y.germToFunctionField _ (s false) ∧
        a ^ n = algebraMap _ _ (e RatFunc.X) ∧
        b ^ n = algebraMap _ _ (e RatFunc.X - 1) ∧
        IntermediateField.adjoin
          (ProjectiveSpace (ULift.{u} Bool) U).functionField {a, b} = ⊤) ∧
      (∀ (V : U.affineOpens) (_ : Nonempty V.1) (i : Bool),
        ∃ (_ : Nonempty (sourceChart q V.1 i))
          (_ : Algebra Γ(ProjectiveSpace (ULift.{u} Bool) U, targetChart U V.1 i)
            Y.functionField),
          (∀ t : Γ(ProjectiveSpace (ULift.{u} Bool) U, targetChart U V.1 i),
            algebraMap _ _ t =
              Y.germToFunctionField (sourceChart q V.1 i) (q.app (targetChart U V.1 i) t)) ∧
          IsDomain Γ(Y, sourceChart q V.1 i) ∧
          IsIntegrallyClosed Γ(Y, sourceChart q V.1 i) ∧
          IsFractionRing Γ(Y, sourceChart q V.1 i) Y.functionField ∧
          (integralClosure Γ(ProjectiveSpace (ULift.{u} Bool) U, targetChart U V.1 i)
            Y.functionField : Set Y.functionField) =
            Set.range (Y.germToFunctionField (sourceChart q V.1 i))) ∧
      ∃ E : Y ≅ (ProjectiveSpace (ULift.{u} Bool) U).normalizationIn Y.functionField,
        E.hom ≫ (ProjectiveSpace (ULift.{u} Bool) U).fromNormalizationIn Y.functionField = q ∧
        Y.fromSpecFunctionField ≫ E.hom =
          ((ProjectiveSpace (ULift.{u} Bool) U).fromSpecOfAlgebraFunctionField
            Y.functionField).toNormalization := by
  sorry

end AlgebraicGeometry.TwoRootNormalModel
