/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.NumberTheory.Padics.PadicIntegersIntegralClosure
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.Paper.PadicIntegersInvertEll
import Sheaf.Topology.ProfiniteCondensedRing

/-!
# Finite free integral and rational pro-etale coefficients

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-cartesian-coefficients-finite-free.md
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The integral inclusion for finite subfields, using the existing integers map.
Source: blueprint finite-free coefficient detail, integral inclusion
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free). -/
noncomputable abbrev finiteCoefficientIntegersMap
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    PadicAlgCl.integers ℓ E.1 →+* PadicAlgCl.integers ℓ F.1 :=
  letI := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower E.1 F.1 (PadicAlgCl ℓ) :=
    Subalgebra.inclusion.isScalarTower_right
      (show E.1.toSubalgebra ≤ F.1.toSubalgebra from h) (PadicAlgCl ℓ)
  PadicAlgCl.integersMap ℓ E.1 F.1

/-- The degree of the indicated inclusion, with its actual scalar action.
Source: blueprint finite-free coefficient detail, d = [F:E]
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free). -/
noncomputable abbrev finiteCoefficientDegree
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) : ℕ :=
  @Module.finrank E.1 F.1 inferInstance inferInstance
    (Module.compHom F.1 (IntermediateField.inclusion h).toRingHom)

/-- The type of integral bases for the actual inclusion of integer rings.
Source: blueprint finite-free coefficient detail, choice of b_1,...,b_d
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free). -/
noncomputable abbrev finiteCoefficientIntegralBasis
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :=
  @Module.Basis (Fin (finiteCoefficientDegree ℓ h))
    (PadicAlgCl.integers ℓ E.1) (PadicAlgCl.integers ℓ F.1)
    inferInstance inferInstance
    (Module.compHom (PadicAlgCl.integers ℓ F.1) (finiteCoefficientIntegersMap ℓ h))

/-- The condensed integral inclusion, by postcomposition on continuous functions.
Source: blueprint finite-free coefficient detail, integral coefficient inclusion
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free). -/
noncomputable def finiteCoefficientIntegersPointMap
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Profinite.padicIntegersRingObj.{u} ℓ E.1 ⟶ Profinite.padicIntegersRingObj ℓ F.1 :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (finiteCoefficientIntegersMap ℓ h)
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _))

/-- The integral coefficient inclusion is a ring-object map.
Source: blueprint finite-free coefficient detail, integral coefficient inclusion
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free). -/
noncomputable instance isMonHom_finiteCoefficientIntegersPointMap
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    IsMonHom (finiteCoefficientIntegersPointMap.{u} ℓ h) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (finiteCoefficientIntegersMap ℓ h)
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _))))

/-- The basis summand on the point: postcompose a continuous function with a ↦ φ(a)t.
Source: blueprint finite-free coefficient detail, displayed sum formula
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free). -/
noncomputable def finiteCoefficientPointSummand
    {R T : Type} [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (φ : R →+* T) (hφ : Continuous φ) (t : T) :
    Profinite.continuousMapRingObj.{u} R ⟶ Profinite.continuousMapRingObj T :=
  ⟨{ app S := AddCommGrpCat.ofHom
        (ULift.ringEquiv.symm.toAddMonoidHom.comp
          ((((AddMonoidHom.mulRight t).comp φ.toAddMonoidHom).compLeftContinuous S.unop
            (hφ.mul_const t)).comp ULift.ringEquiv.toAddMonoidHom))
     naturality _ _ _ := rfl }⟩

/-- The integral summand on X, with exactly the multiplication-by-b formula.
Source: blueprint finite-free coefficient detail, apply p_X^*
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free). -/
noncomputable abbrev finiteCoefficientIntegralSummand (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (b : PadicAlgCl.integers ℓ F.1) :=
  (upperStarFromPoint X).map (finiteCoefficientPointSummand
    (finiteCoefficientIntegersMap ℓ h)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _) b)

/-- The rational summand on X, using the same integral basis vector in F.
Source: blueprint finite-free coefficient detail, rational displayed sum formula
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free). -/
noncomputable abbrev finiteCoefficientRationalSummand (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (b : PadicAlgCl.integers ℓ F.1) :=
  (upperStarFromPoint X).map (finiteCoefficientPointSummand
    (IntermediateField.inclusion h).toRingHom
    (continuous_subtype_val.subtype_mk _) (b : F.1))

/-- The i-th integral free-module summand, on underlying abelian sheaves.
Source: blueprint finite-free coefficient detail, integral direct power
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free). -/
noncomputable abbrev finiteCoefficientIntegralLeg (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (i : Fin (finiteCoefficientDegree ℓ h)) :=
  (biproduct.ι (fun _ : Fin (finiteCoefficientDegree ℓ h) =>
    Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) i).hom

/-- The i-th rational free-module summand, on underlying abelian sheaves.
Source: blueprint finite-free coefficient detail, rational direct power
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free). -/
noncomputable abbrev finiteCoefficientRationalLeg (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (i : Fin (finiteCoefficientDegree ℓ h)) :=
  (biproduct.ι (fun _ : Fin (finiteCoefficientDegree ℓ h) =>
    Mod.regular (padicSubfieldRingObj X ℓ E)) i).hom

/-- Integral and rational coefficient sheaves are finite free, by the specified basis maps.
All squares are stated on coproduct injections, which jointly determine the full square.

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-cartesian-coefficients-finite-free.md
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free).

Proof:
1. The integer rings are DVRs by lem-weil-l-adic-extension-integers-dvr. The lower
   ring is a Noetherian normal PID by lem-weil-pbc-pid-noetherian-normal. The upper
   ring is its integral closure by lem-sfb-padic-integers-integral-closure.
   Characteristic zero gives separability; apply
   lem-weil-pbc-noetherian-normal-separable-integral-closure-finite and then
   lem-sc-dvr-fg-torsionfree-free to get a finite integral basis.
2. Multiplying an element of F, or all coefficients in a relation, by a sufficiently
   large power of ell puts it in the integral ring. Thus this basis is an E-basis
   of F, and its rank is d. This also applies to every chosen integral basis.
3. The rational basis map is a homeomorphism by lem-weil-l-adic-extension-complete
   and lem-weil-pbc-finite-dimensional-linear-homeomorphism. Restricting it to the
   integral lattices gives the integral homeomorphism, with the subspace topologies
   of def-sfb-padic-integers-condensed-ring.
4. Applying continuous functions on each profinite S gives mutually inverse linear
   maps; their formulas commute with precomposition (sk-def-sfb-condensed-ring).
5. Apply p_X^* (sk-def-sfb-pullback-from-point). It preserves finite coproducts and
   transports module structures (sk-def-sfb-transport), giving the integral iso
   on the rings of sk-def-sfb-pulled-back-coefficients, with the specified summands.
6. Invert ell using det-prop-sfb-qlbar-colimit-x-invert-ell. Restriction of scalars
   preserves colimits by sk-def-sfb-change-of-scalars. Finite sums commute with
   these colimits, so this gives the rational iso. The condensed inclusion square
   commutes sectionwise; applying p_X^* and the localization universal property
   identifies the rational action with def-sfb-subfield-coefficient-map. Term zero
   gives the square with def-sfb-integers-to-subfield.
7. Naturality of sk-def-sfb-pullback-from-point-comp on multiplication by each b_i
   gives both inverse-image squares with the sk-def-sfb-coefficient-morphisms maps.
8. The balanced coequalizer of sk-def-sfb-change-of-scalars identifies extension
   by either finite free ring with the d-fold sum of the underlying module:
   (sum a_i b_i) tensor m maps to (a_i m), with inverse sum b_i tensor m_i.
9. Finite limits of abelian sheaves and module objects are computed on underlying
   sheaves, and commute with finite powers. Thus both scalar extensions preserve
   finite limits, which is the asserted flatness (sk-def-sfb-module-objects).
-/
theorem cartesianCoefficients_finiteFree
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Nonempty (finiteCoefficientIntegralBasis ℓ h) ∧
    (∀ b : finiteCoefficientIntegralBasis ℓ h,
      ∃ e₀ : ∀ X : Scheme.{u},
        Mod.finiteFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
            (finiteCoefficientDegree ℓ h) ≅
          (Mod.comap (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) X)).obj
            (Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) X)),
      ∃ e₁ : ∀ X : Scheme.{u},
        Mod.finiteFree (padicSubfieldRingObj X ℓ E) (finiteCoefficientDegree ℓ h) ≅
          (Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
            (Mod.regular (padicSubfieldRingObj X ℓ F)),
      (∀ (X : Scheme.{u}) (i : Fin (finiteCoefficientDegree ℓ h)),
        finiteCoefficientIntegralLeg ℓ X h i ≫ (e₀ X).hom.hom =
          finiteCoefficientIntegralSummand ℓ X h (b i)) ∧
      (∀ (X : Scheme.{u}) (i : Fin (finiteCoefficientDegree ℓ h)),
        finiteCoefficientRationalLeg ℓ X h i ≫ (e₁ X).hom.hom =
          finiteCoefficientRationalSummand ℓ X h (b i)) ∧
      (∀ (X : Scheme.{u}) (i : Fin (finiteCoefficientDegree ℓ h)),
        finiteCoefficientIntegralLeg ℓ X h i ≫ (e₀ X).hom.hom ≫
            padicIntegersToPadicSubfield X ℓ F =
          padicIntegersToPadicSubfield X ℓ E ≫
            finiteCoefficientRationalLeg ℓ X h i ≫ (e₁ X).hom.hom) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (i : Fin (finiteCoefficientDegree ℓ h)),
        (f)^*[AddCommGrpCat.{u + 1}].map
            (finiteCoefficientIntegralLeg ℓ Y h i ≫ (e₀ Y).hom.hom) ≫
              condensedPullbackHom (Profinite.padicIntegersRingObj ℓ F.1) f =
          condensedPullbackHom (Profinite.padicIntegersRingObj ℓ E.1) f ≫
            finiteCoefficientIntegralLeg ℓ X h i ≫ (e₀ X).hom.hom) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (i : Fin (finiteCoefficientDegree ℓ h)),
        (f)^*[AddCommGrpCat.{u + 1}].map
            (finiteCoefficientRationalLeg ℓ Y h i ≫ (e₁ Y).hom.hom) ≫
              condensedPullbackHom (Profinite.continuousMapRingObj F.1) f =
          condensedPullbackHom (Profinite.continuousMapRingObj E.1) f ≫
            finiteCoefficientRationalLeg ℓ X h i ≫ (e₁ X).hom.hom)) ∧
    (∀ X : Scheme.{u},
      PreservesFiniteLimits
          (Mod.extendScalars (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) X)) ∧
        PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))) := by
  sorry

end AlgebraicGeometry.ProEtale
