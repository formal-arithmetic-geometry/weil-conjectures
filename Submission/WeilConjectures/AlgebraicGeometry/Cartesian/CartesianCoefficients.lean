/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import Submission.WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Cartesian coefficient sheaves

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-sfb-cartesian-coefficients/_section.md`, assertions (1), (2), and the final paragraph
(blueprint: sk-prop-sfb-cartesian-coefficients).

The assertions below use the published coefficient comparison and module pullback.
The inverse-image lift and its comparison with extension of scalars are actual constructions.
The signed lines are the recorded Tate twists, including their sectionwise module encoding.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}}

/-- The inverse-image lift with action transported through the inverse of alpha_f.
Its underlying objects and arrows are literally those of abelian inverse image.
Source: blueprint final paragraph (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def cartesianCoefficientLift
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : X ⟶ Y) :=
  (upperStar AddCommGrpCat.{u + 1} f).mapMod (condensedRingObj Λ Y) ⋙
    Mod.comap (inv (condensedPullbackHom Λ f))

/-- The canonical comparison: extension along alpha is restriction along its inverse.
This is the uniqueness-of-left-adjoints comparison of the published scalar adjunctions.
Source: blueprint final paragraph (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def cartesianCoefficientPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : X ⟶ Y) :
    CondensedRing.upperStar Λ f ≅ cartesianCoefficientLift Λ f :=
  Functor.isoWhiskerLeft
    ((upperStar AddCommGrpCat.{u + 1} f).mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))

/-- The untwisted assertions for one specified condensed coefficient ring.
The first conjunct concerns the canonical ring-object morphism, whose ring structure
is recorded by isMonHom_condensedPullbackHom; the lift comparison is the actual
cartesianCoefficientPullbackIso above. The last equality retains the whole underlying
functor, on objects and morphisms.
Source: blueprint (1) and final paragraph (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianCoefficientProperty
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : X ⟶ Y) : Prop :=
  IsIso (condensedPullbackHom Λ f) ∧
    PreservesFiniteLimits (CondensedRing.upperStar Λ f) ∧
    PreservesFiniteColimits (CondensedRing.upperStar Λ f) ∧
    cartesianCoefficientLift Λ f ⋙ Mod.forget (condensedRingObj Λ X) =
      Mod.forget (condensedRingObj Λ Y) ⋙ upperStar AddCommGrpCat.{u + 1} f

/-- Finite coefficients have the discrete topology, fixed here rather than supplied
as an extra hypothesis. This is the recorded continuous-function condensed ring.
Source: blueprint coefficient list (blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianFinitePointRing (A : Type u) [CommRing A] :
    Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  Profinite.continuousCoefficientRingObj A

/-- Exactly the admissible untwisted coefficient list. Z_ell and Q_ell are included
explicitly, in addition to all finite intermediate extensions and their integer rings.
Qbar is the finite-subextension-valued condensed ring, not all continuous functions.
Source: blueprint (1) (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianUntwistedAssertions (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y) : Prop :=
  (∀ (A : Type u) [CommRing A] [Finite A],
    CartesianCoefficientProperty (cartesianFinitePointRing A) f) ∧
  CartesianCoefficientProperty (Profinite.continuousMapRingObj (PadicInt ℓ)) f ∧
  CartesianCoefficientProperty (Profinite.continuousMapRingObj (Padic ℓ)) f ∧
  (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
    CartesianCoefficientProperty (Profinite.padicIntegersRingObj ℓ E.1) f ∧
    CartesianCoefficientProperty (Profinite.continuousMapRingObj E.1) f) ∧
  CartesianCoefficientProperty (Profinite.padicAlgClRingObj ℓ) f

/-- The normalized finite signed comparisons over the recorded constant coefficient map.
The first-line formula fixes the map on root tensors; the second clause retains all
Kummer identifications. Every signed comparison includes zero, tensor and evaluation
normalizations, and is an isomorphism of coefficient modules in every degree.
Source: blueprint finite coefficients and powers and duals paragraphs
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
@[irreducible] def CartesianFiniteTwistAssertions (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] : Prop :=
  ∀ (A : Type u) [CommRing A] [Finite A],
    ∃ β : ∀ (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* (ULift.{u + 1} A)),
      SpSignedComparison f (Scheme.tateFiniteCoefficient Y (ULift.{u + 1} A))
        (Scheme.tateFiniteCoefficient X (ULift.{u + 1} A))
        (StrictTower.constantRingIso (ULift.{u + 1} A) f)
        (Scheme.tateFiniteLine Y ℓ (ULift.{u + 1} A) r a)
        (Scheme.tateFiniteLine X ℓ (ULift.{u + 1} A) r a),
      (∀ (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* (ULift.{u + 1} A)) (V : Y.ProEt)
        (b : (Scheme.tateFiniteCoefficient Y (ULift.{u + 1} A)).obj.obj (op V))
        (z : (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (r + 1))).obj.obj (op V)),
        (((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _)
          ((β r a).signed 1).hom).val.app (op V)
            (Scheme.tateFiniteTensor Y ℓ (ULift.{u + 1} A) r a V b z) =
          Scheme.tateFiniteTensor X ℓ (ULift.{u + 1} A) r a ((Scheme.proEtaleBaseChange f).obj V)
            ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
              (CommRingCat.of (ULift.{u + 1} A))).hom.app (op V) b)
            ((Scheme.proEtaleRootsOfUnityDirectImageMap f (ℓ ^ (r + 1))).hom.app
              (op V) z)) ∧
      (∀ (r n : ℕ) (h : r ≤ n) (a : ZMod (ℓ ^ (r + 1)) →+* (ULift.{u + 1} A)),
        (Scheme.proEtaleRingModulePullback f _ _ _).map
          (spFiniteKummer Y ℓ (ULift.{u + 1} A) r n h a) ≫ ((β r a).signed 1).hom =
        ((β n (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ h))
          (ZMod (ℓ ^ (r + 1)))))).signed 1).hom ≫ spFiniteKummer X ℓ (ULift.{u + 1} A) r n h a)

/-- The normalized integral, rational and algebraic-closure signed comparisons.
Integral maps are fixed by all finite projections through spIntegralComparison;
rational maps by the displayed scalar-extension equation, and Qbar by its finite-field
coprojections. SpInternalCartesian retains precisely alpha_f and the sectionwise
signed coefficient-module comparisons, together with their tensor and dual equations.
Source: blueprint integral, rational, colimit, powers and duals paragraphs
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
structure CartesianAdicComparison (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] where
  rational : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
        (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (spRationalTwist.{u} Y ℓ E).X ⟶ (spRationalTwist.{u} X ℓ E).X
  qbar : (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (spQbarTwist.{u} Y ℓ).X ⟶ (spQbarTwist.{u} X ℓ).X
  rational_scalar : (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist.{u} Y ℓ E)) ≫
        rational E =
      Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f)
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) Y)
        (spIntegralTwist.{u} Y ℓ E).X ≫
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ
        spIntegralComparison f ℓ E) ≫
      Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist.{u} X ℓ E))
  qbar_coprojection : (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (colimit.ι (spRationalTwistDiagram Y ℓ) E) ≫ qbar =
        rational E ≫ colimit.ι (spRationalTwistDiagram X ℓ) E)
  integral_rational_cartesian : (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SpInternalCartesian f (Profinite.padicIntegersRingObj.{u} ℓ E.1)
        (spIntegralTwist.{u} Y ℓ E) (spIntegralTwist.{u} X ℓ E) (spIntegralComparison f ℓ E) ∧
      SpInternalCartesian f (Profinite.continuousMapRingObj.{u} E.1)
        (spRationalTwist.{u} Y ℓ E) (spRationalTwist.{u} X ℓ E) (rational E))
  qbar_cartesian : SpInternalCartesian f (Profinite.padicAlgClRingObj.{u} ℓ)
      (spQbarTwist.{u} Y ℓ) (spQbarTwist.{u} X ℓ) qbar
  integral_inclusion : (∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (spIntegralTwistMap Y ℓ h) ≫ spIntegralComparison f ℓ F =
        spIntegralComparison f ℓ E ≫ spIntegralTwistMap X ℓ h)
  rational_inclusion : (∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (spRationalTwistMap Y ℓ h) ≫ rational F =
        rational E ≫ spRationalTwistMap X ℓ h)
  root_transition : (∀ (n m : ℕ) (h : n ≤ m),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
        (Scheme.proEtaleRootsOfUnityTransition Y (ℓ ^ n) (ℓ ^ m)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ h)) ≫ Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ n) =
      Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ m) ≫
        Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ n) (ℓ ^ m)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ h))

/-- Existence of the normalized adic signed comparison data.
Source: blueprint twists (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianAdicTwistAssertions (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] : Prop :=
  Nonempty (CartesianAdicComparison ℓ f)

/-- The canonical normalized comparisons of roots and every signed coefficient twist.
The finite comparisons cover every finite coefficient ring annihilated by an ell power:
its unital quotient map is the input a. The adic comparisons use the recorded internal
and sectionwise encodings and their same coefficient map alpha_f.
Source: blueprint (1), twists (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianTwistAssertions (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y) : Prop :=
  ∀ (hX : ∀ x : X, Invertible (ℓ : X.residueField x))
    (hY : ∀ y : Y, Invertible (ℓ : Y.residueField y)),
    letI := hX
    letI := hY
    (∀ n : ℕ, IsIso (Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ n))) ∧
    CartesianFiniteTwistAssertions ℓ f ∧ CartesianAdicTwistAssertions ℓ f

/-- Finite-free means isomorphic to a finite sum of copies of the regular module.
Both scalar restrictions are the coefficient maps induced by the given inclusion.
Source: blueprint (2) (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianFiniteFreeAssertions (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) : Prop :=
  ∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
    (∃ n : ℕ, Nonempty
      (Mod.finiteFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) n ≅
        (Mod.comap (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) X)).obj
          (Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) X)))) ∧
    ∃ n : ℕ, Nonempty
      (Mod.finiteFree (padicSubfieldRingObj X ℓ E) n ≅
        (Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
          (Mod.regular (padicSubfieldRingObj X ℓ F)))

private theorem cartesianCoefficientProperty_proof
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : X ⟶ Y) :
    CartesianCoefficientProperty Λ f := by
  exact ⟨inferInstance, inferInstance, inferInstance, rfl⟩

private theorem cartesianFiniteFreeAssertions_proof (ℓ : ℕ) [Fact ℓ.Prime] :
    CartesianFiniteFreeAssertions ℓ X := by
  intro E F h
  obtain ⟨⟨b⟩, hb, _⟩ := cartesianCoefficients_finiteFree ℓ h
  obtain ⟨e₀, e₁, _⟩ := hb b
  exact ⟨⟨_, ⟨e₀ X⟩⟩, ⟨_, ⟨e₁ X⟩⟩⟩

end AlgebraicGeometry.ProEtale
