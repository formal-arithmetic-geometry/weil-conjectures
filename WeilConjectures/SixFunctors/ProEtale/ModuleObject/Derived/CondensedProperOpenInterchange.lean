/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.ClopenLocalization.ProEtaleClopenUnboundedDerivedLocalization
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantStratifiedZariskiLocality
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenBoundaryZero
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchangeIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchangeNormalized
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenPastingData

/-! # Normalized condensed proper/open interchange

Source: Stacks Tag 0F7B, `more-etale.tex`, lemma-shriek-proper-and-open;
latest blueprint det-sf-comp-composition-interchange, proof (1)--(3), with the
agent-formulated ordinary condensed extension and clopen/nonseparated refinement
(blueprint: lem-sf-condensed-proper-open-interchange).

The coefficient abbreviations specialize the existing continuous condensed ring construction
with the discrete quotient topology or the unique extended ell-adic absolute value.
The theorem uses the existing pullback/counit mate normalization in the ordinary
unbounded derived categories, including non-Cartesian compactification squares.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The finite quotient coefficient with its discrete topology, using the recorded
coefficient extension ring and the continuous condensed ring construction.
Source: def-weil-l-adic-coefficient-extension, clause 4, and Stacks Tag 0F7B
(blueprint: lem-sf-condensed-proper-open-interchange). -/
abbrev properOpenFiniteCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n : ℕ) : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing ℓ E n) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ℓ E n) := ⟨rfl⟩
  Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionRing ℓ E n)

/-- The integral coefficient, with the topology induced by the unique extended absolute
value on the finite extension. The ring of integers itself is the recorded construction.
Source: def-weil-l-adic-coefficient-extension, clauses 1--2, and Stacks Tag 0F7B
(blueprint: lem-sf-condensed-proper-open-interchange). -/
abbrev properOpenIntegralCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : NormedField E := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers ℓ E)

/-- The finite extension coefficient with its unique extended ell-adic topology.
Source: def-weil-l-adic-coefficient-extension, clause 1, and Stacks Tag 0F7B
(blueprint: lem-sf-condensed-proper-open-interchange). -/
abbrev properOpenFieldCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : NormedField E := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  Profinite.continuousCoefficientRingObj E

/-- The unique normalized proper/open interchange is natural on the entire unbounded
category and invertible on bounded constructible finite-Tor objects. The compactification
contains the proper morphism r, open j, and equation rj = ip; no density is required.
Source: Stacks Tag 0F7B, with the ordinary condensed extension along latest blueprint
fix-lem-tensor-adjunction Step 2 and det-sf-comp-composition-interchange proof (1)--(3)
(blueprint: lem-sf-condensed-proper-open-interchange).

Proof plan (the eight steps of the node):
1. Form U = W ×_Ybar Y. The lift s = (j,p) is an open immersion. Since p is proper
and U → Y separated, s is proper, hence closed: U is the disjoint union of X and U₀.
2. Normalized open restriction, open base change, and clopen localization give the
natural isomorphism lambda : i* Rr* Jj A ≅ Rp* A. The direct-image mate composed with
lambda inverse is Rp* of the open unit; check the mate by pasting the units and counits.
3. Take the Ji-adjunct of lambda inverse. The invertible source open unit and restriction
mate imply existence and pointwise uniqueness. Naturality follows from the adjunction.
4. Restrict to affine opens V of Ybar. Properness and finite type persist; W_V, U_V,
and X_V are separated over k. The normalized pasting formula identifies the restricted
interchange with that of the pulled-back square via open-restriction isomorphisms.
5. Constructibility restricts by finite-stratification locality. The open tensor formula
and exact fully faithful extension by zero preserve the given Tor interval. Thus
J_sV A_V is bounded constructible finite-Tor on U_V.
6. Apply proper-open-boundary-zero to the Cartesian preimage open U_V in W_V and this
input. It gives zero restriction of RrV* JjV A_V to the reduced closed complement of Y_V.
7. Exact inverse image and cohomology comparison give zero boundary for each cohomology
sheaf. The ringed open-closed exact sequence makes the actual open counit invertible
on cohomology, hence in the unbounded derived category. The factorization in step 3
then makes the normalized interchange invertible on each affine chart.
8. Internal/sectionwise operations transport and ringed pro-etale open-cover conservativity
give global invertibility. Empty schemes, unused clopen components, and zero inputs
are included. No absolute separatedness, density or Cartesian assumption is introduced. -/
theorem condensedProperOpenInterchange
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (_hℓ : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (properOpenFiniteCoefficient ℓ E n)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (properOpenIntegralCoefficient ℓ E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (properOpenFieldCoefficient ℓ E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {X Y Ybar : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Ybar) [IsOpenImmersion i]
    (c : Compactification.BoundaryCompactification (p ≫ i))
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [Ybar.Over (Spec (.of D.k))] [c.obj.obj.Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Ybar ↘ Spec (.of D.k))]
    [QuasiCompact (Ybar ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of D.k))]
    [QuasiCompact (c.obj.obj.Z ↘ Spec (.of D.k))]
    [p.IsOver (Spec (.of D.k))] [i.IsOver (Spec (.of D.k))]
    [c.obj.obj.i.IsOver (Spec (.of D.k))] [c.obj.obj.g.IsOver (Spec (.of D.k))]
    [IsProper p] :
    ∃ δ : (moduleObjectDerivedPushforward Λ p ⋙
        (openImmersionLowerShriek Λ i).mapDerivedCategory) ⟶
      ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⋙
        moduleObjectDerivedPushforward Λ c.obj.obj.g),
      ∀ A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)),
        compositionInterchangeIsNormalized Λ p i c A (δ.app A) ∧
        (∀ m, compositionInterchangeIsNormalized Λ p i c A m → m = δ.app A) ∧
        ((constantModelBoundedConstructible Λ X A ∧
            DerivedCategory.finiteTorAmplitude _ A) → IsIso (δ.app A)) := by
  obtain ⟨data⟩ := condensedProperOpenPastingData Λ ℓ E n (by
    simpa only [properOpenFiniteCoefficient, properOpenIntegralCoefficient,
      properOpenFieldCoefficient, finiteCoefficient, integralCoefficient,
      fieldCoefficient] using _hΛ)
  obtain ⟨δ, hδ⟩ := condensedProperOpenInterchangeNormalized Λ p i c data
  refine ⟨δ, ?_⟩
  intro A
  rcases hδ A with ⟨hδnorm, hδuniq⟩
  refine ⟨hδnorm, hδuniq, ?_⟩
  intro hA
  exact condensedProperOpenInterchangeIso Λ p i c data δ (fun B ↦ (hδ B).1) A hA

end AlgebraicGeometry.ProEtale.CondensedRing
