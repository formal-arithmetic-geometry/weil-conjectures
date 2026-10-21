/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G6
-/
module

public import Sheaf.Paper.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import Sheaf.Paper.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-! # Etale origin of finite discrete constructible finite-Tor internal complexes

Source: blueprint main-20261015, finite compactness proof, coefficient identification
and finite-Tor comparison steps (blueprint: lem-finite-discrete-ctf-origin).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- An internal constructible finite-Tor complex over finite discrete coefficients has
an ordinary etale constructible finite-Tor antecedent under the specified comparison.

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-ctf-finite-compact/sk-prop-ctf-finite-compact-proetale.proof.md`, first paragraph;
`sec-proetale-coefficients/sk-cor-pe-finite-tor-comparison/`
`sk-cor-pe-finite-tor-comparison-noetherian.proof.md`, The equivalence
(blueprint: lem-finite-discrete-ctf-origin).

Proof. Identify the sheafified constant coefficient ring with the continuous condensed
ring using the specified ring isomorphism and its pullback to X. Sectionwise scalar
multiplication identifies ordinary module sheaves with internal modules. This exact
equivalence preserves tensor products and constant finite modules, hence bounded
constructibility and the Tor interval. On the Noetherian scheme, constructible
comparison gives an etale antecedent for the resulting bounded constructible
pro-etale complex. The comparison tensor isomorphism reflects its Tor interval:
test against inverse images of etale modules and reflect vanishing by full faithfulness.
Convert constructible stalks to finite module values; on a finite ring these conventions
agree. Widen the interval to its ordered hull if necessary. This also covers the empty
scheme and zero ring, with the zero complex as antecedent. -/
theorem finiteDiscreteCtfOrigin
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
        Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]
    (K : DerivedCategory (pulledBackModuleObjects
      (Profinite.continuousMapRingObj A) X))
    (hK : (constantModelBoundedConstructible (Profinite.continuousMapRingObj A) X ⊓
      fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M) K) :
    ∃ L : Etale.DerivedCategoryModule (ULift.{u + 1} A) X,
      Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) X L ∧
      (∃ a b : ℤ, a ≤ b ∧
        Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) X a b L) ∧
      Nonempty (((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory ⋙
        (finiteComparisonRealization A X eR).mapDerivedCategory).obj L ≅ K) := by
  classical
  let R := (finiteComparisonRealization A X eR).mapDerivedCategory
  let : (finiteComparisonRealization A X eR).IsEquivalence :=
    (finiteComparisonRealization_exact A X eR).1
  let P := R.objPreimage K
  let eP : R.obj P ≅ K := R.objObjPreimageIso K
  let := (constantModelConstructibleFiniteTor_wellDefined
    (Profinite.continuousMapRingObj A) X).2.1
  have hP : (constantModelBoundedConstructible (Profinite.continuousMapRingObj A) X ⊓
      fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M) (R.obj P) :=
    ObjectProperty.prop_of_iso _ eP.symm hK
  obtain ⟨L, hL, ⟨eL⟩⟩ := (finiteComparisonGenerators_identification A eR X).2 P hP
  obtain ⟨a, b, htor⟩ := hL.2
  refine ⟨L, hL.1, ⟨min a b, max a b, min_le_max, ?_⟩, ⟨R.mapIso eL ≪≫ eP⟩⟩
  apply Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
  exact _root_.DerivedCategory.torAmplitudeIn.mono
    (min_le_left a b) (le_max_right a b) htor

end AlgebraicGeometry.ProEtale
