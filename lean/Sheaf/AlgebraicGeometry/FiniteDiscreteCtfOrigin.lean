/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G6
-/
module

public import Sheaf.Paper.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization
import Sheaf.Paper.ConstantModelTorAmplitude
import all Sheaf.Paper.ProEtaleConstructibleOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-! # Etale origin of finite discrete constructible finite-Tor internal complexes

Source: blueprint main-20261015, finite compactness proof, coefficient identification
and finite-Tor comparison steps (blueprint: lem-finite-discrete-ctf-origin).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

private theorem fixedCtfOrigin (X : Scheme.{u}) [IsNoetherian X]
    (A : Type) [CommRing A] [Finite A]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (hK : (_root_.DerivedCategory.TStructure.t.bounded K ∧
      ∀ q : ℤ, IsConstructible (ULift.{u + 1} A)
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      _root_.DerivedCategory.finiteTorAmplitude _ K) :
    ∃ L : Etale.DerivedCategoryModule (ULift.{u + 1} A) X,
      Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) X L ∧
      (∃ a b : ℤ, a ≤ b ∧
        Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) X a b L) ∧
      Nonempty
        (((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory).obj L
          ≅ K) := by
  classical
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1.1
  have hz (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K) := by
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff K a).mp ha q hq
    · exact (_root_.DerivedCategory.isLE_iff K b).mp hb q hq
  obtain ⟨L, hL, ⟨eL⟩⟩ := fixedDerivedOrigin X (ULift.{u + 1} A) K hK.1.2 a b hz
  obtain ⟨c, d, htor⟩ := hK.2
  have htor' := (_root_.DerivedCategory.torAmplitudeIn _ c d).prop_of_iso eL.symm htor
  have htL := ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory
    (ULift.{u + 1} A) htor'
  refine ⟨L, hL, ⟨min c d, max c d, le_trans (min_le_left _ _) (le_max_left _ _), ?_⟩,
    ⟨eL⟩⟩
  have ht := htL.mono (min_le_left c d) (le_max_right c d)
  intro N q hq
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff _ _).mp (ht N).1 q hq
  · exact (_root_.DerivedCategory.isLE_iff _ _).mp (ht N).2 q hq

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
  obtain ⟨L, hL, htL, ⟨eL⟩⟩ := fixedCtfOrigin X A P
    (finiteDiscreteCtfRealization X A eR P hP)
  exact ⟨L, hL, htL, ⟨R.mapIso eL ≪≫ eP⟩⟩

end AlgebraicGeometry.ProEtale
