/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Paper.IntegralModelsEmbedded
import Sheaf.AlgebraicGeometry.IntegralModelsStacks
import all Sheaf.Paper.IntegralCoefficientExtComparison
import all Sheaf.Paper.IntegralConstantModelHeartClosure
import Sheaf.AlgebraicGeometry.IntegralConstantModelRealization
import Sheaf.Paper.ConstantModelStratificationTransport
import Sheaf.Paper.EmbeddedIntegralCompletenessTransport
import Sheaf.Paper.EmbeddedIntegralResidueTransport

/-! # Stacks criterion for embedded coefficients

Source: the integral-models Stacks criterion, Stacks Project Tag 09C1 (blueprint:
lem-sfb-embedded-integral-stacks-criterion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  IntegralModelsStacks.smallDerivedObject IntegralModelsStacks.smallModules
  IntegralModelsStacks.smallMap

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- The Stacks integral constructibility criterion in the independent-universe embedded
coefficient presentation.

Source: integral-models-stacks detail of the integral-models unit; Stacks Project Tag 09C1
(blueprint: lem-sfb-embedded-integral-stacks-criterion).

Proof: apply integral_models_stacks to the finite extension ULift E in the scheme
universe. The spectral-norm identification with the original embedded norm identifies
its integers with ULift of the embedded integers. The uniformizer hypothesis identifies
the chosen principal ideal with the maximal ideal, hence identifies every power quotient
with the corresponding coefficientExtensionRing. Apply constant sheafification and the
continuous-function functor to these ring isomorphisms. They commute with the canonical
constant-to-continuous map and the first residue quotient. Exact inverse image to X,
section-module equivalence and equivalent-small-site transport preserve these squares.
Restriction along the resulting coefficient isomorphisms gives equivalences of derived
categories; the scalar squares identify the restriction and derived reduction functors.
These equivalences identify finite constant models and their constructible
stratifications, homology and bounds, relative derived tensor and finite Tor amplitude.
The same first-quotient square identifies the local kernel-ideal completeness predicates.
Transporting the pointwise iff in integral_models_stacks gives the displayed iff for
arbitrary K, without changing either ambient category or imposing a universe equality.
-/
theorem integralModelsEmbeddedStacksCriterion
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X] :
    ∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (integralCoefficientObject X ℓ E)),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K ↔
        IntegralModelsEmbedded.stacksConstructible ℓ E π X
          ((IntegralModelsEmbedded.restriction ℓ E X).obj K) := by
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.val)).symm.finiteDimensional
  let e₀ := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (integerRingSheafIso.{u} ℓ E)
  have : IsMonHom e₀.hom := Sheaf.isMonHom_sheafCompose_map _
    (integerRingSheafIso.{u} ℓ E).hom
  let e := Mon.mkIso' e₀ ≪≫ IntegralConstantModel.pointComparison ℓ (ULift.{u} E.val)
  let φ := e.inv.hom
  have : IsMonHom φ := inferInstance
  have : IsIso φ := by
    change IsIso ((Mon.forget _).map e.inv)
    infer_instance
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    ((upperStarFromPoint X).map φ)
  intro K
  have hc : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K ↔
      constantModelBoundedConstructible (IntegralModelsStacks.integersObj ℓ (ULift.{u} E.val))
        X (F.mapDerivedCategory.obj K) := by
    apply and_congr
    · exact ⟨F.bounded_mapDerivedCategory_obj, F.bounded_of_bounded_mapDerivedCategory_obj⟩
    · apply forall_congr'
      intro q
      let ε := (F.mapDerivedCategoryHomologyFunctorIso q).app K
      exact (constantModel_comap_iff φ X _).symm.trans
        ⟨fun h ↦ constantModelConstructible_transport _ ε h,
          fun h ↦ constantModelConstructible_transport _ ε.symm h⟩
  have hs := (IntegralModelsStacks.integral_models_stacks ℓ (ULift.{u} E.val) X).1
    (F.mapDerivedCategory.obj K)
  refine (hc.trans hs).trans ?_
  exact (and_congr
    (embeddedIntegralCompletenessTransport ℓ E π hπ e X K)
    (embeddedIntegralResidueTransport ℓ E π hπ e X K)).symm

end AlgebraicGeometry.ProEtale
