/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.IntegralModelOpenClosedBasic
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

import Sheaf.Paper.LatticeCoefficientPullbackIso
import Sheaf.Paper.ContinuousModuleLocalization
import Sheaf.Paper.ContinuousExtensionScalarChange
import Sheaf.Paper.ContinuousConstructibleSupported
import Sheaf.AlgebraicGeometry.ClosedImmersionScalarChange

/-!
# Integral models of the open and closed pieces

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 6.8.10 and
Lemma 6.8.13; Stacks Project, Tags 09AA, 09AH, 09BN and 03DI
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces).

The continuous coefficients use the published lattice encoding. `WithAbs` equips the
finite extension with its canonical topology, and `latticeCoefficientIntegers` is its
valuation subring. The four constructions, publicly reexported from the basic module, are explicit
specializations of the published module operations; no module or coefficient ring is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private theorem exact_localization_transport
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D A' D' : C} (f : A ⟶ B) (g : B ⟶ D)
    [Mono f] [Epi g] (h : (ComposableArrows.mk₂ f g).Exact)
    (a : A' ≅ A) (d : D' ≅ D) :
    Mono (a.hom ≫ f) ∧ Epi (g ≫ d.inv) ∧
      (ComposableArrows.mk₂ (a.hom ≫ f) (g ≫ d.inv)).Exact := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  let e : ComposableArrows.mk₂ (a.hom ≫ f) (g ≫ d.inv) ≅
      ComposableArrows.mk₂ f g :=
    ComposableArrows.isoMk₂ a (Iso.refl B) d
      (by change (a.hom ≫ f) ≫ 𝟙 B = a.hom ≫ f; rw [Category.comp_id])
      (by
        change (g ≫ d.inv) ≫ d.hom = 𝟙 B ≫ g
        rw [Category.assoc, d.inv_hom_id, Category.comp_id, Category.id_comp])
  exact ComposableArrows.exact_of_iso e.symm h

private theorem latticeCoefficientMap_pullback_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T S : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
    (a : T →+* S) (ha : Continuous a) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (latticeCoefficientSheafMap Y a ha) ≫ continuousCoefficientInverseImageMap f S =
      continuousCoefficientInverseImageMap f T ≫ latticeCoefficientSheafMap X a ha := by
  unfold continuousCoefficientInverseImageMap
  rw [← (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv_naturality_left_symm,
    ← (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv_naturality_right_symm]
  congr 1


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Integral open and closed pieces are continuous-constructible, commute with
rationalization, and give the canonical localization sequence with the displayed
transported arrows. The coefficient identifications are fixed to be the actual
continuous-function pullback maps. The adjunctions are for the displayed module
functors, rather than for unconstrained replacement functors.
Source: Bhatt--Scholze, Lemma 6.8.13, constructible-filtration assembly;
Stacks Project, Tags 09AA, 09AH, 09BN, 03DI and 0E8I
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces).

Proof:
1. The canonical lattice coefficient pullbacks along both immersions are invertible.
Choose their actual inverses, and use noetherian quasi-compactness for the open immersion.
2. Supported constructibility composes a witnessing finite stratification with the
immersion and adds the complementary locus with the zero local model. Coefficient
pullback compatibility and the open unit or closed counit retain the old local models.
3. Open scalar change follows from uniqueness of left adjoints: scalar restriction and
restriction to the open commute sectionwise. This identifies the actual ordinary changes
of rings, without a flatness hypothesis.
4. Closed scalar change is the coefficient-linear underived projection formula, with
its coefficient square given by naturality of the continuous-function adjuncts.
5. Transport ringed localization to the continuous-coefficient functors through the
explicit open-site equivalence and closed coefficient equivalence. For the specified
alpha and beta, compose the endpoint isomorphisms with j_!(alpha) and i_*(beta).
An isomorphism of three-term sequences with identity middle component gives exactly
the displayed arrows and preserves monicity, epicity and exactness. Empty complementary
loci and zero modules cause no exception. -/
theorem integralModel_open_closed_pieces (X : Scheme.{u}) [IsNoetherian X]
    (_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) :
    ∃ (cU : (Scheme.proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj
        (latticeCoefficientSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))) ≅
          latticeCoefficientSheaf U.left (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
      (cZ : (Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj
        (latticeCoefficientSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))) ≅
          latticeCoefficientSheaf Z (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))),
      cU.hom = continuousCoefficientInverseImageMap U.hom
        (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ∧
      cZ.hom = continuousCoefficientInverseImageMap i
        (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ∧
      ∃ (aj : continuousModuleExtensionByZero U
            (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ⊣
          Scheme.proEtaleRingModulePullback U.hom
            (latticeCoefficientSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
            (latticeCoefficientSheaf U.left
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))) cU)
        (ai : Scheme.proEtaleRingModulePullback i
            (latticeCoefficientSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
            (latticeCoefficientSheaf Z (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
            cZ ⊣ continuousModuleDirectImage i
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))),
        ∀ (MU : SheafOfModules.{u + 1}
            (latticeModuleRing U.left (latticeCoefficientIntegers l E)))
          (MZ : SheafOfModules.{u + 1} (latticeModuleRing Z (latticeCoefficientIntegers l E))),
          @IsContinuousConstructible U.left
            (U.hom.isEmbedding.isInducing.noetherianSpace (α := X)) (latticeCoefficientIntegers l E)
            inferInstance inferInstance inferInstance MU →
          @IsContinuousConstructible Z (i.isEmbedding.isInducing.noetherianSpace (α := X))
            (latticeCoefficientIntegers l E) inferInstance inferInstance inferInstance MZ →
          IsContinuousConstructible X (latticeCoefficientIntegers l E)
            ((continuousModuleExtensionByZero U (latticeCoefficientIntegers l E)).obj MU) ∧
          IsContinuousConstructible X (latticeCoefficientIntegers l E)
            ((continuousModuleDirectImage i (latticeCoefficientIntegers l E)).obj MZ) ∧
          ∃ (eU : integralModelRationalize l E X
                ((continuousModuleExtensionByZero U (latticeCoefficientIntegers l E)).obj MU) ≅
              (continuousModuleExtensionByZero U
                (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
                  (integralModelRationalize l E U.left MU))
            (eZ : integralModelRationalize l E X
                ((continuousModuleDirectImage i (latticeCoefficientIntegers l E)).obj MZ) ≅
              (continuousModuleDirectImage i
                (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
                  (integralModelRationalize l E Z MZ)),
            ∀ (L : SheafOfModules.{u + 1} (latticeModuleRing X
                (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
              (α : integralModelRationalize l E U.left MU ≅ (Scheme.proEtaleRingModulePullback U.hom
                  (latticeCoefficientSheaf X
                    (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
                  (latticeCoefficientSheaf U.left
                    (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))) cU).obj L)
              (β : integralModelRationalize l E Z MZ ≅ (Scheme.proEtaleRingModulePullback i
                  (latticeCoefficientSheaf X
                    (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
                  (latticeCoefficientSheaf Z
                    (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))) cZ).obj L),
              Mono (eU.hom ≫ (continuousModuleExtensionByZero U
                  (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).map α.hom ≫
                    aj.counit.app L) ∧
              Epi (ai.unit.app L ≫ (continuousModuleDirectImage i
                  (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).map β.inv ≫ eZ.inv) ∧
              (ComposableArrows.mk₂
                (eU.hom ≫ (continuousModuleExtensionByZero U
                  (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).map α.hom ≫
                    aj.counit.app L)
                (ai.unit.app L ≫ (continuousModuleDirectImage i
                  (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).map β.inv ≫
                    eZ.inv)).Exact := by
  let K := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  let A := latticeCoefficientIntegers l E
  let := (latticeCoefficientPullback_isIso l E (Y := X) U.hom).2
  let := (latticeCoefficientPullback_isIso l E i).2
  let := (latticeCoefficientPullback_isIso l E i).1
  let cU := asIso (continuousCoefficientInverseImageMap U.hom K)
  let cZ := asIso (continuousCoefficientInverseImageMap i K)
  let cA := asIso (continuousCoefficientInverseImageMap i A)
  have hNoethU : TopologicalSpace.NoetherianSpace U.left :=
    U.hom.isEmbedding.isInducing.noetherianSpace (α := X)
  let : QuasiCompact U.hom :=
    @quasiCompact_of_noetherianSpace_source U.left X hNoethU U.hom
  obtain ⟨aj, ai, hseq⟩ := continuousModule_localization i U hU K cU cZ rfl rfl
  refine ⟨cU, cZ, rfl, rfl, aj, ai, ?_⟩
  intro MU MZ hMU hMZ
  have hc := continuousConstructible_supported A
    (fun Y W _ f _ ↦ (latticeCoefficientPullback_isIso l E f).1) i U hU
  refine ⟨hc.1 MU hMU, hc.2 MZ hMZ, ?_⟩
  obtain ⟨eU⟩ := continuousExtension_scalar_change U A K A.subtype continuous_subtype_val MU
  have hs : (Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).map
        (integralLatticeCoefficientMap X l E) ≫ cZ.hom =
      cA.hom ≫ integralLatticeCoefficientMap Z l E :=
    latticeCoefficientMap_pullback_square i A K A.subtype continuous_subtype_val
  obtain ⟨eZ⟩ := Scheme.closedImmersion_scalar_change i U hU
    (latticeCoefficientSheaf X A) (latticeCoefficientSheaf X K)
    (latticeCoefficientSheaf Z A) (latticeCoefficientSheaf Z K)
    (integralLatticeCoefficientMap X l E) (integralLatticeCoefficientMap Z l E)
    cA cZ hs MZ
  refine ⟨eU, eZ, ?_⟩
  intro L α β
  obtain ⟨hf, hg, hex⟩ := hseq L
  let := hf
  let := hg
  have ht := exact_localization_transport (aj.counit.app L) (ai.unit.app L) hex
    (eU ≪≫ (continuousModuleExtensionByZero U K).mapIso α)
    (eZ ≪≫ (continuousModuleDirectImage i K).mapIso β)
  simpa only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc] using ht

end AlgebraicGeometry.ProEtale
