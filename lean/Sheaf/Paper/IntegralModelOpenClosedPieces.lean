/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.CategoryTheory.RingedSliceExtensionTensor

/-!
# Integral models of the open and closed pieces

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 6.8.10 and
Lemma 6.8.13; Stacks Project, Tags 09AA, 09AH, 09BN and 03DI
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces).

The continuous coefficients use the published lattice encoding. `WithAbs` equips the
finite extension with its canonical topology, and `latticeCoefficientIntegers` is its
valuation subring. All four constructions below are explicit specializations of the
published module operations; no module, coefficient ring or comparison is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Regard a module on the open scheme as a module on the slice site. The concrete
site equivalence retains the underlying schemes and maps, so the coefficient map is
sectionwise the identity on continuous functions. Only the site presentation changes.
Source: Stacks Project, Tags 09BN and 00XZ, and the localization used in Tag 03DI
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces). -/
def openSliceModules {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing U.left T) ⥤
      SheafOfModules.{u + 1} ((latticeModuleRing X T).over U) := by
  letI := Scheme.ProEt.sliceDense X U
  letI : (Scheme.ProEt.sliceEquiv X U).functor.IsContinuous
      ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology U.left) := inferInstance
  exact SheafOfModules.pushforward (F := (Scheme.ProEt.sliceEquiv X U).functor)
    (J := (Scheme.ProEt.topology X).over U) (K := Scheme.ProEt.topology U.left)
    (S := (latticeModuleRing X T).over U) (R := latticeModuleRing U.left T)
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩

/-- Direct image with the continuous coefficient action. First restrict scalars along
the canonical coefficient inverse-image map, then apply the published ringed direct
image. Its action is through the adjoint continuous-function pullback map.
Source: Stacks Project, Tags 09AA and 03D6; Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces). -/
def continuousModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing X T) ⥤
      SheafOfModules.{u + 1} (latticeModuleRing Y T) :=
  SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (continuousCoefficientInverseImageMap f T)) ⋙
    Scheme.proEtaleRingedDirectImage f (latticeCoefficientSheaf Y T)

/-- Extension by zero with continuous coefficients: use the concrete slice-site
transport, followed by the published direct-sum presheaf extension and sheafification.
Source: Stacks Project, Tags 03DI and 09BN
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces). -/
def continuousModuleExtensionByZero {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :=
  openSliceModules U T ⋙ Scheme.proEtaleRingedExtensionByZero U (latticeCoefficientSheaf X T)

/-- Ordinary rationalization `E_X ⊗_{A_X} M`, as the published sheafified
sectionwise change of rings along the continuous integral inclusion.
Source: Bhatt--Scholze, Lemma 6.8.13; Stacks Project, Tag 03EK
(blueprint: lem-weil-pbc-integral-model-open-closed-pieces). -/
def integralModelRationalize (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (M : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E))) :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1} (integralLatticeCoefficientMap X l E) M

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

Proof following the node:
1. Noetherian closed subsets have minimal elements, hence descending chains stop
(lem-weil-pbc-noetherian-scheme-closed-subsets-minimal). Every subset is quasi-compact
(lem-sfb-noetherian-space-compact-subsets). Apply this to the inverse images of affine
opens to obtain quasi-compactness of the complementary open immersion.
2. Take the finite stratification for MU from def-weil-pbc-continuous-constructible-module.
Compose its strata with the open immersion and append Z. The ringed open/closed lemma
(lem-weil-pbc-proetale-ringed-open-closed) identifies the old restrictions with those
of MU and the restriction to Z with zero. Composition of inverse images and coefficient
restriction (lem-pur-proetale-inverse-image-tensor-comparison and
lem-weil-pbc-continuous-coefficients-immersion-restriction) preserve the old local models.
The new stratum has the finitely presented zero module as its local model.
3. Similarly compose an adapted stratification for MZ with i and append U.
The closed counit identifies restrictions on the old strata, and open restriction is
zero. Keep the original covering families and finitely presented modules, with zero
on U. These finite partitions are def-constructible-stratification.
4. Identify the open site with the slice
(lem-weil-proetale-weakly-etale-localization). Apply
lem-weil-pbc-ringed-slice-extension-tensor with ambient module E_X and use tensor
symmetry and coefficient restriction. The open counit on the resulting supported
module is invertible by the triangle identities. Its inverse gives the comparison,
which is the identity after open restriction. On pure tensors the counit preserves
multiplication on the E factor, hence the comparison is E_X-linear.
5. Apply lem-weil-pbc-proetale-closed-underived-projection with R=A_X and F=B=E_X.
Tensor symmetry and the coefficient restriction identifications give the closed
comparison, with its E_X action. The canonical projection restricts to the identity
under the closed counit. This is ordinary tensor; no derived tensor or flatness is used.
6. Use the E_X-coefficient localization sequence from the ringed open/closed lemma.
For the specified alpha and beta, transport its counit arrow by eU and j_!(alpha),
and its unit arrow by i_*(beta inverse) and eZ inverse. These are exactly the two
morphisms written below. Transport by these isomorphisms preserves monicity,
epicity and exactness. Empty complementary loci and zero modules cause no exception. -/
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
  sorry

end AlgebraicGeometry.ProEtale
