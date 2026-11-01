/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarData
public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicReindexingData
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarOrdinary
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarCharts

/-! # Balanced derived scalar reindexing before completion

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-balanced-scalar)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.AdicQbarRealization.completedScalarSheafReindex
  WeilConjectures.AdicQbarRealization.nativeScalarSheafAssociator
  WeilConjectures.AdicQbarRealization.completedScalarReindex
  WeilConjectures.AdicQbarRealization.scalarExactModel
  WeilConjectures.AdicQbarRealization.completedReindexModel
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.completedCoefficientMap
  WeilConjectures.LocallyFiniteAdicRealization.ringSheaf
  WeilConjectures.podCompletedDerivedInverseImage
  AlgebraicGeometry.Scheme.pbcReductionNormalization
  WeilConjectures.AdicQbarRealization.derivedPull

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

private theorem map_hom_inv {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} (e : A ≅ B) : F.map e.hom ≫ F.map e.inv = 𝟙 _ := by
  rw [← F.map_comp, e.hom_inv_id, F.map_id]

set_option maxHeartbeats 800000 in
-- Large coefficient transports need additional elaborator steps, within the time limit.
/-- The two normalized derived balanced tensor maps commute with ordinary scalar
extension on every ambient complex, before any completion or constructibility.
Source: BS Proposition 6.8.14 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-reindex-balanced-scalar).

Proof in words: choose a flat-term K-flat representative of K. Expand the
representative equations of the two IntegralReindex records. The derived counits
identify their components with the degreewise balance maps. The normalized scalar
model and the defining two scalar associators identify the remaining cochain maps
with successive ordinary tensor extension. On a pure section a tensor (b tensor x),
the sections equations of the two integral reindexings and the coefficient_scalar
equations for R and S identify both routes with the reindexed product ab tensor x.
The functions equation of B fixes the coefficient reindexing. Tensor balancing and
sheafification extend this to all sections, and cochain extensionality gives the
same complex map. The derived representative equations and universal scalar
counits descend it through the good-complex localization. Naturality transports
through the representative isomorphism to arbitrary K. No completion, complete
unit cancellation, common-stage functor or realization integral comparison occurs
in this argument. Identity embeddings and zero objects use the same tensor units. -/
theorem integralReindex_balanced_scalar (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (IE : IntegralReindex l X g B E) (IL : IntegralReindex l X g B L)
    (K : DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y)) :
    let i := coefficientInclusion l (PadicAlgCl l) E L h
    let C := Coefficient.{u} l (PadicAlgCl l)
    let aX := pbcReductionNormalization (completedCoefficientMap l (C E) (C L) i X)
      (coefficientMap l X R L) (coefficientMap l X R E) (R.coefficient_scalar E L h)
    let aY := pbcReductionNormalization (completedCoefficientMap l (C E) (C L) i Y)
      (coefficientMap l Y S L) (coefficientMap l Y S E) (S.coefficient_scalar E L h)
    (aX ((podCompletedDerivedInverseImage l (C E) g).obj K)).inv ≫
      (pbcDerivedExtend (coefficientMap l X R L)).map
        ((completedScalarReindex l (C E) (C L) i g).hom.app K) ≫
      IL.derived.inv.app ((completedDerivedScalarExtension l (C E) (C L) i Y).obj K) =
    IE.derived.inv.app K ≫ (derivedPull l X g B).map (aY K).inv  := by
  dsimp only
  let charts := Classical.choice
    (integralReindex_scalar_charts l g R S B E L h IE.balance IL.balance
      IE.derived IL.derived IE.representative IL.representative K)
  refine ScalarComputationCharts.paste_complex (.up ℤ) DerivedCategory.Q charts ?_ ?_ ?_
  · exact map_hom_inv (derivedPull l X g B)
      (pbcReductionNormalization
        (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L)
          (coefficientInclusion l (PadicAlgCl l) E L h) Y)
        (coefficientMap l Y S L) (coefficientMap l Y S E)
        (S.coefficient_scalar E L h) K)
  · intro n
    exact integralReindex_scalar_ordinary l g R S B E L h IE IL (charts.P.X n)

end WeilConjectures.AdicQbarRealization
