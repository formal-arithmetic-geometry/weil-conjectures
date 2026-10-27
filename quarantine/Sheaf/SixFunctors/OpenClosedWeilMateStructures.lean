/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.SixFunctors.OpenClosedWeilMateData
import Sheaf.SixFunctors.OpenClosedWeilMateFinite
import Sheaf.SixFunctors.OpenClosedWeilMateIntegral
import Sheaf.SixFunctors.OpenClosedWeilMateCoefficient
import Sheaf.SixFunctors.OpenClosedWeilMateDescent

/-! # Proof of the open and closed Frobenius mate assertions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe uX vX uU vU uZ vZ uX' vX' uU' vU' uZ' vZ' u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem openClosedMateAssertions_of_isIso
    {X : Type uX} [Category.{vX} X]
    {U : Type uU} [Category.{vU} U]
    {Z : Type uZ} [Category.{vZ} Z]
    (jL : U ⥤ X) (jR : X ⥤ U) (iL : X ⥤ Z) (iR : Z ⥤ X)
    (adjJ : jL ⊣ jR) (adjI : iL ⊣ iR)
    (FX : X ⥤ X) (FU : U ⥤ U) (FZ : Z ⥤ Z)
    (b : jR ⋙ FU ≅ FX ⋙ jR) (d : iL ⋙ FZ ≅ FX ⋙ iL)
    (hAlpha : IsIso (openClosedAlpha adjJ b)) (hC : IsIso (openClosedC adjI d)) :
    OpenClosedWeilMateAssertions jL jR iL iR adjJ adjI FX FU FZ b d := by
  let alpha := ((mateEquiv adjJ adjJ).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans
  let c := (mateEquiv adjI adjI (TwoSquare.mk _ _ _ _ d.inv)).natTrans
  have : IsIso alpha := hAlpha
  have : IsIso c := hC
  let a := asIso alpha
  let ci := asIso c
  have ha (K : X) : FX.map (adjJ.counit.app K) =
      a.inv.app (jR.obj K) ≫ jL.map (b.hom.app K) ≫ adjJ.counit.app (FX.obj K) := by
    have h := mateEquiv_counit_symm adjJ adjJ (TwoSquare.mk _ _ _ _ b.hom) K
    change jL.map (b.hom.app K) ≫ adjJ.counit.app (FX.obj K) =
      a.hom.app (jR.obj K) ≫ FX.map (adjJ.counit.app K) at h
    rw [h, ← Category.assoc, a.inv_hom_id_app, Category.id_comp]
  have hc (K : X) : FX.map (adjI.unit.app K) ≫ ci.hom.app (iL.obj K) ≫
      iR.map (d.hom.app K) = adjI.unit.app (FX.obj K) := by
    have h := unit_mateEquiv adjI adjI (TwoSquare.mk _ _ _ _ d.inv) K
    change FX.map (adjI.unit.app K) ≫ ci.hom.app (iL.obj K) =
      adjI.unit.app (FX.obj K) ≫ iR.map (d.inv.app K) at h
    rw [← Category.assoc, h, Category.assoc, ← iR.map_comp,
      d.inv_hom_id_app]
    change adjI.unit.app (FX.obj K) ≫ iR.map (𝟙 _) = _
    rw [iR.map_id]
    exact Category.comp_id (adjI.unit.app (FX.obj K))
  refine ⟨a, ci, rfl, rfl, ?_, ?_, ha, hc, ?_⟩
  · intro N
    simp [a, alpha]
  · intro M
    simp [ci, c]
  · intro K theta
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · have hn := adjJ.counit.naturality theta.hom
      change jL.map (jR.map theta.hom) ≫ adjJ.counit.app K =
        adjJ.counit.app (FX.obj K) ≫ theta.hom at hn
      rw [Category.assoc, Category.assoc, hn, ha K]
      simp only [Category.assoc]
    · have hn := adjI.unit.naturality theta.hom
      change theta.hom ≫ adjI.unit.app K =
        adjI.unit.app (FX.obj K) ≫ iR.map (iL.map theta.hom) at hn
      rw [hn, ← hc K]
      simp only [Category.assoc]


attribute [local irreducible] sfWeilPrimeInvertible rationalDerivedPullback
  commonStageDerivedPullback fieldWeilPull fieldWeilOpen fieldWeilProper zlPull
  zlCommonStageOpenShriek zlCommonStageProperPush
  fieldWeilOpenAdj fieldWeilProperAdj zlCommonStageOpenAdjunction
  zlCommonStageProperAdjunction sfWeilFrobeniusPullback
  sfCommonStageWeilFrobeniusPullback
  sfFiniteOpenClosedWeilMateAssertions sfFinitePresentationOpenClosedWeilMateAssertions
  sfIntegralOpenClosedWeilMateAssertions sfCoefficientOpenClosedWeilMateAssertions
  sfCompletionOpenClosedWeilMateAssertions sfRationalizationOpenClosedWeilMateAssertions
  sfRationalScalarOpenClosedWeilMateAssertions sfCommonStageOpenClosedWeilMateAssertions
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit Frobenius mates and the first two Weil squares, at every coefficient
stage, for the actual open and closed adjunctions.
Source: main-20261015, prop-sf-open-closed-triangle-all-stages.proof.md,
Weil-structures paragraph (blueprint: lem-sf-open-closed-weil-mate-structures).

Proof plan:
1. Geometric Frobenius and its arithmetic inverse give scheme automorphisms on X,U,Z.
   Their pullbacks are equivalences by lem-sf-automorphism-constructible-stage-equivalence.
   The two commuting squares give the fixed pullback-composition isomorphisms b and d.
2. Apply def-weil-pbc-adjunction-mate inversely to b for j_! ⊣ j*; expanding its three
   factors gives alpha. Apply it to d inverse for i* ⊣ i_*; expansion gives c.
3. lem-stage3-inverse-mate-equivalences and lem-weil-mate-iso-along-equivalences give
   invertibility of these particular transformations. Define a as alpha inverse.
4. lem-amb-mate-unit-counit and lem-pur-mate-unit-compatibility, followed by cancellation
   of alpha and d, give the two normalized equations.
5. Use lem-sf-immersion-completed-pullback-comparison and lem-sf-open-roos-unit-adjunction
   to retain the ordinary units on complete objects. lem-sf-integral-open-reduction-comparison
   and prop-weil-pbc-direct-image-limits identify the prescribed integral functors with
   these restrictions. The completion clause pins each comparison to the actual
   strict-tower unit followed by the normalized gamma inverse; its fixed mates
   identify the ordinary units, counits and alpha/c with those on the tower category.
   Its b/d equations identify the ordinary and zlIntegralPullComp Frobenius squares.
6. lem-fix-operation-reduction preserves each of the three mate factors, including all
   quotient transitions. Finite-to-finite reduction is used only on its finite-Tor domain.
   prop-weil-pbc-rational-transport tensors each factor with one; prop-weil-pbc-descent-functors
   descends the resulting compatible words through common finite coefficient stages.
7. Compose j_!j*(theta), j_!(b), a, and respectively i_*i*(theta), i_*(d), c.
   Every factor is invertible, so these are the stated outer Weil structures.
8. Naturality of the open counit and the closed unit, followed by the normalized equations,
   gives exactly the two required squares. No connecting arrow or triangulated Weil
   category enters the argument. -/
theorem sf_openClosed_weil_mate_structures
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (_ιE : E →ₐ[Padic l] Ω)
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left]
    (_hij : Set.range i₀.left.base = (Set.range j₀.left.base)ᶜ) :
    (∀ n : ℕ, sfFiniteOpenClosedWeilMateAssertions D l E j₀ i₀ n) ∧
    (∀ n : ℕ, sfFinitePresentationOpenClosedWeilMateAssertions D l E j₀ i₀ n) ∧
    sfIntegralOpenClosedWeilMateAssertions D l E j₀ i₀ ∧
    sfCoefficientOpenClosedWeilMateAssertions D l E j₀ i₀ ∧
    sfCompletionOpenClosedWeilMateAssertions D l hl E j₀ i₀ ∧
    sfRationalizationOpenClosedWeilMateAssertions D l hl E j₀ i₀ ∧
    sfRationalScalarOpenClosedWeilMateAssertions D l hl E j₀ i₀ ∧
    sfCommonStageOpenClosedWeilMateAssertions D l hl Ω j₀ i₀ ∧
    OpenClosedWeilMateAssertions
      (fieldWeilOpen D l hl E j₀) (fieldWeilPull D l hl E j₀)
      (fieldWeilPull D l hl E i₀) (fieldWeilProper D l hl E i₀)
      (fieldWeilOpenAdj D l hl E j₀) (fieldWeilProperAdj D l hl E i₀)
      (sfWeilFrobeniusPullback D l hl X₀ E) (sfWeilFrobeniusPullback D l hl U₀ E)
      (sfWeilFrobeniusPullback D l hl Z₀ E)
      (fieldWeilPullSquare D l hl E j₀) (fieldWeilPullSquare D l hl E i₀) ∧
    OpenClosedWeilMateAssertions
      (zlCommonStageOpenShriek D l hl Ω j₀) (zlPull D l hl Ω j₀)
      (zlPull D l hl Ω i₀) (zlCommonStageProperPush D l hl Ω i₀)
      (zlCommonStageOpenAdjunction D l hl Ω j₀) (zlCommonStageProperAdjunction D l hl Ω i₀)
      (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
      (sfCommonStageWeilFrobeniusPullback D l hl U₀ Ω)
      (sfCommonStageWeilFrobeniusPullback D l hl Z₀ Ω)
      (zlFrobeniusSquare D l hl Ω j₀) (zlFrobeniusSquare D l hl Ω i₀) := by
  have hf := sf_openClosed_weil_finite_stage D l hl E Ω _ιE j₀ i₀ _hij
  have hi := sf_openClosed_weil_integral_stage D l hl E Ω _ιE j₀ i₀ _hij
  have hc := sf_openClosed_weil_coefficient_stage D l hl E Ω _ιE j₀ i₀ _hij
  have hd := sf_openClosed_weil_descent_stage D l hl E Ω _ιE j₀ i₀ _hij
  refine ⟨hf.1, hf.2, hi.1, hc, hi.2, hd.1, hd.2.1, hd.2.2, ?_, ?_⟩
  · exact openClosedMateAssertions_of_isIso _ _ _ _ _ _ _ _ _ _ _
      ((fieldWeilExchange_isIso D l hl E).2 j₀)
      ((fieldWeilExchange_isIso D l hl E).1 i₀)
  · exact openClosedMateAssertions_of_isIso _ _ _ _ _ _ _ _ _ _ _
      (zlOpenFrobeniusInverseMap_isIso D l hl Ω j₀)
      (zlProperFrobeniusMap_isIso D l hl Ω i₀)

end WeilConjectures
