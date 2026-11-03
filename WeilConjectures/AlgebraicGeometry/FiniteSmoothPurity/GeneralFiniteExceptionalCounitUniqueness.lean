/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation

/-! # Faithfulness of the transported exceptional counit transpose

Source: sk-thm-purity-transport proof, Step 1; sk-lem-sp-reduction, equation (10.15).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

local instance (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem comparison_preimage
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    {M N : DerivedCategoryModule A X}
    (hN : _root_.DerivedCategory.TStructure.t.plus N)
    (a : (comparison A X).obj M ⟶ (comparison A X).obj N) :
    ∃ v : M ⟶ N, (comparison A X).map v = a := by
  let adj := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) X N hN
  let v := adj.homEquiv M _ a ≫ inv (adj.unit.app N)
  refine ⟨v, ?_⟩
  apply (adj.homEquiv M _).injective
  rw [Adjunction.homEquiv_unit]
  have hn := adj.unit.naturality v
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  erw [← hn]
  dsimp only [v]
  dsimp only [Functor.id_obj]
  erw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- On bounded-below comparison images, the transported exceptional counit determines
an arrow uniquely. This is an injectivity assertion, independent of coefficients,
orientations, purity isomorphisms and the scalar/compact comparison.
Source: sk-thm-purity-transport proof, Step 1, exceptional adjunction constituent;
sk-lem-sp-reduction, equation (10.15).
(blueprint: lem-pur-general-exceptional-counit-uniqueness).

Proof: use the comparison adjunction and its invertible unit at f!Rnu_*K to lift
both arrows to ordinary etale arrows. The compact-support site comparison is natural
on the bounded-below source and target; it is invertible at the source. Cancel it in
the equality of counit transposes. Injectivity of the comparison Hom bijection then
identifies the two ordinary compact-support/exceptional counit transposes. The ordinary
exceptional adjunction Hom bijection is injective too, so the lifts, and hence their
comparison images, agree. -/
theorem exceptionalCounit_injective
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (K : proCategory A Y)
    (hG : _root_.DerivedCategory.TStructure.t.plus
      ((rightDerivedUpperShriek A f).obj ((origin A Y).obj K)))
    (a b : (comparison A X).obj M ⟶ (exceptional A f).obj K)
    (h : (proCompact A f).map a ≫ proCounit A f K =
      (proCompact A f).map b ≫ proCounit A f K) : a = b := by
  obtain ⟨v, rfl⟩ := comparison_preimage A X hG a
  obtain ⟨w, rfl⟩ := comparison_preimage A X hG b
  have hv := compactSiteNaturality A f hM hG v
  have hw := compactSiteNaturality A f hM hG w
  have : IsIso (compactSiteMap A f M) := by
    unfold compactSiteMap
    rw [dif_pos hM]
    infer_instance
  dsimp only [proCounit, exceptional, Functor.comp_obj] at h ⊢
  rw [reassoc_of% hv, reassoc_of% hw] at h
  have hh := (cancel_epi (compactSiteMap A f M)).mp h
  simp only [← (comparison A Y).map_comp_assoc] at hh
  have he :
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map v ≫
          (rightDerivedUpperShriekAdjunction A f).counit.app ((origin A Y).obj K) =
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map w ≫
          (rightDerivedUpperShriekAdjunction A f).counit.app ((origin A Y).obj K) := by
    apply ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} A) Y).homEquiv _ K).symm.injective
    simpa only [Adjunction.homEquiv_counit, comparison] using hh
  have hvw : v = w := ((rightDerivedUpperShriekAdjunction A f).homEquiv
    M ((origin A Y).obj K)).symm.injective he
  exact congrArg (comparison A X).map hvw

end AlgebraicGeometry.Etale.FiniteSmoothPurity
