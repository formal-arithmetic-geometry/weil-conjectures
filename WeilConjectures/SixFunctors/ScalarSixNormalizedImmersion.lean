/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
import WeilConjectures.SixFunctors.ScalarSixImmersionComparisonExistence
import WeilConjectures.SixFunctors.ScalarSixRestrictionComposition
import WeilConjectures.SixFunctors.ScalarSixImmersionIdentifiers
import WeilConjectures.CategoryTheory.NormalizedExtensionComparisonComposition

/-! # The normalized locally closed scalar comparison before tower coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarSixChange scalarSixPull scalarSixExtension scalarSixRestriction
  scalarSixExtensionComp scalarSixOpenIso scalarSixPullComp

private theorem inversePullComparison_comp
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (R : A₂ ⥤ A₁) (S : A₁ ⥤ A₀) (U : A₂ ⥤ A₀)
    (R' : B₂ ⥤ B₁) (S' : B₁ ⥤ B₀) (U' : B₂ ⥤ B₀)
    (T₀ : A₀ ⥤ B₀) (T₁ : A₁ ⥤ B₁) (T₂ : A₂ ⥤ B₂)
    (c : U ≅ R ⋙ S) (c' : U' ≅ R' ⋙ S')
    (qF : R ⋙ T₁ ≅ T₂ ⋙ R') (qG : S ⋙ T₀ ≅ T₁ ⋙ S')
    (qH : U ⋙ T₀ ≅ T₂ ⋙ U') (K : A₂)
    (h : qH.hom.app K ≫ c'.hom.app (T₂.obj K) =
      T₀.map (c.hom.app K) ≫ qG.hom.app (R.obj K) ≫ S'.map (qF.hom.app K)) :
    c'.hom.app (T₂.obj K) ≫ S'.map (qF.inv.app K) ≫ qG.inv.app (R.obj K) =
      qH.inv.app K ≫ T₀.map (c.hom.app K) := by
  let i := S'.mapIso (qF.app K)
  let j := qG.app (R.obj K)
  let l := qH.app K
  change l.hom ≫ c'.hom.app (T₂.obj K) = T₀.map (c.hom.app K) ≫ j.hom ≫ i.hom at h
  change c'.hom.app (T₂.obj K) ≫ i.inv ≫ j.inv = l.inv ≫ T₀.map (c.hom.app K)
  have hh := congrArg (fun z ↦ l.inv ≫ z ≫ i.inv ≫ j.inv) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using hh

private theorem extension_full (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : S ⟶ X) [IsImmersion f.left] : (scalarSixExtension E G Λ f).Full := by
  have hD := D.full (scalarSixImmersion G Λ f)
  have hF := (scalarSixEquivalence Λ S.left).fullyFaithfulFunctor.full
  have hB := (scalarSixEquivalence Λ X.left).symm.fullyFaithfulFunctor.full
  unfold scalarSixExtension
  exact @Functor.Full.comp _ _ _ _ _ _ _ _ hF
    (@Functor.Full.comp _ _ _ _ _ _ _ _ hD hB)

/-- Normalized immersion comparison, its geometric compositor, and its specified open value.

Source: blueprint det-prop-scalar-six-pullback.proof.md (2), normalized locally closed
assembly; Stacks Tags 03DI, 03DJ, 09BM and 09AH.
(blueprint: lem-sfb-scalar-six-normalized-immersion).

Proof: individual comparison existence (lem-sfb-scalar-six-individual-immersion-comparisons)
supplies the family beta, its restriction normalization by inverse C.theta and its
specified open value. The coefficient immersions compose literally by
lem-sfb-scalar-six-immersion-identifiers. For the geometric composition law, each
transported extension is full, since the fixed equivalence functors and D.full are full.
A full extension with an invertible restriction detects maps between supported objects
(lem-sfb-normalized-extension-comparison-composition). After restriction to the
composite immersion and postcomposition with its restriction isomorphism, the two sides
agree by beta normalization, the restriction-composition equation at each coefficient
ring (lem-sfb-scalar-six-restriction-composition), naturality, and the inverse form of
C.composition. This assertion concerns one coefficient arrow at a time; coefficient
towers are deduced separately from normalized restriction and full faithfulness. -/
theorem scalarSixNormalizedImmersion_exists
    (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k) :
    Nonempty (ScalarSixNormalizedImmersionData E D G C k O) := by
  -- Individual comparison existence supplies no geometric composition law.
  obtain ⟨beta, hn, ho⟩ := scalarSixIndividualImmersionComparisons_exists E hE D G C k O
  let I := scalarSixImmersionIdentifiers G k
  refine ⟨{ beta := beta
            normalization := hn
            compositionIdentifier := I
            composition := ?_
            openComparison := ho }⟩
  dsimp only [ScalarSixImmersionComposition]
  intro Λ Λ' a T S X _ _ _ _ _ _ _ _ _ f g _ _ M
  have := extension_full E D G Λ' (g ≫ f)
  apply normalizedExtensionComparison_comp
    (scalarSixExtension E G Λ f) (scalarSixExtension E G Λ g)
    (scalarSixExtension E G Λ (g ≫ f))
    (scalarSixExtension E G Λ' f) (scalarSixExtension E G Λ' g)
    (scalarSixExtension E G Λ' (g ≫ f))
    (scalarSixPull Λ f.left) (scalarSixPull Λ g.left) (scalarSixPull Λ (g ≫ f).left)
    (scalarSixPull Λ' f.left) (scalarSixPull Λ' g.left) (scalarSixPull Λ' (g ≫ f).left)
    (scalarSixRestriction E D G Λ f) (scalarSixRestriction E D G Λ g)
    (scalarSixRestriction E D G Λ (g ≫ f))
    (scalarSixRestriction E D G Λ' f) (scalarSixRestriction E D G Λ' g)
    (scalarSixRestriction E D G Λ' (g ≫ f))
    (scalarSixExtensionComp E D G Λ f g (I Λ f g))
    (scalarSixExtensionComp E D G Λ' f g (I Λ' f g))
    (scalarSixPullComp Λ g.left f.left) (scalarSixPullComp Λ' g.left f.left)
    (scalarSixChange a T.left) (scalarSixChange a S.left) (scalarSixChange a X.left)
    (C.theta a f.left).symm (C.theta a g.left).symm (C.theta a (g ≫ f).left).symm
    (beta a f) (beta a g) (beta a (g ≫ f))
    (hn a f) (hn a g) (hn a (g ≫ f))
    (scalarSixRestriction_comp E hE D G Λ f g (I Λ f g))
    (scalarSixRestriction_comp E hE D G Λ' f g (I Λ' f g)) ?_ M
  intro K
  exact inversePullComparison_comp
    (scalarSixPull Λ f.left) (scalarSixPull Λ g.left) (scalarSixPull Λ (g ≫ f).left)
    (scalarSixPull Λ' f.left) (scalarSixPull Λ' g.left) (scalarSixPull Λ' (g ≫ f).left)
    (scalarSixChange a T.left) (scalarSixChange a S.left) (scalarSixChange a X.left)
    (scalarSixPullComp Λ g.left f.left) (scalarSixPullComp Λ' g.left f.left)
    (C.theta a f.left) (C.theta a g.left) (C.theta a (g ≫ f).left) K
    (C.composition a g.left f.left K)

end AlgebraicGeometry.ProEtale.CondensedRing
