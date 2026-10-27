/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SequenceSiteOpenData
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Localization.Adjunction
import Sheaf.Paper.SequenceOpenCoefficientConstruction
import Sheaf.Paper.SequenceOpenOrdinary
import Sheaf.Paper.SequenceOpenScalars
import Sheaf.Paper.SequenceOpenDerivedTransitions

/-! # Existence of open extension on ringed sequence sites

Source: Stacks Project, Tags 03DI, 03DJ and 05RU
(blueprint: lem-pur-sequence-site-open-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r u s
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (U : C)
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem derivedAdjunction
    (O : SequenceOpenOrdinary.{c, v, r} J U B τ) :
    Nonempty (SequenceOpenDerivedAdjunction.{c, v, r} J U B τ O) := by
  let F := O.Jfun
  let G := O.L
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  let adj := (O.adjunction.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory
  refine ⟨{ adjunction := adj, unit := ?_, counit := ?_ }⟩
  · intro K
    dsimp only [adj]
    rw [Adjunction.localization_unit_app]
    change (DerivedCategory.Q.map _ ≫
      G.mapDerivedCategoryFactors.inv.app _ ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K)) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app _ = _
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    rw [G.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app]
    exact Category.comp_id
      (DerivedCategory.Q.map ((O.adjunction.mapHomologicalComplex (.up ℤ)).unit.app K))
  · intro K
    dsimp only [adj]
    rw [Adjunction.localization_counit_app]
    change F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app K) ≫
      (F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map
            ((O.adjunction.mapHomologicalComplex (.up ℤ)).counit.app K)) = _
    rw [← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
      F.mapDerivedCategory.map_id, Category.id_comp]

/-- Geometric and levelwise open extension on the ringed sequence site.
Source: Stacks 03DI, 03DJ, 03CY, 04GZ and 0791
(blueprint: lem-pur-sequence-site-open-extension).

Proof: identify the element site of the constant open subterminal with the product
of the localized base site and the index poset; covers are precisely vertical covers.
Its restricted ring is B_n on every object, giving the geometric localization and L.
Apply the ringed-sheaf slice adjunction, transporting chosen small presentations.
For every coefficient map the two extension presheaves have identical additive sums
and the same restricted action. Sheafification therefore gives the normalized comparison.
Identity and composition hold on every summand; the transpose formula gives the unit
and counit equations. Define the system transition by extension of the old transition
followed by this coefficient comparison. Naturality and composition give the strict
system laws. Transposing levelwise morphisms gives exactly the system morphism squares,
so the resulting J is left adjoint to L. Uniqueness of left adjoints identifies it,
with units and counits, with geometric extension; it is consequently additive and exact.
Finally localize these exact functors and all their comparisons termwise. The universal
property of localization preserves their equations and naturality on every derived
morphism. On each summand, a compatible scalar acts by its actual restricted section;
sheafification and then localization preserve this endomorphism. -/
theorem sequenceSiteOpenExtension (W : Scheme.{u}) (V : W.ProEt)
    [IsOpenImmersion V.hom]
    (B : ℕ → Sheaf (Scheme.ProEt.topology W) CommRingCat.{max (u + 1) r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) :
    ∃ O : SequenceOpenOrdinary.{u + 1, u, r} (Scheme.ProEt.topology W) V B τ,
      O.Transitions ∧ O.Scalars.{u + 1, u, r, s} ∧ O.DerivedTransitions ∧
        Nonempty (SequenceOpenDerivedAdjunction.{u + 1, u, r}
          (Scheme.ProEt.topology W) V B τ O) := by
  obtain ⟨A⟩ := sequenceOpenCoefficients.{u + 1, u, r} (Scheme.ProEt.topology W) V
  obtain ⟨O, _, ht⟩ := sequenceOpenOrdinary W V B τ A
  exact ⟨O, ht, O.scalars _ _ _ _, O.derivedTransitions _ _ _ _ ht,
    derivedAdjunction _ _ _ _ O⟩

end WeilConjectures.SemilinearSections
