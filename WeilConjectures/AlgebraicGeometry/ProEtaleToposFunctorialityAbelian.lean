/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Functoriality of pro-étale sheaves with Grothendieck abelian coefficients

Source: Weil conjectures blueprint, pro-etale coefficients,
`sk-def-sfb-finite-pushforward-pullback/prop-pe-topos-functoriality-abelian.md`,
both paragraphs (blueprint: prop-pe-topos-functoriality-abelian).

The functors, adjunction and comparisons are the existing upstream constructions.
`lowerStar` is restriction along base change; `upperStar` is left Kan extension
followed by sheafification. This statement assembles their exactness, coherence,
and conditional symmetric monoidal compatibility without redefining any of them.
-/

@[expose] public section

universe u v w w'

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

/-- Functoriality with arbitrary Grothendieck abelian coefficients of the stipulated size.

Source: blueprint, pro-etale coefficients, proposition
`prop-pe-topos-functoriality-abelian`, both paragraphs
(blueprint: prop-pe-topos-functoriality-abelian).

Proof, assembling existing declarations (the node's seven proof paragraphs):
1. The adjunction is `upperStarLowerStarAdjunction` (def-sfb-finite-lower-star,
   def-sfb-finite-upper-star, def-sfb-finite-upper-lower-star-adjunction): `lowerStar` is
   restriction along base change, `upperStar` is left Kan extension followed by
   sheafification.
2. Finite-limit preservation and exactness are the instances
   `preservesFiniteLimits_upperStar` and `preservesHomology_upperStar`
   (lem-sfb-finite-upper-star-exact); colimits are preserved because `upperStar` is a left
   adjoint, `Adjunction.leftAdjoint_preservesColimits`
   (lem-weil-pbc-left-adjoint-preserves-colimits).
3. The identity comparisons are `lowerStarId` and its conjugate `upperStarId`
   (def-weil-pbc-composite-adjunction, lem-weil-pbc-conjugate-iso-unit-equation).
4. The composition comparisons are `lowerStarComp` (def-sfb-finite-lower-star-comp) and its
   conjugate `upperStarComp` (def-sfb-finite-upper-star-comp); the six coherence equations are
   `legacy_lowerStarComp_assoc`, `upperStarComp_assoc`, `legacy_lowerStarComp_id_left`,
   `lowerStarComp_id_right`, `upperStarComp_id_left` and `upperStarComp_id_right`.
5. With the canonical sheaf tensor (lem-weil-pbc-sheaf-tensor-closed), the braiding equation
   for `μ` of `lowerStar` is `Functor.LaxBraided.braided` for `laxBraided_lowerStar`
   (def-sfb-finite-lower-star-lax-monoidal).
6. Invertibility of `η` and `δ` of the mate oplax structure is `isIso_η_upperStar` and
   `isIso_δ_upperStar` (lem-sfb-finite-upper-star-unit, lem-sfb-finite-upper-star-tensor;
   the strong structure is def-sfb-finite-upper-star-monoidal). The braiding equation for
   `δ` is `Adjunction.map_braiding_comp_δ` for the monoidal adjunction, reversed.
7. The adjunction is monoidal by `isMonoidal_upperStarLowerStarAdjunction`
   (lem-sfb-finite-monoidal-adjunction).

The monoidal clauses are stated for the canonical structures in scope: the lax structure
`laxMonoidal_lowerStar` of the restriction and the mate oplax structure
`oplaxMonoidal_upperStar` of the pullback, i.e. the very structures for which
`upperStarLowerStarAdjunction` is monoidal. Symmetry of `f_*` is the braiding equation for
its `μ`; strength of `f^*` is invertibility of its `η` and `δ` (the strong structure is the
inverse, `Functor.Monoidal.ofOplaxMonoidal`), and its symmetry is the braiding equation for
its `δ`, equivalently for the inverse `μ`. -/
theorem toposFunctorialityAbelian (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    Nonempty (upperStar A f ⊣ lowerStar A f) ∧
    PreservesFiniteLimits (upperStar A f) ∧
    PreservesColimitsOfSize.{w, w'} (upperStar A f) ∧
    (upperStar A f).PreservesHomology ∧
    Nonempty (lowerStar A (𝟙 X) ≅ 𝟭 _) ∧
    Nonempty (upperStar A (𝟙 X) ≅ 𝟭 _) ∧
    Nonempty (lowerStar A f ⋙ lowerStar A g ≅ lowerStar A (f ≫ g)) ∧
    Nonempty (upperStar A (f ≫ g) ≅ upperStar A g ⋙ upperStar A f) ∧
    ((lowerStar A f).associator (lowerStar A g) (lowerStar A h) ≪≫
        Functor.isoWhiskerLeft (lowerStar A f) (lowerStarComp A g h) ≪≫
        lowerStarComp A f (g ≫ h) =
      Functor.isoWhiskerRight (lowerStarComp A f g) (lowerStar A h) ≪≫
        lowerStarComp A (f ≫ g) h ≪≫ lowerStarCongr A (Category.assoc f g h)) ∧
    (upperStarComp A f (g ≫ h) ≪≫
        Functor.isoWhiskerRight (upperStarComp A g h) (upperStar A f) ≪≫
        (upperStar A h).associator (upperStar A g) (upperStar A f) =
      upperStarCongr A (Category.assoc f g h).symm ≪≫ upperStarComp A (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (upperStar A h) (upperStarComp A f g)) ∧
    (lowerStarComp A (𝟙 X) f =
      Functor.isoWhiskerRight (lowerStarId A X) (lowerStar A f) ≪≫
        (lowerStar A f).leftUnitor ≪≫ (lowerStarCongr A (Category.id_comp f)).symm) ∧
    (lowerStarComp A f (𝟙 Y) =
      Functor.isoWhiskerLeft (lowerStar A f) (lowerStarId A Y) ≪≫
        (lowerStar A f).rightUnitor ≪≫ (lowerStarCongr A (Category.comp_id f)).symm) ∧
    (upperStarComp A (𝟙 X) f = upperStarCongr A (Category.id_comp f) ≪≫
      (upperStar A f).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (upperStar A f) (upperStarId A X).symm) ∧
    (upperStarComp A f (𝟙 Y) = upperStarCongr A (Category.comp_id f) ≪≫
      (upperStar A f).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (upperStarId A Y).symm (upperStar A f)) ∧
    (∀ [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A],
      (∀ F G : Sheaf (Scheme.ProEt.topology X) A,
        Functor.LaxMonoidal.μ (lowerStar A f) F G ≫ (lowerStar A f).map (β_ F G).hom =
          (β_ ((lowerStar A f).obj F) ((lowerStar A f).obj G)).hom ≫
            Functor.LaxMonoidal.μ (lowerStar A f) G F) ∧
      IsIso (Functor.OplaxMonoidal.η (upperStar A f)) ∧
      (∀ F G : Sheaf (Scheme.ProEt.topology Y) A,
        IsIso (Functor.OplaxMonoidal.δ (upperStar A f) F G)) ∧
      (∀ F G : Sheaf (Scheme.ProEt.topology Y) A,
        Functor.OplaxMonoidal.δ (upperStar A f) F G ≫
            (β_ ((upperStar A f).obj F) ((upperStar A f).obj G)).hom =
          (upperStar A f).map (β_ F G).hom ≫ Functor.OplaxMonoidal.δ (upperStar A f) G F) ∧
      (upperStarLowerStarAdjunction A f).IsMonoidal) := by
  refine ⟨⟨upperStarLowerStarAdjunction A f⟩, inferInstance,
    (upperStarLowerStarAdjunction A f).leftAdjoint_preservesColimits, inferInstance,
    ⟨lowerStarId A X⟩, ⟨upperStarId A X⟩, ⟨lowerStarComp A f g⟩,
    ⟨upperStarComp A f g⟩, legacy_lowerStarComp_assoc A f g h,
    upperStarComp_assoc A f g h, legacy_lowerStarComp_id_left A f,
    lowerStarComp_id_right A f, upperStarComp_id_left A f,
    upperStarComp_id_right A f, ?_⟩
  intro _ _ _
  exact ⟨fun F G ↦ by apply Functor.LaxBraided.braided,
    inferInstance, fun F G ↦ inferInstance,
    fun F G ↦ ((upperStarLowerStarAdjunction A f).map_braiding_comp_δ F G).symm,
    inferInstance⟩

end AlgebraicGeometry.ProEtale
