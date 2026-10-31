/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-!
# Coherent common-stage pullback comparison data

The native condensed-module derived pullback is equipped with its canonical tensor and unit
comparisons, and these comparisons are coherent with pullback composition.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-proetale-coefficients/sec-pe-localization-completion/
sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md,
native derived pullback, tensor comparison, and compositor coherence
(blueprint: lem-weil-common-stage-pullback-comparison-data).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

-- The large native derived-category expressions require a larger elaboration budget.
set_option linter.style.maxHeartbeats false in
set_option linter.style.setOption false in
set_option maxHeartbeats 1000000 in
/--
The native condensed-module pullback comparison and its coherence data.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-proetale-coefficients/sec-pe-localization-completion/
sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md,
native derived pullback, tensor comparison, and compositor coherence
(blueprint: lem-weil-common-stage-pullback-comparison-data).

Proof plan (the four steps of the node):
1. Fix `Λ` and the schemes. The ambient operations of def-weil-derived-pullback-tensor-hom are
   the total derived functors of internal module pullback and relative tensor. By
   prop-sfb-module-left-derived-upper-star-levelwise, `P_f ≅ D(f^*)` canonically, so the
   derived counit of `L(f^*)` is an isomorphism at the coefficient complex `Λ_Y[0]` as well
   as at K-flat representatives.
2. For each scheme `T`, clause 4 of det-prop-sfb-module-category gives the closed symmetric
   monoidal Grothendieck module category with unit `Λ_T` and functorial flat resolutions,
   with additive relative tensor. Hence lem-sfb-derived-monoidal applies: the K-flat derived
   tensor has unit `Λ_T[0]` and associator and unitors induced from complexes; these are the
   constraints `α_`, `λ_`, `ρ_` used below, with no further normalization.
3. Apply lem-sfb-derived-pullback-strong-monoidal to `f`: it supplies the canonical comparison
   `δ = leftDerivedUpperStarTensorIso Λ f` (the `leftDerived₂Lift` of the counit) and the
   counit-then-coefficient comparison `e = leftDerivedUpperStarUnitIso Λ f`, natural and
   invertible, whose inverses are the tensorator and unit of a strong monoidal structure.
   Its associativity and two unitality axioms, composed with the inverse tensorators, are
   the three clauses with `α_`, `λ_`, `ρ_`.
4. Take the compositor `c_{f,g} = leftDerivedUpperStarComp Λ f g` of
   prop-sfb-module-left-derived-upper-star-comp, induced from ordinary module composition,
   with identity comparisons `leftDerivedUpperStarId`. lem-fix-condensed-pullback-coherence,
   applied to these native pullbacks and the comparisons of step 3, gives associativity and
   the identity laws of the compositors and the tensor and coefficient-unit equations in the
   displayed directions, for every commutative condensed ring, every scheme morphism and
   arbitrary unbounded complexes.
-/
theorem commonStagePullback_comparison_data :
    ∃ (δ : leftDerivedUpperStarTensorLeft Λ f ≅ leftDerivedUpperStarTensorRight Λ f)
      (e : ((f)^*⟦Λ⟧).leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _),
      δ = leftDerivedUpperStarTensorIso Λ f ∧
      e = leftDerivedUpperStarUnitIso Λ f ∧
      (∀ (M N V :
          DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))),
        (δ.hom.app (M ⊗ N)).app V ≫
          (((δ.hom.app M).app N) ⊗ₘ 𝟙 _) ≫
          (α_ (((f)^*⟦Λ⟧).leftDerivedFunctor.obj M)
            (((f)^*⟦Λ⟧).leftDerivedFunctor.obj N)
            (((f)^*⟦Λ⟧).leftDerivedFunctor.obj V)).hom =
        ((f)^*⟦Λ⟧).leftDerivedFunctor.map (α_ M N V).hom ≫
          (δ.hom.app M).app (N ⊗ V) ≫
          (𝟙 _ ⊗ₘ ((δ.hom.app N).app V))) ∧
      (∀ (M :
          DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))),
        (δ.hom.app (𝟙_ _)).app M ≫
          (e.hom ⊗ₘ 𝟙 _) ≫
          (λ_ (((f)^*⟦Λ⟧).leftDerivedFunctor.obj M)).hom =
        ((f)^*⟦Λ⟧).leftDerivedFunctor.map (λ_ M).hom) ∧
      (∀ (M :
          DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))),
        (δ.hom.app M).app (𝟙_ _) ≫
          (𝟙 _ ⊗ₘ e.hom) ≫
          (ρ_ (((f)^*⟦Λ⟧).leftDerivedFunctor.obj M)).hom =
        ((f)^*⟦Λ⟧).leftDerivedFunctor.map (ρ_ M).hom) ∧
      (∀ {Z : Scheme.{u}} (g : Y ⟶ Z)
          (M N :
            DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))),
        (leftDerivedUpperStarComp Λ f g).hom.app (M ⊗ N) ≫
            ((f)^*⟦Λ⟧).leftDerivedFunctor.map
              (((leftDerivedUpperStarTensorIso Λ g).hom.app M).app N) ≫
            ((δ.hom.app (((g)^*⟦Λ⟧).leftDerivedFunctor.obj M)).app
              (((g)^*⟦Λ⟧).leftDerivedFunctor.obj N)) =
          ((leftDerivedUpperStarTensorIso Λ (f ≫ g)).hom.app M).app N ≫
            ((leftDerivedUpperStarComp Λ f g).hom.app M ⊗ₘ
              (leftDerivedUpperStarComp Λ f g).hom.app N)) ∧
      (∀ {W Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) (k : Z ⟶ W)
          (M :
            DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))),
        (leftDerivedUpperStarComp Λ (g ≫ h) k).hom.app M ≫
            (leftDerivedUpperStarComp Λ g h).hom.app
              (((k)^*⟦Λ⟧).leftDerivedFunctor.obj M) =
          eqToHom (by rw [Category.assoc]) ≫
            (leftDerivedUpperStarComp Λ g (h ≫ k)).hom.app M ≫
            ((g)^*⟦Λ⟧).leftDerivedFunctor.map
              ((leftDerivedUpperStarComp Λ h k).hom.app M)) ∧
      (∀ (g : X ⟶ Y) (M :
          DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))),
        (leftDerivedUpperStarComp Λ (𝟙 X) g).hom.app M ≫
            (leftDerivedUpperStarId Λ X).hom.app
              (((g)^*⟦Λ⟧).leftDerivedFunctor.obj M) =
          eqToHom (by rw [Category.id_comp]; rfl)) ∧
      (∀ (g : X ⟶ Y) (M :
          DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))),
        (leftDerivedUpperStarComp Λ g (𝟙 Y)).hom.app M ≫
            ((g)^*⟦Λ⟧).leftDerivedFunctor.map ((leftDerivedUpperStarId Λ Y).hom.app M) =
          eqToHom (by rw [Category.comp_id]; rfl)) ∧
      (∀ {Z : Scheme.{u}} (g : Y ⟶ Z),
        (leftDerivedUpperStarComp Λ f g).hom.app (𝟙_ _) ≫
            ((f)^*⟦Λ⟧).leftDerivedFunctor.map (leftDerivedUpperStarUnitIso Λ g).hom ≫ e.hom =
          (leftDerivedUpperStarUnitIso Λ (f ≫ g)).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
