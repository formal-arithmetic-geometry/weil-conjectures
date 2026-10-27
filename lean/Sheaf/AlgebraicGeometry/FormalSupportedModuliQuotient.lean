/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.AlgebraicGeometry.FormalModuliQuotient

/-! # Quotient presentations whose coherent arrows are defined on formal support

Source: Stacks, Tags 044Q, 04M9, 044W; Pikaart--de Jong, §2.3.6
(blueprint: def-sfb-formal-supported-moduli-quotient).

The existing global coherent-action interface requires isomorphisms on the entire
atlas. Here they are required only on maps supported on its formal closed locus.
This retains exactly the formal quotient assumption, without asserting effectivity
of its arrows away from that locus. As in `IsFormalModuliQuotient`, étale local
objects and arrows describe torsors, including nontrivial torsors.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Coherent action arrows restricted to supported atlas maps, natural in every
base change. They are the arrows of the formal action groupoid. The unit and
multiplication equations use heterogeneous equality solely for action-law transports.
Source: Stacks, Tags 0444 and 044Q; Pikaart--de Jong, §2.3.6
(blueprint: def-sfb-formal-supported-moduli-quotient). -/
structure FormalSupportedAtlasAction {S : Scheme.{u}} {Q : Over S}
    {F : BasedCategory.{v, w} (Over S)} {H : Type u} [Group H]
    (σ : H →* Aut Q) (f : BasedFunctor (discreteModuli (yoneda.obj Q)) F)
    (Z : Set Q.left) where
  stable : ∀ (h : H) (z : Q.left), (σ h).hom.left z ∈ Z ↔ z ∈ Z
  arrow : ∀ (T : Over S) (a : T ⟶ Q) (_ha : Set.range a.left ⊆ Z) (h : H),
    ModuliTwoIso (moduliChartMap (a ≫ (σ h).hom) f) (moduliChartMap a f)
  naturality : ∀ (T W : Over S) (a : T ⟶ Q) (ha : Set.range a.left ⊆ Z)
    (c : W ⟶ T) (hc : Set.range (c ≫ a).left ⊆ Z) (h : H),
    HEq (Functor.whiskerLeft (discreteModuliMap (yoneda.map c)).toFunctor
      (arrow T a ha h).val.hom) (arrow W (c ≫ a) hc h).val.hom
  one : ∀ (T : Over S) (a : T ⟶ Q) (ha : Set.range a.left ⊆ Z),
    HEq (arrow T a ha 1).val.hom (𝟙 (moduliChartMap a f).toFunctor)
  mul : ∀ (T : Over S) (a : T ⟶ Q) (ha : Set.range a.left ⊆ Z) (h k : H)
    (hk : Set.range (a ≫ (σ k).hom).left ⊆ Z),
    HEq (arrow T a ha (h * k)).val.hom
      ((arrow T (a ≫ (σ k).hom) hk h).val.hom ≫ (arrow T a ha k).val.hom)

/-- The torsor quotient presentation of the formal locus, with the specified effective
map as its atlas. Local lifting and the full local arrow description are required;
uniqueness is tested on nonempty schemes, since empty restrictions forget all labels.
The completion predicate is the recorded `ModuliCompletionAt`, not a chosen property.
Source: Stacks, Tags 04M9 and 044W; Pikaart--de Jong, §2.3.6
(blueprint: def-sfb-formal-supported-moduli-quotient). -/
def IsFormalSupportedModuliQuotient {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {Q : Over (Spec (.of Ω))}
    {F : BasedCategory.{v, w} (Over (Spec (.of Ω)))} {H : Type u} [Group H]
    (x : BasedFunctor (discreteModuli (yoneda.obj (Over.mk (𝟙 (Spec (.of Ω)))))) F)
    (σ : H →* Aut Q) (f : BasedFunctor (discreteModuli (yoneda.obj Q)) F)
    (Z : Set Q.left) (θ : FormalSupportedAtlasAction σ f Z) : Prop :=
  (∀ (T : Over (Spec (.of Ω))) (a : T ⟶ Q), Set.range a.left ⊆ Z →
    ModuliCompletionAt x (moduliChartMap a f)) ∧
  (∀ (T : Over (Spec (.of Ω))) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
    ModuliCompletionAt x t →
    ∃ R : Sieve T, R ∈ (Scheme.etaleTopology.over (Spec (.of Ω))) T ∧
      ∀ (W : Over (Spec (.of Ω))) (b : W ⟶ T), R b →
        ∃ a : W ⟶ Q, Set.range a.left ⊆ Z ∧
          Nonempty (ModuliTwoIso (moduliChartMap a f) (moduliChartMap b t))) ∧
  (∀ (T : Over (Spec (.of Ω))) (a b : T ⟶ Q)
    (_ha : Set.range a.left ⊆ Z), Set.range b.left ⊆ Z →
    ∀ η : ModuliTwoIso (moduliChartMap a f) (moduliChartMap b f),
      ∃ R : Sieve T, R ∈ (Scheme.etaleTopology.over (Spec (.of Ω))) T ∧
        ∀ (W : Over (Spec (.of Ω))) (c : W ⟶ T), R c →
          ∃ (h : H) (hc : Set.range (c ≫ a).left ⊆ Z),
            (c ≫ a) ≫ (σ h).hom = c ≫ b ∧
            HEq (Functor.whiskerLeft (discreteModuliMap (yoneda.map c)).toFunctor η.val.hom)
              (θ.arrow W (c ≫ a) hc h).val.inv) ∧
  (∀ (T : Over (Spec (.of Ω))) (_ : Nonempty T.left) (a : T ⟶ Q)
    (ha : Set.range a.left ⊆ Z) (h k : H), a ≫ (σ h).hom = a ≫ (σ k).hom →
      HEq (θ.arrow T a ha h).val.inv (θ.arrow T a ha k).val.inv → h = k)

end CategoryTheory
