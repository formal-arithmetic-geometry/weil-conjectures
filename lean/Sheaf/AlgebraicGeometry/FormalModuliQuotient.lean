/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.CategoryTheory.Whiskering

/-! # Formal quotient charts of fibred groupoids

Source: Stacks, Tags 003R, 044Q, 0444, 04M9 and 044W; Pikaart--de Jong, §2.3.6
(blueprint: def-sfb-formal-moduli-quotient).

A quotient presentation is specified by its coherent action on the atlas, local
lifting of objects, and the local arrow description, including uniqueness. These
are precisely the torsor description of the quotient stack: local trivializations
of a torsor give lifts, and changes of trivialization are the indicated group
arrows. Descent retains nontrivial torsors. Formal support means that the image
lies in the closed fibre; for a finitely generated ideal on a Noetherian atlas
this is equivalent to locally killing a power of that ideal.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Precomposition of a scheme-valued atlas map, retaining its 2-morphisms.
Source: Stacks 003R (blueprint: def-sfb-formal-moduli-quotient). -/
def moduliChartMap {S : Scheme.{u}} {T Q : Over S}
    {F : BasedCategory.{v, w} (Over S)} (a : T ⟶ Q)
    (f : BasedFunctor (discreteModuli (yoneda.obj Q)) F) :
    BasedFunctor (discreteModuli (yoneda.obj T)) F :=
  (discreteModuliMap (yoneda.map a)).comp f

/-- The geometric object specified by a scheme map to a fibred groupoid, in its
actual fibre. Source: Stacks 003T (blueprint: def-sfb-formal-moduli-quotient). -/
def moduliChartPoint {S : Scheme.{u}} {T : Over S}
    {F : BasedCategory.{v, w} (Over S)}
    (f : BasedFunctor (discreteModuli (yoneda.obj T)) F) : Functor.Fiber F.p T :=
  Functor.Fiber.mk (f.w_obj (CostructuredArrow.mk (𝟙 (yoneda.obj T))))

/-- The coherent equivariant structure on a map from an atlas. Multiplication in
`Aut` is function composition, so the cocycle first restricts the arrow for `h`
along `k`, and then uses the arrow for `k`. Heterogeneous equality only transports
across the functor equalities induced by the group-action laws.
Source: Stacks 0444 (blueprint: def-sfb-formal-moduli-quotient). -/
structure ModuliAtlasAction {S : Scheme.{u}} {Q : Over S}
    {F : BasedCategory.{v, w} (Over S)} {H : Type u} [Group H]
    (ρ : H →* Aut Q) (f : BasedFunctor (discreteModuli (yoneda.obj Q)) F) where
  arrow : ∀ h : H, ModuliTwoIso (moduliChartMap (ρ h).hom f) f
  one : HEq (arrow 1).val.hom (𝟙 f.toFunctor)
  mul : ∀ h k : H, HEq (arrow (h * k)).val.hom
    ((Functor.whiskerLeft (discreteModuliMap (yoneda.map (ρ k).hom)).toFunctor
      (arrow h).val.hom) ≫ (arrow k).val.hom)

/-- The formal completion along the residual gerbe of a geometric object is tested
on geometric points. Membership means that every such point is isomorphic to the
specified object after its residue-field extension, retaining the entire gerbe.
Source: Stacks, formal completion along a closed substack; Pikaart--de Jong §2.3.6
(blueprint: def-sfb-formal-moduli-quotient). -/
def ModuliCompletionAt {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {F : BasedCategory.{v, w} (Over (Spec (.of Ω)))}
    (x : BasedFunctor (discreteModuli (yoneda.obj (Over.mk (𝟙 (Spec (.of Ω)))))) F)
    {T : Over (Spec (.of Ω))} (t : BasedFunctor (discreteModuli (yoneda.obj T)) F) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Ω →+* K)
      (b : Over.mk (Spec.map (CommRingCat.ofHom a)) ⟶ T),
    Nonempty (ModuliTwoIso (moduliChartMap b t)
      (moduliChartMap (Over.homMk (V := Over.mk (𝟙 (Spec (.of Ω))))
        (Spec.map (CommRingCat.ofHom a))) x))

/-- A formal quotient presentation, expressed in the atlas-and-arrows description
of the torsor quotient. `Z` is the closed support on the atlas; `P` describes the
completion in the target. Covers are arbitrary étale covering sieves, so torsors
are not required to admit a global trivialization. Arrow uniqueness is imposed on
nonempty tests, since two group labels restrict to the same arrow on the empty scheme.
Source: Stacks 04M9 and 044W; Pikaart--de Jong §2.3.6
(blueprint: def-sfb-formal-moduli-quotient). -/
def IsFormalModuliQuotient {S : Scheme.{u}} {Q : Over S}
    {F : BasedCategory.{v, w} (Over S)} {H : Type u} [Group H]
    (ρ : H →* Aut Q) (f : BasedFunctor (discreteModuli (yoneda.obj Q)) F)
    (θ : ModuliAtlasAction ρ f) (Z : Set Q.left)
    (P : ∀ (T : Over S), BasedFunctor (discreteModuli (yoneda.obj T)) F → Prop) : Prop :=
  (∀ h : H, ∀ z : Q.left, (ρ h).hom.left z ∈ Z ↔ z ∈ Z) ∧
  (∀ (T : Over S) (a : T ⟶ Q), Set.range a.left ⊆ Z → P T (moduliChartMap a f)) ∧
  (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F), P T t →
    ∃ R : Sieve T, R ∈ (Scheme.etaleTopology.over S) T ∧
      ∀ (W : Over S) (b : W ⟶ T), R b →
        ∃ a : W ⟶ Q, Set.range a.left ⊆ Z ∧
          Nonempty (ModuliTwoIso (moduliChartMap a f) (moduliChartMap b t))) ∧
  (∀ (T : Over S) (a b : T ⟶ Q), Set.range a.left ⊆ Z → Set.range b.left ⊆ Z →
    ∀ η : ModuliTwoIso (moduliChartMap a f) (moduliChartMap b f),
      ∃ R : Sieve T, R ∈ (Scheme.etaleTopology.over S) T ∧
        ∀ (W : Over S) (c : W ⟶ T), R c →
          ∃ h : H, (c ≫ a) ≫ (ρ h).hom = c ≫ b ∧
            HEq (Functor.whiskerLeft (discreteModuliMap (yoneda.map c)).toFunctor η.val.hom)
              (Functor.whiskerLeft (discreteModuliMap (yoneda.map (c ≫ a))).toFunctor
                (θ.arrow h).val.inv)) ∧
  (∀ (T : Over S) (_ : Nonempty T.left) (a : T ⟶ Q), Set.range a.left ⊆ Z →
    ∀ h k : H, a ≫ (ρ h).hom = a ≫ (ρ k).hom →
      HEq (Functor.whiskerLeft (discreteModuliMap (yoneda.map a)).toFunctor (θ.arrow h).val.inv)
        (Functor.whiskerLeft (discreteModuliMap (yoneda.map a)).toFunctor (θ.arrow k).val.inv) →
      h = k)

/-- The action on geometric atlas maps induced by the specified scheme action.
Its stabilizers use Mathlib's `MulAction.stabilizer` without a second definition.
Source: Stacks 0444 and 0447 (blueprint: def-sfb-formal-moduli-quotient). -/
@[instance_reducible]
def moduliChartPointAction {S : Scheme.{u}} {Q : Over S} {H : Type u} [Group H]
    (ρ : H →* Aut Q) (T : Over S) : MulAction H (T ⟶ Q) where
  smul h b := b ≫ (ρ h).hom
  one_smul b := by
    change b ≫ (ρ 1).hom = b
    rw [map_one]
    exact Category.comp_id b
  mul_smul h k b := by
    change b ≫ (ρ (h * k)).hom = (b ≫ (ρ k).hom) ≫ (ρ h).hom
    rw [map_mul]
    exact (Category.assoc _ _ _).symm

end CategoryTheory
