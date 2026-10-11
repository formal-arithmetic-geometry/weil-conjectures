/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.InternalModule
public import Sheaf.CategoryTheory.FiniteContinuousModule
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Equivalences of module objects and finite continuous linear actions

Source: Stacks Project, Tag 0DV5, proof of (2)-(3)
(blueprint: lem-pod-equivalence-induces-module-objects).
-/

@[expose] public section

section

universe r v₁ v₂ u₁ u₂ g u

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory

/-- Equivalences preserve finite products, terminal objects, and internal left modules,
with exactly the transported operations and the original underlying functor.
Source: Stacks Tag 0DV5, proof of (2)-(3)
(blueprint: lem-pod-equivalence-induces-module-objects).
Proof, step 1: an equivalence preserves limits. Apply its functor to each operation and
conjugate using the product and terminal comparison isomorphisms. Functoriality transports
all axiom diagrams. The inverse equivalence transports structures back; naturality of
unit and counit gives the lifted equivalence. Operation-preserving maps are transported
by the original functor. This step is elementary and has no proof dependencies. -/
theorem equivalence_induces_internalModules (R : Type r) [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D] (e : C ≌ D) :
    PreservesFiniteProducts e.functor ∧
    PreservesLimit (Functor.empty.{0} C) e.functor ∧
    ∃ E : InternalModule R C ≌ InternalModule R D,
      E.functor ⋙ InternalModule.forget R D = InternalModule.forget R C ⋙ e.functor ∧
      (∀ A : InternalModule R C,
        HEq (E.functor.obj A).add
          (inv (prodComparison e.functor A.X A.X) ≫ e.functor.map A.add) ∧
        HEq (E.functor.obj A).zero
          (inv (terminalComparison e.functor) ≫ e.functor.map A.zero) ∧
        HEq (E.functor.obj A).neg (e.functor.map A.neg) ∧
        ∀ a : R, HEq ((E.functor.obj A).smul a) (e.functor.map (A.smul a))) ∧
      ∀ (A B : InternalModule R C) (f : A ⟶ B),
        HEq (E.functor.map f).val (e.functor.map f.val) := by
  sorry

/-- Internal modules in finite continuous group sets identify with finite continuous
linear representations, with the same operations and equivariant linear morphisms.
Source: Stacks Tag 0DV5, proof of (3)
(blueprint: lem-pod-equivalence-induces-module-objects).
Proof, step 2: the equivariant addition, zero, negation and scalar maps give the carrier
a left module structure. Their equivariance says every group element acts linearly;
inverses in the group give linear automorphisms. Conversely a continuous linear action
makes all four operations equivariant. These constructions are mutually inverse on
objects and maps, an isomorphism of categories and not only an equivalence.
The action retains its discrete topology and finite carrier.
This step is elementary and has no proof dependencies. -/
theorem internalModules_finiteContAction (R : Type r) [Ring R]
    (G : Type g) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ E : InternalModule R (ContAction FintypeCat.{u} G) ≌
        FiniteContinuousModule.{r, g, u} R G,
      E.functor ⋙ E.inverse = 𝟭 _ ∧
      E.inverse ⋙ E.functor = 𝟭 _ ∧
      ∃ i : InternalModule.forget R (ContAction FintypeCat.{u} G) ⋙
          finiteContActionForget G ≅ E.functor ⋙ FiniteContinuousModule.forget R G,
        ∀ (A : InternalModule R (ContAction FintypeCat.{u} G))
          (T : ContAction FintypeCat.{u} G) (a b : T ⟶ A.X) (t : T.obj.V),
          (fun (f : (T ⟶ A.X) → (T.obj.V → A.X.obj.V))
            (k : A.X.obj.V → (E.functor.obj A).obj.obj.V) ↦
            k (f (prod.lift a b ≫ A.add) t) = k (f a t) + k (f b t) ∧
            k (f (terminal.from T ≫ A.zero) t) = (0 : (E.functor.obj A).obj.obj.V) ∧
            k (f (a ≫ A.neg) t) = -k (f a t) ∧
            ∀ c : R, k (f (a ≫ A.smul c) t) = c • k (f a t))
            (fun h ↦ ((finiteContActionForget G).map h).hom) (i.hom.app A).hom := by
  sorry

end CategoryTheory

end
