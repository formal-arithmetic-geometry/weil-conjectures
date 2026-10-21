/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Internal modules with an action of a profinite condensed group

Source: blueprint, direct-image stability, paragraph (3), internal-action categorical input
(blueprint: def-sfb-condensed-action-module).

The underlying object is the recorded internal module object. Its section module is read
through the existing section-module equivalence. Actions use all continuous maps from a
profinite test object and commute with restriction; they are not abstract group actions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.CondensedAction

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The existing internal-module category on the coherent profinite site.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
abbrev Modules := Mod (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) R.X

/-- Read the sectionwise module through the recorded internal-module equivalence.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
noncomputable abbrev sectionModule (M : Modules R) (S : Profinite.{u}) :=
  ((InternalAbelianSheafModule.sectionModuleFunctor
    (coherentTopology Profinite.{u}) R.X).obj M).val.obj (op S)

variable (P : Type u) [TopologicalSpace P] [Group P] [IsTopologicalGroup P]

/-- A linear internal action: sectionwise linear endomorphisms, unit and multiplication
encoded by a monoid homomorphism, compatible with every profinite restriction. Inverses
in the group imply these endomorphisms are automorphisms.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
structure ActionModule where
  /-- The internal module object, with no topological presentation assumed. -/
  module : Modules R
  /-- The action by every continuous-map section. -/
  act : ∀ S : Profinite.{u}, C(S, P) →*
    Module.End ((InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) R.X).obj (op S)) (sectionModule R module S)
  /-- Naturality of the action in profinite test objects. -/
  naturality : ∀ (S T : Profinite.{u}) (f : T ⟶ S) (g : C(S, P))
    (m : sectionModule R module S),
    (module.X.obj.map f.op).hom (act S g m) =
      act T (g.comp f.hom.hom) ((module.X.obj.map f.op).hom m)

variable {R P}

/-- Equivariance is required at every profinite test object.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
def Equivariant (M N : ActionModule R P) (f : M.module ⟶ N.module) : Prop :=
  ∀ (S : Profinite.{u}) (g : C(S, P)) (m : sectionModule R M.module S),
    (f.hom.hom.app (op S)).hom (M.act S g m) =
      N.act S g ((f.hom.hom.app (op S)).hom m)

/-- Equivariant linear maps contain identities and zero and are closed under composition,
addition and negation. Source: blueprint paragraph (3)
(blueprint: def-sfb-condensed-action-module).
Proof: evaluate on a test object. The identity and composite commute with the action by
substitution. Zero, sums and negatives commute because each action endomorphism is linear.
-/
theorem equivariant_closure (M N L : ActionModule R P) :
    Equivariant M M (𝟙 M.module) ∧
    (∀ (f : M.module ⟶ N.module) (g : N.module ⟶ L.module),
      Equivariant M N f → Equivariant N L g → Equivariant M L (f ≫ g)) ∧
    Equivariant M N 0 ∧
    (∀ (f g : M.module ⟶ N.module), Equivariant M N f → Equivariant M N g →
      Equivariant M N (f + g)) ∧
    (∀ (f : M.module ⟶ N.module), Equivariant M N f → Equivariant M N (-f)) := by
  sorry

/-- The additive subgroup of equivariant internal-module morphisms.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
def homSubgroup (M N : ActionModule R P) : AddSubgroup (M.module ⟶ N.module) where
  carrier := {f | Equivariant M N f}
  zero_mem' := (equivariant_closure M N N).2.2.1
  add_mem' := (equivariant_closure M N N).2.2.2.1 _ _
  neg_mem' := (equivariant_closure M N N).2.2.2.2 _

/-- The category has exactly the equivariant linear maps and ordinary composition.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
instance actionCategory : Category (ActionModule R P) where
  Hom M N := homSubgroup M N
  id M := ⟨𝟙 M.module, (equivariant_closure M M M).1⟩
  comp {M N L} f g :=
    ⟨f.val ≫ g.val, (equivariant_closure M N L).2.1 _ _ f.property g.property⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

/-- Addition of equivariant maps is the underlying addition of internal-module maps.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
instance actionPreadditive : Preadditive (ActionModule R P) where
  homGroup M N := inferInstanceAs (AddCommGroup (homSubgroup M N))
  add_comp _ _ _ f g h := Subtype.ext (Preadditive.add_comp _ _ _ f.val g.val h.val)
  comp_add _ _ _ f g h := Subtype.ext (Preadditive.comp_add _ _ _ f.val g.val h.val)

/-- Forget the action while retaining the original internal module and map.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
def forgetAction : ActionModule R P ⥤ Modules R where
  obj M := M.module
  map f := f.val

variable {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]

/-- Inflation precomposes the section action and changes neither the module nor its maps.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
def inflate (π : P →ₜ* Q) : ActionModule R Q ⥤ ActionModule R P where
  obj M :=
    { module := M.module
      act := fun S ↦ (M.act S).comp
        (MonoidHom.compLeftContinuous S π.toMonoidHom π.continuous)
      naturality := fun S T f g m ↦ M.naturality S T f (π.toContinuousMap.comp g) m }
  map f := ⟨f.val, fun S g m ↦ f.property S (π.toContinuousMap.comp g) m⟩

/-- Inflation from the trivial group, directly on ordinary internal modules.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
def trivial : Modules R ⥤ ActionModule R P where
  obj M := { module := M, act := fun _ ↦ 1, naturality := fun _ _ _ _ _ ↦ rfl }
  map f := ⟨f, fun _ _ _ ↦ rfl⟩

/-- Fixed sections quantify over every profinite base change and every section of the kernel.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
def Fixed (M : ActionModule R P) (π : P →ₜ* Q) (S : Profinite.{u})
    (m : sectionModule R M.module S) : Prop :=
  ∀ (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, P)),
    (∀ t : T, π (g t) = 1) →
      M.act T g ((M.module.X.obj.map f.op).hom m) = (M.module.X.obj.map f.op).hom m

/-- Simultaneous fixed sections, retaining the same quantification over base changes.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
def FixedAll (M : ActionModule R P) (S : Profinite.{u})
    (m : sectionModule R M.module S) : Prop :=
  ∀ (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, P)),
    M.act T g ((M.module.X.obj.map f.op).hom m) = (M.module.X.obj.map f.op).hom m

variable (R P)

/-- A normalized invariants adjunction. The inclusion identifies its sections with exactly
all fixed sections; the two adjunction directions retain the original section maps.
This is a specification, not a choice of unspecified invariants data.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
structure Invariants where
  /-- The invariants functor. -/
  functor : ActionModule R P ⥤ Modules R
  /-- Its additive structure. -/
  additive : functor.Additive
  /-- The inclusion of the invariant subsheaf. -/
  inclusion : functor ⟶ forgetAction
  /-- Inflation is left adjoint to invariants. -/
  adjunction : trivial ⊣ functor
  /-- The inclusion is injective on each section module. -/
  injective : ∀ (M : ActionModule R P) (S : Profinite.{u}),
    Function.Injective (((inclusion.app M).hom.hom.app (op S)).hom)
  /-- Its image is exactly the sections fixed after every base change. -/
  image : ∀ (M : ActionModule R P) (S : Profinite.{u}) (m : sectionModule R M.module S),
    (∃ x : sectionModule R (functor.obj M) S,
      ((inclusion.app M).hom.hom.app (op S)).hom x = m) ↔ FixedAll M S m
  /-- Forward transpose restricts the codomain to invariant sections. -/
  transpose : ∀ (N : Modules R) (M : ActionModule R P) (f : trivial.obj N ⟶ M),
    adjunction.homEquiv N M f ≫ inclusion.app M = f.val
  /-- Inverse transpose composes with the inclusion. -/
  untranspose : ∀ (N : Modules R) (M : ActionModule R P) (f : N ⟶ functor.obj M),
    ((adjunction.homEquiv N M).symm f).val = f ≫ inclusion.app M

variable (G H : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [TopologicalSpace H] [Group H] [IsTopologicalGroup H]

/-- Kernel invariants for the first projection retain the induced first-factor action.
The inclusion, residual action and both transpose formulas specify the canonical functor.
Source: blueprint paragraph (3) (blueprint: def-sfb-condensed-action-module). -/
structure ProductInvariants where
  /-- Invariants under the second factor. -/
  functor : ActionModule R (G × H) ⥤ ActionModule R G
  /-- Restricting sums of maps gives sums. -/
  additive : functor.Additive
  /-- Inclusion into the original underlying module. -/
  inclusion : functor ⋙ forgetAction ⟶ forgetAction
  /-- The first-projection inflation adjunction. -/
  adjunction : inflate (ContinuousMonoidHom.fst G H) ⊣ functor
  /-- Invariant sections embed. -/
  injective : ∀ (M : ActionModule R (G × H)) (S : Profinite.{u}),
    Function.Injective (((inclusion.app M).hom.hom.app (op S)).hom)
  /-- The image is precisely the kernel-fixed sections after all base changes. -/
  image : ∀ (M : ActionModule R (G × H)) (S : Profinite.{u})
    (m : sectionModule R M.module S),
    (∃ x : sectionModule R (functor.obj M).module S,
      ((inclusion.app M).hom.hom.app (op S)).hom x = m) ↔
        Fixed M (ContinuousMonoidHom.fst G H) S m
  /-- The residual action is the action of `(g,1)`. -/
  residual : ∀ (M : ActionModule R (G × H)) (S : Profinite.{u}) (g : C(S, G))
    (x : sectionModule R (functor.obj M).module S),
    ((inclusion.app M).hom.hom.app (op S)).hom ((functor.obj M).act S g x) =
      M.act S ((ContinuousMonoidHom.inl G H).toContinuousMap.comp g)
        (((inclusion.app M).hom.hom.app (op S)).hom x)
  /-- Forward transpose retains the underlying map and restricts its codomain. -/
  transpose : ∀ (N : ActionModule R G) (M : ActionModule R (G × H))
    (f : (inflate (ContinuousMonoidHom.fst G H)).obj N ⟶ M),
    (adjunction.homEquiv N M f).val ≫ inclusion.app M = f.val
  /-- Inverse transpose composes with the invariant-submodule inclusion. -/
  untranspose : ∀ (N : ActionModule R G) (M : ActionModule R (G × H))
    (f : N ⟶ functor.obj M),
    ((adjunction.homEquiv N M).symm f).val = f.val ≫ inclusion.app M

end Profinite.CondensedAction
