/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Normed.Algebra.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # Tame inertia with all-continuous norm-topological coefficients

Source: main-20261015, direct-image stability, paragraph (3), analytic tame-boundary input
(blueprint: lem-sfb-tame-inertia-continuous-koszul).

Normalized models below specify actual internal modules by their sections and restriction
maps. Their existence is part of the theorem; no object is chosen from that theorem.

## Main definitions

* `Inputs`: the continuous finite-dimensional representations in the assertion.
* `Realization`: normalized all-continuous internal modules and the signed Koszul functor.
* `Context`: ordinary derived invariants with the existing derived universal property.
* `ScalarRestriction`, `derivedCoefficient`: normalized ordinary coefficient restriction.
* `Result`: all comparison and coefficient-square clauses.

## Main statement

* `continuous_koszul`: existence of the normalized natural derived comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace Profinite.TameInertiaKoszul

/-- The product of all prime-to-p additive integer coordinates, written multiplicatively.
Source: the displayed definition of G (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
abbrev Group (p r : ℕ) := Multiplicative
  (Fin r → (q : {q : Nat.Primes // (q : ℕ) ≠ p}) →
    ULift.{u} (@PadicInt q.1 (Fact.mk q.1.2)))

/-- The standard ell-coordinate generator, with zero in every other coordinate.
Source: the chosen gamma_i (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def generator (p ℓ r : ℕ) (i : Fin r) : Group.{u} p r :=
  Multiplicative.ofAdd fun j q ↦ if j = i ∧ (q : ℕ) = ℓ then 1 else 0

/-- The complementary tame factors, as the subgroup whose ell-coordinates vanish.
Source: the displayed definition of H (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def complement (p ℓ r : ℕ) : Subgroup (Group.{u} p r) where
  carrier := {g | ∀ (i : Fin r) (q : {q : Nat.Primes // (q : ℕ) ≠ p}),
    (q : ℕ) = ℓ → g.toAdd i q = 0}
  one_mem' := fun _ _ _ ↦ rfl
  mul_mem' := fun {a b} ha hb i q hq ↦ by
    change a.toAdd i q + b.toAdd i q = 0
    rw [ha i q hq, hb i q hq, add_zero]
  inv_mem' := fun {a} ha i q hq ↦ by
    change -(a.toAdd i q) = 0
    rw [ha i q hq, neg_zero]

variable (E : Type u) [NormedField E] (p ℓ r : ℕ)

/-- Finite-dimensional representations with continuous joint action and finite
prime-to-ell complementary image. The topology is the finite-dimensional module topology.
Source: the hypotheses on M and Q (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def admissible : ObjectProperty (Rep.{u} E (Group.{u} p r)) := fun M ↦
  FiniteDimensional E M.V ∧
  @Continuous (Group.{u} p r × M.V) M.V
    (@instTopologicalSpaceProd (Group.{u} p r) M.V inferInstance
      (moduleTopology E M.V)) (moduleTopology E M.V)
    (fun x ↦ M.ρ x.1 x.2) ∧
  Finite (Set.range (M.ρ.comp (complement p ℓ r).subtype)) ∧
  Nat.Coprime (Nat.card (Set.range (M.ρ.comp (complement p ℓ r).subtype))) ℓ

/-- Equivariant linear maps between exactly the representations of the statement.
Source: naturality in M (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
abbrev Inputs := (admissible E p ℓ r).FullSubcategory

/-- The existing invariant-submodule construction applied to the complementary subgroup.
Source: N=M^H (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
abbrev fixed (M : Inputs E p ℓ r) : Submodule E M.obj.V :=
  Representation.invariants (M.obj.ρ.comp (complement p ℓ r).subtype)

/-- The finite averaging operator over the actual complementary image, without an infinite sum.
Source: the displayed idempotent e (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def average (M : Inputs E p ℓ r) : Module.End E M.obj.V := by
  letI : Finite (Set.range (M.obj.ρ.comp (complement p ℓ r).subtype)) := M.property.2.2.1
  letI := Fintype.ofFinite (Set.range (M.obj.ρ.comp (complement p ℓ r).subtype))
  exact (Nat.card (Set.range (M.obj.ρ.comp (complement p ℓ r).subtype)) : E)⁻¹ •
    ∑ q : Set.range (M.obj.ρ.comp (complement p ℓ r).subtype), q.val

/-- The induced linear map on complementary invariants.
Source: naturality of N (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def fixedMap {M M' : Inputs E p ℓ r} (f : M ⟶ M') :
    fixed E p ℓ r M →ₗ[E] fixed E p ℓ r M' :=
  (f.hom.hom.toLinearMap.comp (fixed E p ℓ r M).subtype).codRestrict _ fun x ↦ by
    change ∀ g : complement p ℓ r, M'.obj.ρ g.val (f.hom.hom x) = f.hom.hom x
    intro g
    exact (Representation.IntertwiningMap.isIntertwining
      M.obj.ρ M'.obj.ρ f.hom.hom g.val x.val).symm.trans
        (congrArg f.hom.hom (x.property g))

/-- The restricted standard-generator operator on N.
Source: rho(gamma_i)|N (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def operator (M : Inputs E p ℓ r) (i : Fin r) :
    fixed E p ℓ r M →ₗ[E] fixed E p ℓ r M :=
  Representation.toInvariants M.obj.ρ (complement p ℓ r) (generator p ℓ r i)

variable (F : Type u) [NormedField F] [Algebra E F]

/-- Scalar extension with the finite-dimensional module topology, without completion.
Source: F tensor_E V (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def Space (V : Type u) [AddCommGroup V] [Module E V] : Type u := F ⊗[E] V

/-- The tensor-product additive structure.
Source: F tensor_E V (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
instance spaceAdd (V : Type u) [AddCommGroup V] [Module E V] :
    AddCommGroup (Space E F V) := inferInstanceAs (AddCommGroup (F ⊗[E] V))

/-- The scalar-extended module structure.
Source: F tensor_E V (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
instance spaceModule (V : Type u) [AddCommGroup V] [Module E V] :
    Module F (Space E F V) := inferInstanceAs (Module F (F ⊗[E] V))

/-- The usual topology on each finite-dimensional scalar extension.
Source: the product norm topology (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
instance spaceTopology (V : Type u) [AddCommGroup V] [Module E V] :
    TopologicalSpace (Space E F V) := moduleTopology F (Space E F V)

/-- This is the module topology by construction.
Source: the product norm topology (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
instance spaceModuleTopology (V : Type u) [AddCommGroup V] [Module E V] :
    IsModuleTopology F (Space E F V) := ⟨rfl⟩

/-- Addition and negation are continuous for the module topology.
Source: topological coefficient modules (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
instance spaceTopologicalAddGroup (V : Type u) [AddCommGroup V] [Module E V] :
    IsTopologicalAddGroup (Space E F V) := IsModuleTopology.topologicalAddGroup F _

/-- All continuous maps, with just the prescribed universe lift.
Source: M_F and N_F (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
abbrev Sections (V : Type u) [AddCommGroup V] [Module E V] (S : Profinite.{u}) :=
  ULift.{u + 1} C(S, Space E F V)

/-- The recorded continuous-map condensed ring as a bundled internal ring.
Source: C_F (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def ring : Profinite.CondensedRing.{u} :=
  @Mon.mk _ _ _ (continuousMapRingObjOfUniverse.{u, u} F)
    (continuousMapRingObjOfUniverseMonObj F)

/-- The pointwise internal ring is commutative.
Source: the coefficient field (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
instance ringCommutative : IsCommMonObj (ring F).X :=
  isCommMonObj_continuousMapRingObjOfUniverse F

/-- A normalized all-continuous presentation of an internal module. The additive
bijections, scalar law and restrictions determine the object up to its unique isomorphism.
Source: M_F and N_F section formulas (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
structure Model (V : Type u) [AddCommGroup V] [Module E V]
    (obj : CondensedAction.Modules (ring F)) where
  /-- Exactly all continuous functions on every profinite test space. -/
  sections : ∀ S : Profinite.{u},
    CondensedAction.sectionModule (ring F) obj S ≃+ Sections E F V S
  /-- Scalar multiplication is pointwise multiplication by continuous F-valued functions. -/
  scalar : ∀ (S : Profinite.{u})
    (a : (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) (ring F).X).obj (op S))
    (x : CondensedAction.sectionModule (ring F) obj S) (s : S),
    (sections S (a • x)).down s = a.down s • (sections S x).down s
  /-- Restrictions are precomposition. -/
  restriction : ∀ (S T : Profinite.{u}) (f : T ⟶ S)
    (x : CondensedAction.sectionModule (ring F) obj S) (t : T),
    (sections T ((obj.X.obj.map f.op).hom x)).down t = (sections S x).down (f t)

/-- Coordinate indices, including negative degrees and degrees above r as empty types.
Source: the displayed terms of K (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
abbrev Indices (a : ℤ) := {I : Finset (Fin r) // (I.card : ℤ) = a}

/-- Each coordinate set is finite, also when empty.
Source: the finite Koszul terms (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
instance indicesFintype (a : ℤ) : Fintype (Indices r a) := Fintype.ofFinite _

/-- The coefficient realization and the signed Koszul complex, normalized on all sections.
These are specifications of the canonical objects and maps, not arbitrary choices.
Source: the formulas defining M_F, N_F and K_F(M)
(blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
structure Realization where
  /-- Continuous representations become internal condensed-group actions. -/
  action : Inputs E p ℓ r ⥤ CondensedAction.ActionModule (ring F) (Group.{u} p r)
  /-- The action's underlying module has exactly the prescribed sections. -/
  module : ∀ M : Inputs E p ℓ r, Model E F M.obj.V (action.obj M).module
  /-- The invariant coefficient modules. -/
  invariants : Inputs E p ℓ r ⥤ CondensedAction.Modules (ring F)
  /-- The N_F sections. -/
  fixedModule : ∀ M : Inputs E p ℓ r,
    Model E F (fixed E p ℓ r M) (invariants.obj M)
  /-- Action by every continuous local group section is the extended original action. -/
  action_sections : ∀ (M : Inputs E p ℓ r) (S : Profinite.{u}) (g : C(S, Group.{u} p r))
    (x : CondensedAction.sectionModule (ring F) (action.obj M).module S) (s : S),
    ((module M).sections S ((action.obj M).act S g x)).down s =
      LinearMap.baseChange F (M.obj.ρ (g s)) (((module M).sections S x).down s)
  /-- Equivariant maps are scalar extension followed by postcomposition. -/
  map_sections : ∀ {M M' : Inputs E p ℓ r} (f : M ⟶ M') (S : Profinite.{u})
    (x : CondensedAction.sectionModule (ring F) (action.obj M).module S) (s : S),
    ((module M').sections S ((((action.map f).val).hom.hom.app (op S)).hom x)).down s =
      LinearMap.baseChange F f.hom.hom.toLinearMap (((module M).sections S x).down s)
  /-- The functor on N_F is induced by restriction to the H-invariant submodules. -/
  fixed_map_sections : ∀ {M M' : Inputs E p ℓ r} (f : M ⟶ M') (S : Profinite.{u})
    (x : CondensedAction.sectionModule (ring F) (invariants.obj M) S) (s : S),
    ((fixedModule M').sections S (((invariants.map f).hom.hom.app (op S)).hom x)).down s =
      LinearMap.baseChange F (fixedMap E p ℓ r f) (((fixedModule M).sections S x).down s)
  /-- The signed Koszul complexes, as a functor. -/
  koszul : Inputs E p ℓ r ⥤ CochainComplex (CondensedAction.Modules (ring F)) ℤ
  /-- Finite subset coordinates in every degree and on every profinite test space. -/
  coordinates : ∀ (M : Inputs E p ℓ r) (a : ℤ) (S : Profinite.{u}),
    CondensedAction.sectionModule (ring F) ((koszul.obj M).X a) S ≃+
      (Indices r a → Sections E F (fixed E p ℓ r M) S)
  /-- The coordinate isomorphisms are linear for pointwise scalars. -/
  coordinates_scalar : ∀ (M : Inputs E p ℓ r) (a : ℤ) (S : Profinite.{u})
    (c : (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) (ring F).X).obj (op S))
    (x : CondensedAction.sectionModule (ring F) ((koszul.obj M).X a) S)
    (I : Indices r a) (s : S),
    (coordinates M a S (c • x) I).down s = c.down s • (coordinates M a S x I).down s
  /-- The finite direct-sum coordinates commute with every restriction. -/
  coordinates_restriction : ∀ (M : Inputs E p ℓ r) (a : ℤ) (S T : Profinite.{u})
    (f : T ⟶ S)
    (x : CondensedAction.sectionModule (ring F) ((koszul.obj M).X a) S)
    (I : Indices r a) (t : T),
    (coordinates M a T ((((koszul.obj M).X a).X.obj.map f.op).hom x) I).down t =
      (coordinates M a S x I).down (f t)
  /-- Exactly the differential in the statement, expressed as its finite subset matrix. -/
  differential : ∀ (M : Inputs E p ℓ r) (a : ℤ) (S : Profinite.{u})
    (x : CondensedAction.sectionModule (ring F) ((koszul.obj M).X a) S)
    (J : Indices r (a + 1)) (s : S),
    (coordinates M (a + 1) S
      ((((koszul.obj M).d a (a + 1)).hom.hom.app (op S)).hom x) J).down s =
      ∑ I : Indices r a, ∑ i : Fin r,
        if i ∈ J.val ∧ J.val.erase i = I.val then
          (-1 : ℤ) ^ (J.val.filter (fun j ↦ j < i)).card •
            (LinearMap.baseChange F (operator E p ℓ r M i - LinearMap.id)
              ((coordinates M a S x I).down s)) else 0
  /-- Naturality of K is termwise the map on N_F, with no coordinate permutations. -/
  koszul_map_sections : ∀ {M M' : Inputs E p ℓ r} (f : M ⟶ M') (a : ℤ)
    (S : Profinite.{u})
    (x : CondensedAction.sectionModule (ring F) ((koszul.obj M).X a) S)
    (I : Indices r a) (s : S),
    (coordinates M' a S (((((koszul.map f).f a).hom.hom.app (op S)).hom x)) I).down s =
      LinearMap.baseChange F (fixedMap E p ℓ r f) ((coordinates M a S x I).down s)


/-- The standard ordinary localization for the module category.
Source: ordinary D(C_F) (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
instance modulesDerived : HasDerivedCategory.{u + 2} (CondensedAction.Modules (ring F)) :=
  HasDerivedCategory.standard _

/-- Abelianness data retaining the existing equivariant linear-map addition definitionally.
Source: the abelian action category (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
class ActionAbelianData (p r : ℕ) (F : Type u) [NormedField F] where
  /-- Every mono is normal. -/
  [normalMono : IsNormalMonoCategory (CondensedAction.ActionModule (ring F) (Group.{u} p r))]
  /-- Every epi is normal. -/
  [normalEpi : IsNormalEpiCategory (CondensedAction.ActionModule (ring F) (Group.{u} p r))]
  /-- Finite products. -/
  [products : HasFiniteProducts (CondensedAction.ActionModule (ring F) (Group.{u} p r))]
  /-- Kernels for the original zero maps. -/
  [kernels : HasKernels (CondensedAction.ActionModule (ring F) (Group.{u} p r))]
  /-- Cokernels for the original zero maps. -/
  [cokernels : HasCokernels (CondensedAction.ActionModule (ring F) (Group.{u} p r))]

/-- Assemble abelianness using precisely the existing preadditive structure.
Source: the ordinary action category (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
instance actionAbelian [d : ActionAbelianData p r F] :
    Abelian (CondensedAction.ActionModule (ring F) (Group.{u} p r)) where
  toPreadditive := CondensedAction.actionPreadditive
  toIsNormalMonoCategory := d.normalMono
  toIsNormalEpiCategory := d.normalEpi
  has_finite_products := d.products
  has_kernels := d.kernels
  has_cokernels := d.cokernels

/-- The ordinary unbounded derived invariants context. The abelian structure uses the
existing additive structure. Its existence is asserted, not assumed, in the final theorem.
Source: the ordinary total derived invariants in the statement
(blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
class Context (p r : ℕ) (F : Type u) [NormedField F] [ActionAbelianData p r F] where
  /-- The ordinary localization at quasi-isomorphisms. -/
  [actionDerived : HasDerivedCategory.{u + 2}
    (CondensedAction.ActionModule (ring F) (Group.{u} p r))]
  /-- The normalized invariants adjunction, with its fixed-section inclusion. -/
  invariants : CondensedAction.Invariants (ring F) (Group.{u} p r)
  /-- The ordinary total right derived functor. -/
  derived : DerivedCategory (CondensedAction.ActionModule (ring F) (Group.{u} p r)) ⥤
    DerivedCategory (CondensedAction.Modules (ring F))
  /-- Its comparison from the functor on the homotopy category. -/
  unit : letI := invariants.additive
    invariants.functor.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ derived
  /-- The universal property of total right derivation at all quasi-isomorphisms. -/
  isDerived : letI := invariants.additive
    derived.IsRightDerivedFunctor unit
    (HomotopyCategory.quasiIso (CondensedAction.ActionModule (ring F) (Group.{u} p r))
      (.up ℤ))

attribute [instance_reducible, instance] Context.actionDerived

/-- The normalized invariants functor is additive by its recorded interface.
Source: ordinary derived invariants (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
instance contextAdditive [ActionAbelianData p r F] [c : Context p r F] :
    c.invariants.functor.Additive :=
  c.invariants.additive

/-- The actual ordinary total right derived functor, applied to M_F in degree zero.
Source: R Gamma_G(M_F) (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def derivedInvariants [ActionAbelianData p r F] [c : Context p r F] (d : Realization E p ℓ r F) :
    Inputs E p ℓ r ⥤ DerivedCategory (CondensedAction.Modules (ring F)) :=
  d.action ⋙ CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q ⋙
    c.derived

/-- The canonical degree-zero derived unit, using the existing total derived functor.
Source: compatibility with the inclusion of invariants
(blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def augmentation [ActionAbelianData p r F] [c : Context p r F]
    (A : CondensedAction.ActionModule (ring F) (Group.{u} p r)) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
      (c.invariants.functor.obj A)) ⟶
      c.derived.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj A)) :=
  DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex c.invariants.functor (.up ℤ) 0).inv.app A) ≫
    (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    c.unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj A)) ≫
    c.derived.map ((DerivedCategory.quotientCompQhIso _).hom.app
      ((CochainComplex.singleFunctor _ 0).obj A))

/-- Section, derived-unit and rank-zero normalizations for the comparison.
Source: the comparison clauses (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def ComparisonNormalization [ActionAbelianData p r F] [c : Context p r F]
    (d : Realization E p ℓ r F)
    (kappa : d.koszul ⋙ DerivedCategory.Q ≅ derivedInvariants E p ℓ r F d)
    (inclusion : ∀ M : Inputs E p ℓ r,
      (CochainComplex.singleFunctor _ 0).obj (c.invariants.functor.obj (d.action.obj M)) ⟶
        d.koszul.obj M) : Prop :=
  (∀ (M : Inputs E p ℓ r) (S : Profinite.{u})
    (x : CondensedAction.sectionModule (ring F) (c.invariants.functor.obj (d.action.obj M)) S)
    (I : Indices r 0) (s : S),
    LinearMap.baseChange F (fixed E p ℓ r M).subtype
      ((d.coordinates M 0 S
        (((((inclusion M).f 0).hom.hom.app (op S)).hom)
          ((((HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (c.invariants.functor.obj (d.action.obj M))).inv).hom.hom.app (op S)).hom x))
        I).down s) =
      ((d.module M).sections S
        (((c.invariants.inclusion.app (d.action.obj M)).hom.hom.app (op S)).hom x)).down s) ∧
  (∀ M : Inputs E p ℓ r,
    DerivedCategory.Q.map (inclusion M) ≫ kappa.hom.app M = augmentation p r F (d.action.obj M)) ∧
  (r = 0 → ∀ M : Inputs E p ℓ r,
    IsIso (inclusion M) ∧ IsIso (c.invariants.inclusion.app (d.action.obj M)))

/-- The comparison with its actual invariant augmentation and rank-zero normalization.
Source: all comparison clauses (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
structure Comparison [ActionAbelianData p r F] [c : Context p r F]
    (d : Realization E p ℓ r F) where
  /-- The natural derived-category isomorphism in the stated direction. -/
  kappa : d.koszul ⋙ DerivedCategory.Q ≅ derivedInvariants E p ℓ r F d
  /-- The inclusion of invariant sections, placed in degree zero. -/
  inclusion : ∀ M : Inputs E p ℓ r,
    (CochainComplex.singleFunctor _ 0).obj (c.invariants.functor.obj (d.action.obj M)) ⟶
      d.koszul.obj M
  /-- All three normalizations, including the literal section formula. -/
  normalization : ComparisonNormalization E p ℓ r F d kappa inclusion

/-- Postcomposition along the field inclusion, using the recorded continuous ring map.
Source: C_E to C_Omega (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def coefficientMap (Ω : Type u) [NormedField Ω] [Algebra E Ω]
    (h : Continuous (algebraMap E Ω)) : ring E ⟶ ring Ω := by
  letI := isMonHom_continuousMapRingObjMapOfUniverse (algebraMap E Ω) h
  exact Mon.Hom.mk (continuousMapRingObjMapOfUniverse (algebraMap E Ω) h)

/-- The actual restriction of internal scalars for the continuous field inclusion.
Source: the Res in the coefficient square
(blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def coefficientRestriction (Ω : Type u) [NormedField Ω] [Algebra E Ω]
    (h : Continuous (algebraMap E Ω)) :
    CondensedAction.Modules (ring Ω) ⥤ CondensedAction.Modules (ring E) :=
  Mod.comap (coefficientMap E Ω h).hom


variable (Ω : Type u) [NormedField Ω] [Algebra E Ω]
  (h : Continuous (algebraMap E Ω))
  [ActionAbelianData p r E] [ActionAbelianData p r Ω]
  [cE : Context p r E] [cΩ : Context p r Ω]

/-- Ordinary exact scalar restriction, including its action and invariant normalizations.
Its existence is a conclusion, rather than an additional hypothesis of the main theorem.
Source: the coefficient square (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
class ScalarRestriction where
  /-- Restrict scalars on the actual internal action category. -/
  action : CondensedAction.ActionModule (ring Ω) (Group.{u} p r) ⥤
    CondensedAction.ActionModule (ring E) (Group.{u} p r)
  /-- Ordinary module restriction is additive. -/
  [moduleAdditive : (coefficientRestriction E Ω h).Additive]
  /-- Ordinary module restriction is left exact. -/
  [moduleLimits : PreservesFiniteLimits (coefficientRestriction E Ω h)]
  /-- Ordinary module restriction is right exact. -/
  [moduleColimits : PreservesFiniteColimits (coefficientRestriction E Ω h)]
  /-- Action restriction is additive. -/
  [actionAdditive : action.Additive]
  /-- Action restriction is left exact. -/
  [actionLimits : PreservesFiniteLimits action]
  /-- Action restriction is right exact. -/
  [actionColimits : PreservesFiniteColimits action]
  /-- The underlying module is the recorded ordinary scalar restriction. -/
  underlying : action ⋙ CondensedAction.forgetAction ≅
    CondensedAction.forgetAction ⋙ coefficientRestriction E Ω h
  /-- This identification preserves every local group action. -/
  action_sections : ∀ (A : CondensedAction.ActionModule (ring Ω) (Group.{u} p r))
    (S : Profinite.{u}) (g : C(S, Group.{u} p r))
    (x : CondensedAction.sectionModule (ring E) (action.obj A).module S),
    (((underlying.hom.app A).hom.hom.app (op S)).hom ((action.obj A).act S g x)) =
      A.act S g (((underlying.hom.app A).hom.hom.app (op S)).hom x)
  /-- Invariants of the restricted action are exactly restricted invariants. -/
  invariants : action ⋙ cE.invariants.functor ≅
    cΩ.invariants.functor ⋙ coefficientRestriction E Ω h
  /-- The invariant identification preserves the actual inclusions. -/
  invariants_inclusion : ∀ A,
    invariants.hom.app A ≫ (coefficientRestriction E Ω h).map
      (cΩ.invariants.inclusion.app A) =
      cE.invariants.inclusion.app (action.obj A) ≫ underlying.hom.app A

attribute [instance] ScalarRestriction.moduleAdditive
  ScalarRestriction.moduleLimits ScalarRestriction.moduleColimits
  ScalarRestriction.actionAdditive ScalarRestriction.actionLimits ScalarRestriction.actionColimits

variable [s : ScalarRestriction E p r Ω h]

/-- The derived unit for first restricting the action and then taking derived invariants.
Source: canonical coefficient comparison
(blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def restrictionDerivedUnit :
    (s.action ⋙ cE.invariants.functor).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (s.action.mapDerivedCategory ⋙ cE.derived) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (s.action ⋙ cE.invariants.functor)) (.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (s.action.mapHomotopyCategory (.up ℤ)) cE.unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight s.action.mapDerivedCategoryFactorsh.inv cE.derived ≫
    (Functor.associator _ _ _).hom

/-- The target unit, transporting invariant sections by the normalized coefficient map.
Source: canonical coefficient comparison
(blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def restrictionTargetUnit :
    (s.action ⋙ cE.invariants.functor).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        (cΩ.derived ⋙ (coefficientRestriction E Ω h).mapDerivedCategory) :=
  Functor.whiskerRight (NatTrans.mapHomotopyCategory s.invariants.hom (.up ℤ)) DerivedCategory.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (cΩ.invariants.functor ⋙ coefficientRestriction E Ω h)) (.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (cΩ.invariants.functor.mapHomotopyCategory (.up ℤ))
      (coefficientRestriction E Ω h).mapDerivedCategoryFactorsh.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight cΩ.unit (coefficientRestriction E Ω h).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- The universal property that makes coefficient restriction a derived comparison.
This is asserted to exist in the theorem, and supplies no additional representation hypothesis.
Source: ordinary scalar restriction in the coefficient square
(blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
class RestrictionUniversal : Prop where
  /-- Exact restriction followed by derived invariants is the ordinary right derived functor. -/
  universal : (s.action.mapDerivedCategory ⋙ cE.derived).IsRightDerivedFunctor
    (restrictionDerivedUnit E p r Ω h)
    (HomotopyCategory.quasiIso (CondensedAction.ActionModule (ring Ω) (Group.{u} p r))
      (.up ℤ))

/-- The canonical derived coefficient transformation, defined by the derived universal property.
Source: the induced coefficient map (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def derivedCoefficient [RestrictionUniversal E p r Ω h] :
    s.action.mapDerivedCategory ⋙ cE.derived ⟶
      cΩ.derived ⋙ (coefficientRestriction E Ω h).mapDerivedCategory := by
  letI := RestrictionUniversal.universal (E := E) (p := p) (r := r) (Ω := Ω) (h := h)
  exact (s.action.mapDerivedCategory ⋙ cE.derived).rightDerivedDesc
    (restrictionDerivedUnit E p r Ω h)
    (HomotopyCategory.quasiIso (CondensedAction.ActionModule (ring Ω) (Group.{u} p r))
      (.up ℤ))
    (cΩ.derived ⋙ (coefficientRestriction E Ω h).mapDerivedCategory)
    (restrictionTargetUnit E p r Ω h)

/-- The literal algebraic scalar inclusion; no completion or coefficient union occurs.
Source: m maps to 1 tensor m (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def extension (V : Type u) [AddCommGroup V] [Module E V] :
    Space E E V → Space E Ω V :=
  TensorProduct.map (Algebra.linearMap E Ω) (LinearMap.id : V →ₗ[E] V)

/-- The two literal coefficient maps, normalized on all sections and every Koszul coordinate.
Source: the coefficient inclusions (blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
structure CoefficientMaps (dE : Realization E p ℓ r E) (dΩ : Realization E p ℓ r Ω) where
  /-- The map on internal action modules. -/
  action : dE.action ⟶ dΩ.action ⋙ s.action
  /-- The termwise map of cochain complexes. -/
  koszul : dE.koszul ⟶ dΩ.koszul ⋙
    (coefficientRestriction E Ω h).mapHomologicalComplex (.up ℤ)
  /-- The action-module map is literally the scalar inclusion. -/
  action_sections : ∀ (M : Inputs E p ℓ r) (S : Profinite.{u})
    (x : CondensedAction.sectionModule (ring E) (dE.action.obj M).module S) (t : S),
    ((dΩ.module M).sections S
      (((s.underlying.hom.app (dΩ.action.obj M)).hom.hom.app (op S)).hom
        ((((action.app M).val).hom.hom.app (op S)).hom x))).down t =
      extension E Ω M.obj.V (((dE.module M).sections S x).down t)
  /-- Every finite subset coordinate is sent by the same inclusion. -/
  koszul_sections : ∀ (M : Inputs E p ℓ r) (a : ℤ) (S : Profinite.{u})
    (x : CondensedAction.sectionModule (ring E) ((dE.koszul.obj M).X a) S)
    (I : Indices r a) (t : S),
    (dΩ.coordinates M a S
      (((((koszul.app M).f a).hom.hom.app (op S)).hom x)) I).down t =
      extension E Ω (fixed E p ℓ r M) ((dE.coordinates M a S x I).down t)

variable [RestrictionUniversal E p r Ω h]

/-- The derived map induced by the literal representation inclusion and the canonical
scalar-restriction comparison, with the degree-zero and exact-functor transports explicit.
Source: the right vertical map of the square
(blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def representationCoefficient (dE : Realization E p ℓ r E) (dΩ : Realization E p ℓ r Ω)
    (m : CoefficientMaps E p ℓ r Ω h dE dΩ) (M : Inputs E p ℓ r) :
    (derivedInvariants E p ℓ r E dE).obj M ⟶
      (coefficientRestriction E Ω h).mapDerivedCategory.obj
        ((derivedInvariants E p ℓ r Ω dΩ).obj M) :=
  cE.derived.map
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map (m.action.app M)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex s.action (.up ℤ) 0).inv.app
          (dΩ.action.obj M)) ≫
      s.action.mapDerivedCategoryFactors.inv.app
        ((CochainComplex.singleFunctor _ 0).obj (dΩ.action.obj M))) ≫
    (derivedCoefficient E p r Ω h).app
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (dΩ.action.obj M)))

/-- The full coefficient square in the ordinary derived category.
Source: compatibility of kappa_E and kappa_Omega
(blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
def CoefficientSquare (dE : Realization E p ℓ r E) (dΩ : Realization E p ℓ r Ω)
    (bE : Comparison E p ℓ r E dE) (bΩ : Comparison E p ℓ r Ω dΩ)
    (m : CoefficientMaps E p ℓ r Ω h dE dΩ) : Prop :=
  ∀ M : Inputs E p ℓ r,
    bE.kappa.hom.app M ≫ representationCoefficient E p ℓ r Ω h dE dΩ m M =
      DerivedCategory.Q.map (m.koszul.app M) ≫
        (coefficientRestriction E Ω h).mapDerivedCategoryFactors.inv.app (dΩ.koszul.obj M) ≫
        (coefficientRestriction E Ω h).mapDerivedCategory.map (bΩ.kappa.hom.app M)

/-- The complete conclusion, existentially packaging normalized models and derived comparisons.
All data are fixed by section formulas or universal properties up to the isomorphism used;
no arbitrary scalar map or choice of coefficient sheaf is admitted.
Source: the whole tame-inertia assertion
(blueprint: lem-sfb-tame-inertia-continuous-koszul). -/
structure Result (E : Type u) [NormedField E] (p ℓ r : ℕ)
    (Ω : Type u) [NormedField Ω] [Algebra E Ω] (h : Continuous (algebraMap E Ω)) where
  /-- Abelianness of the actual E-action category. -/
  [abelianE : ActionAbelianData p r E]
  /-- Abelianness of the actual Omega-action category. -/
  [abelianΩ : ActionAbelianData p r Ω]
  /-- Ordinary total derived invariants over E. -/
  [contextE : Context p r E]
  /-- Ordinary total derived invariants over Omega. -/
  [contextΩ : Context p r Ω]
  /-- Exact coefficient restriction with its normalized local actions. -/
  [restriction : ScalarRestriction E p r Ω h]
  /-- The universal property used to define the canonical comparison. -/
  [restrictionUniversal : RestrictionUniversal E p r Ω h]
  /-- The invariant submodule is exactly the image of the displayed finite average. -/
  average_range : ∀ M : Inputs E p ℓ r,
    fixed E p ℓ r M = LinearMap.range (average E p ℓ r M)
  /-- All-continuous E coefficients and the signed Koszul complex. -/
  modelE : Realization E p ℓ r E
  /-- All-continuous Omega coefficients and the signed Koszul complex. -/
  modelΩ : Realization E p ℓ r Ω
  /-- The natural derived isomorphism over E, with its normalizations. -/
  comparisonE : Comparison E p ℓ r E modelE
  /-- The natural derived isomorphism over Omega, with its normalizations. -/
  comparisonΩ : Comparison E p ℓ r Ω modelΩ
  /-- The literal coefficient inclusions. -/
  maps : CoefficientMaps E p ℓ r Ω h modelE modelΩ
  /-- The prescribed derived coefficient square commutes. -/
  coefficientSquare : CoefficientSquare E p ℓ r Ω h modelE modelΩ comparisonE comparisonΩ maps

end Profinite.TameInertiaKoszul

universe v

/-- The all-continuous tame-inertia Koszul calculation, with both coefficient fields,
the natural derived isomorphisms, invariant normalization, coefficient square and rank zero.
Source: main-20261015, direct-image stability, paragraph (3), analytic tame-boundary input
(blueprint: lem-sfb-tame-inertia-continuous-koszul).

Proof plan: average over the finite prime-to-ell image to obtain N=M^H=im(e).
The commuting ell-generators preserve N. Apply
lem-sfb-prime-to-ell-derived-invariants-reduction to remove H, then
lem-sfb-dense-lattice-derived-invariants-comparison to restrict Z_ell^r to Z^r.
Apply lem-sfb-discrete-lattice-koszul-resolution with increasing-subset coordinates;
the position of the omitted generator is the number of smaller indices, giving the sign.
Compose the reduction isomorphism, inverse lattice comparison, and Koszul isomorphism.
Their invariant normalizations give the stated derived unit equation. Their three
coefficient squares, with the middle square inverted, give the full coefficient square
for the literal algebraic inclusions. At rank zero all three normalized maps are
identities. All objects throughout use all continuous functions in the norm topology;
there is no completion and no union of finite coefficient fields.
The existence of the normalized internal models and ordinary derived contexts is
included in the conclusion, rather than imposed as an extra hypothesis.
-/
theorem Profinite.TameInertiaKoszul.continuous_koszul
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_distinct : p ≠ ℓ)
    (k : Type v) [Field k] [CharP k p]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω]
    [IsAlgClosure ℚ_[ℓ] Ω] (E : IntermediateField ℚ_[ℓ] Ω)
    [FiniteDimensional ℚ_[ℓ] E] (r : ℕ) :
    Nonempty (Profinite.TameInertiaKoszul.Result E p ℓ r Ω continuous_subtype_val) := by
  sorry
