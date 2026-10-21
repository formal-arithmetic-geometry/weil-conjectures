/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Continuous representations as internal condensed modules

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
continuous-representation coefficients (blueprint: def-sfb-continuous-representation-condensation).

A realization is specified on every profinite test object, including scalar action,
restriction and generalized group action. Its section identifications prevent replacing
continuous functions by locally constant functions. No realization is chosen from an
uncharacterized existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace Profinite.CondensedAction.ContinuousRepresentation

open AlgebraicGeometry.ProEtale

variable (F : Type u) [NormedField F]

variable (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  (V : Type (u + 1)) [AddCommGroup V] [Module F V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul F V]
  (ρ : Representation F P V)

/-- The continuous-section realization of a representation. Every structure map is
specified on sections; the additive equivalences identify the actual continuous maps.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
structure Realization where
  /-- The internal module equipped with its condensed-group action. -/
  object : ActionModule (normContinuousRing F) P
  /-- Its additive sections are precisely all continuous maps into V. -/
  sections (S : Profinite.{u}) : sectionModule (normContinuousRing F) object.module S ≃+
    ULift.{u + 1} C(S, V)
  /-- Pointwise scalar multiplication, over the original continuous-map coefficient ring. -/
  scalar (S : Profinite.{u})
      (r : (InternalAbelianSheafModule.sectionRings
        (coherentTopology Profinite.{u}) (normContinuousRing F).X).obj (op S))
      (m : sectionModule (normContinuousRing F) object.module S) (s : S) :
    (sections S (r • m)).down s = r.down s • (sections S m).down s
  /-- Restriction is precomposition. -/
  restriction (S T : Profinite.{u}) (f : T ⟶ S)
      (m : sectionModule (normContinuousRing F) object.module S) (t : T) :
    (sections T ((object.module.X.obj.map f.op).hom m)).down t =
      (sections S m).down (f t)
  /-- The group action is the given joint continuous action, pointwise. -/
  action (S : Profinite.{u}) (g : C(S, P))
      (m : sectionModule (normContinuousRing F) object.module S) (s : S) :
    (sections S (object.act S g m)).down s = ρ (g s) ((sections S m).down s)

/-- Every joint continuous linear action has its continuous-section realization.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).

Proof: form the presheaf with section modules ULift C(S,V), pointwise C(S,F)-action,
and precomposition restrictions. A finite coproduct of profinite sets turns sections
into a finite product; a surjection is a quotient map and continuous maps descend
uniquely along it. Thus this is a module sheaf. Apply the inverse of
`InternalAbelianSheafModule.sectionModuleEquivalence` to obtain the internal module.
Its counit gives the section identifications, intertwining scalars and restrictions.
Joint continuity makes s mapping to rho(g(s))(v(s)) continuous. Transport these
linear actions through the counit. The representation laws give the monoid homomorphism
and naturality under every base change, including the empty profinite set. -/
theorem exists_realization
    (_hρ : Continuous (fun x : P × V ↦ ρ x.1 x.2)) :
    Nonempty (Realization F P V ρ) := by
  sorry

variable {F P V ρ}

/-- A map between continuous realizations is characterized by its actual section formula.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def RepresentsMap {W : Type (u + 1)} [AddCommGroup W] [Module F W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul F W] {σ : Representation F P W}
    (M : Realization F P V ρ) (N : Realization F P W σ)
    (f : V →ₗ[F] W) (g : M.object ⟶ N.object) : Prop :=
  ∀ (S : Profinite.{u}) (m : sectionModule (normContinuousRing F) M.object.module S) (s : S),
    (N.sections S ((g.val.hom.hom.app (op S)).hom m)).down s =
      f ((M.sections S m).down s)

/-- Continuous equivariant linear maps induce unique morphisms of realizations.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).

Proof: postcomposition by f is continuous and sectionwise C(S,F)-linear. It commutes
with restriction and, by equivariance, with generalized group elements. Transport it
through the two section identifications and the fully faithful internal-module
section functor. Uniqueness follows by evaluating on every section of every test
object. Consequently identities, compositions and additions are preserved. -/
theorem exists_unique_map {W : Type (u + 1)} [AddCommGroup W] [Module F W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul F W]
    {σ : Representation F P W} (M : Realization F P V ρ) (N : Realization F P W σ)
    (f : V →ₗ[F] W) (_hf : Continuous f)
    (_heq : ∀ (p : P) (v : V), f (ρ p v) = σ p (f v)) :
    ∃! g : M.object ⟶ N.object, RepresentsMap M N f g := by
  sorry

/-- The morphism determined uniquely by postcomposition on every continuous section.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def map {W : Type (u + 1)} [AddCommGroup W] [Module F W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul F W] {σ : Representation F P W}
    (M : Realization F P V ρ) (N : Realization F P W σ) (f : V →ₗ[F] W)
    (hf : Continuous f) (heq : ∀ (p : P) (v : V), f (ρ p v) = σ p (f v)) :
    M.object ⟶ N.object :=
  Classical.choose (exists_unique_map M N f hf heq).exists

/-- Restriction keeps the realization and its sections and precomposes the group action.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def Realization.inflate {Q : Type u} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] {σ : Representation F Q V}
    (M : Realization F Q V σ) (π : P →ₜ* Q) :
    Realization F P V (σ.comp π.toMonoidHom) where
  object := (CondensedAction.inflate (R := normContinuousRing F) π).obj M.object
  sections := M.sections
  scalar := M.scalar
  restriction := M.restriction
  action S g m s := M.action S (π.toContinuousMap.comp g) m s

section ScalarMaps
variable (F)

/-- Bundle the existing norm-continuous ring with its existing commutativity proof.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def coefficientRing : CategoryTheory.CondensedBar.Ring.{u} :=
  { X := (normContinuousRing F).X }

variable {K : Type u} [NormedField K] (φ : F →+* K) (hφ : Continuous φ)

/-- The recorded continuous-map ring morphism, with commutativity bundled.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def coefficientRingMap : coefficientRing F ⟶ coefficientRing K :=
  CommMon.homMk {
    hom := continuousMapRingObjMapOfUniverse φ hφ
    isMonHom_hom := isMonHom_continuousMapRingObjMapOfUniverse φ hφ }

variable {F}

/-- Scalar-changing maps have the specified pointwise section formula after the
normalized underlying scalar-restriction identification.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def RepresentsScalarMap {W : Type (u + 1)} [AddCommGroup W] [Module K W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul K W]
    {σ : Representation K P W} (M : Realization F P V ρ) (N : Realization K P W σ)
    (s : CategoryTheory.CondensedBar.ScalarAction (coefficientRingMap F φ hφ) P)
    (f : V →+ W) (g : M.object ⟶ s.functor.obj N.object) : Prop :=
  ∀ (S : Profinite.{u}) (m : sectionModule (normContinuousRing F) M.object.module S)
      (t : S),
    (N.sections S (((g.val ≫ s.underlying.hom.app N.object).hom.hom.app (op S)).hom m)).down t =
      f ((M.sections S m).down t)

/-- Continuous semilinear equivariant maps induce uniquely characterized scalar-changing
maps of continuous realizations.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).

Proof: postcompose continuous sections by f. The scalar equation makes this linear
for the section ring map given by postcomposition with phi. Transport through the
section equivalences and the normalized underlying scalar-action comparison. The
ScalarAction.action equation and equivariance give an action morphism. Restriction
naturality is pointwise precomposition. The section functor is fully faithful, so
this constructs a unique morphism, including on the empty test object. -/
theorem exists_unique_scalarMap {W : Type (u + 1)} [AddCommGroup W] [Module K W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul K W]
    {σ : Representation K P W} (M : Realization F P V ρ) (N : Realization K P W σ)
    (s : CategoryTheory.CondensedBar.ScalarAction (coefficientRingMap F φ hφ) P)
    (f : V →+ W) (_hf : Continuous f)
    (_hscalar : ∀ (a : F) (v : V), f (a • v) = φ a • f v)
    (_heq : ∀ (p : P) (v : V), f (ρ p v) = σ p (f v)) :
    ∃! g : M.object ⟶ s.functor.obj N.object, RepresentsScalarMap φ hφ M N s f g := by
  sorry

/-- The unique scalar-changing morphism with its prescribed continuous section formula.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def scalarMap {W : Type (u + 1)} [AddCommGroup W] [Module K W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul K W]
    {σ : Representation K P W} (M : Realization F P V ρ) (N : Realization K P W σ)
    (s : CategoryTheory.CondensedBar.ScalarAction (coefficientRingMap F φ hφ) P)
    (f : V →+ W) (hf : Continuous f)
    (hscalar : ∀ (a : F) (v : V), f (a • v) = φ a • f v)
    (heq : ∀ (p : P) (v : V), f (ρ p v) = σ p (f v)) :
    M.object ⟶ s.functor.obj N.object :=
  Classical.choose (exists_unique_scalarMap φ hφ M N s f hf hscalar heq).exists

end ScalarMaps

end Profinite.CondensedAction.ContinuousRepresentation

namespace Profinite.CondensedAction.PrimeToEll

section Representations
variable (E F : Type u) [Field E] [Field F] [Algebra E F]
  (V : Type (u + 1)) [AddCommGroup V] [Module E V]

/-- Scalar extension with its finite-dimensional module topology. The underlying module
is the recorded algebraic tensor product; the copy pins its topology without altering
any pre-existing topology instance on tensor products.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def Extended := F ⊗[E] V

/-- The original additive structure on scalar extension.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
@[instance_reducible]
instance extendedAdd : AddCommGroup (Extended E F V) :=
  inferInstanceAs (AddCommGroup (F ⊗[E] V))

/-- The original F-module structure on scalar extension.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
@[instance_reducible]
instance extendedModule : Module F (Extended E F V) :=
  inferInstanceAs (Module F (F ⊗[E] V))

/-- The original restricted E-module on the tensor product.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
@[instance_reducible]
instance extendedRestrictModule : Module E (Extended E F V) :=
  inferInstanceAs (Module E (F ⊗[E] V))

/-- The actual scalar tower on the tensor product.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
instance extendedScalarTower : IsScalarTower E F (Extended E F V) :=
  inferInstanceAs (IsScalarTower E F (F ⊗[E] V))

variable [TopologicalSpace F]

/-- Finite-dimensional product topology, without any completion of F.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
@[instance_reducible]
instance extendedTopology : TopologicalSpace (Extended E F V) :=
  moduleTopology F (Extended E F V)

/-- The topology is by construction the module topology.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
instance extendedModuleTopology : IsModuleTopology F (Extended E F V) := ⟨rfl⟩

/-- Topological addition and negation in the specified module topology.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
instance extendedTopologicalAddGroup [IsTopologicalRing F] :
    IsTopologicalAddGroup (Extended E F V) :=
  IsModuleTopology.topologicalAddGroup F _

variable (P : Type u) [Group P] (ρ : Representation E P V)

/-- The extended action sends a pure tensor a tensor v to a tensor rho(p)v.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def extendedRepresentation : Representation F P (Extended E F V) :=
  (Module.End.baseChangeHom E F V).toMonoidHom.comp ρ

variable {E V} (B L : Type u) [Group B] [Group L]

/-- The ordinary E-linear B-fixed subspace, using Mathlib invariants.
It carries the induced subspace topology when V is topological.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
abbrev fixedSpace (ρ : Representation E (B × L) V) :=
  Representation.invariants (ρ.comp (MonoidHom.inl B L))

/-- The commuting L-action preserves B-fixed vectors.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).

Proof: for b in B and l in L, (b,1)(1,l)=(1,l)(b,1). Apply the representation
law and the defining equation rho(b,1)v=v. This works for the zero subspace. -/
theorem fixed_stable (ρ : Representation E (B × L) V) :
    ∀ l : L, fixedSpace B L ρ ≤ (fixedSpace B L ρ).comap (ρ (1, l)) := by
  sorry

/-- Restriction to the actual fixed subspace, with its residual L-action.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def fixedRepresentation (ρ : Representation E (B × L) V) :
    Representation E L (fixedSpace B L ρ) :=
  Representation.subrepresentation (ρ.comp (MonoidHom.inr B L)) (fixedSpace B L ρ)
    (fixed_stable B L ρ)

/-- The scalar-extended inclusion of the invariant subspace.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def fixedInclusion (ρ : Representation E (B × L) V) :
    Extended E F (fixedSpace B L ρ) →ₗ[F] Extended E F V :=
  (fixedSpace B L ρ).subtype.baseChange F

/-- The invariant inclusion intertwines projection inflation with the original action.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).

Proof: on a pure tensor a tensor v, write (b,l)=(1,l)(b,1) and use fixedness
of v. Both maps are F-linear, so tensor induction proves the formula on all tensors. -/
theorem fixedInclusion_equivariant (ρ : Representation E (B × L) V) :
    ∀ (p : B × L) (v : Extended E F (fixedSpace B L ρ)),
      fixedInclusion F B L ρ
        (extendedRepresentation E F (fixedSpace B L ρ) L (fixedRepresentation B L ρ) p.2 v) =
      extendedRepresentation E F V (B × L) ρ p (fixedInclusion F B L ρ v) := by
  sorry

/-- An equivariant linear map sends B-fixed vectors to B-fixed vectors.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).
Proof: for a fixed vector v, equivariance gives rho'(b,1)f(v)=f(rho(b,1)v)=f(v).
This is precisely membership in the target invariant subspace. -/
theorem mapFixed_mem {V' : Type (u + 1)} [AddCommGroup V'] [Module E V']
    (σ : Representation E (B × L) V) (σ' : Representation E (B × L) V')
    (f : V →ₗ[E] V') (heq : ∀ (p : B × L) (v : V), f (σ p v) = σ' p (f v))
    (v : fixedSpace B L σ) : f v ∈ fixedSpace B L σ' := by
  sorry

/-- Restriction of an equivariant map to the actual B-fixed subspaces.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def fixedMap {V' : Type (u + 1)} [AddCommGroup V'] [Module E V']
    (σ : Representation E (B × L) V) (σ' : Representation E (B × L) V')
    (f : V →ₗ[E] V') (heq : ∀ (p : B × L) (v : V), f (σ p v) = σ' p (f v)) :
    fixedSpace B L σ →ₗ[E] fixedSpace B L σ' :=
  (f.comp (fixedSpace B L σ).subtype).codRestrict (fixedSpace B L σ')
    (mapFixed_mem B L σ σ' f heq)

/-- Coefficient insertion on scalar-extended vectors: a tensor v maps to a tensor v,
where a is carried by the E-algebra map. Under E tensor V = V this is v to 1 tensor v.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation). -/
def scalarInsertion (V : Type (u + 1)) [AddCommGroup V] [Module E V] :
    Extended E E V →ₗ[E] Extended E F V :=
  TensorProduct.map (Algebra.linearMap E F) (LinearMap.id : V →ₗ[E] V)

/-- Scalar insertion intertwines the two representations on the nose.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).
Proof: on a tensor a tensor v, both composites give the image of a tensor rho(p)v.
Tensor induction proves the equality, including for zero vectors and zero modules. -/
theorem scalarInsertion_equivariant : ∀ (p : P) (v : Extended E E V),
    scalarInsertion F V (extendedRepresentation E E V P ρ p v) =
      extendedRepresentation E F V P ρ p (scalarInsertion F V v) := by
  sorry

/-- Scalar insertion commutes with the actual fixed-space inclusion.
Source: paragraph (3) (blueprint: def-sfb-continuous-representation-condensation).
Proof: tensor functoriality reduces the equation to a pure tensor. Both maps take
a tensor v in the fixed subspace to the image of a tensor its inclusion in V. -/
theorem scalarInsertion_fixed (σ : Representation E (B × L) V) :
    (scalarInsertion F V).comp (fixedInclusion E B L σ) =
      ((fixedInclusion F B L σ).restrictScalars E).comp
        (scalarInsertion F (fixedSpace B L σ)) := by
  sorry

end Representations

end Profinite.CondensedAction.PrimeToEll
