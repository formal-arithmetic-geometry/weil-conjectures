/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Continuous realization of integral finite scalar models

Source: Hemo--Richarz--Scholbach, Example 3.1 and Remark 3.2, with the finite-presentation
and compact-reduction argument recorded in the DAG
(blueprint: lem-sfb-profinite-integral-scalar-realization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.Obj

namespace Profinite.IntegralScalar

/-- The profinite slice with finite jointly surjective covers.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-integral-scalar-realization). -/
abbrev topology (P : Profinite.{u}) := (coherentTopology Profinite.{u}).over P

/-- The discrete constant abelian sheaf; universe lifting changes no sections.
Source: HRS Remark 3.2 (blueprint: lem-sfb-profinite-integral-scalar-realization). -/
abbrev constant (P : Profinite.{u}) (B : Type u) [AddCommGroup B] :=
  (constantSheaf (topology P) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} B))

/-- The canonical constant section, from the unit of sheafification.
Source: HRS Remark 3.2 (blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def constantSection (P : Profinite.{u}) (B : Type u) [AddCommGroup B]
    (Q : Over P) (b : B) : (constant P B).obj.obj (op Q) :=
  (toSheafify (topology P)
    ((Functor.const (Over P)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))).app
      (op Q) (ULift.up b)

/-- The constant scalar ring object with its monoidal constant-sheaf structure.
Source: HRS Remark 3.2 (blueprint: lem-sfb-profinite-integral-scalar-realization). -/
instance constantMonObj (P : Profinite.{u}) (O : Type u) [CommRing O] :
    MonObj (constant P O) :=
  Sheaf.monObj_presheafToSheaf_obj (topology P)
    ((Functor.const (Over P)ᵒᵖ).obj (RingCat.of (ULift.{u + 1} O)) ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})

/-- Commutativity of the constant scalar ring is inherited under sheafification.
Source: HRS Remark 3.2 (blueprint: lem-sfb-profinite-integral-scalar-realization). -/
instance constantIsCommMonObj (P : Profinite.{u}) (O : Type u) [CommRing O] :
    IsCommMonObj (constant P O) := by
  let A := (Functor.const (Over P)ᵒᵖ).obj (RingCat.of (ULift.{u + 1} O))
  have := A.isCommMonObj_compForget₂
    (fun _ a b ↦ @mul_comm (ULift.{u + 1} O) inferInstance a b)
  exact Sheaf.isCommMonObj_presheafToSheaf_obj (topology P)
    (A ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})

/-- Continuous scalar functions restricted to the slice.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-integral-scalar-realization). -/
abbrev ring (P : Profinite.{u}) (O : Type u) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] :=
  ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P).obj
    (continuousMapRingObjOfUniverse.{u, u} O)

/-- The restricted pointwise ring structure.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-integral-scalar-realization). -/
instance ringMonObj (P : Profinite.{u}) (O : Type u) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] : MonObj (ring P O) := by
  letI := continuousMapRingObjOfUniverseMonObj.{u, u} O
  exact ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P).monObjObj _

/-- The actual submodule of multiples of the positive uniformizer power.
Source: the node's reduction construction
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def power (O : Type u) [CommRing O] (π : O) (B : Type u) [AddCommGroup B]
    [Module O B] (k : ℕ) : Submodule O B :=
  LinearMap.range (LinearMap.lsmul O B (π ^ (k + 1)))

/-- Positive-level reduction, with exponent k+1 so that every positive level occurs.
Source: the node's reduction construction
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
abbrev residue (O : Type u) [CommRing O] (π : O) (B : Type u) [AddCommGroup B]
    [Module O B] (k : ℕ) := B ⧸ power O π B k

/-- The actual quotient transition, induced by the identity on B.
Source: the node's actual quotient transitions
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def transition (O : Type u) [CommRing O] (π : O) (B : Type u) [AddCommGroup B]
    [Module O B] (k : ℕ) : residue O π B (k + 1) →ₗ[O] residue O π B k :=
  (power O π B (k + 1)).mapQ (power O π B k) LinearMap.id (by
    rintro x ⟨b, rfl⟩
    refine ⟨π • b, ?_⟩
    simp only [LinearMap.lsmul_apply, LinearMap.id_apply, ← mul_smul]
    simp only [← pow_succ])

/-- Reduction of a linear map, with no choices of quotient identifications.
Source: the node's finite bundle reductions
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def reduce (O : Type u) [CommRing O] (π : O) {B D : Type u}
    [AddCommGroup B] [Module O B] [AddCommGroup D] [Module O D]
    (f : B →ₗ[O] D) (k : ℕ) : residue O π B k →ₗ[O] residue O π D k :=
  (power O π B k).mapQ (power O π D k) f (by
    rintro x ⟨b, rfl⟩
    exact ⟨f b, (f.map_smul (π ^ (k + 1)) b).symm⟩)

/-- The presheaf pure tensor's canonical image in a sheaf tensor.
Source: HRS Remark 3.2 (blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def generator (P : Profinite.{u}) (F G : Sheaf (topology P) Ab.{u + 1})
    (Q : Over P) (x : F.obj.obj (op Q)) (y : G.obj.obj (op Q)) :
    (F ⊗ G).obj.obj (op Q) :=
  (Functor.LaxMonoidal.μ (sheafToPresheaf (topology P) Ab.{u + 1}) F G).app
    (op Q) (x ⊗ₜ[ℤ] y)

/-- Coordinates identify the discrete constant module, including its scalar action.
The action equation on constant generators determines it after sheafification.
Source: HRS Remark 3.2 (blueprint: lem-sfb-profinite-integral-scalar-realization). -/
structure ConstantCoordinates (P : Profinite.{u}) (O B : Type u) [CommRing O]
    [AddCommGroup B] [Module O B]
    (M : Mod (Sheaf (topology P) Ab.{u + 1}) (constant P O)) where
  /-- The underlying sheaf is the actual discrete constant sheaf. -/
  iso : M.X ≅ constant P B
  /-- The ordinary O-action on constant sections. -/
  action : ∀ (Q : Over P) (a : O) (b : B),
    iso.hom.hom.app (op Q)
      ((ModObj.smul (M := constant P O) (X := M.X)).hom.app (op Q)
        (generator P (constant P O) M.X Q (constantSection P O Q a)
          (iso.inv.hom.app (op Q) (constantSection P B Q b)))) =
      constantSection P B Q (a • b)

/-- Coordinates for continuous functions, their precomposition restrictions and pointwise action.
This specifies the ordinary internal module, with no completion or arbitrary module action.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-integral-scalar-realization). -/
structure ContinuousCoordinates (P : Profinite.{u}) (O B : Type u) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [AddCommGroup B] [Module O B]
    [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul O B]
    (M : Mod (Sheaf (topology P) Ab.{u + 1}) (ring P O)) where
  /-- Continuous sections, with their pointwise addition. -/
  sections : ∀ Q : Over P, M.X.obj.obj (op Q) ≃+ C(Q.left, B)
  /-- Restriction along an actual map over P is precomposition. -/
  restriction : ∀ (Q T : Over P) (f : T ⟶ Q) (b : M.X.obj.obj (op Q)),
    sections T (M.X.obj.map f.op b) = (sections Q b).comp f.left.hom.hom
  /-- The action of a continuous scalar function is pointwise multiplication. -/
  action : ∀ (Q : Over P) (a : C(Q.left, O)) (b : M.X.obj.obj (op Q)) (q : Q.left),
    sections Q ((ModObj.smul (M := ring P O) (X := M.X)).hom.app (op Q)
      (generator P (ring P O) M.X Q (ULift.up a) b)) q = a q • sections Q b q

/-- The scalar-extension comparison is normalized on 1 tensor b. Linearity then fixes
its value on every f tensor b, so the isomorphism is the canonical comparison.
Source: HRS Remark 3.2 (blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def ScalarComparison (P : Profinite.{u}) (O : Type u) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] : Prop :=
  ∃ φ : constant P O ⟶ ring P O,
    (∀ (Q : Over P) (a : O),
      (φ.hom.app (op Q) (constantSection P O Q a)).down = ContinuousMap.const Q.left a) ∧
    ∃ hφ : IsMonHom φ,
      letI := hφ
      ∀ (B : Type u) [AddCommGroup B] [Module O B] [Module.FinitePresentation O B],
      letI := moduleTopology O B
      letI := IsModuleTopology.topologicalAddGroup O B
      ∃ (M₀ : Mod (Sheaf (topology P) Ab.{u + 1}) (constant P O))
        (M : Mod (Sheaf (topology P) Ab.{u + 1}) (ring P O))
        (c₀ : ConstantCoordinates P O B M₀) (c : ContinuousCoordinates P O B M),
        ∃ e : (Mod.extendScalars φ).obj M₀ ≅ M,
          ∀ (Q : Over P) (b : B),
            c.sections Q (e.hom.hom.hom.app (op Q)
              ((Mod.extendUnitHom φ M₀).hom.app (op Q)
                (c₀.iso.inv.hom.app (op Q) (constantSection P B Q b)))) =
              ContinuousMap.const Q.left b

/-- The morphism formula on every object of the profinite slice.
Source: HRS Example 3.1 and the node's universal-section argument
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def Represents (P : Profinite.{u}) (O B D : Type u) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O]
    [AddCommGroup B] [Module O B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [ContinuousSMul O B]
    [AddCommGroup D] [Module O D] [TopologicalSpace D] [IsTopologicalAddGroup D]
    [ContinuousSMul O D]
    {M N : Mod (Sheaf (topology P) Ab.{u + 1}) (ring P O)}
    (c : ContinuousCoordinates P O B M) (d : ContinuousCoordinates P O D N)
    (v : M ⟶ N) (g : C(P × B, D)) : Prop :=
  (∀ p : P, ∃ f : B →ₗ[O] D, ∀ b : B, f b = g (p, b)) ∧
  ∀ (Q : Over P) (b : M.X.obj.obj (op Q)) (q : Q.left),
    d.sections Q (v.hom.hom.app (op Q) b) q = g (Q.hom q, c.sections Q b q)

/-- The ordinary inverse limit as the submodule of genuinely compatible quotient families.
Source: the node's positive reduction tower
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def compatible (O : Type u) [CommRing O] (π : O) (B : Type u) [AddCommGroup B]
    [Module O B] : Submodule O (∀ k : ℕ, residue O π B k) where
  carrier := {b | ∀ k : ℕ, transition O π B k (b (k + 1)) = b k}
  zero_mem' := by intro k; exact map_zero (transition O π B k)
  add_mem' := by
    intro a b ha hb k
    exact (map_add (transition O π B k) _ _).trans (congrArg₂ (· + ·) (ha k) (hb k))
  smul_mem' := by
    intro a b hb k
    exact (map_smul (transition O π B k) a _).trans (congrArg (a • ·) (hb k))

/-- The canonical O-linear map to the actual quotient limit.
Source: the node's compact-reduction reconstruction
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def limitMap (O : Type u) [CommRing O] (π : O) (B : Type u) [AddCommGroup B]
    [Module O B] : B →ₗ[O] compatible O π B where
  toFun b := ⟨fun k ↦ (power O π B k).mkQ b, fun _ ↦ rfl⟩
  map_add' a b := Subtype.ext (funext fun k ↦ (power O π B k).mkQ.map_add a b)
  map_smul' a b := Subtype.ext (funext fun k ↦ (power O π B k).mkQ.map_smul a b)

/-- Presentation-independent profinite topology and the canonical positive reduction limit.
The limit topology is the subspace topology from the product of the quotient modules.
Source: the node's finite-presentation supplement to HRS Example 3.1
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def TopologyStatement (O : Type u) [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (π : O) : Prop :=
  ∀ (B : Type u) [AddCommGroup B] [Module O B] [Module.FinitePresentation O B],
    letI := moduleTopology O B
    (∀ (n : ℕ) (q : (Fin n → O) →ₗ[O] B),
      Function.Surjective q → Topology.IsQuotientMap q) ∧
    CompactSpace B ∧ T2Space B ∧ TotallyDisconnectedSpace B ∧
    IsTopologicalAddGroup B ∧ ContinuousSMul O B ∧
    (∀ k : ℕ, Finite (residue O π B k) ∧ DiscreteTopology (residue O π B k)) ∧
    IsHomeomorph (limitMap O π B)

/-- Sections of the kernel of the family L over an actual object Q over P.
Source: the node's sectionwise kernel calculation
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
abbrev kernelSections (P : Profinite.{u}) (O : Type u) [CommRing O]
    (B D : Type u) [AddCommGroup B] [Module O B] [AddCommGroup D] [Module O D]
    [TopologicalSpace B] (L : P → B →ₗ[O] D) (Q : Over P) :=
  {b : C(Q.left, B) // ∀ q : Q.left, L (Q.hom q) (b q) = 0}

/-- The ordinary compatible sequences in the reduction kernels. Both compatibility and
vanishing use the quotient maps defined above; no surjectivity is required.
Source: the node's ordinary inverse limit of kernels
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
abbrev kernelSequences (P : Profinite.{u}) (O : Type u) [CommRing O] (π : O)
    (B D : Type u) [AddCommGroup B] [Module O B] [AddCommGroup D] [Module O D]
    [TopologicalSpace B] (L : P → B →ₗ[O] D) (Q : Over P) :=
  {b : ∀ k : ℕ, C(Q.left, residue O π B k) //
    (∀ (k : ℕ) (q : Q.left), transition O π B k (b (k + 1) q) = b k q) ∧
    (∀ (k : ℕ) (q : Q.left), reduce O π (L (Q.hom q)) k (b k q) = 0)}

/-- The canonical kernel comparison, given by actual reduction of every section.
Source: the node's compact-reduction kernel comparison
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def kernelLimitMap (P : Profinite.{u}) (O : Type u) [CommRing O] (π : O)
    (B D : Type u) [AddCommGroup B] [Module O B] [AddCommGroup D] [Module O D]
    [TopologicalSpace B] (L : P → B →ₗ[O] D) (Q : Over P) :
    kernelSections P O B D L Q → kernelSequences P O π B D L Q :=
  fun b ↦ ⟨fun k ↦ ⟨fun q ↦ (power O π B k).mkQ (b.val q),
    (power O π B k).continuous_mkQ.comp b.val.continuous⟩, by
    constructor
    · intro k q
      rfl
    · intro k q
      change (power O π D k).mkQ (L (Q.hom q) (b.val q)) = 0
      rw [b.property q, map_zero]⟩

/-- A morphism is a continuous fibrewise-linear family, unique among all families with the
morphism formula. Its finite reductions are
constant on a finite clopen partition, commute with the actual transitions, and the
canonical kernel comparison is bijective on every object's sections. Limits and kernels
of sheaves are computed sectionwise, so the last clause is precisely the sheaf isomorphism.
Source: the node's universal-section and compact-reduction arguments after HRS Example 3.1
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def MorphismStatement (P : Profinite.{u}) (O : Type u) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (π : O) : Prop :=
  ∀ (B D : Type u) [AddCommGroup B] [Module O B] [Module.FinitePresentation O B]
      [AddCommGroup D] [Module O D] [Module.FinitePresentation O D],
    letI := moduleTopology O B
    letI := moduleTopology O D
    letI := IsModuleTopology.topologicalAddGroup O B
    letI := IsModuleTopology.topologicalAddGroup O D
    ∀ (M N : Mod (Sheaf (topology P) Ab.{u + 1}) (ring P O))
      (c : ContinuousCoordinates P O B M) (d : ContinuousCoordinates P O D N) (v : M ⟶ N),
      ∃ g : C(P × B, D),
        (∀ g' : C(P × B, D), Represents P O B D c d v g' ↔ g' = g) ∧
        ∀ L : P → B →ₗ[O] D, (∀ (p : P) (b : B), L p b = g (p, b)) →
          (∀ k : ℕ, IsLocallyConstant (fun p : P ↦ reduce O π (L p) k) ∧
            (Set.range (fun p : P ↦ reduce O π (L p) k)).Finite ∧
            ∀ f : residue O π B k →ₗ[O] residue O π D k,
              IsClopen {p : P | reduce O π (L p) k = f}) ∧
          (∀ (k : ℕ) (p : P) (b : residue O π B (k + 1)),
            transition O π D k (reduce O π (L p) (k + 1) b) =
              reduce O π (L p) k (transition O π B k b)) ∧
          ∀ Q : Over P, Function.Bijective (kernelLimitMap P O π B D L Q)

/-- The complete integral scalar realization assertion, with the spectral valuation topology
on the recorded integer ring and the recorded uniformizer. Every module topology, action,
comparison and reduction occurring in this proposition is specified above.
Source: HRS Example 3.1, Remark 3.2 and the node's finite-presentation supplement
(blueprint: lem-sfb-profinite-integral-scalar-realization). -/
def Statement (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] : Prop :=
  letI := spectralNorm.normedField (Padic l) E
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  TopologyStatement O π ∧
    ∀ P : Profinite.{u}, ScalarComparison P O ∧ MorphismStatement P O π

end Profinite.IntegralScalar
