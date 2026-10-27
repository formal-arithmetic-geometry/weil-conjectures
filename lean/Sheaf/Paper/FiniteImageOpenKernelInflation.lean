/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.Paper.ContinuousRepresentationCondensation
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.CondensedDerivedInflationArrows
public import Sheaf.CategoryTheory.CondensedNormalInvariantData
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.PrimeToEllCondensedAcyclicity
import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
import Sheaf.CategoryTheory.CondensedNormalSubgroupComparison
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Open finite-image kernels and canonical derived quotient inflation

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent expansion of prime-to-ell factor removal, steps 1--7
(blueprint: lem-sfb-finite-image-open-kernel-inflation).

The helper predicates spell out the conclusions, including existence of realizations
and normalized invariants. Every coefficient morphism is fixed on sections; no arbitrary
map or choice of an unspecified model replaces a canonical arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace Profinite.CondensedAction.PrimeToEll
open ContinuousRepresentation AlgebraicGeometry.ProEtale

variable {B : ProfiniteGrp.{u}}

/-- Identify the actual finite operator image, with its evaluation topology, with B/K.
The equation specifies the first-isomorphism-theorem map, including its topology.
Source: paragraph (3), steps 1--2
(blueprint: lem-sfb-finite-image-open-kernel-inflation). -/
def FiniteKernelImageIdentified {E : Type u} [Field E]
    {V : Type (u + 1)} [AddCommGroup V] [Module E V] [TopologicalSpace V]
    (L : ProfiniteGrp.{u}) (ρ : Representation E (B × L) V)
    (K : OpenNormalSubgroup B) : Prop := by
  let φ := (Representation.asGroupHom (ρ.comp (MonoidHom.inl B L)))
  letI : TopologicalSpace φ.range :=
    TopologicalSpace.induced (fun q : φ.range ↦ fun v : V ↦ (q.val.val : V →ₗ[E] V) v)
      inferInstance
  exact ∃ e : (B ⧸ K.toSubgroup) ≃ₜ* φ.range,
    ∀ b : B, e (QuotientGroup.mk b) = φ.rangeRestrict b

/-- The canonical augmentation from a module with trivial action to derived invariants.
Its coefficient map i is required below to be the identity on the underlying module.
The normalized adjunction transpose followed by the ordinary derived unit fixes the map.
Source: paragraph (3), finite-rank augmentation in step 4
(blueprint: lem-sfb-finite-image-open-kernel-inflation). -/
def finiteKernelAugmentation (F : Type u) [NormedField F]
    (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (d : Invariants (normContinuousRing F) K)
    (N : ActionModule (normContinuousRing F) K)
    (i : (trivial (R := normContinuousRing F) (P := K)).obj N.module ⟶ N) :
    (DerivedCategory.singleFunctor (Modules (normContinuousRing F)) 0).obj N.module ⟶
      d.functor.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj N) :=
  (DerivedCategory.singleFunctor _ 0).map (d.adjunction.homEquiv N.module N i) ≫
    unitZero (normContinuousRing F) K d N

/-- The coefficientwise assertion, using the actual tensor product with module topology.
The residual action is specified by descent of rho, not by a splitting of B to B/K.
Realizations and normalized invariants exist. For every realization the K-action is
trivial, it is free of rank dim_E V, and its canonical augmentation and quotient
inflation are invertible for every normalized invariants datum. The quotient coefficient
map is uniquely prescribed as the identity on all continuous sections.
Source: paragraph (3), steps 3--7
(blueprint: lem-sfb-finite-image-open-kernel-inflation). -/
def FiniteKernelCoefficientAssertion (E F : Type u) [Field E] [NormedField F]
    [Algebra E F] (B L : ProfiniteGrp.{u}) (V : Type (u + 1)) [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (ρ : Representation E (B × L) V)
    (K : OpenNormalSubgroup B) : Prop :=
  ∃ σ : Representation E ((B ⧸ K.toSubgroup) × L) V,
    (∀ (b : B) (l : L), σ (QuotientGroup.mk b, l) = ρ (b, l)) ∧
    Nonempty (Realization F (B × L) (Extended E F V)
      (extendedRepresentation E F V (B × L) ρ)) ∧
    Nonempty (Realization F ((B ⧸ K.toSubgroup) × L) (Extended E F V)
      (extendedRepresentation E F V ((B ⧸ K.toSubgroup) × L) σ)) ∧
    Nonempty (Invariants (normContinuousRing F) (normalKernel B K)) ∧
    Nonempty (Invariants (normContinuousRing F) (B × L)) ∧
    Nonempty (Invariants (normContinuousRing F) ((B ⧸ K.toSubgroup) × L)) ∧
    ∀ (M : Realization F (B × L) (Extended E F V)
        (extendedRepresentation E F V (B × L) ρ))
      (MQ : Realization F ((B ⧸ K.toSubgroup) × L) (Extended E F V)
        (extendedRepresentation E F V ((B ⧸ K.toSubgroup) × L) σ)),
      (∀ (S : Profinite.{u}) (g : C(S, normalKernel B K))
          (m : sectionModule (normContinuousRing F) M.object.module S),
          ((inflate (R := normContinuousRing F)
            (normalKernelInclusion B K L)).obj M.object).act S g m = m) ∧
        Nonempty (((inflate (R := normContinuousRing F)
          (normalKernelInclusion B K L)).obj M.object) ≅
          (trivial (R := normContinuousRing F) (P := normalKernel B K)).obj
            (∏ᶜ fun _ : Fin (Module.finrank E V) ↦ Mod.regular (normContinuousRing F).X)) ∧
        ∃ iK : (trivial (R := normContinuousRing F) (P := normalKernel B K)).obj M.object.module ⟶
            (inflate (R := normContinuousRing F) (normalKernelInclusion B K L)).obj M.object,
          iK.val = 𝟙 M.object.module ∧
          (∀ dK : Invariants (normContinuousRing F) (normalKernel B K),
            IsIso (finiteKernelAugmentation F (normalKernel B K) dK
              ((inflate (R := normContinuousRing F) (normalKernelInclusion B K L)).obj M.object)
              iK)) ∧
          ∃ i : (inflate (R := normContinuousRing F)
                (normalProjection B K L)).obj
                  MQ.object ⟶ M.object,
            RepresentsMap (MQ.inflate
              (normalProjection B K L)) M
                (LinearMap.id : Extended E F V →ₗ[F] Extended E F V) i ∧
            ∀ (dBL : Invariants (normContinuousRing F) (B × L))
              (dQL : Invariants (normContinuousRing F) ((B ⧸ K.toSubgroup) × L)),
              IsIso (inflationZero (normContinuousRing F) (B × L)
                ((B ⧸ K.toSubgroup) × L)
                (normalProjection B K L) dBL dQL i)

/-- Finite B-image has an open normal pro-prime-to-ell kernel; both scalar realizations
are finite free with trivial kernel action and have invertible canonical augmentations
and quotient inflations. The field Omega has its norm topology and is never completed.
Source: blueprint direct-images proof, paragraph (3), expanded finite-image kernel input
(blueprint: lem-sfb-finite-image-open-kernel-inflation).

Proof:
1. For each nonidentity operator q choose v with qv unequal to v and an open neighborhood
   of v missing qv. The finitely many inverse images under b mapping to rho(b,1)v
   intersect in exactly the kernel. Thus the kernel is open, normal and closed.
2. The first isomorphism theorem sends bK to rho(b,1). Evaluation separates distinct
   operators, so the finite Hausdorff image is discrete; this is a topological group
   isomorphism. For a finite continuous quotient of K take the normal core in B of its
   open kernel. It is open normal of finite index. The orders of the K-quotients divide
   the order of this finite B-quotient and are consequently prime to ell.
3. The kernel acts identically on F tensor_E V and on every continuous section after
   every base change. Basis coordinates give V_F isomorphic to C_F^d with trivial action.
   Descending rho gives the residual quotient action without a choice of splitting.
4. Apply lem-sfb-prime-to-ell-condensed-acyclicity to K. Finite sums of K-injectives
   remain K-injective by coordinatewise null homotopies. Resolutions, invariants and
   their augmentations respect these sums; lem-sfb-condensed-derived-restriction-calculus
   supplies additivity. The scalar augmentation therefore gives the asserted rank-d one.
5. Apply lem-sfb-derived-invariants-normal-subgroup-comparison. Its beta identifies the
   underlying residual unit with this augmentation. The resolution description of
   lem-sfb-normal-inflation-resolution-naturality makes this the actual canonical map.
6. Forgetting actions computes cohomology and reflects isomorphisms, so the residual
   unit is invertible. Localization at quasi-isomorphisms uses
   def-weil-abstract-derived-category and sk-def-sfb-derived-categories.
7. The normal-subgroup comparison equation c_N inf_N = RΓ(eta_N) makes quotient
   inflation invertible. Its coefficient inclusion is the identity on the underlying
   sections and its H^0 normalization is the invariant inclusion, exactly as in
   def-sfb-condensed-derived-inflation-arrows. Apply separately to E and Omega. For
   rank zero the finite sum is empty; trivial K or Q give the same identity comparisons.
-/
theorem finite_image_open_kernel_inflation (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E]
    (B L : ProfiniteGrp.{u}) (V : Type (u + 1))
    [NormedAddCommGroup V] [NormedSpace E V] [FiniteDimensional E V]
    (ρ : Representation E (B × L) V)
    (_hB : ∀ (H : Type u) [Group H] [Fintype H] [TopologicalSpace H] [DiscreteTopology H]
      (q : B →ₜ* H), Function.Surjective q → Nat.Coprime (Nat.card H) ell)
    (_hρ : Continuous (fun x : (B × L) × V ↦ ρ x.1 x.2))
    (_hfinite : Finite (Set.range (fun b : B ↦ ρ (b, 1)))) :
    ∃ K : OpenNormalSubgroup B,
      K.toSubgroup = (Representation.asGroupHom (ρ.comp (MonoidHom.inl B L))).ker ∧
      FiniteKernelImageIdentified L ρ K ∧
      (∀ (H : Type u) [Group H] [Fintype H] [TopologicalSpace H] [DiscreteTopology H]
        (q : normalKernel B K →ₜ* H), Function.Surjective q → Nat.Coprime (Nat.card H) ell) ∧
      FiniteKernelCoefficientAssertion E E B L V ρ K ∧
      FiniteKernelCoefficientAssertion E Ω B L V ρ K := by
  sorry

end Profinite.CondensedAction.PrimeToEll
