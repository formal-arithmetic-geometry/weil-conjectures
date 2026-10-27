module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Basis.Basic

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Universally extended homotopies for fixed based rational retracts

Source: six-functors basics, direct-images proof, paragraph (3), rational
linear-algebra obligation extracted below the trivial-lattice calculation
(blueprint: lem-sfb-rational-based-retract-universal-homotopy).

The kernel, cycles, complement condition, matrix extension and identity packages
below are the explicit formulas in this one statement. Negative degrees use
subsingleton modules, so the bottom-degree formulas need no truncated subtraction.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe r u v w t

open CategoryTheory Limits

namespace RationalBasedRetract

/-- Extend a rational map on specified bases by its finite matrix columns.
Source: the scalar-extension formula, proof step 6
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
def extend (B : Type t) [CommRing B] [Algebra ℚ B]
    {V W : ModuleCat.{v} ℚ} {I J : Type w}
    (bV : Module.Basis I ℚ V) (bW : Module.Basis J ℚ W) (f : V →ₗ[ℚ] W) :
    (I →₀ B) →ₗ[B] (J →₀ B) :=
  Finsupp.linearCombination B fun a ↦
    (bW.repr (f (bV a))).mapRange (algebraMap ℚ B) (map_zero (algebraMap ℚ B))

/-- All retraction, differential and normalized homotopy identities, including h⁰ = 0.
Source: the two displayed identity lists
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
def Identities (R : Type r) [CommRing R] (P K : ℤ → ModuleCat.{v} R)
    (d : ∀ n, P n →ₗ[R] P (n + 1))
    (i : ∀ n, K n →ₗ[R] P n) (p : ∀ n, P n →ₗ[R] K n)
    (h : ∀ n, P n →ₗ[R] P (n - 1)) : Prop :=
  h 0 = 0 ∧
    (∀ n, (d (n + 1)).comp (d n) = 0) ∧
    (∀ n, (d n).comp (i n) = 0) ∧
    (∀ n, (p (n + 1)).comp (d n) = 0) ∧
    (∀ n, (p n).comp (i n) = LinearMap.id) ∧
    (∀ n, ∀ x : P n,
      cast (congrArg (fun j ↦ ↥(P j)) (sub_add_cancel n 1)) (d (n - 1) (h n x)) +
        cast (congrArg (fun j ↦ ↥(P j)) (add_sub_cancel_right n 1))
          (h (n + 1) (d n x)) = x - i n (p n x)) ∧
    (∀ n, (h n).comp (i n) = 0) ∧
    (∀ n, (p (n - 1)).comp (h n) = 0) ∧
    (∀ n, (h (n - 1)).comp (h n) = 0)

/-- The direct sum of a family of modules, using Mathlib's dependent finite support.
Source: the direct sum over m, proof step 5
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
abbrev sumModule {R : Type r} [CommRing R] {M : Type u}
    (V : M → ModuleCat.{v} R) : ModuleCat.{max u v} R :=
  ModuleCat.of R (Π₀ m, V m)

/-- The same identities on the direct sums, with every map preserving the m-component.
Source: proof step 5
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
def SumIdentities (R : Type r) [CommRing R] {M : Type u}
    (P K : M → ℤ → ModuleCat.{v} R)
    (d : ∀ m n, P m n →ₗ[R] P m (n + 1))
    (i : ∀ m n, K m n →ₗ[R] P m n) (p : ∀ m n, P m n →ₗ[R] K m n)
    (h : ∀ m n, P m n →ₗ[R] P m (n - 1)) : Prop :=
  Identities R (fun n ↦ sumModule fun m ↦ P m n)
    (fun n ↦ sumModule fun m ↦ K m n)
    (fun n ↦ DFinsupp.mapRange.linearMap fun m ↦ d m n)
    (fun n ↦ DFinsupp.mapRange.linearMap fun m ↦ i m n)
    (fun n ↦ DFinsupp.mapRange.linearMap fun m ↦ p m n)
    (fun n ↦ DFinsupp.mapRange.linearMap fun m ↦ h m n)

private theorem extend_zero (B : Type t) [CommRing B] [Algebra ℚ B]
    {V W : ModuleCat.{v} ℚ} {I J : Type w}
    (bV : Module.Basis I ℚ V) (bW : Module.Basis J ℚ W) :
    extend B bV bW (0 : V →ₗ[ℚ] W) = 0 := by
  apply Finsupp.lhom_ext
  intro a c
  simp [extend]

private theorem extend_id (B : Type t) [CommRing B] [Algebra ℚ B]
    {V : ModuleCat.{v} ℚ} {I : Type w} (bV : Module.Basis I ℚ V) :
    extend B bV bV LinearMap.id = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro a c
  simp [extend]

private def coordinates (B : Type t) [CommRing B] [Algebra ℚ B]
    {V : ModuleCat.{v} ℚ} {I : Type w} (b : Module.Basis I ℚ V) :
    V →ₗ[ℚ] (I →₀ B) :=
  (Finsupp.mapRange.linearMap (Algebra.linearMap ℚ B)).comp b.repr.toLinearMap

private theorem extend_single (B : Type t) [CommRing B] [Algebra ℚ B]
    {V W : ModuleCat.{v} ℚ} {I J : Type w}
    (bV : Module.Basis I ℚ V) (bW : Module.Basis J ℚ W) (f : V →ₗ[ℚ] W)
    (a : I) (c : B) :
    extend B bV bW f (Finsupp.single a c) = c • coordinates B bW (f (bV a)) := by
  simp [extend, coordinates, Algebra.coe_linearMap]

private theorem extend_coordinates (B : Type t) [CommRing B] [Algebra ℚ B]
    {V W : ModuleCat.{v} ℚ} {I J : Type w}
    (bV : Module.Basis I ℚ V) (bW : Module.Basis J ℚ W) (f : V →ₗ[ℚ] W) (x : V) :
    extend B bV bW f (coordinates B bV x) = coordinates B bW (f x) := by
  have hh : ((extend B bV bW f).restrictScalars ℚ).comp (coordinates B bV) =
      (coordinates B bW).comp f := by
    apply bV.ext
    intro a
    simp [coordinates, extend, Algebra.coe_linearMap]
  exact LinearMap.congr_fun hh x

private theorem extend_comp (B : Type t) [CommRing B] [Algebra ℚ B]
    {U V W : ModuleCat.{v} ℚ} {I J N : Type w}
    (bU : Module.Basis I ℚ U) (bV : Module.Basis J ℚ V) (bW : Module.Basis N ℚ W)
    (f : U →ₗ[ℚ] V) (g : V →ₗ[ℚ] W) :
    extend B bU bW (g.comp f) = (extend B bV bW g).comp (extend B bU bV f) := by
  apply Finsupp.lhom_ext
  intro a c
  simp only [LinearMap.comp_apply, extend_single, map_smul, extend_coordinates]

private theorem extend_add (B : Type t) [CommRing B] [Algebra ℚ B]
    {V W : ModuleCat.{v} ℚ} {I J : Type w}
    (bV : Module.Basis I ℚ V) (bW : Module.Basis J ℚ W) (f g : V →ₗ[ℚ] W) :
    extend B bV bW (f + g) = extend B bV bW f + extend B bV bW g := by
  apply Finsupp.lhom_ext
  intro a c
  simp only [extend_single, LinearMap.add_apply, map_add, smul_add]

private theorem extend_sub (B : Type t) [CommRing B] [Algebra ℚ B]
    {V W : ModuleCat.{v} ℚ} {I J : Type w}
    (bV : Module.Basis I ℚ V) (bW : Module.Basis J ℚ W) (f g : V →ₗ[ℚ] W) :
    extend B bV bW (f - g) = extend B bV bW f - extend B bV bW g := by
  apply Finsupp.lhom_ext
  intro a c
  simp only [extend_single, LinearMap.sub_apply, map_sub, smul_sub]

private def transport {R : Type r} [CommRing R] (P : ℤ → ModuleCat.{v} R)
    {a b : ℤ} (hab : a = b) : P a →ₗ[R] P b := by
  subst b
  exact LinearMap.id

private theorem transport_apply {R : Type r} [CommRing R]
    (P : ℤ → ModuleCat.{v} R) {a b : ℤ} (hab : a = b) (x : P a) :
    transport P hab x = cast (congrArg (fun j ↦ ↥(P j)) hab) x := by
  subst b
  rfl

private theorem extend_transport (B : Type t) [CommRing B] [Algebra ℚ B]
    (P : ℤ → ModuleCat.{v} ℚ) {I : ℤ → Type w}
    (bP : ∀ n, Module.Basis (I n) ℚ (P n)) {a b : ℤ} (hab : a = b) :
    extend B (bP a) (bP b) (transport P hab) =
      transport (fun n ↦ ModuleCat.of B (I n →₀ B)) hab := by
  subst b
  exact extend_id B (bP a)

private theorem extend_identities (B : Type t) [CommRing B] [Algebra ℚ B]
    (P K : ℤ → ModuleCat.{v} ℚ) {IP IK : ℤ → Type w}
    (bP : ∀ n, Module.Basis (IP n) ℚ (P n))
    (bK : ∀ n, Module.Basis (IK n) ℚ (K n))
    (d : ∀ n, P n →ₗ[ℚ] P (n + 1)) (i : ∀ n, K n →ₗ[ℚ] P n)
    (p : ∀ n, P n →ₗ[ℚ] K n) (h : ∀ n, P n →ₗ[ℚ] P (n - 1))
    (hh : Identities ℚ P K d i p h) :
    Identities B (fun n ↦ ModuleCat.of B (IP n →₀ B))
      (fun n ↦ ModuleCat.of B (IK n →₀ B))
      (fun n ↦ extend B (bP n) (bP (n + 1)) (d n))
      (fun n ↦ extend B (bK n) (bP n) (i n))
      (fun n ↦ extend B (bP n) (bK n) (p n))
      (fun n ↦ extend B (bP n) (bP (n - 1)) (h n)) := by
  obtain ⟨h0, hdd, hdi, hpd, hpi, hhom, hhi, hph, hhh⟩ := hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [h0, extend_zero]
  · intro n
    rw [← extend_comp, hdd, extend_zero]
  · intro n
    rw [← extend_comp, hdi, extend_zero]
  · intro n
    rw [← extend_comp, hpd, extend_zero]
  · intro n
    rw [← extend_comp, hpi, extend_id]
  · intro n x
    have hlin :
        (transport P (sub_add_cancel n 1)).comp ((d (n - 1)).comp (h n)) +
          (transport P (add_sub_cancel_right n 1)).comp ((h (n + 1)).comp (d n)) =
            LinearMap.id - (i n).comp (p n) := by
      ext y
      simpa only [LinearMap.add_apply, LinearMap.comp_apply, transport_apply,
        LinearMap.sub_apply, LinearMap.id_apply] using hhom n y
    have hext := congrArg (extend B (bP n) (bP n)) hlin
    rw [extend_add, extend_sub,
      extend_comp B (bP n) (bP (n - 1 + 1)) (bP n),
      extend_comp B (bP n) (bP (n - 1)) (bP (n - 1 + 1)),
      extend_comp B (bP n) (bP (n + 1 - 1)) (bP n),
      extend_comp B (bP n) (bP (n + 1)) (bP (n + 1 - 1)),
      extend_comp B (bP n) (bK n) (bP n),
      extend_transport B P bP, extend_transport B P bP, extend_id] at hext
    simpa only [LinearMap.add_apply, LinearMap.comp_apply,
      transport_apply (fun n ↦ ModuleCat.of B (IP n →₀ B)),
      LinearMap.sub_apply, LinearMap.id_apply] using LinearMap.congr_fun hext x
  · intro n
    rw [← extend_comp, hhi, extend_zero]
  · intro n
    rw [← extend_comp, hph, extend_zero]
  · intro n
    rw [← extend_comp, hhh, extend_zero]

private theorem cast_dfinsupp_apply {M : Type u} (P : M → ℤ → Type v) [∀ m n, Zero (P m n)]
    {a b : ℤ} (hab : a = b)
    (x : Π₀ m, P m a) (m : M) :
    (cast (congrArg (fun j ↦ Π₀ m, P m j) hab) x) m =
      cast (congrArg (fun j ↦ P m j) hab) (x m) := by
  subst b
  rfl

private theorem sum_identities {R : Type r} [CommRing R] {M : Type u}
    (P K : M → ℤ → ModuleCat.{v} R)
    (d : ∀ m n, P m n →ₗ[R] P m (n + 1))
    (i : ∀ m n, K m n →ₗ[R] P m n) (p : ∀ m n, P m n →ₗ[R] K m n)
    (h : ∀ m n, P m n →ₗ[R] P m (n - 1))
    (hh : ∀ m, Identities R (P m) (K m) (d m) (i m) (p m) (h m)) :
    SumIdentities R P K d i p h := by
  have heval {A B : M → ModuleCat.{v} R} (f : ∀ m, A m →ₗ[R] B m)
      (x : Π₀ m, A m) (m : M) :
      (DFinsupp.mapRange.linearMap f x) m = f m (x m) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x m
    simpa only [heval, LinearMap.zero_apply, DFinsupp.zero_apply] using
      LinearMap.congr_fun (hh m).1 (x m)
  · intro n
    ext x m
    simpa only [LinearMap.comp_apply, heval, LinearMap.zero_apply, DFinsupp.zero_apply]
      using LinearMap.congr_fun ((hh m).2.1 n) (x m)
  · intro n
    ext x m
    simpa only [LinearMap.comp_apply, heval, LinearMap.zero_apply, DFinsupp.zero_apply]
      using LinearMap.congr_fun ((hh m).2.2.1 n) (x m)
  · intro n
    ext x m
    simpa only [LinearMap.comp_apply, heval, LinearMap.zero_apply, DFinsupp.zero_apply]
      using LinearMap.congr_fun ((hh m).2.2.2.1 n) (x m)
  · intro n
    ext x m
    simpa only [LinearMap.comp_apply, heval, LinearMap.id_apply]
      using LinearMap.congr_fun ((hh m).2.2.2.2.1 n) (x m)
  · intro n x
    ext m
    change
      (cast (congrArg (fun j ↦ Π₀ m, P m j) (sub_add_cancel n 1))
        (DFinsupp.mapRange.linearMap (fun m ↦ d m (n - 1))
          (DFinsupp.mapRange.linearMap (fun m ↦ h m n) x))) m +
      (cast (congrArg (fun j ↦ Π₀ m, P m j) (add_sub_cancel_right n 1))
        (DFinsupp.mapRange.linearMap (fun m ↦ h m (n + 1))
          (DFinsupp.mapRange.linearMap (fun m ↦ d m n) x))) m =
        x m - i m n (p m n (x m))
    rw [cast_dfinsupp_apply (fun m n ↦ ↥(P m n)) (sub_add_cancel n 1),
      cast_dfinsupp_apply (fun m n ↦ ↥(P m n)) (add_sub_cancel_right n 1)]
    exact (hh m).2.2.2.2.2.1 n (x m)
  · intro n
    ext x m
    simpa only [LinearMap.comp_apply, heval, LinearMap.zero_apply, DFinsupp.zero_apply]
      using LinearMap.congr_fun ((hh m).2.2.2.2.2.2.1 n) (x m)
  · intro n
    ext x m
    simpa only [LinearMap.comp_apply, heval, LinearMap.zero_apply, DFinsupp.zero_apply]
      using LinearMap.congr_fun ((hh m).2.2.2.2.2.2.2.1 n) (x m)
  · intro n
    ext x m
    simpa only [LinearMap.comp_apply, heval, LinearMap.zero_apply, DFinsupp.zero_apply]
      using LinearMap.congr_fun ((hh m).2.2.2.2.2.2.2.2 n) (x m)

section Retract

variable {M : Type u} (P K : M → CochainComplex (ModuleCat.{v} ℚ) ℤ)
    (i : ∀ m, K m ⟶ P m) (p : ∀ m, P m ⟶ K m)

/-- Cⁿ = ker pⁿ, viewed in the ambient Pⁿ.
Source: the definition of C in the statement
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
def kernel (m : M) (n : ℤ) : Submodule ℚ ((P m).X n) :=
  LinearMap.ker ((p m).f n).hom

/-- Zⁿ is the kernel of d restricted to Cⁿ, embedded in Pⁿ.
Source: the definition of Z in the statement
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
def cycles (m : M) (n : ℤ) : Submodule ℚ ((P m).X n) :=
  kernel P K p m n ⊓ LinearMap.ker ((P m).d n (n + 1)).hom

/-- A choice of complements together with the differential isomorphisms.
The indexing eⁿ : Lⁿ⁻¹ ≃ Zⁿ makes its inverse exactly the prescribed sⁿ.
Source: the displayed complement and differential-isomorphism clauses
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
def Complements (L : ∀ m n, Submodule ℚ ((P m).X n))
    (e : ∀ m n, L m (n - 1) ≃ₗ[ℚ] cycles P K p m n) : Prop :=
  (∀ m n, cycles P K p m n ⊔ L m n = kernel P K p m n) ∧
    (∀ m n, Disjoint (cycles P K p m n) (L m n)) ∧
    (∀ m n (l : L m (n - 1)),
      ((e m n l : cycles P K p m n) : (P m).X n) =
        (P m).d (n - 1) n (l : (P m).X (n - 1)))

/-- The identities for the rational matrices after scalar extension, on each summand
and on their direct sum. No nontriviality instance is requested for B.
Source: proof steps 5–6
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
def ExtendedIdentities {IP IK : M → ℤ → Type w}
    (bP : ∀ m n, Module.Basis (IP m n) ℚ ((P m).X n))
    (bK : ∀ m n, Module.Basis (IK m n) ℚ ((K m).X n))
    (h : ∀ m n, (P m).X n →ₗ[ℚ] (P m).X (n - 1))
    (B : Type t) [CommRing B] [Algebra ℚ B] : Prop :=
  (∀ m, Identities B
    (fun n ↦ ModuleCat.of B (IP m n →₀ B))
    (fun n ↦ ModuleCat.of B (IK m n →₀ B))
    (fun n ↦ extend B (bP m n) (bP m (n + 1)) ((P m).d n (n + 1)).hom)
    (fun n ↦ extend B (bK m n) (bP m n) ((i m).f n).hom)
    (fun n ↦ extend B (bP m n) (bK m n) ((p m).f n).hom)
    (fun n ↦ extend B (bP m n) (bP m (n - 1)) (h m n))) ∧
  SumIdentities B
    (fun m n ↦ ModuleCat.of B (IP m n →₀ B))
    (fun m n ↦ ModuleCat.of B (IK m n →₀ B))
    (fun m n ↦ extend B (bP m n) (bP m (n + 1)) ((P m).d n (n + 1)).hom)
    (fun m n ↦ extend B (bK m n) (bP m n) ((i m).f n).hom)
    (fun m n ↦ extend B (bP m n) (bK m n) ((p m).f n).hom)
    (fun m n ↦ extend B (bP m n) (bP m (n - 1)) (h m n))

private theorem pi_apply (hpi : ∀ m, i m ≫ p m = 𝟙 (K m))
    (m : M) (n : ℤ) (x : (K m).X n) : (p m).f n ((i m).f n x) = x := by
  have hh := congrArg (fun f ↦ f.f n) (hpi m)
  exact ConcreteCategory.congr_hom hh x

private theorem di_apply (hKzero : ∀ m a b, (K m).d a b = 0)
    (m : M) (a b : ℤ) (x : (K m).X a) :
    (P m).d a b ((i m).f a x) = 0 := by
  have hh : (i m).f a ≫ (P m).d a b = 0 := by
    rw [(i m).comm, hKzero, zero_comp]
  exact ConcreteCategory.congr_hom hh x

private theorem pd_apply (hKzero : ∀ m a b, (K m).d a b = 0)
    (m : M) (a b : ℤ) (x : (P m).X a) :
    (p m).f b ((P m).d a b x) = 0 := by
  have hh : (P m).d a b ≫ (p m).f b = 0 := by
    rw [← (p m).comm, hKzero, comp_zero]
  exact ConcreteCategory.congr_hom hh x

private theorem dd_apply (m : M) (a b c : ℤ) (x : (P m).X a) :
    (P m).d b c ((P m).d a b x) = 0 := by
  exact ConcreteCategory.congr_hom ((P m).d_comp_d a b c) x

private theorem retract_isCompl (hpi : ∀ m, i m ≫ p m = 𝟙 (K m))
    (m : M) (n : ℤ) :
    IsCompl (LinearMap.range ((i m).f n).hom) (kernel P K p m n) := by
  constructor
  · rw [disjoint_iff_inf_le]
    rintro x ⟨⟨k, rfl⟩, hx⟩
    have hk : k = 0 := (pi_apply P K i p hpi m n k).symm.trans hx
    simp [hk]
  · rw [codisjoint_iff_le_sup]
    intro x _
    refine Submodule.mem_sup.mpr ⟨(i m).f n ((p m).f n x), ⟨_, rfl⟩,
      x - (i m).f n ((p m).f n x), ?_, by abel⟩
    change (p m).f n (x - (i m).f n ((p m).f n x)) = 0
    simp only [map_sub, pi_apply P K i p hpi, sub_self]

private theorem boundary_of_homology_injective
    (hH : ∀ m n, IsIso (HomologicalComplex.homologyMap (p m) n))
    (m : M) (n : ℤ) (z : (P m).X n)
    (hz : (P m).d n (n + 1) z = 0) (hpz : (p m).f n z = 0) :
    ∃ y : (P m).X (n - 1), (P m).d (n - 1) n y = z := by
  have hn : (ComplexShape.up ℤ).next n = n + 1 :=
    (ComplexShape.up ℤ).next_eq' rfl
  have hp : (ComplexShape.up ℤ).prev n = n - 1 :=
    (ComplexShape.up ℤ).prev_eq' (by simp)
  have hzS : z ∈ LinearMap.ker ((P m).sc n).g.hom := by
    change (P m).d n ((ComplexShape.up ℤ).next n) z = 0
    rwa [hn]
  let zc : (P m).cycles n := ((P m).sc n).moduleCatCyclesIso.inv ⟨z, hzS⟩
  have hzc : (P m).iCycles n zc = z := by
    exact ConcreteCategory.congr_hom ((P m).sc n).moduleCatCyclesIso_inv_iCycles ⟨z, hzS⟩
  have hmap : HomologicalComplex.cyclesMap (p m) n zc = 0 := by
    apply (ModuleCat.mono_iff_injective ((K m).iCycles n)).mp inferInstance
    have hh := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (p m) n) zc
    simpa only [ModuleCat.comp_apply, hzc, hpz, map_zero] using hh
  have hclass : (P m).homologyπ n zc = 0 := by
    have := hH m n
    apply (ModuleCat.mono_iff_injective
      (HomologicalComplex.homologyMap (p m) n)).mp inferInstance
    have hh := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality (p m) n) zc
    simpa only [ModuleCat.comp_apply, hmap, map_zero] using hh
  have hop : ((P m).sc n).pOpcycles z = 0 := by
    have hh := ConcreteCategory.congr_hom ((P m).homology_π_ι n) zc
    simpa only [ModuleCat.comp_apply, hzc, hclass, map_zero,
      HomologicalComplex.opcycles, HomologicalComplex.pOpcycles,
      HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor'] using hh.symm
  have hb : ∃ y : (P m).X ((ComplexShape.up ℤ).prev n),
      (P m).d ((ComplexShape.up ℤ).prev n) n y = z :=
    (((P m).sc n).moduleCat_pOpcycles_eq_zero_iff z).mp hop
  rw [hp] at hb
  exact hb

private theorem cycles_eq_boundaries
    (hKzero : ∀ m a b, (K m).d a b = 0)
    (hpi : ∀ m, i m ≫ p m = 𝟙 (K m))
    (hH : ∀ m n, IsIso (HomologicalComplex.homologyMap (p m) n))
    (m : M) (n : ℤ) : cycles P K p m n =
      (kernel P K p m (n - 1)).map ((P m).d (n - 1) n).hom := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y, hy⟩ := boundary_of_homology_injective P K p hH m n z hz.2 hz.1
    refine ⟨y - (i m).f (n - 1) ((p m).f (n - 1) y), ?_, ?_⟩
    · change (p m).f (n - 1) (y - (i m).f (n - 1) ((p m).f (n - 1) y)) = 0
      simp only [map_sub, pi_apply P K i p hpi, sub_self]
    · simp only [map_sub, di_apply P K i hKzero, sub_zero, hy]
  · rintro z ⟨y, hy, rfl⟩
    exact ⟨pd_apply P K p hKzero m _ _ y, dd_apply P m _ _ _ y⟩

private theorem cycles_zero
    (hPneg : ∀ m n, n < 0 → Subsingleton ((P m).X n))
    (hacyc : ∀ m n, cycles P K p m n =
      (kernel P K p m (n - 1)).map ((P m).d (n - 1) n).hom) (m : M) :
    cycles P K p m 0 = ⊥ := by
  rw [hacyc]
  apply le_antisymm _ bot_le
  rintro z ⟨y, hy, rfl⟩
  let := hPneg m (0 - 1) (by norm_num)
  simp only [Subsingleton.elim y 0, map_zero, Submodule.zero_mem]

private theorem exists_complements
    (hKzero : ∀ m a b, (K m).d a b = 0)
    (hacyc : ∀ m n, cycles P K p m n =
      (kernel P K p m (n - 1)).map ((P m).d (n - 1) n).hom) :
    ∃ (L : ∀ m n, Submodule ℚ ((P m).X n))
      (e : ∀ m n, L m (n - 1) ≃ₗ[ℚ] cycles P K p m n),
      Complements P K p L e := by
  classical
  have hex (m : M) (n : ℤ) : ∃ l : Submodule ℚ ((P m).X n),
      Disjoint (cycles P K p m n) l ∧
        cycles P K p m n ⊔ l = kernel P K p m n :=
    IsModularLattice.exists_disjoint_and_sup_eq
      (show cycles P K p m n ≤ kernel P K p m n from inf_le_left)
  choose L hdis hsup using hex
  have hL (m : M) (n : ℤ) : L m n ≤ kernel P K p m n :=
    le_sup_right.trans (le_of_eq (hsup m n))
  let f (m : M) (n : ℤ) : L m (n - 1) →ₗ[ℚ] cycles P K p m n :=
    (((P m).d (n - 1) n).hom.comp (L m (n - 1)).subtype).codRestrict _
      (fun x ↦ by
        change (P m).d (n - 1) n (x : (P m).X (n - 1)) ∈ cycles P K p m n
        constructor
        · exact pd_apply P K p hKzero m _ _ (x : (P m).X (n - 1))
        · simpa using dd_apply P m (n - 1) n (n + 1) (x : (P m).X (n - 1)))
  have hf (m : M) (n : ℤ) : Function.Bijective (f m n) := by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply le_antisymm _ bot_le
      intro l hl
      have hd : (P m).d (n - 1) n l = 0 := congrArg Subtype.val hl
      have hz : (l : (P m).X (n - 1)) ∈ cycles P K p m (n - 1) := by
        refine ⟨hL m (n - 1) l.property, ?_⟩
        change (P m).d (n - 1) (n - 1 + 1) l = 0
        rw [sub_add_cancel]
        exact hd
      have he : (l : (P m).X (n - 1)) = 0 :=
        (Submodule.disjoint_def.mp (hdis m (n - 1))) _ hz l.property
      exact Subtype.ext he
    · intro z
      have hzmem : (z : (P m).X n) ∈
          (kernel P K p m (n - 1)).map ((P m).d (n - 1) n).hom :=
        (hacyc m n).le z.property
      obtain ⟨y, hy, hdy⟩ := hzmem
      obtain ⟨z₀, hz₀, l, hl, hsum⟩ :=
        Submodule.mem_sup.mp ((hsup m (n - 1)).ge hy)
      refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
      change (P m).d (n - 1) n l = z
      have hdz : (P m).d (n - 1) n z₀ = 0 := by
        have hz₀d := hz₀.2
        change (P m).d (n - 1) (n - 1 + 1) z₀ = 0 at hz₀d
        rwa [sub_add_cancel] at hz₀d
      rw [← hsum, map_add, hdz, zero_add] at hdy
      exact hdy
  refine ⟨L, fun m n ↦ LinearEquiv.ofBijective (f m n) (hf m n), ?_⟩
  exact ⟨hsup, hdis, fun _ _ _ ↦ rfl⟩

private theorem decompose
    (hpi : ∀ m, i m ≫ p m = 𝟙 (K m))
    (L : ∀ m n, Submodule ℚ ((P m).X n))
    (hsup : ∀ m n, cycles P K p m n ⊔ L m n = kernel P K p m n)
    (m : M) (n : ℤ) (x : (P m).X n) :
    ∃ (k : (K m).X n) (z : cycles P K p m n) (l : L m n),
      x = (i m).f n k + z + l := by
  have hq : x - (i m).f n ((p m).f n x) ∈ kernel P K p m n := by
    change (p m).f n (x - (i m).f n ((p m).f n x)) = 0
    simp only [map_sub, pi_apply P K i p hpi, sub_self]
  obtain ⟨z, hz, l, hl, he⟩ := Submodule.mem_sup.mp ((hsup m n).symm ▸ hq)
  exact ⟨(p m).f n x, ⟨z, hz⟩, ⟨l, hl⟩, by dsimp; rw [add_assoc, he]; abel⟩

private theorem ambient_isCompl
    (hpi : ∀ m, i m ≫ p m = 𝟙 (K m))
    (L : ∀ m n, Submodule ℚ ((P m).X n))
    (hsup : ∀ m n, cycles P K p m n ⊔ L m n = kernel P K p m n)
    (hdis : ∀ m n, Disjoint (cycles P K p m n) (L m n)) (m : M) (n : ℤ) :
    IsCompl (cycles P K p m n) (LinearMap.range ((i m).f n).hom ⊔ L m n) := by
  constructor
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hz, hx⟩
    obtain ⟨_, ⟨k, rfl⟩, l, hl, rfl⟩ := Submodule.mem_sup.mp hx
    have hpl : (p m).f n l = 0 :=
      (show L m n ≤ kernel P K p m n from le_sup_right.trans (le_of_eq (hsup m n))) hl
    have hk : k = 0 := by
      have hx0 := hz.1
      change (p m).f n ((i m).f n k + l) = 0 at hx0
      simpa only [map_add, pi_apply P K i p hpi, hpl, add_zero] using hx0
    have hzl : l ∈ cycles P K p m n := by simpa [hk] using hz
    have hl0 := (Submodule.disjoint_def.mp (hdis m n)) l hzl hl
    simp [hk, hl0]
  · rw [codisjoint_iff_le_sup]
    intro x _
    obtain ⟨k, z, l, rfl⟩ := decompose P K i p hpi L hsup m n x
    refine Submodule.mem_sup.mpr ⟨z, z.property, (i m).f n k + l,
      Submodule.mem_sup.mpr ⟨_, ⟨k, rfl⟩, _, l.property, rfl⟩, by abel⟩

private theorem cast_d_target (m : M) (a b c : ℤ) (hbc : b = c)
    (x : (P m).X a) :
    cast (congrArg (fun j ↦ ↥((P m).X j)) hbc) ((P m).d a b x) =
      (P m).d a c x := by
  subst c
  rfl

private theorem homotopy_from_complements
    (hPneg : ∀ m n, n < 0 → Subsingleton ((P m).X n))
    (hKzero : ∀ m a b, (K m).d a b = 0)
    (hpi : ∀ m, i m ≫ p m = 𝟙 (K m))
    (L : ∀ m n, Submodule ℚ ((P m).X n))
    (e : ∀ m n, L m (n - 1) ≃ₗ[ℚ] cycles P K p m n)
    (hc : Complements P K p L e) :
    (∀ m, (e m 0).symm.toLinearMap = 0) ∧
    ∃ h : ∀ m n, (P m).X n →ₗ[ℚ] (P m).X (n - 1),
      (∀ m n (k : (K m).X n) (z : cycles P K p m n) (l : L m n),
        h m n ((i m).f n k + (z : (P m).X n) + (l : (P m).X n)) =
          ((e m n).symm z : (P m).X (n - 1))) ∧
      (∀ m, Identities ℚ (P m).X (K m).X
        (fun n ↦ ((P m).d n (n + 1)).hom)
        (fun n ↦ ((i m).f n).hom) (fun n ↦ ((p m).f n).hom) (h m)) := by
  classical
  obtain ⟨hsup, hdis, he⟩ := hc
  have hL (m : M) (n : ℤ) : L m n ≤ kernel P K p m n :=
    le_sup_right.trans (le_of_eq (hsup m n))
  let pr (m : M) (n : ℤ) : (P m).X n →ₗ[ℚ] cycles P K p m n :=
    (cycles P K p m n).projectionOnto
      (LinearMap.range ((i m).f n).hom ⊔ L m n)
      (ambient_isCompl P K i p hpi L hsup hdis m n)
  let h (m : M) (n : ℤ) : (P m).X n →ₗ[ℚ] (P m).X (n - 1) :=
    (L m (n - 1)).subtype.comp ((e m n).symm.toLinearMap.comp (pr m n))
  have hform (m : M) (n : ℤ) (k : (K m).X n)
      (z : cycles P K p m n) (l : L m n) :
      h m n ((i m).f n k + (z : (P m).X n) + (l : (P m).X n)) =
        ((e m n).symm z : (P m).X (n - 1)) := by
    have hi0 : pr m n ((i m).f n k) = 0 :=
      Submodule.projectionOnto_apply_of_mem_right _ (Submodule.mem_sup_left ⟨k, rfl⟩)
    have hl0 : pr m n l = 0 :=
      Submodule.projectionOnto_apply_of_mem_right _ (Submodule.mem_sup_right l.property)
    have hz : pr m n z = z := Submodule.projectionOnto_apply_left _ z
    simp [h, hi0, hl0, hz]
  have hi0 (m : M) (n : ℤ) (k : (K m).X n) : h m n ((i m).f n k) = 0 := by
    simpa using hform m n k 0 0
  have hl0 (m : M) (n : ℤ) (l : L m n) : h m n l = 0 := by
    simpa using hform m n 0 0 l
  have hz (m : M) (n : ℤ) (z : cycles P K p m n) :
      h m n z = ((e m n).symm z : (P m).X (n - 1)) := by
    simpa using hform m n 0 z 0
  have hd (m : M) (n : ℤ) (l : L m (n - 1)) :
      h m n ((P m).d (n - 1) n l) = l := by
    rw [← he m n l, hz, LinearEquiv.symm_apply_apply]
  have hdc (m : M) (a b : ℤ) (hab : b - 1 = a) (l : L m a) :
      cast (congrArg (fun j ↦ ↥((P m).X j)) hab)
        (h m b ((P m).d a b l)) = l := by
    subst a
    rw [hd]
    rfl
  refine ⟨?_, h, hform, ?_⟩
  · intro m
    let := hPneg m (0 - 1) (by norm_num)
    exact Subsingleton.elim _ _
  · intro m
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · let := hPneg m (0 - 1) (by norm_num)
      exact Subsingleton.elim _ _
    · intro n
      ext x
      exact dd_apply P m _ _ _ x
    · intro n
      ext k
      exact di_apply P K i hKzero m _ _ k
    · intro n
      ext x
      exact pd_apply P K p hKzero m _ _ x
    · intro n
      ext k
      exact pi_apply P K i p hpi m n k
    · intro n x
      obtain ⟨k, z, l, rfl⟩ := decompose P K i p hpi L hsup m n x
      have hdz : (P m).d n (n + 1) z = 0 := z.property.2
      have hdh : (P m).d (n - 1) n (h m n
          ((i m).f n k + (z : (P m).X n) + (l : (P m).X n))) = z := by
        rw [hform, ← he, LinearEquiv.apply_symm_apply]
      have hdl : (P m).d n (n + 1)
          ((i m).f n k + (z : (P m).X n) + (l : (P m).X n)) =
          (P m).d n (n + 1) l := by
        simp only [map_add, di_apply P K i hKzero, hdz, zero_add]
      have hpz : (p m).f n z = 0 := z.property.1
      have hpl : (p m).f n l = 0 := hL m n l.property
      dsimp only
      rw [cast_d_target P m (n - 1) (n - 1 + 1) n (sub_add_cancel n 1),
        hdh, hdl, hdc m n (n + 1) (add_sub_cancel_right n 1) l]
      simp only [map_add, pi_apply P K i p hpi, hpz, hpl, add_zero]
      abel
    · intro n
      ext k
      exact hi0 m n k
    · intro n
      ext x
      exact hL m (n - 1) ((e m n).symm (pr m n x)).property
    · intro n
      ext x
      exact hl0 m (n - 1) ((e m n).symm (pr m n x))

/-- Fixed rational retractions have the stated decompositions and universally
extended normalized homotopies, for every choice of cycle complements.
Source: six-functors direct-images paragraph (3), extracted algebraic obligation
(blueprint: lem-sfb-rational-based-retract-universal-homotopy).

Proof, following the node's seven steps:
1. q = 1 - ip lands in C, fixes C, and x = i(px) + qx uniquely. The chain-map
identities give d(iK) = 0 and d(C) ⊆ C, so this splits complexes with the fixed i,p.
2. A cycle z in C has zero cohomology class by injectivity of H(p). Write z = dy
and replace y by y - i(py), which lies in C and has the same differential.
Thus C is acyclic; the incoming module at degree zero vanishes, so Z⁰ = 0.
3. Apply lem-trf-vector-subspace-complement (Submodule.exists_isCompl) to Z in C
for every m,n. The differential from each complement to the next cycles is
injective by disjointness and surjective by acyclicity, hence a linear equivalence.
4. For any such choices define h(ik+z+l) = e.symm z. On z, dh = 1; on l, hd = 1;
on iK both vanish. The image lies in L ⊆ C; h kills L and iK. Hence all side
identities, including h² = 0, hold, and h⁰ = 0 follows from Z⁰ = 0.
5. Take componentwise maps on direct sums; finite m-support is preserved, also
when M is empty. Basis coordinates of each output have finite support.
6. extend maps each basis vector to its finite rational column with coefficients
sent along ℚ → B. Finite sums show compatibility with addition, composition,
zero and identity. All identities therefore persist over every B, including zero.
7. The constant-complex specialization is stated separately below in this module:
its alternating differentials and homotopies give the identities degree by degree. -/
theorem universal_homotopy
    {IP IK : M → ℤ → Type w}
    (bP : ∀ m n, Module.Basis (IP m n) ℚ ((P m).X n))
    (bK : ∀ m n, Module.Basis (IK m n) ℚ ((K m).X n))
    (hPneg : ∀ m n, n < 0 → Subsingleton ((P m).X n))
    (hKneg : ∀ m n, n < 0 → Subsingleton ((K m).X n))
    (hKzero : ∀ m a b, (K m).d a b = 0)
    (hpi : ∀ m, i m ≫ p m = 𝟙 (K m))
    (hH : ∀ m n, IsIso (HomologicalComplex.homologyMap (p m) n)) :
    (∀ m n, IsCompl (LinearMap.range ((i m).f n).hom) (kernel P K p m n)) ∧
    (∀ m n, Set.MapsTo ((P m).d n (n + 1))
      (kernel P K p m n) (kernel P K p m (n + 1))) ∧
    (∀ m n, ((P m).d n (n + 1)).hom.comp ((i m).f n).hom = 0) ∧
    (∀ m n, cycles P K p m n =
      (kernel P K p m (n - 1)).map ((P m).d (n - 1) n).hom) ∧
    (∀ m, cycles P K p m 0 = ⊥) ∧
    (∃ (L : ∀ m n, Submodule ℚ ((P m).X n))
      (e : ∀ m n, L m (n - 1) ≃ₗ[ℚ] cycles P K p m n),
      Complements P K p L e) ∧
    (∀ (L : ∀ m n, Submodule ℚ ((P m).X n))
      (e : ∀ m n, L m (n - 1) ≃ₗ[ℚ] cycles P K p m n),
      Complements P K p L e →
      (∀ m, (e m 0).symm.toLinearMap = 0) ∧
      ∃ h : ∀ m n, (P m).X n →ₗ[ℚ] (P m).X (n - 1),
        (∀ m n (k : (K m).X n) (z : cycles P K p m n) (l : L m n),
          h m n ((i m).f n k + (z : (P m).X n) + (l : (P m).X n)) =
            ((e m n).symm z : (P m).X (n - 1))) ∧
        (∀ m, Identities ℚ (P m).X (K m).X
          (fun n ↦ ((P m).d n (n + 1)).hom)
          (fun n ↦ ((i m).f n).hom) (fun n ↦ ((p m).f n).hom) (h m)) ∧
        SumIdentities ℚ (fun m n ↦ (P m).X n) (fun m n ↦ (K m).X n)
          (fun m n ↦ ((P m).d n (n + 1)).hom)
          (fun m n ↦ ((i m).f n).hom) (fun m n ↦ ((p m).f n).hom) h ∧
        (∀ (B : Type t) [CommRing B] [Algebra ℚ B],
          ExtendedIdentities P K i p bP bK h B)) := by
  have _negative_terms := hKneg
  have hacyc := cycles_eq_boundaries P K i p hKzero hpi hH
  refine ⟨retract_isCompl P K i p hpi, ?_, ?_, hacyc,
    cycles_zero P K p hPneg hacyc, exists_complements P K p hKzero hacyc, ?_⟩
  · intro m n x hx
    exact pd_apply P K p hKzero m _ _ x
  · intro m n
    ext k
    exact di_apply P K i hKzero m _ _ k
  · intro L e hc
    obtain ⟨hs, h, hf, hh⟩ := homotopy_from_complements P K i p hPneg hKzero hpi L e hc
    refine ⟨hs, h, hf, hh, ?_, ?_⟩
    · exact sum_identities _ _ _ _ _ _ hh
    · intro B _ _
      have hB (m : M) := extend_identities B (P m).X (K m).X (bP m) (bK m)
        (fun n ↦ ((P m).d n (n + 1)).hom)
        (fun n ↦ ((i m).f n).hom) (fun n ↦ ((p m).f n).hom) (h m) (hh m)
      exact ⟨hB, sum_identities _ _ _ _ _ _ hB⟩

end Retract

/-- The singleton basis in degree zero and the empty basis in all positive degrees.
Source: the constant-complex clause
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
abbrev constantKIndex (n : ℕ) := {_a : Unit // n = 0}

/-- Constant-complex differential, in the singleton basis of each nonnegative term.
Source: the constant-complex clause
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
def constantD (R : Type r) [CommRing R] (n : ℕ) :
    (Unit →₀ R) →ₗ[R] (Unit →₀ R) :=
  if Even n then 0 else LinearMap.id

/-- Constant-complex inclusion, identity in degree zero and zero otherwise.
Source: the constant-complex clause
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
def constantI (R : Type r) [CommRing R] (n : ℕ) :
    (constantKIndex n →₀ R) →ₗ[R] (Unit →₀ R) :=
  Finsupp.linearCombination R fun a ↦ Finsupp.single a.val 1

/-- Constant-complex projection, identity in degree zero and zero otherwise.
Source: the constant-complex clause
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
def constantP (R : Type r) [CommRing R] (n : ℕ) :
    (Unit →₀ R) →ₗ[R] (constantKIndex n →₀ R) :=
  if hn : n = 0 then
    Finsupp.linearCombination R fun a ↦ Finsupp.single ⟨a, hn⟩ 1
  else 0

/-- The map h^(n+1), identity when n+1 is positive even and zero otherwise.
The omitted h⁰ has target zero, so is the zero map.
Source: the constant-complex clause
(blueprint: lem-sfb-rational-based-retract-universal-homotopy). -/
def constantH (R : Type r) [CommRing R] (n : ℕ) :
    (Unit →₀ R) →ₗ[R] (Unit →₀ R) :=
  if Even (n + 1) then LinearMap.id else 0

private theorem constantI_pos (R : Type r) [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    constantI R n = 0 := by
  apply Finsupp.lhom_ext
  intro a c
  exact (hn a.property).elim

private theorem constantPI_zero (R : Type r) [CommRing R] :
    (constantP R 0).comp (constantI R 0) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro a c
  simp [constantP, constantI]

private theorem constantIP_zero (R : Type r) [CommRing R] :
    (constantI R 0).comp (constantP R 0) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro a c
  simp [constantP, constantI]

/-- The prescribed constant homotopy and all the retraction identities, universally
in B; its four matrices are the extensions of these very rational matrices.
Source: constant-complex clause, proof step 7
(blueprint: lem-sfb-rational-based-retract-universal-homotopy).

Proof: H⁰ is ℚ and positive cohomology is zero. In positive even degrees the
incoming differential is 1; in odd degrees the outgoing differential is 1.
The kernel of p has cycles equal to the whole term in positive even degrees,
and zero in odd degrees. Thus the complements are zero in even degrees and the
whole term in odd degrees. The inverse-differential formula gives precisely
hⁿ = 1 for even n ≥ 2, zero otherwise. In degree zero both 1-ip and dh+hd are
zero. In positive even degrees dh = 1, hd = 0; in odd degrees dh = 0, hd = 1.
Every consecutive pair of h-components contains zero, hence h² = 0; hi = ph = 0
by degree support. All matrix entries are 0 or 1, so scalar extension preserves
the displayed matrices and all identities, including over the zero algebra. -/
theorem constant_universal_homotopy (B : Type t) [CommRing B] [Algebra ℚ B] :
    constantH B 0 = 0 ∧
    (∀ n, (constantD B (n + 1)).comp (constantD B n) = 0) ∧
    (∀ n, (constantD B n).comp (constantI B n) = 0) ∧
    (∀ n, (constantP B (n + 1)).comp (constantD B n) = 0) ∧
    (∀ n, (constantP B n).comp (constantI B n) = LinearMap.id) ∧
    (constantH B 0).comp (constantD B 0) =
      LinearMap.id - (constantI B 0).comp (constantP B 0) ∧
    (∀ n, (constantD B n).comp (constantH B n) +
      (constantH B (n + 1)).comp (constantD B (n + 1)) =
        LinearMap.id - (constantI B (n + 1)).comp (constantP B (n + 1))) ∧
    (∀ n, (constantH B n).comp (constantI B (n + 1)) = 0) ∧
    (∀ n, (constantP B n).comp (constantH B n) = 0) ∧
    (∀ n, (constantH B n).comp (constantH B (n + 1)) = 0) ∧
    (∀ n, extend B (V := ModuleCat.of ℚ (Unit →₀ ℚ))
      (W := ModuleCat.of ℚ (Unit →₀ ℚ)) Finsupp.basisSingleOne
      Finsupp.basisSingleOne (constantD ℚ n) = constantD B n) ∧
    (∀ n, extend B (V := ModuleCat.of ℚ (constantKIndex n →₀ ℚ))
      (W := ModuleCat.of ℚ (Unit →₀ ℚ)) Finsupp.basisSingleOne Finsupp.basisSingleOne
      (constantI ℚ n) = constantI B n) ∧
    (∀ n, extend B (V := ModuleCat.of ℚ (Unit →₀ ℚ))
      (W := ModuleCat.of ℚ (constantKIndex n →₀ ℚ))
      Finsupp.basisSingleOne Finsupp.basisSingleOne (constantP ℚ n) = constantP B n) ∧
    (∀ n, extend B (V := ModuleCat.of ℚ (Unit →₀ ℚ))
      (W := ModuleCat.of ℚ (Unit →₀ ℚ)) Finsupp.basisSingleOne Finsupp.basisSingleOne
      (constantH ℚ n) = constantH B n) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [constantH]
  · intro n
    by_cases hn : Even n <;> simp [constantD, Nat.even_add_one, hn]
  · intro n
    by_cases hn : n = 0
    · subst n; simp [constantD]
    · simp [constantI_pos B n hn]
  · intro n
    simp [constantP]
  · intro n
    by_cases hn : n = 0
    · subst n; exact constantPI_zero B
    · have : IsEmpty (constantKIndex n) := ⟨fun a ↦ hn a.property⟩
      exact Subsingleton.elim _ _
  · simp [constantH, constantIP_zero]
  · intro n
    by_cases hn : Even n <;>
      simp [constantD, constantH, Nat.even_add_one, hn, constantI_pos B (n + 1)
        (Nat.succ_ne_zero n)]
  · intro n
    simp [constantI_pos B (n + 1) (Nat.succ_ne_zero n)]
  · intro n
    by_cases hn : n = 0
    · subst n; simp [constantH]
    · simp [constantP, hn]
  · intro n
    by_cases hn : Even n <;> simp [constantH, Nat.even_add_one, hn]
  · intro n
    by_cases hn : Even n
    · simp [constantD, hn, extend_zero]
    · simp only [constantD, if_neg hn]
      exact extend_id B (V := ModuleCat.of ℚ (Unit →₀ ℚ)) Finsupp.basisSingleOne
  · intro n
    apply Finsupp.lhom_ext
    intro a c
    simp [extend, constantI, Finsupp.basisSingleOne]
  · intro n
    by_cases hn : n = 0
    · subst n
      apply Finsupp.lhom_ext
      intro a c
      simp [extend, constantP, Finsupp.basisSingleOne]
    · simp [constantP, hn, extend_zero]
  · intro n
    by_cases hn : Even (n + 1)
    · simp only [constantH, if_pos hn]
      exact extend_id B (V := ModuleCat.of ℚ (Unit →₀ ℚ)) Finsupp.basisSingleOne
    · simp [constantH, hn, extend_zero]

end RationalBasedRetract
