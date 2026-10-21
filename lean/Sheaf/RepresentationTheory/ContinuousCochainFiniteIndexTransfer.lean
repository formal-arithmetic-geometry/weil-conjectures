module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Finite-index transfer on continuous cochains

Source: Stacks Project, Tag 0DVG, and the finite-coset construction and prism cancellation
in the arithmetic expansion of blueprint direct-images paragraph (3)
(blueprint: lem-sfb-continuous-cochain-finite-index-transfer).

The complexes are in abstract `ModuleCat`, not topological modules. Their cohomology
therefore uses the image of the differential without taking its closure.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {E : Type u} [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
variable {J : Type v} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]

/-- The inhomogeneous differential on jointly continuous cochains, with the final face
included by `Fin.contractNth` at its last index. In degree zero it is `gv - v`.
Source: Stacks Project, Tag 0DVG
(blueprint: lem-sfb-continuous-cochain-finite-index-transfer). -/
def continuousInhomogeneousD (A : TopRep.{w} E J)
    (hA : Continuous (fun p : J × A ↦ A.ρ p.1 p.2)) (n : ℕ) :
    C(Fin n → J, A) →ₗ[E] C(Fin (n + 1) → J, A) where
  toFun f :=
    { toFun := fun g ↦ A.ρ (g 0) (f (fun i ↦ g i.succ)) +
        ∑ j : Fin (n + 1), (-1 : E) ^ (j.val + 1) •
          f (Fin.contractNth j (· * ·) g)
      continuous_toFun := by
        apply Continuous.add
        · have ht : Continuous (fun g : Fin (n + 1) → J ↦
              (g 0, f (fun i : Fin n ↦ g i.succ))) :=
            (continuous_apply 0).prodMk
              (f.continuous.comp (continuous_pi (fun i ↦ continuous_apply i.succ)))
          exact hA.comp ht
        · apply continuous_finsetSum
          intro j _
          apply Continuous.const_smul
          apply f.continuous.comp
          apply continuous_pi
          intro k
          unfold Fin.contractNth
          split_ifs
          · exact continuous_apply _
          · exact (continuous_apply _).mul (continuous_apply _)
          · exact continuous_apply _ }
  map_add' f g := by
    ext x
    simp [map_add, Finset.sum_add_distrib, smul_add, add_add_add_comm]
  map_smul' r f := by
    ext x
    simp [map_smul, Finset.smul_sum, smul_smul, mul_comm]

/-- Consecutive differentials of continuous inhomogeneous cochains compose to zero.
Source: Stacks Project, Tag 0DVG
(blueprint: lem-sfb-continuous-cochain-finite-index-transfer).

Proof: apply the homogeneous coordinate identities of
`lem-sfb-topological-homogeneous-cochain-coordinates`. Alternating deletion squares to
zero because each pair of deleted coordinates occurs twice with opposite signs.
Conjugating by the inverse coordinate maps gives the displayed identity, also at zero.
-/
theorem continuousInhomogeneousD_comp (A : TopRep.{w} E J)
    (hA : Continuous (fun p : J × A ↦ A.ρ p.1 p.2)) (n : ℕ) :
    (continuousInhomogeneousD A hA (n + 1)).comp (continuousInhomogeneousD A hA n) = 0 := by
  sorry

/-- The ordinary nonnegative continuous cochain complex of abstract vector spaces.
Its degree zero consists of continuous functions on the one-point space `J^0`, canonically
`A` by evaluation; negative degrees are absent.
Source: Stacks Project, Tag 0DVG
(blueprint: lem-sfb-continuous-cochain-finite-index-transfer). -/
noncomputable abbrev continuousInhomogeneousComplex (A : TopRep.{w} E J)
    (hA : Continuous (fun p : J × A ↦ A.ρ p.1 p.2)) :
    CochainComplex (ModuleCat.{max v w} E) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of E C(Fin n → J, A))
    (fun n ↦ ModuleCat.ofHom (continuousInhomogeneousD A hA n))
    (fun n ↦ ModuleCat.hom_ext (continuousInhomogeneousD_comp A hA n))

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Restrict the continuous cochain complex to a subgroup with its subspace topology.
Source: Stacks Project, Tag 0DVG and the arithmetic finite-coset expansion
(blueprint: lem-sfb-continuous-cochain-finite-index-transfer). -/
noncomputable abbrev subgroupContinuousInhomogeneousComplex (H : Subgroup G)
    (A : TopRep.{w} E G) (hA : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)) :
    CochainComplex (ModuleCat.{max v w} E) ℕ :=
  continuousInhomogeneousComplex (TopRep.res H.subtype A)
    (hA.comp (continuous_subtype_val.prodMap continuous_id))

/-- Pointwise restriction commutes with the specified inhomogeneous differential.
Source: Stacks Project, Tag 0DVG and the arithmetic finite-coset expansion
(blueprint: lem-sfb-continuous-cochain-finite-index-transfer).

Proof: evaluate on an `H`-tuple. The action of each entry is its action as an element of
`G`; subgroup multiplication and all tuple contractions are inherited from `G`.
Thus the initial action term and each signed face agree separately.
-/
theorem continuousInhomogeneousRestriction_comm (H : Subgroup G)
    (A : TopRep.{w} E G) (hA : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)) (n : ℕ) :
    (ModuleCat.ofHom
        (ContinuousMap.compCLM E A
          ⟨fun g : Fin n → H ↦ fun i ↦ (g i : G), by fun_prop⟩).toLinearMap) ≫
        (subgroupContinuousInhomogeneousComplex H A hA).d n (n + 1) =
      (continuousInhomogeneousComplex A hA).d n (n + 1) ≫
        (ModuleCat.ofHom
          (ContinuousMap.compCLM E A
            ⟨fun g : Fin (n + 1) → H ↦ fun i ↦ (g i : G), by fun_prop⟩).toLinearMap) := by
  sorry

/-- The canonical restriction cochain map, given by restriction of continuous functions.
Source: Stacks Project, Tag 0DVG and the arithmetic finite-coset expansion
(blueprint: lem-sfb-continuous-cochain-finite-index-transfer). -/
noncomputable def continuousInhomogeneousRestriction (H : Subgroup G)
    (A : TopRep.{w} E G) (hA : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)) :
    continuousInhomogeneousComplex A hA ⟶ subgroupContinuousInhomogeneousComplex H A hA :=
  CochainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom
      (ContinuousMap.compCLM E A
        ⟨fun g : Fin n → H ↦ fun i ↦ (g i : G), by fun_prop⟩).toLinearMap)
    (continuousInhomogeneousRestriction_comm H A hA)

/-- Finite-index transfer and a restriction-index homotopy can be chosen simultaneously
naturally in all jointly continuous coefficient representations. The second naturality
identity concerns every component of the actual homotopy, including the bottom degree.
In particular coefficient inclusions, hence closed stable subspaces, are respected.
Source: arithmetic expansion of blueprint direct-images paragraph (3); continuous cochains
as in Stacks Tag 0DVG; prism cancellation adapted from Tag 019S
(blueprint: lem-sfb-continuous-cochain-finite-index-transfer).

Proof: (1) use the homogeneous coordinate isomorphisms of
`lem-sfb-topological-homogeneous-cochain-coordinates`, including restriction compatibility.
(2) Compactness makes the open right cosets finite. Choose representatives `S`, and write
`x = r(x)s(x)`; the clopen cosets make `r : G → H` continuous and `H`-equivariant.
(3) Extend an `H`-homogeneous cochain by `r` in each coordinate, then sum
`s⁻¹ F(r(sx₀),…,r(sxₙ))` over `S`. Reindexing `sa = hu` proves `G`-equivariance.
(4) Coordinate deletion commutes with this finite sum, so it is a cochain map. Put
`a_s(x) = s⁻¹ r(sx)`; transfer after restriction is the sum of pullbacks by `a_s`.
(5) In positive degree use the prism sum over `s` and `i` with sign `(-1)^i`, inserting
`a_s(x_i)` after `x_i` and applying `a_s` to subsequent coordinates. It is continuous,
linear and equivariant, since `a_s(ax) = a a_u(x)` under the same coset permutation.
(6) In `δK + Kδ`, faces before or after the inserted pair cancel in opposite-sign pairs.
(7) The two remaining faces telescope to `TR - |S| id`. At degree zero this follows
directly from `K₁ δF(x) = Σ_s (F(a_s x) - F(x))`; set the negative component to zero.
(8) Conjugate transfer and homotopy by the coordinate maps to obtain the specified
inhomogeneous maps. (9) A continuous equivariant linear coefficient map commutes with
all sums, actions and tuple substitutions, proving both naturality identities with one
choice of coset representatives. Applying this to a stable subspace inclusion gives
preservation; no completeness, local compactness or discreteness was used.
-/
theorem exists_continuousCochainFiniteIndexTransfer
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (H : OpenSubgroup G) :
    ∃ cor : ∀ (A : TopRep.{w} E G)
        (hA : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)),
        subgroupContinuousInhomogeneousComplex H.toSubgroup A hA ⟶
          continuousInhomogeneousComplex A hA,
      ∃ homotopy : ∀ (A : TopRep.{w} E G)
          (hA : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)),
          Homotopy (continuousInhomogeneousRestriction H.toSubgroup A hA ≫ cor A hA)
            (H.toSubgroup.index • 𝟙 (continuousInhomogeneousComplex A hA)),
        ∀ (A B : TopRep.{w} E G)
          (hA : Continuous (fun p : G × A ↦ A.ρ p.1 p.2))
          (hB : Continuous (fun p : G × B ↦ B.ρ p.1 p.2)) (b : A ⟶ B),
          (∀ (n : ℕ) (f : C(Fin n → H, A)) (g : Fin n → G),
            b ((cor A hA).f n f g) =
              (cor B hB).f n
                (ContinuousLinearMap.compLeftContinuous E (Fin n → H)
                  b.hom.toContinuousLinearMap f) g) ∧
          (∀ (i j : ℕ) (f : C(Fin i → G, A)) (g : Fin j → G),
            b ((homotopy A hA).hom i j f g) =
              (homotopy B hB).hom i j
                (ContinuousLinearMap.compLeftContinuous E (Fin i → G)
                  b.hom.toContinuousLinearMap f) g) := by
  sorry

end ContinuousCohomology
