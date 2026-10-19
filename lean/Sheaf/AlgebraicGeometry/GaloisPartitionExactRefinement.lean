/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.Paper.GaloisPartitionModules
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Sheaf.RepresentationTheory.NormalSubgroupIndUnipotence
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.CategoryTheory.Galois.StacksGaloisCategory
import Sheaf.AlgebraicGeometry.FiniteEtaleFiniteLimits
import Sheaf.CategoryTheory.Galois.StacksGaloisAxioms
import Sheaf.CategoryTheory.Galois.StacksGaloisObjectExists
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Sheaf.Topology.NoetherianGoodStratificationRefinement
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageColimits
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.AlgebraicGeometry.TorsionLocalSystemMonodromy
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic

/-!
# Exactness and directed common refinements of Galois partitions

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, 7.3.4, 7.3.6,
7.3.8 and 7.4.5 (blueprint: lem-per-galois-partition-exact-refinement).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.GaloisPartition

/-- The constructible objects in the weak class of a Galois partition. The existing
constructibility predicate means locally constant with finitely generated stalks on a finite
locally closed stratification; on Noetherian schemes every locally closed stratum is
constructible. Source: ILO XVII, 7.4.5
(blueprint: lem-per-galois-partition-exact-refinement). -/
def constructible {X : Scheme.{u}} (P : GaloisPartition X)
    (A : Type (u + 1)) [CommRing A] :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  fun F => P.modules A F ∧ IsConstructibleSheaf F

/-- Directed means some ordering of the strata has closed complements after every initial
segment. Equivalently, each next stratum is open in the remaining reduced closed complement:
the reduced structure leaves this topological condition unchanged. This includes the empty
partition. Source: ILO XVII, Definition 7.3.5
(blueprint: lem-per-galois-partition-exact-refinement). -/
def IsDirected {X : Scheme.{u}} (P : GaloisPartition X) : Prop :=
  ∃ e : Equiv.Perm (Fin P.n), ∀ k : Fin (P.n + 1),
    IsClosed ((⋃ i : Fin P.n, ⋃ (_ : i.val < k.val), P.stratum (e i))ᶜ)

/-- The weak class is abelian with exact inclusion, closed under extensions and all small
filtered colimits. Its constructible objects are closed under kernels, cokernels and
extensions. Any finite family of partitions has a directed common refinement, with weak-class
inclusions simultaneously for every commutative coefficient ring.

Source: ILO XVII, 7.3.4, 7.3.6, Exercise 7.3.8 and Definition 7.4.5
(blueprint: lem-per-galois-partition-exact-refinement).

Proof plan:
1. Constant-coefficient inverse image is exact (lem-pe-constant-left-module-inverse-image)
and commutes with filtered colimits (lem-weil-pbc-inverse-image-preserves-colimits and
lem-weil-pbc-module-sheaves-colimits-forgetful). Thus restrictions compute kernels,
cokernels, extensions and filtered colimits in the ambient module sheaves.
2. On each stratum its Galois cover determines an open normal subgroup H of pi_1
(thm-galois-fundamental, def-galois-object). By finite-etale descent and the monodromy
comparison of lem-per-torsion-local-system-monodromy, the generators are precisely the
representations trivial on H; finite extensions and filtered colimits are H-ind-unipotent.
Finite generation is unnecessary. Over Noetherian A finite-orbit spans exhaust a discrete
representation, and the finite-generation clause of lem-per-normal-subgroup-ind-unipotence
and lem-weil-pbc-noetherian-submodule-finite identify the finite-type version as well.
3. The kernel, cokernel, extension and filtered-colimit closure of H-ind-unipotent modules
(lem-per-normal-subgroup-ind-unipotence), transported by that exact monodromy equivalence,
gives the corresponding ambient closure. Zero and sums belong. Fullness transports the
ambient coimage-image isomorphism, giving an abelian category with exact inclusion.
4. Within the weak class constructible means finite stalks over A (finite generation).
Kernel stalks are finite by Noetherianity, cokernels by images of generators, extensions
by generators of the submodule and lifts of quotient generators. This proves all three
closure assertions for constructible objects.
5. Intersect the finite stratifications using actual fibre products
(lem-weil-pbc-constructible-stratification-intersection), take a good refinement
(lem-sfb-noetherian-good-stratification-refinement), and equip the pieces with reduced
locally closed structures (lem-weil-pbc-reduced-induced-closed-subscheme).
For no inputs start with X; for empty X use the empty partition.
6. Order the good pieces by maximal remaining closure: goodness and disjointness make
each next piece open in the remaining closed complement. Split each into finitely many
clopen connected components (lem-sfb-noetherian-connected-components-open).
7. Over each connected new stratum take the product of pulled-back old covers
(lem-fet-finite-limits), choose a nonempty connected component in its Galois category
(lem-fet-galois-category, def-galois-category), and dominate it by a Galois object
(lem-galois-object-exists). Its automorphism action is simply transitive
(lem-galois-axioms), so it supplies the new Galois cover. With no old covers use the identity.
8. For every commutative B, pulling an old generator to a new stratum makes it constant
on the chosen cover (lem-sfb-geometric-inverse-image-constant-module). Exactness pulls back
finite filtrations, and preservation of filtered colimits pulls back their colimits.
This proves all the weak-class inclusions with the same directed partition. -/
theorem exact_refinement (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] [Algebra (ZMod ℓ) A] :
    (∀ P : GaloisPartition X,
      Nonempty (Abelian (P.modules A).FullSubcategory) ∧
      PreservesFiniteLimits (P.modules A).ι ∧
      PreservesFiniteColimits (P.modules A).ι ∧
      (P.modules A).IsClosedUnderExtensions ∧
      (∀ (J : Type (u + 1)) [SmallCategory J] [IsFiltered J],
        (P.modules A).IsClosedUnderColimitsOfShape J) ∧
      (P.constructible A).IsClosedUnderKernels ∧
      (P.constructible A).IsClosedUnderCokernels ∧
      (P.constructible A).IsClosedUnderExtensions) ∧
    (∀ (n : ℕ) (P : Fin n → GaloisPartition X),
      ∃ R : GaloisPartition X, R.IsDirected ∧
        ∀ (i : Fin n) (B : Type (u + 1)) [CommRing B], R.Refines (P i) B) := by
  sorry

end AlgebraicGeometry.Scheme.GaloisPartition
