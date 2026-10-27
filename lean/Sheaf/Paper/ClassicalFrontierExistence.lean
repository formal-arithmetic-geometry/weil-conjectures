/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.ClassicalLisseWeilFrontierData

/-! # Classical Weil restriction along finite-field frontiers

Source: blueprint `thm-zl-real-mixed-by-curves`, proof paragraphs 6--7;
BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-zl-classical-frontier-exists).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlFrontier
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
variable (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- A finite-field frontier subordinate to the supplied reduced partition, with
its actual scheme-theoretic geometric factorizations. No Weil structure is used.
Source: blueprint thm-zl-real-mixed-by-curves, paragraphs 6--7;
Stacks 0B8X, 06LH, 01ZM
(blueprint: lem-zl-classical-frontier-exists).

Proof: if the original finite-field scheme is empty, take degree one and the
length-zero chain on its empty reduction, using the unique isomorphism to the empty
scheme. Otherwise factor every reduced stratum scheme-theoretically through the
nilradical subscheme when the given support is the unreduced fibre: a map to a
reduced ring kills nilpotents. These maps give the same locally closed partition
of the reduction. Apply smooth_affine_frontier_stratification to that partition.
Its finite-field diagram gives the reduced closed chain, open differences, finite
clopen covers, nonempty smooth affine geometrically connected pieces and their
constant dimensions. Turn the start and finish equalities into Over isomorphisms.
The theorem's ambient comparison need not be the canonical associativity map.
Compose it with the inverse canonical comparison to get an automorphism of the
geometric ambient scheme. By finite presentation descend that automorphism, its
inverse and their two inverse equations to one further finite extension. Base
change the entire frontier to that field and compose every ambient map with this
automorphism. Transport the initial reduction isomorphism by its induced reduction
automorphism. All differences, clopen covers and dimensions are preserved; geometric
connectedness persists under the field extension. Now the geometric ambient maps
are the canonical maps followed by the original comparison, as required. This is
also obtained by doing the finite-diagram descent with its ambient projection fixed.
On each piece the finite-type, quasi-compact and separated structures follow from
its immersion into the finite-type separated ambient scheme. Use the corrected
piece ambient map for inclusion and the supplied stratum factor for factor and
intoSupport. The preceding comparison equation gives geometric_piece, and the
factor is an immersion as in the frontier theorem.
Its dimension-zero isomorphism supplies zero_dimension. Reattach the original
lattice label at the same stratum: the frontier itself does not choose a new
classical object or a new lattice. The empty case has no pieces or smoothness
obligations.
-/
theorem classical_frontier_exists
    (R : Realization D l Ω)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (reduced : Bool)
    (M : sfCommonStageHeart l (supportBase D (fiberBase D Y₀) reduced).scheme Ω)
    (P : PartitionData D l Ω R (supportBase D (fiberBase D Y₀) reduced) M) :
    Nonempty (Frontier D l Ω R Y₀ (supportBase D (fiberBase D Y₀) reduced) M P
      (supportInclusion D (fiberBase D Y₀) reduced)) := by sorry

end WeilConjectures.ZlFrontier
