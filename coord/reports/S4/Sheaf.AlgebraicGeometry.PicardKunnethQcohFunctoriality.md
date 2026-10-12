## What changed

Replaced `AlgebraicGeometry.Scheme.Modules.picard_kunneth_functoriality`'s proof hole
by an explicit Lean combination of two generic scalar-cohomology identities.
Unfold the external cup product and its coefficient comparison, apply pullback
and coefficient naturality of the scalar cup product, then apply commutative-square
pullback compatibility separately to the first and second projections. Signatures,
definitions, visibility and public imports of the existing module are unchanged.
Two new modules state the two missing scalar normalization identities, each with a
source and a complete proof in words. This is a decomposition, not a sorry-free proof.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.picard_kunneth_functoriality`
(lem-sc-picard-kunneth-qcoh-functoriality), 1 of 1 original holes.
No sorry remains in the assigned module.

Added, and still sorry:
- `AlgebraicGeometry.Scheme.Modules.scalarCup_pullback_coefficient_naturality`
  (lem-sc-scalar-cup-pullback-coefficient-naturality), in
  Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality.
- `AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_square`
  (lem-sc-scalar-cohomology-pullback-square), in
  Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackSquare.

The new statements are independent parts of the argument: one concerns a single
pullback and arbitrary coefficient maps, the other concerns two paths in an
arbitrary commutative square and contains no cup product or fibre-product claim.
The latter is applied twice. Neither is a restatement of the assigned theorem.
Both cover degree zero, identity morphisms, zero coefficients and empty schemes;
their section formulas have the indicated directions. The unchanged theorem is
proved from these statements, with no arbitrary choice of data added.

## No longer needed

Removed direct proof imports:
- Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine
  (lem-sc-cech-comparison-map-iso-affine).
- Sheaf.AlgebraicGeometry.ModulePullbackTensor
  (lem-weil-pbc-module-pullback-tensor).
- Sheaf.AlgebraicGeometry.TensorPullback
  (def-pc-module-pullback).
- Sheaf.Paper.CechCupPullbackCompat
  (lem-sc-picard-cech-cup-pullback-compat).

Pruned from the assigned node's proof dependencies:
- lem-sc-cech-comparison-map-iso-affine
- lem-sc-picard-affine-diagonal-intersections
- lem-sc-picard-cech-cup-pullback-compat
- lem-pc-module-pullback-identity-composition
- lem-weil-pbc-module-pullback-tensor
- def-pc-fibre-product

The affine-cover comparison and the affine-diagonal intersection lemma are not
needed by this functoriality proof: the general identities require no acyclicity
or inverse Cech comparisons. The tensor pullback definitions and tensor comparison
remain available through the unchanged public import of FieldLinearModuleCohomologyOperations;
the composition and tensor-pullback arguments remain dependencies of the two new nodes.
The Cech compatibility module is not used as a theorem by this reduction: its
quasi-coherence hypotheses do not cover the generic new statements. The source's
resolution arguments apply directly to all modules. Fibre-product notions remain
statement dependencies of the assigned node and in its public imports.
Thus removed direct imports do not imply those modules leave the targets' closure.
The unit's cube route and the parent Kunneth isomorphism are not bypassed.

## Where the brief, the DAG or earlier work was wrong

The initial S4 repository snapshot lacked the assigned module and its node, although
the synchronized Lean library contained its source and compiled dependencies.
The sandbox module was copied from that synchronized source; the delivery tool
refreshes and checks against the current sheaf-dag base.

The Cech naturality statements concern module cohomology operations, whereas the
assigned statement uses operations transported from scalar Ext. Their normalization
and comparison compatibility must be stated: the two new nodes isolate that glue.
No definition or statement was changed. The local literature files were absent;
source tags 01FD, 07MB, 0FKV and 0097 were read from the official Stacks Project pages.
Mathlib semantic search found only scheme pullback/section identities; Loogle knew
no project scalar operation; Mathlib grep had no hits. LeanSearch was unavailable.

## New nodes

`lem-sc-scalar-cup-pullback-coefficient-naturality`: scalar cup compatibility with a
single pullback and arbitrary maps on both coefficient modules. Source: Stacks
Tags 01FD, 07MB and 0FKV, and the tensor section argument in Kunneth Step 8.
The generic resolution and scalar comparison normalization are the remaining work.

`lem-sc-scalar-cohomology-pullback-square`: compatibility of successive scalar
pullbacks around a commutative square, with the precise unit-normalized coefficient
isomorphism. Source: Stacks Tags 0097 and 01FD, and Kunneth Step 8. It is used once
for each projection. No change record or forced adaptation is required.


## Second reading by S4

1. **Unchanged interface — pass.** Diffed every delivered module against the
   current repository. The only existing declaration is
   `AlgebraicGeometry.Scheme.Modules.picard_kunneth_functoriality`; its signature
   is byte for byte unchanged. Its definitions, visibility and public imports
   are unchanged. The two other modules are new, and no change record is needed.
2. **Proof and axioms — pass as a decomposition.** Compiled all three modules in
   import order with lcompile.py, without errors or warnings. Scratch copies with
   `#print axioms` for all three theorems showed exactly propext, Classical.choice,
   Quot.sound and sorryAx. The only two local sorries are the named scalar lemmas
   listed above; there is no new definition or prohibited declaration. Inspected
   the chosen coefficient comparisons: module_pullback_tensor is section-normalized,
   scalarPullbackCoefficient is determined through its adjunction, and the scalar
   Ext equivalence uses a fixed map and its inverse. No arbitrary existence
   witness or hollow definition was introduced.
3. **Split statements — pass.** Read the coefficient, cup, pullback, Ext comparison,
   composition and square definitions. The square is directed from a*b to c*d,
   and the cup comparison is directed from t*(F tensor G) to t*F tensor t*G.
   Checked degree zero, identity maps, zero coefficient maps, zero modules and
   empty schemes: the formulas reduce to section naturality and composition,
   with no sign change or extra hypothesis. Both lemmas are true independent
   parts of the argument and neither restates the external-product theorem.
   Read Stacks Tags [01FD](https://stacks.math.columbia.edu/tag/01FD),
   [07MB](https://stacks.math.columbia.edu/tag/07MB),
   [0FKV](https://stacks.math.columbia.edu/tag/0FKV), and
   [0097](https://stacks.math.columbia.edu/tag/0097).
   Their resolution, cup-comparison and adjunction arguments support the supplied
   natural-language proofs. Repeated semantic, type-pattern and text searches with
   different queries; Ext functor transport and adjunction uniqueness are available,
   but neither normalized scalar statement is already proved. The remaining
   comparison/unit/tensor diagrams prevent closing either in a few minutes.
4. **Reduction and pruning — pass.** Read the proof from the original hole:
   unfold externalCup and its coefficient iso, use cup naturality, then apply the
   square lemma separately to both projections. All new proof imports are plain
   imports, and each is used. The report lists all six old proof dependencies
   removed and all four direct proof imports removed. Public imports preserve the
   existing interface. No claim is made that these removals prune the entire
   target import closure. Read dag/units/sk-prop-av-cube.json: this node is not a
   realized unit statement or step; the unit's realization is unchanged and the
   parent Kunneth isomorphism and cube route are retained.
5. **DAG — pass.** The three proof steps and their dependency union match the
   Lean reduction. Checked both new nodes' statement/signature agreement, source,
   proof, proof_deps, proof_origin, searches, status, created, blueprint, chapter,
   unit and lean records. The parent node changes only allowed stage-3 fields.

Changed the existing theorem's stale Cech-proof docstring to describe the actual
scalar reduction; changed no proof or signature. Added independent search evidence
in the two new nodes and this review section. Closed no additional hole.
One original hole is closed and two are added: this is a decomposition with local
net -1, not a sorry-free proof or a claim of ledger progress.
