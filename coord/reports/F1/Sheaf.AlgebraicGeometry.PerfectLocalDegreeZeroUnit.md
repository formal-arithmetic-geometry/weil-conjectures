## What changed

Proved the body of `AlgebraicGeometry.surjective_stalk_homology_of_perfect_local_unit`
in `Sheaf.AlgebraicGeometry.PerfectLocalDegreeZeroUnit`, with its signature and all public
imports unchanged. The proof now evaluates the negative zero fibre cohomology sheaves,
uses subsingleton finrank to prove their Betti numbers zero, proves the degree-zero Betti
number one, and applies `Scheme.exists_finiteFreeResidueModel`. It constructs strict
perfectness from the finite-free term isomorphisms, proves each negative term zero using
the empty generator type, and rewrites the degree-zero term rank to one. Finally it
applies the separate fixed-model stalk calculation.

Added `Sheaf.AlgebraicGeometry.DerivedResidueUnitBetti`, whose public theorem proves the
degree-zero Betti number calculation without a direct sorry. Its private helper computes
derived residue pullback of the structure sheaf from `flatComplexDerivedPullback`, the
single/homotopy localization comparisons, the tensor pullback adjunction, and ordinary
pullback of the unit. Taking cohomology and sections and transporting scalars along
`GammaSpecIso` gives an isomorphism to the residue field as a module over itself.

Added `Sheaf.AlgebraicGeometry.ConnectiveRankOneModelStalk`, with the remaining local
chain-map and stalk calculation as one public theorem. Its proof dependencies are
imported privately. Updated the item's DAG proof and added records for both new modules.
No existing statement, definition, visibility, or public import changed. No adapted
modules or change records are needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.surjective_stalk_homology_of_perfect_local_unit`
(node `lem-sc-perfect-local-degree-zero-unit`). There are no sorries left in the item.

Also proved `AlgebraicGeometry.Scheme.derivedFiberBetti_zero_eq_one_of_unit_iso`
(node `lem-sc-derived-residue-unit-betti`) and its private helper
`AlgebraicGeometry.Scheme.residue_unit_single_iso`. They contain no direct sorry;
existing imported theorem dependencies remain as in the library.

Added exactly one hole:
`AlgebraicGeometry.surjective_stalk_homology_of_connective_rank_one_model`
(node `lem-sc-connective-rank-one-model-stalk`), in its own new module, with proof exactly
`:= by sorry`. This is a decomposition: one original hole closed and one lower hole
added, net zero holes. It does not finish the full mathematical proof.

The lower statement is the fixed-representative part of the argument, rather than the
original theorem under another name. It assumes an explicit affine model, its strict
perfectness, zero negative terms, and a rank-one degree-zero term; it does not produce
that model, derive its ranks, or assume perfectness or negative residue cohomology of E.
The item's Lean proof supplies all these missing steps from existing theorems and the
proved dimension calculation.

All three modules compile together in import order with `lcompile.py --all`, without
warnings. The delivery dry run is the final mechanical check.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative`
from the item. It remains needed in the new fixed-model stalk lemma, so its module and
node `lem-pc-perfect-affine-map-representative` are not globally pruned.

The item's direct proof dependency `def-pc-module-stalk-functor` is likewise now used in
the fixed-model lemma instead. `lem-sc-perfect-finite-free-residue-model` stays needed.
No nodes or modules of the original route become globally unnecessary: pruning is none.
The cube unit and its route are preserved.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or mathematical error found. The DAG's second step bundles
chain-map representation, restriction and residue comparisons, lifting a nonzero residue
coefficient to a local unit, and naturality of stalk cohomology. The representative
lemma only supplies a chain map once the source and target representatives and arrow
are in place; it does not supply those other comparisons. Those are the precise work
remaining in the new fixed-model item. The first step's dimension calculation and
model specialization are now formalized.

Read the two existing dependency modules and their node records and the module-stalk
node. Checked the cube unit record. The local source pages were read at
https://stacks.math.columbia.edu/tag/0E62 and https://stacks.math.columbia.edu/tag/0BCD;
the latter supplies the prescribed-rank model, and the former supplies the residue unit
argument. The fixed-model proof in words elaborates that local argument.

Searches: LeanFinder found residue/stalk ring theorems and HomComplex/Ext representative
APIs but no exact theorem. Loogle found no joint finrank/IsZero result. Grep found
`Module.finrank_zero_of_subsingleton`, `ModuleCat.restrictScalarsIsoOfEquiv`,
`LinearEquiv.finrank_eq`, the bounded-flat pullback comparison, and the ordinary unit
pullback isomorphism, all used in the proof. LeanSearch returned Internal Server Error;
its unavailability is recorded, not treated as evidence of no match. Blueprint searches
for rank one and 0E62 found no duplicate of either new statement.

Edge cases checked mathematically: the chosen point makes the affine neighbourhood and
its residue field nonempty. The zero target cannot satisfy ha, since the source residue
H^0 is the nonzero residue field. Positive higher terms are allowed. In the fixed-model
lemma, zero incoming terms make residue H^0 a kernel; an invertible residue H^0 map
forces a nonzero degree-zero coefficient even if the residue outgoing differential was
not assumed zero. That coefficient is a unit in the local ring, and the chain-map
equation forces the outgoing stalk differential zero. No hypothesis on other points,
properness, noetherianness, or global connectivity was added.

## New nodes

`lem-sc-derived-residue-unit-betti` records the proved fibre dimension calculation in
`lean/Sheaf/AlgebraicGeometry/DerivedResidueUnitBetti.lean`. It works for arbitrary E and
uses no perfectness or negative cohomology hypothesis. Its dependency on the generic
flat-complex pullback theorem is a tool use for the structure-sheaf single complex.

`lem-sc-connective-rank-one-model-stalk` records the remaining explicit-model local
calculation in `lean/Sheaf/AlgebraicGeometry/ConnectiveRankOneModelStalk.lean`. Its docstring
and node spell out the chain-map, unit-coefficient and stalk transport argument. The
existing affine map representative and exact module stalk theorems are generic tools.
Both nodes belong to the item's chapter and cube unit and retain its blueprint ancestor.

## Second reading by F1

1. **Existing interfaces — pass.** Compared the item with the repository using `diff -u`.
   The sole existing theorem signature is byte-for-byte unchanged, as are all public
   imports, definitions and visibility. Changes are its proof and private imports;
   the other two modules are new. No change record or forced adaptation is needed.
2. **Proof and axioms — pass as a decomposition.** Independently compiled all three
   modules in import order with `lcompile.py --all`: no errors or warnings. Compiled
   scratch copies with `#print axioms` for the original theorem, the new Betti theorem,
   its private helper, and the fixed-model theorem. All four report only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The last reflects the one declared
   new hole and existing open imported results; these are not axiom-free completed
   proofs. A source scan finds exactly one direct sorry, the named fixed-model theorem,
   and no forbidden declarations or hollow definitions. All witness elimination is
   inside proposition proofs; no data definition chooses an arbitrary existence witness.
3. **Split statements — pass.** The remaining statement supplies the actual affine
   representative, vanishing negative terms and a rank-one term. It omits the model
   construction and fibre-dimension calculation now performed by the item, so is
   strictly a part of the original argument. Over a field it reduces to the elementary
   rank-one chain-map calculation. Over an arbitrary local ring, nonzero residue of
   the coefficient makes it a unit, and the chain-map equation annihilates the outgoing
   differential. Incoming boundaries vanish. Empty U cannot contain s; a zero E cannot
   satisfy ha; positive terms and nonzero positive cohomology are allowed. The docstring
   includes the restriction, residue and naturality transports and gives a full proof
   in words, with sources and a matching node. Re-read Stacks 0E62 and 0BCD. Independent
   LeanFinder search for connective perfect complexes and derived tensor surjectivity,
   Loogle search for `SheafOfModules.unit, _ ≅ _`, and grep of Sheaf, upstream and
   Mathlib found component APIs but no available exact replacement. The related flat
   single helper in DerivedPullbackSingleCohomology is private; its public theorem needs
   derived-category instances for all schemes, stronger than this item's assumptions.
   The monoidal unit theorems require additional supplied monoidal comparison data.
4. **Route and pruning — pass, inherited bookkeeping limitation recorded.** The proof
   uses the prescribed finite-free model followed by the local unit calculation. The
   remaining hole cannot be closed by a small API application: it still requires the
   chain-map, restriction, residue and stalk comparisons. The item's previous direct
   dependencies on the affine representative and module stalk move to that lower
   theorem; the finite-free model remains. Thus none of the old proof dependencies is
   globally pruned. The cube unit record's `realized.statement` and sole step list are
   already empty on the repository baseline; this delivery preserves them and the
   existing cube route, without claiming to repair that inherited omission. The
   fixed-model proof imports are retained as dependencies of its documented proof plan.
5. **DAG — pass after repair.** Checked all three node records against the Lean,
   including the new-node fields, chapter, unit, blueprint ancestry and dependencies.
   Corrected the Betti node: the proof actually uses the existing nonempty adjunction
   from `def-pc-module-pullback` and the proved upstream `Modules.pullbackObjUnitIso`,
   rather than the stronger pinned adjunction and tensor-unit theorem previously cited.
   Its proof steps and proof_deps now reflect those uses. Recorded both new signatures
   verbatim, preserving their formatting, in their lean records.

Second reading changed only DAG dependency/signature records and this report. The Lean
proofs and statements were retained. One original hole closed and one strictly lower
hole added is a decomposition with net zero holes; pruning remains none.
