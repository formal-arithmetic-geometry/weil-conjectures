## What changed

Replaced the named hole `AlgebraicGeometry.clopenRankStrata_formality` with a
compiling proof. The original signature and docstring are unchanged.

The proof builds the finite set of integer ranks, proves the comparison terms
are zero outside it using the existing
`Scheme.Modules.isZero_of_isEmpty`, and uses `hK` to prove vanishing of K in
all omitted integer degrees. It lifts each supported homology isomorphism to
a map from its single complex, then assembles those maps.

Added `Sheaf.AlgebraicGeometry.FiniteZeroDifferentialAssembly`, whose public
theorem `DerivedCategory.finiteZeroDifferentialAssembly` is fully proved for
an arbitrary abelian category. Its proof constructs degree projections,
sums their composites with the lifted maps, and proves that the sum is an
isomorphism by `DerivedCategory.isIso_iff`. The supported-degree calculation
is proved using `ShortComplex.LeftHomologyMapData.ofZeros`; other summands
factor through zero homology of single complexes. Outside the finite support,
both homology objects are zero. No coproduct-preservation assumption is used.

Added `Sheaf.AlgebraicGeometry.ClopenRankStrataHomologyLift`, with the one
remaining named hole. It isolates a one-stratum map-lifting step: n is fixed,
the other homology degrees have their prescribed supports, but degree-n
homology is not specified, and an arbitrary map into it must lift. It assumes
no finite image of r and concludes no global isomorphism. It is therefore a
strict part of the original argument, rather than formality under another name.
The parent now contains the finite support, lift-to-isomorphism, and assembly
argument in Lean. Updated its proof, proof_deps and proof_origin accordingly.

Added proof imports of these two modules and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` to the item. Existing
public imports and visibility are unchanged. No existing interface changes,
forced adaptations, or change records are needed. All writes are in the sandbox;
no delivery was pushed.

## Proved and sorry left

Original holes closed: one,
`AlgebraicGeometry.clopenRankStrata_formality`
(`lem-sc-clopen-rank-strata-formality`). No sorry remains in the item's module.

New holes added: one,
`AlgebraicGeometry.clopenRankStrata_homology_lift`
(`lem-sc-clopen-rank-strata-homology-lift`), in its own new module. Its proof
is exactly `:= by sorry`; its docstring and node give the characteristic
idempotent, termwise image construction, homology computation, canonical
truncations, and factorization of the prescribed map.

The other new public theorem,
`DerivedCategory.finiteZeroDifferentialAssembly`
(`lem-sc-finite-zero-differential-assembly`), and its private projection helper
have complete proofs and no sorry. This delivery is a decomposition: one upper
hole closed and one strictly smaller geometric hole added, net zero holes.
The categorical assembly and finite-support parts are actually proved.

Edge cases checked against the statements and proofs: negative degrees are
included in hK and in the new helper's hother; an empty source or empty stratum
has zero terms; an empty finite support gives the empty sum between acyclic
derived objects; rank zero is an ordinary supported degree. The new lifting
statement permits zero maps and arbitrary degree-n target homology. Its
proof factors maps into the characteristic-idempotent image by module
linearity, so neither projectivity nor injectivity of E is needed. Objects
are not constructed from arbitrary existence witnesses in definitions:
there are no new definitions; all choices are morphisms inside theorem proofs.

Validation: all three delivered Lean modules compile together in import order.
The explicit axiom check of `DerivedCategory.finiteZeroDifferentialAssembly`
prints exactly `propext`, `Classical.choice`, and `Quot.sound` (no sorryAx).
The delivery tool's own probes found no forbidden axioms. The dry run printed
OK and passed the preflight except for the second reading, which is reserved
for the independent next worker. LeanSearch returned Internal Server Error;
both new nodes record that service as unavailable, in addition to the completed
LeanFinder, Loogle, and Mathlib-source searches. Nothing was pushed.

## No longer needed

No original import, module, or node is pruned. All four original public imports
are required by the unchanged signature. The original definitions omitted
from the updated proof_deps remain statement dependencies or dependencies of
the one-stratum lifting statement; they are not counted as pruning.

The proof avoids constructing a global finite biproduct of idempotent images
and avoids truncating the comparison complex separately: finite sums of
projections and lifted morphisms supply the assembly instead. There is no
existing separate module for either of those abandoned substeps to prune.
The rejected `clopenRankStrata_formality_on_range` helper from the earlier
attempt remains excluded from the delivery and is not counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier range-restricted helper was false: it imposed no condition on
negative homology of K. This delivery does not use it. Here `hK` controls all
integer degrees. For example the previous counterexample with a nonzero
module in degree -1, r constantly zero and every E zero violates hK at -1;
it also violates the new lifting helper's hother for n = 0 at m = -1.

The original proof dependencies mostly provide definitions, not the rank
idempotent splitting or a morphism lifting theorem. The missing one-stratum
step is now explicit as a strictly smaller statement. The node's final
assembly step is implemented as a finite sum of maps rather than a finite
sum of component isomorphisms. This is a change below the unit level;
`sk-thm-picard-duality` and its realized statements/steps are unchanged.

The original citation of Tag 0BQZ is motivating context, not an exact general
formality theorem: [0BQZ](https://stacks.math.columbia.edu/tag/0BQZ) concerns
Koszul-regular ideals and their dual complexes. The new helper explicitly
labels its rank-stratum expansion as agent-written and supplies the actual
supporting sources, [00EE](https://stacks.math.columbia.edu/tag/00EE) for
idempotents and [0118](https://stacks.math.columbia.edu/tag/0118) for canonical
truncation. [0AVW](https://stacks.math.columbia.edu/tag/0AVW) supplies the
direct-image algebra setup, not a quasi-coherence assumption for this lemma.
The construction needs arbitrary module sheaves only.

## New nodes

`lem-sc-clopen-rank-strata-homology-lift` records the remaining one-stratum
map-lifting step. It inherits the item's chapter and unit, cites the original
steps 1--2 as its origin, and has no proof dependency on the parent. Its proof plan
uses the existing clopen-idempotent theorem and the Mathlib single-degree
concentration leaf. Its Lean module is
`Sheaf.AlgebraicGeometry.ClopenRankStrataHomologyLift`.

`lem-sc-finite-zero-differential-assembly` records the fully proved generic
finite-sum assembly theorem. It inherits the same chapter and unit and realizes
the parent's assembly step. Its Lean module is
`Sheaf.AlgebraicGeometry.FiniteZeroDifferentialAssembly`. Both nodes contain
verbatim Lean signatures, self-contained statements and proofs, and semantic,
type/name and Mathlib-source searches. Whole-blueprint searches found no exact
duplicate. Neither new node depends on the parent, so the replacement route
introduces no DAG or import cycle.

## Second reading by V3

1. I compared the delivered formality module with the repository version. The
existing theorem signature and docstring are unchanged; only proof-only imports,
proofs, and the declared proof route changed. The two added modules and DAG
nodes are the only new declarations, with no target statement changes.

2. I compiled all three delivered modules together with `lcompile.py`. They
compile cleanly. The only remaining `sorry` is the named theorem
`AlgebraicGeometry.clopenRankStrata_homology_lift`, which has a public
statement, source docstring, and matching node; no definition contains a
`sorry`, and no forbidden declarations or axioms were introduced. The complete
assembly theorem uses only the permitted axioms.

3. The assembly theorem is a strict generic reduction and its finite-support
edge cases (empty support, zero terms, and degrees outside support) are valid.
The homology-lifting theorem is a strict one-stratum map-lifting statement,
with weaker conclusion and hypotheses than the parent formality theorem; its
negative-degree and empty-stratum cases are explicitly covered. I found no
existing declaration duplicating either statement.

4. The proof follows the shortest available route in the delivered imports:
finite support is reduced to zero terms, the generic finite assembly theorem is
applied, and the unresolved geometric step is isolated as the smaller lifting
statement. The parent theorem's original public imports remain required. I
removed the unused proof import `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`
from `ClopenRankStrataHomologyLift`; no DAG proof dependency is otherwise
pruned, and the unit reference and route are unchanged.

5. The DAG nodes' Lean signatures, proof dependencies, origins, chapter, and
unit agree with the delivered declarations. The parent node records the finite
support, lifting, and assembly steps actually used. The unit's realized route
is not altered.

Changed in this reading: removed one unused import and documented the checks
above; no theorem statements or definitions were changed.
