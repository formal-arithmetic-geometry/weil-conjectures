## What changed

Repair of reviewer X-1f505, points C1 and C2: the polynomial-lifting node now has
six detailed non-elementary proof steps. They justify inverse closure of the image,
containment of the image of R via the identity triple, containment of the residue
field via localization fractions, separability of the minimal polynomial over the
residue field, finite coefficient lifting, and the derivative condition via a Bezout
identity. Every step cites existing supporting nodes; `proof_deps` is their union.

The existing proof of `AlgebraicGeometry.Scheme.etaleResidueTriples_colimit_surjective`
is retained and compiled.  It applies the polynomial lifting intermediate theorem and
the supplied simple-root lifting hypothesis elementwise.  The proof dependency import
`Sheaf.RingTheory.EtaleResidueTriplesPolynomialLift` is used directly.

## Proved and sorry left

`AlgebraicGeometry.Scheme.etaleResidueTriples_colimit_surjective` is proved by a
complete Lean proof.  The imported intermediate declaration
`AlgebraicGeometry.Scheme.etaleResidueTriples_polynomial_lift` remains a `sorry`; it is
the explicitly split polynomial-lifting node
`lem-weil-pbc-etale-triples-colimit-polynomial-lift`.

## No longer needed

The unused `Mathlib.CategoryTheory.Filtered.Basic` import was removed from both the
item and the new polynomial-lifting module.  The polynomial-lifting dependency is
used; no DAG node was pruned.

## Where the brief, the DAG or earlier work was wrong

The returned polynomial-lifting node incorrectly marked the entire image-field and
separable-polynomial argument as elementary with no dependencies. C1 is repaired by
citing the residue-field identification and localization nodes and the separable
extension and separable-polynomial definition nodes, with explicit fraction and
Bezout arguments. C2 is repaired by separating the six steps, marking each
`elementary: false`, and synchronizing `proof_deps`. The minimal polynomial is taken
over the residue field, so separability over the larger image field is unnecessary.

## New nodes

The node `lem-weil-pbc-etale-triples-colimit-polynomial-lift` was already supplied in this sandbox as a separate
intermediate theorem. Its statement is unchanged; its proof plan
and dependency list are repaired as described above. Its Lean proof remains deferred
to a subsequent worker. No additional nodes or sorries were introduced.


The existing public-import removal is recorded in
`coord/changes/etale-residue-triples-surjective-imports.md`.

## Second reading by F2

1. **Unchanged declarations.** I diffed the delivered surjectivity module against the
repository version. The theorem signature and all existing declarations are byte-for-byte
unchanged; only the proof and the proof-only import changed. Verdict: pass.

2. **Compilation and trust.** Both delivered modules compile with `lcompile.py --all`.
The surjectivity theorem has no `sorry`; the only remaining `sorry` is the named,
documented polynomial-lifting theorem and its matching DAG node. The delivery contains
no forbidden declarations. Scratch-copy `#print axioms` checks show exactly `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx` for both declarations; the latter is expected from
the explicitly deferred polynomial-lifting theorem.
Verdict: pass.

3. **Split-off statement.** The polynomial-lifting statement is a genuine intermediate
coefficient-and-simple-root result that omits the root-lifting hypothesis and
does not assert surjectivity. Its six steps cover inverse closure, residue-field containment,
separability, coefficient lifting, and the derivative argument. The zero-element case is covered by the monic minimal polynomial construction;
a degree-zero minimal polynomial is excluded by its vanishing evaluation. Searches recorded in `searches.jsonl` found no
existing declaration of this result. Verdict: pass.

4. **Route and pruning.** The surjectivity proof follows the shortest available route:
apply polynomial lifting elementwise, then apply `hroot`. The unit route is preserved.
The unused filtered-category import was removed from both modules and recorded in the
change record; no proof dependency node is unused. Verdict: pass.

5. **DAG agreement.** The polynomial-lifting node's six non-elementary steps and
`proof_deps` match its documented Lean theorem and the source route. The item node records
the polynomial-lifting dependency and the surjectivity reduction. Verdict: pass.

I expanded the new polynomial-lifting theorem docstring into the complete six-step
argument, supplied its missing statement dependencies, and recorded the existing
Mathlib monic-lifting lemmas in step 5 of its node. No Lean signatures or proof terms
changed. I also added this second-reading report section.
