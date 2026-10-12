## What changed

Proved `AlgebraicGeometry.Scheme.Hom.etale_fibre_discrete_separable_points` with its statement
unchanged. Added proof-only imports of `Mathlib.AlgebraicGeometry.Sites.EtalePoint` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`.

The proved source instance `LocallyQuasiFinite.of_etale`, Mathlib's discrete set-theoretic fibre,
and `fiberHomeo` prove discreteness. The proved source `etale_residueFieldMap` and residue-field
naturality show that the spectrum of the canonical map `i` is etale; ring-level etale field
results give finite separability, with the minimal polynomial providing each witness.
For the singleton open, lift its residue-field spectrum into it. This is a surjective closed
immersion with reduced target, hence an isomorphism. The lift equation proves the requested
compatibility with `Spec.map i`.

Updated the existing node's proof, proof dependencies, and proof origin to follow this route.
The unit `sk-thm-p1` does not list this node among its realized statement or proof steps;
the shortened argument stays below the unit level. The closed node
`etale-proposition-etale-reduced` is used as a tool for reducedness.

## Proved and sorry left

Proved the only sorry: `AlgebraicGeometry.Scheme.Hom.etale_fibre_discrete_separable_points`
(node `lem-weil-pbc-etale-fibre-discrete-separable-points`). No sorry remains and none is added.
The complete module compiles without warnings. The delivery dry run checks the declaration's
transitive axioms, in addition to local and server compilation.

The empty fibre causes no issue: discreteness is available and the universal point assertion
is vacuous. The proof does not assume the whole fibre is finite or quasi-compact. The algebra
used for finite separability is precisely `i.hom.toAlgebra`; no alternative base-field map is
substituted. The singleton isomorphism's orientation is the one in the original statement.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.SpecFiniteProductFields` and the node
`lem-weil-pbc-spec-finite-product-fields` from this proof's dependencies. Also removed
`lem-weil-pbc-etale-algebra-over-field-product`, whose affine coordinate decomposition is
unnecessary. These are pruned from this item's route; they may still have other users.
Base change, composition, spectra, residue fields, and separability notions remain in use.
No other existing import was removed. No new modules or new nodes are delivered.

## Where the brief, the DAG or earlier work was wrong

The previous plan is mathematically valid, but its missing affine/component glue is avoidable
with the already proved source tools. Its recorded searches had correctly found
`LocallyQuasiFinite.of_etale` for discreteness; the same source library additionally has
`etale_residueFieldMap` and `isReduced_of_etale`, which finish the field and singleton clauses.
The existing theorem docstring records that original plan; the node and this report record
the implemented route. No statement or definition correction was needed.

Searches in this session: LeanFinder on finite separable etale residue fields and singleton
spectra returned ring etale-locus facts and the unramified local-ring separability instance;
Loogle on `Scheme.Hom.finite_residueFieldMap` reported an unknown identifier (it is a source
library theorem, not Mathlib). Local `rg` found and the worker read the source proofs of
`LocallyQuasiFinite.of_etale`, `etale_residueFieldMap`, and `isReduced_of_etale`, and Mathlib's
surjective closed immersion isomorphism theorem. No new statement was needed.

## Second reading by E2

1. Compared the complete delivered module with the repository version using `diff -u`.
   The existing theorem signature and docstring are byte-for-byte unchanged; there are no
   changed definitions or additional declarations. Only its proof and proof-only imports
   differ. No change record is required. Verdict: pass.
2. Compiled the delivered module locally without errors or warnings. Compiled a scratch
   copy with `#print axioms AlgebraicGeometry.Scheme.Hom.etale_fibre_discrete_separable_points`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered
   Lean contains no sorry or forbidden declaration mechanism. Read the source proofs of
   quasi-finiteness, etale residue-field maps, reducedness, and Mathlib's reduced surjective
   closed immersion criterion. Verdict: pass.
3. There are no split-off statements, new nodes, or new declarations to validate or search
   for duplicates. Checked the empty-fibre case and the absence of any global finiteness
   assumption. The finite/separable argument uses precisely `i.hom.toAlgebra`; minimal
   polynomials supply separable annihilating witnesses. The singleton construction uses
   reducedness, so it does not incorrectly infer an isomorphism from a topological bijection.
   Verdict: pass.
4. Read the proof top-down and searched the library and Mathlib residue-field/open-immersion
   sources for existing singleton/residue-spectrum results. The proof directly combines
   closed source and Mathlib tools, without new intermediate assumptions. Both new imports
   are proof-only; the public imports supply notions in the unchanged signature. All old
   proof dependencies absent from the new route are listed under `## No longer needed`:
   the finite-product algebra and finite-product spectrum nodes. Read `sk-thm-p1.json`:
   none of these pruned nodes realizes a unit statement or step. Verdict: pass.
5. Compared the node versions and checked every new proof step against the Lean argument.
   Only `proof`, `proof_deps`, and `proof_origin` change; the step dependency union equals
   `proof_deps`. The records describe the base-change etale projection, residue-field
   naturality, field finiteness/separability, and the reduced singleton lift used in Lean.
   Statement, statement dependencies, Lean declaration record, and unit are preserved.
   Verdict: pass.

Second reading changed only this report, adding the independent checks above. The proof,
imports, and node metadata required no repair. No additional statement is split off.
