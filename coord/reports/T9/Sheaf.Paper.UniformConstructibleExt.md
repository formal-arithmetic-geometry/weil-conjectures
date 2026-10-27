## What changed

Added the proved special-case theorem
`AlgebraicGeometry.ProEtale.uniformConstructibleExt_normalConnectedSource` to the assigned
module. For a nonempty connected source with normal stalks it proves the exact original
cutoff `cd_ell(j) + cd_ell(S) + 2` against every constructible target, for both rational
coefficient choices. Normality is required only on the original source S.

The proof retains the finite coefficient model supplied by the already proved
`uniformConstructibleExt_latticeModel`. The source immersion supplies local
Noetherianness. The declared normal finite-coefficient lattice theorem produces an
embedded integral lattice in that exact model. Its coefficient inclusion is definitionally
the recorded rational inclusion. The proof transports free local models along the
cartesian coefficient isomorphism to obtain the lattice structure required by the
conditional estimate, retaining the actual inclusion and its invertible adjoint. This
discharges the lattice antecedent without a new geometric assumption on any target.

Added private proof imports of `Sheaf.Paper.NormalLisseFiniteCoefficientLattice` and
`all Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`. The latter exposes its
already proved coefficient-transport helpers; its geometric lfp theorem is not invoked.
In the assigned module all original declarations, proofs, docstrings and public imports
are unchanged. The item
node records the proved special case and the remaining obstruction. No source-library
module, shared definition, instance, attribute or target is changed.

Change record: `coord/changes/T9-uniform-ext-normal-connected-source.md`. It records all
640 transitive consumers. The unclaimed consumer ConstructibleCompactness receives a proof-only improvement:
its private uniform_ext_standard helper now uses uniformConstructibleExt_exists directly,
rather than projecting the first clause of the disputed uniformConstructibleExt theorem.
This removes that unsupported declaration from the helper's proof dependencies. The
consumer's signatures, attributes, imports and other proofs are unchanged. The two
direct importers are
`Sheaf.Paper.ConstructibleCompactness` and `Sheaf.Paper.FiniteWindowBounded`.

Validation so far: the unchanged baseline compiled in 26.1 seconds. The final assigned
module, including the normal-source theorem, compiled in 30.7 seconds. All Lean lines
are within 100 characters. A textual check confirms every existing declaration and
docstring in the assigned module is unchanged. Both direct importers compiled successfully against the modified item: the changed
ConstructibleCompactness and unchanged FiniteWindowBounded returned exit code zero.
The service accepted each file under its per-file limit; its printed set timings include
setup and cache work outside the timed Lean invocation. The unchanged FiniteWindowBounded
sandbox copy was removed after validation, so it is not delivered.

## Proved and sorry left

Original holes closed: **0 of 1**. Holes added: **0**. Split off: **0**. This is a supported
partial proof of the original explicit-cutoff clause, not a proof or decomposition of the
unconditional theorem.

Newly proved from existing declarations:
`AlgebraicGeometry.ProEtale.uniformConstructibleExt_normalConnectedSource`, attached to
`sk-lem-uniform-constructible-ext`. It uses the existing declared normal-lattice theorem,
whose own proof is still pending; that is an existing dependency, not a new hole.

The only direct hole left is
`AlgebraicGeometry.ProEtale.uniformConstructibleExt`, node
`sk-lem-uniform-constructible-ext`. Its original statement and whole-proof `sorry` remain
unchanged. The existing completed proofs of `uniformConstructibleExt_exists`,
`uniformConstructibleExt_cutoff` and `uniformConstructibleExt_latticeModel` are retained.
No hole occurs in a private theorem or definition.

## No longer needed

The proof of ConstructibleCompactness.uniform_ext_standard no longer needs the disputed
uniformConstructibleExt declaration: the already proved uniformConstructibleExt_exists
is exactly sufficient. The module import and node remain needed for that existence
clause and the unit statement. No existing import, module or node is removed. The rational estimate and its
refined-source machinery remain necessary for the general existence clause, and no unit
step is bypassed. The added normal-lattice theorem discharges an existing conditional
antecedent only in a supported special case.

## Where the brief, the DAG or earlier work was wrong

The original STATEMENT-DISPUTED annotation remains unresolved. Stratified lattice
existence does not give a global lisse integral lattice on an arbitrary source; the
nodal-curve example in that node expressly rules this out. No comparison between the
refined maximum and the original cutoff is supplied by the repaired rational theorem.
The node's earlier review also records that this unconditional cutoff needs mathematical
correction. This delivery preserves that issue explicitly. It does not replace it with
an unproved stronger rational-stratum theorem or silently assume the missing lattice.

The current item source exists despite its historical quarantine row. Work starts from
that current source. No archive, Lean attachment or parent dependency is withdrawn.
The current T9 return file is empty.

The new theorem deliberately assumes a nonempty connected normal source, exactly matching
the normal-lattice declaration. It makes no claim for an empty or disconnected source.
Rank zero is included by that declaration; targets may be zero or have empty filtrations,
as handled by the existing target-filtration proof. Both finite and algebraic-closure
coefficient cases use the same pinned finite model. No normality of X or Z is added to an
existing statement.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
