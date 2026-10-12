## What changed

Replaced the unfinished earlier sandbox attempt with a compiling reduction of
`CochainComplex.exists_upperTruncationStepSES`, preserving its full original
signature and both public imports. Added proof-only imports of
`Sheaf.Algebra.Homology.UpperTruncationStepQuotient` and
`Sheaf.Algebra.Homology.TwoTermCoimageQuasiIso`.

The main module now constructs the successor inclusion using Mathlib truncation
maps and the inverse of a truncation inclusion that is an isomorphism. It proves
compatibility with the inclusion into K, monicity, the short exact cokernel
sequence, and inclusion naturality. It constructs the cohomology projection using
`HomologicalComplex.mkHomToSingle`, after proving the required differential
annihilation from the cycles inclusion and `toCycles_comp_homologyπ`.
It proves its component formulas and naturality. It constructs the quotient map
by `cokernel.desc`, proves factorization and uniqueness, derives its degree-q
normalization by epi cancellation, proves zero homology at q-1, and constructs
the naturality map by `cokernel.map`. Two smaller coordinate/cohomology statements
supply the remaining parts. The existing node's proof and proof dependencies
now follow this implemented route; the two new nodes document its remaining work.

All three delivery modules compile through lcompile.py. No existing statement,
definition, or public visibility changed. All new definitions are actual
constructions from Mathlib, with no sorry and no choice of arbitrary witnesses.

Repair of reviewer X-35d56, H8: corrected both blueprint references in the
item module (module docstring and theorem docstring) to the existing node
`lem-weil-pbc-truncation-step-ses`.

## Proved and sorry left

Closed the original hole of `CochainComplex.exists_upperTruncationStepSES`
(node `lem-weil-pbc-truncation-step-ses`). There is no sorry in the item module.
This is a decomposition: one hole closed, two holes added; it is not an
axiom-free completion of the original theorem. Net holes closed minus added: -1.

The two remaining holes added by this delivery are:

- `CochainComplex.upperTruncationStep_quotientCoordinates`
  (`lem-weil-pbc-upper-step-quotient-coordinates`): degreewise cokernel coordinates,
  projection/differential equations, and monicity of the quotient differential.
- `CochainComplex.twoTermCoimage_quasiIso`
  (`lem-weil-pbc-two-term-coimage-quasiiso`): a generic two-term coimage complex's
  normalized projection to a single cohomology object is a quasi-isomorphism.

Both are public named theorems in separate new modules, each with exactly
`:= by sorry`, its source, full proof in words, and a matching DAG node. The
combining proof is complete Lean, including all construction, descent, uniqueness,
vanishing and naturality assertions noted above. The quotient-coordinate
existential determines the isomorphisms by their equations with epimorphic
projections; they are unpacked only inside a theorem proof.

## No longer needed

No original imports, nodes or modules are pruned. In particular the coimage-mono
and degreewise-exactness leaves remain needed by the quotient-coordinate node;
they are no longer direct proof dependencies of the parent but remain transitive
ones. The derived-category construction itself is not invoked: its node remains
as the existing definition dependency for complexes, homology and quasi-isomorphisms.
No unit statement or unit proof step is bypassed.

The earlier sandbox-only `upperTruncationStepCore`,
`exists_upperTruncationStepCore`, `upperTruncationStepNaturality`, and
`truncLE_inclusion_naturality` are removed. They were not declarations of the
repository baseline and had no nodes; no adaptation is required.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left an existential core almost as large as the original
statement and a separate naturality sorry, with no new node records; its report
also described a different sandbox state. It did not implement a deliverable
reduction. This attempt replaces it rather than moving that core into a new file.

The original seven-step argument is mathematically sound, but the named leaves
alone do not package its degreewise quotient coordinates or two-term homology
comparison. These are now explicit, strictly smaller obligations. All the other
steps are implemented using existing Mathlib declarations. There is no disputed
statement and no signature change.

Checked the new obligations on the zero complex, a zero incoming differential,
and a complex with a mono incoming differential. For a zero differential the
coimage term is zero and the quotient projection is the identity on cycles;
for a mono differential the q-1 homology is zero and the q homology is the
usual cokernel of that differential. Integer arithmetic keeps q-2, q-1, q and
q+1 distinct even for q=0 or negative q. Neither statement adds a boundedness
or positivity hypothesis. The hypothesis on the differential equation in the
generic comparison is essential: it identifies the correct boundaries, rather
than identifying only the two objects of the complex.

The cited Stacks sources were read at their official Tag 0118, 0114 and 08J5
pages because this machine does not hold the .tex files named by the old node.
The new nodes record those source URLs. The expanded proof details are those
of the original node, with the omitted cokernel/cohomology calculations made
explicit. The unit record was read: this helper realizes none of its own
statement or proof-step nodes; its route through the truncation triangle stays.

## New nodes

`lem-weil-pbc-upper-step-quotient-coordinates` isolates original steps 2-4:
the coordinate calculation for the cokernel of any inclusion compatible into K.
The node and module give the exact normalized isomorphisms needed by the parent.
Its proof uses the existing degreewise-exactness and coimage-mono leaves.

`lem-weil-pbc-two-term-coimage-quasiiso` isolates original step 6 as a generic
lemma about an arbitrary two-term complex with the specified coimage/cycles
coordinates and normalized projection. It does not assert any truncation
inclusion, short exact sequence, factorization, uniqueness, or naturality.

Both inherit the parent's chapter and unit. Searches were run with LeanSearch,
leanfinder, loogle and grep for each; LeanSearch was unavailable (empty response),
and that failure is recorded without claiming a match. The name-based loogle searches returned no hits and their
unknown-name results are recorded, rather than claimed as exact matches.
Blueprint searches for two-term homology and truncation quotient found no
matching imported blueprint statement. No change record is needed.

## Second reading by F2

1. I compared the delivered item module with the repository version. The theorem signature and existing declarations are byte for byte unchanged; only proof imports and proof bodies were added, alongside the two declared split-off modules and their nodes. Verdict: pass.

2. I compiled all three delivery modules with `lcompile.py --all`. The item module has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The only remaining `sorry`s are the two named split-off theorems, each public, separately documented, and matched by a DAG node. Verdict: pass.

3. I checked both split-off statements for truth and strength. The quotient-coordinate theorem isolates the degreewise cokernel calculation; the two-term theorem isolates the final quasi-isomorphism comparison. They are strictly smaller than the parent and include the stated zero and mono edge cases. Verdict: pass.

4. I checked the proof route and imports. Mathlib truncation, cokernel, and homology constructions are used first; the two split-off lemmas are used only at the quotient-coordinate and final comparison steps. The parent proof and node dependencies follow the implemented route. Verdict: pass.

5. I checked the DAG records and unit route. The existing node's proof, dependencies, and origin agree with the Lean proof, and both new nodes contain the required statements, sources, searches, and Lean records. The unit's truncation-triangle route remains intact. Verdict: pass.

I changed this report by adding this second-reading record. No Lean statement or definition was changed.

## Earlier second reading (a previous round; superseded)

1. I compared the delivered item module with the repository version. The public theorem
   signature and all existing declarations are unchanged; the two added modules and
   their DAG nodes are the only additional interfaces. Verdict: pass.

2. I compiled all three modules with `lcompile.py --all`. The item has no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the only remaining
   `sorry`s are the two named split-off theorems, each in its own public module and
   matched by a node. Verdict: pass.

3. I reviewed both split-off statements against their docstrings and source nodes.
   `upperTruncationStep_quotientCoordinates` is the degreewise quotient calculation,
   while `twoTermCoimage_quasiIso` is the strictly more general two-term comparison;
   neither restates the parent theorem. Their edge cases include the zero complex and
   zero incoming differential. Verdict: pass.

4. I checked the proof route from the constructed truncation inclusion downward:
   existing Mathlib helpers are used first, and the two split-off lemmas are used only
   for the quotient coordinates and the final quasi-isomorphism. The proof-only imports
   are minimal for this route, and no old proof dependency is removed. Verdict: pass.

5. I checked that the parent node's proof, proof dependencies, and proof origin match
   the Lean proof, and that both new nodes carry chapter, unit, source, searches,
   statements, and Lean records. The unit route through the truncation triangle remains
   intact. Verdict: pass.

I changed only this report by adding the second-reading record. No Lean source,
statement, definition, or DAG node was changed during the second reading.
