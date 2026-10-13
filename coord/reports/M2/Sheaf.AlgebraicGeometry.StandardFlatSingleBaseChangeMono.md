## What changed

Replaced the proof of
`AlgebraicGeometry.standard_flat_single_baseChange_homology_mono` in
`Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeMono` without changing its signature.
The proof supplies the relative-flat single's localized stalk comparison, its
quasi-coherent source and target, and the pinned-map cancellation in Lean.
Two proved private helpers provide quasi-coherence of a termwise quasi-coherent
complex and of a single's terms. All added imports in the item are proof-only.
A local heartbeat budget is scoped to the theorem, leaving the 60-second
single-file wall-clock limit unchanged.

The existing qcqs induction implementation cannot be imported: it reaches this
item through RelativeMayerVietoris, internal Hom and finite-free-complex theory.
The new module `Sheaf.AlgebraicGeometry.SingleComplexQcqsHomologyMono` isolates
its degreewise monomorphism part for arbitrary quasi-coherent derived objects
and a specified map satisfying the stalk criterion. This intermediate contains
neither a relatively flat module nor the standard single base-change map. The
item establishes its substantive stalk hypothesis by the existing localized
comparison lemmas, then postcomposes by the canonical single identification.
The proof is therefore a reduction with real stalk and canonical-map glue.

## Proved and sorry left

Upper hole closed in the prepared source:
`AlgebraicGeometry.standard_flat_single_baseChange_homology_mono`
(node `lem-pc-standard-flat-single-base-change-mono`).
No sorry remains in the item.

One hole split off:
`AlgebraicGeometry.singleComplexBaseChange_homology_mono`
(node `lem-pc-single-complex-qcqs-homology-mono`) in
`Sheaf.AlgebraicGeometry.SingleComplexQcqsHomologyMono`.
This is a decomposition: one upper hole closed and one lower hole added,
net zero holes closed. The new theorem handles only the qcqs gluing part;
the relative-flatness specialization and pinned-map identity are proved.

Validation: all three sandbox build inputs compiled without warnings through
`lcompile.py --all`; the item's compile took 27.8 seconds, below the unchanged
60-second limit. The new intermediate compiled in 2.9 seconds. The unchanged
`StandardSingleBaseChangeMap` source compiled in 4.0 seconds. That identical
source is included only as a sandbox build input because its published object
file is missing; it introduces no declaration or source change in the delivery.
The final `deliver3.py --no-push` dry run checks compilation, axioms, source
imports, cycles, and preflight. This is a reduction, not a sorry-free proof of
the qcqs gluing theorem.

## No longer needed

`lem-pc-rf-single-complex-qcqs-induction` and its module
`Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction` are no longer needed by
this item's proof; the attempted proof-only import was removed. This does not
claim they are unused by other targets. The new degreewise criterion replaces
that dependency. All other original DAG proof dependencies are retained and
used. No original public import was removed. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan's qcqs dependency would close a source import cycle. The dry
run and `tools/import_direction.py may` both reject that import. The path is
through `SingleComplexOpenUnion`, `RelativeMayerVietoris`, canonical relative
MV presentations, derived internal Hom, derived quasi-coherent generation,
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`,
finite-free-complex and proper-flat model theory, then
`StandardFlatSingleBaseChange`, which imports this item. This is a dependency
problem, not a mathematical counterexample. The new intermediate's source is
Stacks Tag 0DJ9, read at https://stacks.math.columbia.edu/tag/0DJ9.

The assigned item's public dependency `StandardSingleBaseChangeMap` remains
absent from the published compiled snapshot. The earlier report stopped at this
missing artifact. Its existing source is now compiled verbatim in the sandbox
alongside the two proof modules; no library file, definition, interface or tool
is changed. The reduction itself compiles in under 30 seconds and did not
reproduce a slow-compile failure. No increase to the wall-clock limit was used.

## New nodes

`lem-pc-single-complex-qcqs-homology-mono` states the degreewise monomorphism
conclusion of Tag 0DJ9 under the actual localized stalk condition for arbitrary
quasi-coherent derived objects. Its module is
`lean/Sheaf/AlgebraicGeometry/SingleComplexQcqsHomologyMono.lean`. The docstring
and node retain the affine reduction, qcqs source-open induction and relative
Mayer--Vietoris proof. Searches found no exact Mathlib match. The stronger
existing qcqs implementation is acknowledged above but unusable here because
of the import cycle. Empty schemes, zero objects and negative degrees satisfy
the same criterion; no flatness of the base morphism is assumed.
A change record
`coord/changes/standard-flat-single-base-change-mono-proof-options.md` documents
the declaration-local elaboration options; existing signatures, definitions and
public imports are unchanged.

## Second reading by M2

1. **Interfaces: pass.** Compared each existing sandbox module with the repository
   using `diff -u`. The target's signature is byte-for-byte unchanged; no existing
   definition or public import changes. `StandardSingleBaseChangeMap` is identical
   to the repository. The sole new public theorem is in its own module. Added
   imports of the target are proof-only. The recorded options affect elaboration.
2. **Proof and axioms: pass as a decomposition.** Independently compiled all three
   inputs through `lcompile.py --all`: 3.0, 2.9 and 26.9 seconds, without warnings.
   An appended scratch `#print axioms` check compiled in 27.8 seconds. The target
   and the new open theorem use only `propext`, `Classical.choice`, `Quot.sound`
   and `sorryAx`; both private helpers use only the three standard axioms. A
   source scan finds exactly the reported named theorem's `sorry`, no forbidden
   declaration form, and no hollow definition. The local choices are an adjunction
   comparison and a tensor map fixed by its two restrictions, not arbitrary data
   from an unproved existence assertion.
3. **Split-off statement: pass.** Read the actual stalk condition, coordinates,
   localized comparison, and counit comparison, and checked the new theorem
   against https://stacks.math.columbia.edu/tag/0DJ9. That source proves the
   stronger isomorphism under these hypotheses. Empty schemes and zero objects
   give maps between zero cohomology objects; negative degrees and arbitrary
   unbounded quasi-coherent derived objects are covered by the same theorem.
   For the identity square the stalk hypothesis forces the specified comparison,
   so an arbitrary noninjective phi is not a counterexample. The docstring gives
   target locality, affine comparison, compact-open induction, relative MV, and
   top-open normalization, and the node names those dependencies. Independent
   launcher searches used Loogle `"homologyFunctor", "Mono"`, Lean Finder
   `Quasi coherent derived complexes cartesian square stalk tensor criterion
   base change isomorphism`, and grep `baseChange.*(injective|mono)|[Mm]ono.*baseChange`;
   none provides the geometric result. Source searches locate the stronger
   `singleComplexBaseChangeQcqsInduction`; `import_direction.py may` independently
   confirms that importing it closes a cycle. The new hole isolates gluing after
   genuine flatness, quasi-coherence, stalk, and pinned-map proofs; it is not an
   alias of the parent theorem. Closing it here in a few minutes would require
   the same cyclic dependency or a new proof of the gluing machinery.
4. **Route and pruning: pass.** Followed the proof from the target through the
   counit stalk criterion, bounded-flat K-flatness, tensor-stalk flatness, and
   canonical single-map cancellation. Each added proof import supplies a lemma
   actually used. The two private quasi-coherence helpers give short direct
   proofs; the similar helper in `SingleComplexBaseChangeCriterion` is private.
   Compared old and new `proof_deps`: the only removed dependency is precisely
   the qcqs induction node listed under `No longer needed`. No original public
   import is removed. Read `dag/units/sk-thm-picard-coherence.json`: its realized
   entries are empty and unchanged, and this reduction remains within its
   base-change/Noetherian-approximation argument.
5. **DAG: pass.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Its steps match the implemented stalk and canonical-map glue.
   The new node has a verbatim Lean statement, source, three successful search
   modes, creation record, blueprint ancestry, chapter/unit, and the named
   locality/affine/union/top induction plan matching its docstring.

Second-reading changes: corrected the options change record to distinguish
module-local transparency options from the declaration-local heartbeat budget,
and added this independent review and validation evidence. No Lean proof,
statement, definition, import, or DAG route needed repair. One upper hole closed,
one gluing hole added: net zero; this delivery remains a decomposition.
