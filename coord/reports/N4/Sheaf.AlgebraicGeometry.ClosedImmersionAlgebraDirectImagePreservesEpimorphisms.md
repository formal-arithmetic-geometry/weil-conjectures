## What changed

Repaired the duplicate-proof return for
`Sheaf.AlgebraicGeometry.ClosedImmersionAlgebraDirectImagePreservesEpimorphisms`.
Removed the entire private theorem
`TopCat.epi_pushforward_closedEmbedding_for_algebra` and replaced its use with
`TopCat.epi_pushforward_closedEmbedding`, already proved in
`Sheaf.Topology.ClosedImmersionPushforwardCohomology`.
Lean's plain `import all` grants access to that private theorem for this proof;
no visibility change or edit to its original module is needed. Removed the
unfinished exposure adaptation and its change record from the sandbox.
The existing public theorem's signature and docstring remain unchanged.
Updated the DAG proof and dependencies to record the reused lemma's owning node.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.closedImmersion_algebraDirectImage_preservesHomology`
(node `lem-sc-closed-immersion-algebra-direct-image-preserves-homology`).
No sorries remain in the delivered module, and no holes were added or split off.
The proof transfers preservation of epimorphisms from abelian sheaves through
`SheafOfModules.toSheaf`, reflects epimorphisms through its faithful functor,
and combines this with preservation of finite limits to preserve homology.
The reused lemma handles empty opens, empty source, and points outside the image;
no extra hypotheses are imposed.

## No longer needed

Removed direct proof imports `Mathlib.Topology.Sheaves.LocallySurjective` and
`Mathlib.Topology.Sheaves.Abelian`: the proof no longer constructs local lifts
and the new proof import provides the required abelian-sheaf infrastructure.
Removed the duplicate private helper and its complete local-lifting proof.
No original public import or dependency node was removed. Retained the proved
source-library sheafification import for preservation of epis by `toSheaf`.
No entire library module is claimed to leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The previous repair only renamed an identical theorem and did not resolve the
maintainer's duplicate-statement return. This repair removes the duplicate and
actually imports and applies the existing theorem as requested. Its private
visibility is handled by `import all`, without exposing it or changing any
other module. The earlier second readings apply to superseded submissions
and have been removed; a fresh independent reading is required.
The item name mentions epimorphisms, but its sole declaration states preservation
of homology; the unchanged conclusion follows from epis and finite limits.

## Second reading by N4

1. Interface: PASS. Diffed the only delivered Lean module against the repository.
   The complete docstring and theorem signature of
   `AlgebraicGeometry.closedImmersion_algebraDirectImage_preservesHomology`
   are byte-for-byte identical. No definitions or existing declarations were
   changed, and there are no adaptations or change records. The two added imports
   are proof-only imports, including plain `import all` for the private lemma.
2. Proof and axioms: PASS. Independently compiled the delivered file without
   errors or warnings. A fresh scratch copy with `#print axioms` for the public
   theorem and `TopCat.epi_pushforward_closedEmbedding` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound` for each, with no `sorryAx`.
   Scanned the delivered source: no sorry, axiom, unsafe, opaque, implemented_by,
   extern, or new definition. Read the existing local-lifting helper: its image
   case uses the closed complement of the image of Z minus V; its off-image
   case uses the open complement of the closed image and the zero section on
   the empty inverse image. Empty opens and empty source introduce no hypothesis.
3. Split statements: PASS (none). There are no new statements, new nodes, or
   split-off holes. Read the duplicate-proof return in `coord/returns/N4.md`:
   the returned helper has been removed entirely and the existing private
   theorem is actually applied, rather than restated under another name.
4. Route and pruning: PASS. Read the imports and searched Mathlib's sheaf and
   module-sheaf files, upstream algebraic geometry, and the library's closed
   immersion modules for epi/pushforward/homology results. The clopen upstream
   result is more restrictive; the scheme-module cokernel result concerns
   modules over O_Y, whereas this item targets modules over i_*O_Z. Reusing
   the arbitrary closed-embedding abelian-sheaf lemma is the direct route.
   Forgetting modules preserves epis by the source-library finite-colimit
   instance and reflects them by faithfulness; pushforward commutes with this
   forgetting definitionally. Finite limits provide kernels, and Mathlib's
   preserves-epis-and-kernels criterion gives the unchanged conclusion.
   Independently removing the source-library sheafification import failed
   exactly at `(SheafOfModules.toSheaf R).PreservesEpimorphisms`, confirming
   that import is needed. Every old proof dependency remains used; none is
   omitted from No longer needed. The item's `blueprint.is` is null and it is
   absent from its unit's `realized` fields; the unit record and route are kept.
5. DAG agreement: PASS. Diffed the delivered node: only `proof`, `proof_deps`,
   and `proof_origin` change. Read the reused lemma's owning node in
   `sec-curve-estimates`: the delivered node explicitly identifies reuse of
   its private exactness helper, not a deduction from the cohomology-isomorphism
   statement. Its remaining steps describe the actual module-forgetting and
   kernel argument. The dependency list is exactly the union of the steps'
   uses; its statement, Lean record, chapter, unit, and blueprint stay unchanged.

Second reading changed only this report, adding the independent review and
validation evidence. The proof and node needed no repair. Closed one original
hole, added zero holes: this is a proof, not a decomposition. No whole module
is claimed pruned.
