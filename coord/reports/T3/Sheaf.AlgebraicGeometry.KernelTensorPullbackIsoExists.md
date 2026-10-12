## What changed

Completed `AlgebraicGeometry.exists_kernelTensorPullbackIso` in
`Sheaf.AlgebraicGeometry.KernelTensorPullbackIsoExists`, preserving its exact public
signature and docstring. Added proved private helpers for the ideal pushforward map,
the induced tensor-pullback map, and the inverse identity criterion, together with a
private predicate abbreviating the section formula. No data is chosen from an
unproved existence theorem.

The proof uses the ideal-section clause of the existing proved
`AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_functorial`, then the
normalized tensor-pullback adjunction. Construct the forward and reverse maps by
adjunction; check each composite on unit sections and use injectivity of the Hom
bijection. Open-set transports are handled explicitly using naturality and the
preorder structure of opens. This handles identity ambient maps, zero ideals and
empty schemes without extra hypotheses or exceptional cases.

Added the proof-only import
`Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial`. Updated only `proof`,
`proof_deps`, and `proof_origin` of
`lem-weil-pbc-kernel-tensor-pullback-iso-exists` to record the implemented route.
The statement and all realized steps of unit `sk-thm-p1` stay unchanged.
The existing conormal functoriality import change record was read and respected;
no other module is adapted.

Sources checked: Stacks Project [01R4](https://stacks.math.columbia.edu/tag/01R4),
especially its ideal-map construction, and [0096](https://stacks.math.columbia.edu/tag/0096).
The local Stacks source checkout is absent, so these existing cited sources were
read through the official Stacks pages. LeanFinder and Loogle searches found
ideal-data transport and adjunction uniqueness lemmas, but no exact sectionwise
kernel tensor-pullback isomorphism theorem. The existing library theorem provides
the shorter route for the ideal-map step.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.exists_kernelTensorPullbackIso`
(node `lem-weil-pbc-kernel-tensor-pullback-iso-exists`).
All three private helper theorems are proved. No `sorry` remains in this module;
no new hole, new axiom, or split-off statement is added. This is a proof, not a
decomposition. Local compilation passes without warnings. `#print axioms` for the
public theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`; there
is no transitive `sorryAx`. The public theorem signature was compared verbatim with
the assigned source and is unchanged. All Lean lines are at most 100 characters.

## No longer needed

Removed the redundant proof-only direct import
`Sheaf.AlgebraicGeometry.TensorPullback`: it remains available through the necessary
public import `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, and its tensor
pullback construction is used. This removal does not prune that module from the
closure.

No node or module is pruned from the import closure. The original definitions of
schemes, closed immersions, kernel ideals, tensor pullback, and its adjunction are
still needed. The old proof dependency `def-weil-closed-immersion` is no longer used as a
proof step and was removed from `proof_deps`; it remains in `stmt_deps`, and its
public Mathlib import remains because the signature needs `IsClosedImmersion`. A separate reconstruction of the ideal-section map,
identity-pullback comparison, affine conormal calculation, tensor-generation lemma,
and tensor-pullback composition isomorphism are unnecessary: none is imported or
newly stated for this proof.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan can reuse the already proved ideal-map
clause of conormal functoriality, which was missing from this item's proof dependencies.
The inverse check needs no standalone theorem about tensor generators: equality of
adjoints is checked sectionwise at the units. No public definition or statement was
changed, and no unit-level route was bypassed.


## Second reading by T3

1. **Visible interface: PASS.** Diffed the sole delivered Lean module against the
   repository version. The existing public theorem signature is byte-for-byte
   identical, including every hypothesis and the full section formula; its docstring
   is also unchanged. The added predicate and three helpers are private. All public
   imports are unchanged; the new conormal-functoriality import is proof-only. No
   existing definition changes and no change record or adaptation is required.
2. **Proof and axioms: PASS.** Independently compiled the module through `lcompile.py`
   without errors or warnings (4.4 seconds). Compiled a scratch copy with
   `#print axioms` for all three helper theorems and the public theorem: each has
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Scanned the entire delivered source: no `sorry`, forbidden axiom mechanism, or
   hollow definition. The private predicate is an explicit proposition. Adjunctions
   are chosen from a proved normalized adjunction theorem; the ideal and module maps
   are obtained within proofs from proved results, never from an unproved arbitrary
   existence theorem.
3. **Split statements and edge cases: PASS.** No statement is split off and no hole
   is added. Read all private helpers: the first supplies the ideal-section map,
   the second constructs its adjoint for a general compatible ambient morphism,
   and the third proves a one-sided inverse identity from the section formulas.
   None restates the target. Identity ambient maps, zero kernel ideals, and empty
   schemes introduce no missing assumption; the proof uses only naturality,
   injectivity of the ideal inclusion, and the adjunction bijection. Independent
   declaration searches in both library roots found no existing theorem with the
   required normalized section formula. Loogle confirmed `Adjunction.homEquiv_unit`;
   a separate Mathlib ideal-sheaf search found no replacement theorem.
4. **Route, imports, and pruning: PASS.** Read the conormal functoriality theorem and
   its landed import change record. Reusing its proved ideal-section clause avoids
   rebuilding the ideal map; the remaining adjunction and inverse checks are needed
   for the exact formula. All retained imports provide statement dependencies or
   that proved clause. Compared the old and new proof dependencies: the only removed
   node is `def-weil-closed-immersion`, now explicitly named under No longer needed;
   it remains a statement dependency. The removed direct tensor-pullback import is
   redundant through the adjunction import, so no module is pruned from the closure.
   Read `dag/units/sk-thm-p1.json`, including `realized`: this item is below its
   realized statement and steps, and no unit-level route or record is changed.
5. **DAG agreement: PASS.** Diffed the node records: only `proof`, `proof_deps`, and
   `proof_origin` change. The three proof steps describe the three helpers and final
   inverse packaging, and `proof_deps` is exactly the union of their `uses`. The
   statement, source, statement dependencies, chapter, unit, and Lean record stay
   unchanged. No new nodes require checking.

Second reading changed only the report: explicitly recorded the removed old proof
node and added this independent review. The Lean proof and node record needed no
repair. Holes closed: `AlgebraicGeometry.exists_kernelTensorPullbackIso` (1 of 1).
Holes added: none. Split off: none. Modules pruned from the closure: none.
