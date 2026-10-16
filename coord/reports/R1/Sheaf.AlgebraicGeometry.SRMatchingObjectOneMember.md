## What changed

Proved `AlgebraicGeometry.Scheme.sr_matching_object_one_member` with its original signature.
No public interface changed, and no new module, node, or hole is delivered.

Repaired every duplicate named in the return:

- Removed local `covering_of_iso` and `covering_of_split_epi`. The proof now imports
  `Sheaf.AlgebraicGeometry.HypercoverOneMoreSimplex` with `import all` and uses its
  existing proved private `AlgebraicGeometry.Scheme.covering_of_iso` directly.
- Removed local `properFace_finite` and the copied `properFace_finCategory` definition.
  The proof now imports `Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry`
  with `import all` and uses its existing proved private
  `AlgebraicGeometry.Scheme.ProEt.properFace_finCategory` directly. That construction
  already uses the existing `properFace_finite` theorem.

`import all` is Lean's supported way to access these private helpers. Both imports are
proof-only and acyclic. Neither imported module nor its node is changed. Their main
hypercover theorems are not used: the reused helpers are proved elementary facts.
The item's node now records the modules supplying these helpers in its proof and
proof dependencies, and explains exactly which helpers are used.

The rest of the proof is retained. It constructs limiting proper-face cones in the etale
category in degrees zero, one, and at least two using the existing matching-object
lemmas, then uses finite-limit preservation by `Etale.forget`. A componentwise
universal-property proof transports limiting cones through the singleton inclusion.
Limit uniqueness supplies the comparison with the recorded SR matching object and
identifies matching maps. Covering permanence and the singleton small-etale covering
criterion prove the covering equivalence; the hypercover equivalence follows pointwise.
Degree zero and empty schemes need no additional hypotheses.

The unit `sk-prop-h2` assigns no realized statement or step to this item; its route is
unchanged. The delivery contains no copy of a landed theorem and makes no statement or
definition correction. It only reuses the existing helpers requested by the return.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.sr_matching_object_one_member`
(node `lem-weil-pbc-sr-matching-object-one-member`).
No `sorry` remains in the item. No holes were added or split off: 1 closed, 0 added.
The retained private helpers `inclLimit`, `etaleFaces`, `srFaces`, `geometry`, and
`inclCov` are all proved.

This is a proof from existing declarations, including
`SimplicialObject.matching_object_one`, `matching_object_succ_succ`,
`matching_object_proper_faces_one`, `matching_object_proper_faces_succ_succ`, and
`AlgebraicGeometry.Scheme.semiRepresentableCovering_comp_baseChange`.
The latter remains an upstream open theorem and is not modified by this delivery.
The two reused private helpers and their dependencies introduce no new holes.

The repaired module compiles through `lcompile.py` without warnings. The public theorem
signature and existing declaration docstring are unchanged. The required
`deliver3.py R1 Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember --no-push` printed
`OK (dry run)`: compilation and preflight passed except for the independent second
reading, which belongs to the next worker. Nothing was pushed. The axiom check reports
only the three permitted axioms plus `sorryAx` inherited from existing upstream holes.

## No longer needed

Removed the unused original proof import
`WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover`.
Both original public imports are retained because the statement uses them.
`SimplicialMatchingObject` and `SemiRepresentableCoveringPermanence` remain directly used.
The two added `import all` directives are needed to reuse the private helpers.

The following planned direct node dependencies remain pruned:

- `def-weil-pbc-finite-split-hypercover`: no split-hypercover structure or hypothesis is used.
- `def-pc-fibre-product`: no explicit fibre-product construction is used.
- `lem-weil-pbc-finite-limits-from-terminal-pullbacks`: singleton preservation is proved
  directly on arbitrary limiting cones; existing etale instances supply finite limits.
- `lem-weil-pbc-semi-representable-finite-limits`: singleton preservation is proved directly;
  SR finite completeness is already supplied by the definitions module.

These are removals from this node's direct proof dependencies, not claims that other
parents have ceased to use them. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous delivery duplicated three existing private theorems and a private
finite-category construction. Its earlier second reading missed those copies.
The repair removes all four local declarations and imports and uses the originals,
which resolves the exact return rather than renaming or restating the duplicates.
No false statement, mathematical error, or interface defect was found.

## Second reading by R1

1. **Signatures and accidental changes.** I compared the delivered module with the
repository version. The public theorem signature and all existing declarations are
unchanged byte for byte. The only source changes are the completed proof, proof-only
imports, and removal of duplicated private helpers. The DAG change records only the
revised proof route and dependencies; no target or definition was changed.

2. **Compilation and proof soundness.** `lcompile.py` compiles the module cleanly.
There are no `sorry`s, axioms, unsafe declarations, or hollow definitions in the
delivered module. The proof uses only existing declarations and the permitted
upstream open results remain outside this item.

3. **Statements and duplication.** The sole closed declaration is exactly the
recorded node statement. The private helper `inclLimit` is a componentwise
universal-property construction, and `etaleFaces`, `srFaces`, `geometry`, and
`inclCov` are strict intermediate reductions rather than restatements of the target.
The earlier duplicate `covering_of_iso` and `properFace_finCategory` declarations
are removed; searches confirm the existing helpers are reused through `import all`.

4. **Pruning and shortest route.** The unused finite-split-hypercover import and its
direct node dependency are removed. The proof uses the matching-object and
proper-face results, the existing proper-face finite-category construction, the
componentwise singleton-limit argument, and covering permanence. No shorter existing
declaration was found that replaces these reductions, and the remaining imports are
used.

5. **DAG and unit agreement.** The node's `proof`, `proof_deps`, and `proof_origin`
match the Lean proof, including the two reused private helpers. The unit
`sk-prop-h2` has no realized statement or step for this item, so its route is
unchanged. No new node or split-off hole is introduced.

Changed in this second reading: added this review record and verified the repaired
proof, imports, duplicate removal, and DAG metadata. No Lean source repair was needed.
