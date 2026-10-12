## What changed

Completed `Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeAffineChartComparison` by
composing two strict parts of its original argument. First apply the arbitrary-open
restriction theorem to obtain the restricted comparison and its commuting square.
Then apply coordinate transport to this chosen pullback square and the two spectrum
charts. Compose the endpoint isomorphisms and their square equations with the proved
private lemma `AlgebraicGeometry.comparison_comp`. The assigned theorem's signature
and both public imports are unchanged. No definition or existing interface changed.

The two new intermediate modules retain the earlier attempt's open and coordinate
statements, with source citations, complete proofs in words and matching DAG nodes.
Their planned proof dependencies are imported privately where needed. The main node
now records the actual composition route. Removed the earlier attempt's unrelated
public reassociation helper and its unused new node.

Validation: all three modules compile together in import order through `lcompile.py
--all`, without errors or warnings, within the single-file time limit. No heartbeat
limit was raised. The previous elaboration problem is avoided by applying each lemma
before unpacking it, unpacking/building one existential at a time, and checking the
categorical composition calculation in a generic proved private lemma.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_canonicalModuleBaseChange_affineChart_comparison`
(node `lem-pc-canonical-module-base-change-affine-chart-comparison`). Its proof contains
no `sorry`. This is a decomposition, not a proof free of unproved dependencies:
one original hole is closed and two strictly simpler holes are added.

The delivery leaves exactly these two named theorems with `:= by sorry`:

- `AlgebraicGeometry.exists_canonicalModuleBaseChange_open_comparison`, node
  `lem-pc-canonical-module-base-change-open-comparison`, new module
  `Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeOpenComparison`.
- `AlgebraicGeometry.exists_canonicalModuleBaseChange_iso_comparison`, node
  `lem-pc-canonical-module-base-change-iso-comparison`, new module
  `Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeIsoComparison`.

The first statement has arbitrary opens and no spectrum-coordinate transport; the
second has arbitrary scheme isomorphisms and no open restriction. Neither restates
the assigned theorem. Their combination requires both commuting squares, the chosen
restricted pullback's cartesianness, and an actual associativity calculation in Lean.
There is no `sorry` in a definition, private theorem or partial proof.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`
  (`lem-pc-derived-pullback-open-restriction-universes`).
- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
  (`lem-pc-restrict-derived-direct-image-open`).
- `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`
  (`lem-pc-derived-direct-image-composition`).
- `Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`
  (`lem-weil-pbc-module-base-change-map-open-restriction`).

These remain planned dependencies of the new intermediate theorems, so they are
relocated imports, not globally pruned modules. The complete difference between the
old and new direct `proof_deps` also includes these three nodes:

- `lem-pc-ringed-spaces-derived-pullback-composition`: used below the two new nodes.
- `def-pc-derived-base-change-map`: retained in the statement and below the new nodes.
- `def-pc-derived-module-base-change-map`: retained in the statement and below the new nodes.

`def-pc-fibre-product` remains a direct proof dependency for
`IsPullback.of_hasPullback`. No existing node or module is globally pruned by this
decomposition; the net number of holes in the affected closure increases by one.

Discarded the previous attempt's unused
`lem-pc-canonical-module-base-change-affine-chart-reassociation` node and public
`canonicalModuleBaseChange_affineChart_reassociation` helper. The real square-pasting
calculation is proved privately in the assigned module and needs no new item.

## Where the brief, the DAG or earlier work was wrong

The previous attempt left the assigned theorem `sorry` and added an unrelated
associativity lemma; this did not constitute a delivery. Its reported final-composition
timeout is resolved without changing definitions, signatures or compiler limits.

The original DAG provided functor comparisons but did not state the arrow-level
compatibility with the supplied module counit. The two new nodes isolate this missing
compatibility into open restriction and isomorphism transport, with the original
sources and explicit proof steps. Their endpoint isomorphisms and counits are existential
witnesses used inside a proposition proof, not arbitrary data definitions.

Checked edge cases before retaining these statements: empty V or W yields the same
restricted cartesian square and chart constructions; the zero module is allowed;
identity coordinate isomorphisms specialize to transport between the original and
chosen pullback. No nonempty-open, flatness, quasi-coherence or invertibility hypothesis
is required or introduced. The parent unit's `realized` lists do not impose a different
route through this auxiliary node; the original local affine reduction is preserved.

## New nodes

`lem-pc-canonical-module-base-change-open-comparison` isolates restriction to arbitrary
opens, including transport of the supplied derived-to-ordinary comparison and the
arrow square. Its module, Lean statement, four-step proof and dependency union match.

`lem-pc-canonical-module-base-change-iso-comparison` isolates scheme-isomorphism
coordinate transport of an already given cartesian square. Its module, Lean statement,
four-step proof and dependency union match. It is applied to the restricted pullback
with `IsPullback.of_hasPullback` and the actual spectrum charts.

No change record is needed: no existing signature, visibility or definition changed,
and there are no forced adaptations.

## Second reading by N3

1. **Unchanged interfaces: pass.** Diffed every delivered module against the
   repository. The assigned theorem's entire signature is byte-for-byte identical;
   both existing public imports and all options are unchanged. The other two modules
   and their two declarations are new. No existing definition, signature, visibility,
   target or downstream module is changed, and no change record is required.
2. **Proof and compilation: pass as a decomposition.** Independently compiled the
   three-module set in import order through `lcompile.py --all`: no errors or warnings,
   5.5, 7.4 and 13.8 seconds. Read the existential elimination, application to
   `IsPullback.of_hasPullback`, endpoint iso composition and associativity proof.
   Scratch copies with `#print axioms` show only `propext`, `Classical.choice`,
   `Quot.sound` and `sorryAx` for the three public declarations; the private
   `comparison_comp` uses only the three permitted axioms. Source scan finds exactly
   the two reported named theorem holes and no forbidden declarations or hollow data.
   Existential witnesses are eliminated only in a proposition proof.
3. **Split statements: pass, with documentation repaired.** Open restriction removes
   coordinate transport; iso transport removes open restriction. Neither is a renamed
   restatement. Each retains its whole arrow square and is used by the reduction.
   Read their hypotheses, targets, sources, proofs in words and nodes. Checked empty
   V, empty W, zero G, full opens and identity coordinate isos: the chosen pullbacks,
   projections and restriction functors retain their stated types and comparisons;
   no missing flatness or nonemptiness condition appears. For the open counit, replaced
   the unjustified assertion that exactness preserves its Kan property with the
   extension-by-zero construction, K-flat verification and naturality at
   `j_!(M|U) -> M`. This also explains transport of the supplied counit rather than
   an independently chosen counit. Source: [Stacks 0D5U](https://stacks.math.columbia.edu/tag/0D5U),
   alongside [08FE](https://stacks.math.columbia.edu/tag/08FE) and
   [08HY](https://stacks.math.columbia.edu/tag/08HY).
   Repeated leanfinder, loogle and Mathlib grep with different queries (recorded in
   `searches.jsonl` and both new nodes), and searched local Sheaf/upstream sources.
   Restriction equivalences and conjugateIsoEquiv are component tools; the Picard
   degree-zero mate square concerns H^0 and pinned comparisons, not these full
   unbounded derived arrow comparisons for a supplied counit. No duplicate or quick
   way to close either split theorem was found.
4. **Route and pruning: pass after report repair.** The reduction follows the local
   affine reduction of [Stacks 08IB](https://stacks.math.columbia.edu/tag/08IB).
   The assigned unit `sk-thm-picard-f-representable` has empty statement and step
   `realized` lists, which are unchanged. Statement-needed imports remain public;
   all comparison proof imports are private. Completed `No longer needed` with all
   seven old direct proof dependencies removed from the main node. They remain below
   the new intermediate nodes or in statement dependencies; no globally pruned module
   is claimed. One hole closed and two added is a decomposition with net +1 hole.
5. **DAG correspondence: pass after synchronized documentation repair.** Checked the
   main node's actual three-step route, dependency union and origin. Both new nodes
   have the required fields, matching verbatim Lean signatures, chapter/unit,
   source citations, complete proof plans, dependency unions and creation records.
   Updated the open node's counit-transport step and source/origin with its docstring;
   added the independent search records to both new nodes.

Second reading changed the open-counit proof explanation and matching node source/
proof text, completed old-dependency accounting and net-hole accounting in the report,
recorded independent searches, and removed one surplus blank line in each new module.
No Lean statement or proof term changed. Final dry run and delivery use the mandated
`deliver3.py` checks.
