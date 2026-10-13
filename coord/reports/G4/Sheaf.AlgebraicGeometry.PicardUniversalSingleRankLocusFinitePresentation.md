## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation` with a compiling
reduction. The theorem's signature and visibility are unchanged. The proof chooses standard
derived-category localizations, checks stability under precomposition by associativity,
uses the existing source-locality theorem, constructs local representatives using
`exists_perfectLowestCohomologyLocus`, and glues them while retaining local finite presentation.

Added `Sheaf.AlgebraicGeometry.LocalFinitelyPresentedImmersionLocus`, whose public theorem
`AlgebraicGeometry.Scheme.exists_localFinitelyPresentedImmersionLocus` is proved with no direct
holes. Its repaired proof imports and applies the existing public `exists_localImmersionLocus`
for gluing and representability. Global and local representing equivalences identify each
pullback with the given local immersion by inverse maps, whose identities follow by
monomorphy. Local finite presentation then follows by composition and target locality.
The duplicated private `exists_factor_of_locally_factors` helper has been deleted.

Repair of the sole returned point: the existing helper is private, so a plain import cannot
call it. Reusing the existing public locus theorem avoids both duplication and any visibility
change. The original second reading below predates this repair; its descriptions of the old
gluing proof and helper are historical, pending a fresh independent second reading.

Added `Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart` for the missing local
complex/comparison argument. It assumes neither a structure-sheaf unit nor connected fibres.
Its docstring gives all three fibre cases. A homogeneous nonempty fibre uses the perfect
direct image and fixed reference rank. An empty-fibre neighbourhood uses the actual zero
complex and rank zero. A mixed-fibre neighbourhood uses the actual zero complex and rank one,
so its universal freeness condition holds precisely for empty tests. This is a local derived
comparison obligation, with no representing immersion or gluing conclusion.

Read Stacks Tags 0BDP, 0B91 and 0BDL online because the cited local literature checkout is
absent. Checked the empty base, empty test, empty fibre, rank-zero homogeneous fibre,
disconnected homogeneous fibre, mixed-rank fibre, and nonreduced tests in the chart proof.
LeanSearch returned Internal Server Error and is recorded as unavailable. LeanFinder, Loogle,
Mathlib grep, both library roots and whole-blueprint searches supplied no exact replacement.
All three delivered modules compiled together with `lcompile.py --all`.

## Proved and sorry left

Closed the original direct hole:
`AlgebraicGeometry.Scheme.exists_picardUniversalSingleRankLocus_finitePresentation`
(node `lem-sc-picard-universal-single-rank-locus-lfp`). No direct `sorry` remains in the item.

Added one direct hole:
`AlgebraicGeometry.Scheme.exists_picardSingleRankUnrestrictedPerfectChart`
(node `lem-sc-picard-single-rank-unrestricted-perfect-chart`). This theorem's entire proof is
`by sorry` in its own module, with the complete local argument in its docstring and node.

Proved the additional public theorem
`AlgebraicGeometry.Scheme.exists_localFinitelyPresentedImmersionLocus`
(node `lem-sc-local-finitely-presented-immersion-locus`) .
It has no direct holes. The repaired proof uses the existing proved
`exists_localImmersionLocus`, which transitively uses the still-holed
`exists_gluedCompatibleImmersionCharts`; the item also uses the existing, still-holed
`picardUniversalSingleRankMatch_of_source_local`. These are existing downstream obligations,
not added holes. The lowest-cohomology locus theorem is used as already proved.

This is a decomposition: one original hole closed and one smaller local-chart hole added,
so the net direct-hole reduction is zero. No claim of a sorry-free axiom closure is made.

## No longer needed

The repair removes direct proof imports `Mathlib.AlgebraicGeometry.Gluing` and
`Sheaf.AlgebraicGeometry.CompatibleImmersionGluing` from the new finite-presentation module,
and removes its duplicated private helper. The direct node dependencies
`lem-sc-compatible-immersion-gluing` and `lem-weil-pbc-scheme-morphism-gluing` are replaced
by `lem-sc-local-immersion-locus`; their mathematical use remains transitive. No additional
module leaves the target import closure.

Removed the item's direct proof import of
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`. Its mathematical use belongs inside the
new chart obligation; its node `lem-pc-rf-perfect-base-change` remains a proof dependency of
that chart and is not pruned. The same applies to the stalk-rank step
`lem-sc-finite-locally-free-stalk-finrank`, moved from the item's direct dependency list to
the chart's. Retained `PerfectLowestCohomologyLocus` as a directly used proof import.

No module is claimed to leave the target import closure. No mathematical node is pruned.
The older structure-sheaf-unit-dependent `PicardSingleRankPerfectChart` and its
`TensorPullbackAdjunction` assumption are not needed for this item, but were never its imports
or direct proof dependencies. All pre-existing public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan includes essential unstated glue: the unrestricted local perfect chart
and descent retaining local finite presentation. The existing
`exists_picardSingleRankPerfectChart` assumes a universal structure-sheaf unit, which this
item does not assume. It cannot be applied to mixed or empty fibres. The existing
`exists_localImmersionLocus` forgets local finite presentation, so its output alone is
insufficient. The two new statements isolate and address these gaps without changing any
existing statement, definition, instance or visibility. The unit route remains unchanged.

For mixed fibres one must preserve empty tests: saying the predicate is simply false would
be wrong. The rank-one zero-complex chart makes the right-hand condition true on empty tests
and false on all nonempty tests, exactly matching the reference clause.

## New nodes

`lem-sc-picard-single-rank-unrestricted-perfect-chart`:
`lean/Sheaf/AlgebraicGeometry/PicardSingleRankUnrestrictedPerfectChart.lean`.
One local perfect-complex/rank-comparison obligation; no immersion construction. Its proof
spells out the homogeneous, empty and mixed-fibre cases, including residue-field tests and
rank invariance, and cites the existing perfect direct-image and stalk-rank nodes.

`lem-sc-local-finitely-presented-immersion-locus`:
`lean/Sheaf/AlgebraicGeometry/LocalFinitelyPresentedImmersionLocus.lean`.
Proved generic gluing statement with local finite presentation. Its repaired proof uses
the existing local immersion locus, uniqueness of local representatives by monomorphy,
pullback factorization and Mathlib target locality. No new hole, no change record and no forced adaptation is needed.

## Earlier second reading (a previous round; superseded)

1. Compared the item with the repository using diff. Its existing declaration signature,
   visibility, docstring and all public imports are byte-for-byte unchanged. Only proof
   imports and its proof change. The other two modules are new; no existing definition,
   instance, statement or target is changed. No change record is required. Verdict: pass.
2. Independently compiled all three modules in import order through lcompile.py. They
   compile without errors or unexpected warnings. Inspected every proof and scanned for
   forbidden declarations and attributes. The only direct sorry is the reported named
   unrestricted-chart theorem. A scratch-copy #print axioms check of all three public
   theorems reports only propext, Classical.choice, Quot.sound and sorryAx. The latter
   reflects the chart and existing open dependencies, not a sorry-free result. No data
   definition was introduced. The gluing existence specifies Cartesian charts, which
   determine the glued object up to its unique compatible isomorphism. Verdict: pass.
3. Read the new chart statement, its complete docstring argument and node against
   PicardUniversalSingleRankMatch, the existing restricted chart, perfect direct-image
   base change, and Stacks Tags [0BDP](https://stacks.math.columbia.edu/tag/0BDP),
   [0B91](https://stacks.math.columbia.edu/tag/0B91) and
   [0BDL](https://stacks.math.columbia.edu/tag/0BDL).
   Checked nonempty homogeneous rank-zero and positive-rank fibres, disconnected
   homogeneous fibres, empty fibres, mixed fibres, empty bases and tests, and arbitrary
   nonreduced tests. Open/closed images of rank strata justify each neighbourhood;
   nonempty fibres persist under field extension, fixing the reference rank in the
   homogeneous case and excluding all nonempty tests in the mixed case. The zero
   complex with rank one correctly retains empty tests. This local comparison is a
   strict part of the argument: it asserts neither representability nor gluing.
   The proved finite-presentation gluing theorem follows by Cartesian-chart transport
   and target locality, retaining exactly the needed finite-presentation conclusion.
   Repeated LeanFinder search with "Perfect pushforward of a vector bundle under a
   proper flat morphism commutes with arbitrary base change", Loogle search for
   AlgebraicGeometry.LocallyOfFinitePresentation, Mathlib grep with
   perfect.*[Bb]ase[Cc]hange|[Ii]mmersion.*[Ll]ocus|[Rr]ank.*[Cc]hart, and rg across
   both library roots. No replacement for either new statement was found. Verdict: pass.
4. Read the proof from the item downwards. Its actual reduction uses the existing
   lowest-cohomology representative and source-locality theorem, followed by the
   finite-presentation enhancement of the existing local immersion gluing proof.
   The existing restricted chart requires an unavailable structure-sheaf-unit assumption;
   the existing local immersion theorem drops the required finite-presentation property.
   No shorter applicable declaration was found. Proof-only imports are plain imports;
   every new public import supplies the statement's vocabulary or hypotheses. The old
   direct proof dependencies removed are exactly perfect base change and stalk finrank,
   both retained within the chart node. No module is claimed pruned. Read the unit record
   sk-prop-av-cube and its stated step: this reduction stays below that unit's route.
   Its realized arrays were already empty and are unchanged; this delivery makes no
   claim to repair that pre-existing bookkeeping omission. Verdict: pass.
5. Compared all three nodes with the Lean statements and actual proof uses. The item's
   changed fields are confined to proof, proof_deps and proof_origin. Both new nodes
   have sources, proof steps, dependency unions, searches, creation and blueprint
   provenance, chapter/unit, and matching Lean records. The one remaining direct hole
   has exactly its reported node and docstring. Verdict: pass.

Second reading changed only this report and added independent search evidence to the
sandbox search log. No Lean or node repair was needed. One original hole is closed,
one strictly smaller local-chart hole is added: this remains a decomposition, net zero.


## Second reading by G4

1. Compared every delivered module with the repository. The sole existing module's
   declaration signature, visibility, docstring and public imports are byte-for-byte
   unchanged. The other modules are new. No definition, instance or target changed;
   no change record or forced adaptation is needed. Verdict: pass.
2. Independently compiled all three modules with lcompile.py --all. All compile cleanly.
   A scratch module prints axioms for all three public theorems: exactly propext,
   Classical.choice, Quot.sound and sorryAx. The only direct hole is the named
   exists_picardSingleRankUnrestrictedPerfectChart. No forbidden declaration or
   attribute and no data definition is introduced. The proof transports the immersion
   representative supplied by an existing theorem; it does not define data from an
   arbitrary existence witness. Verdict: pass, with the reported open dependencies.
3. Read the split chart statement and docstring against the rank predicate and
   [Stacks 0BDP](https://stacks.math.columbia.edu/tag/0BDP),
   [0B91](https://stacks.math.columbia.edu/tag/0B91) and
   [0BDL](https://stacks.math.columbia.edu/tag/0BDL). Checked empty base/test/fibre,
   rank-zero and positive-rank homogeneous fibres, disconnected homogeneous fibres,
   mixed fibres and nonreduced tests. Field extension preserves nonempty fibres and
   distinct reference ranks. Zero with rank one describes precisely empty tests;
   zero with rank zero describes every test on the empty-fibre component. The chart
   is strictly a local complex/comparison part of the argument, not a restatement
   of representability. Its source and complete word proof are present in its
   docstring and node. Repeated LeanFinder with a derived-pushforward/Tor-amplitude
   query, Loogle for locally finite presentation, Mathlib grep for Tor amplitude and
   finite-presentation immersions, and rg in both library roots and the upstream
   algebraic-geometry sources. No exact replacement was found. The remaining hole
   is substantial and cannot be closed by a short application. Verdict: pass.
4. Read from the target reduction down. It combines source locality, the chart,
   the existing lowest-cohomology locus, and finite-presentation descent. The
   repaired gluing proof correctly reuses exists_localImmersionLocus and explicitly
   identifies each pullback with its local representative by monomorphy. All proof
   imports are plain imports; public imports supply statement vocabulary. Compared
   old proof_deps with the new list: perfect base change and stalk finrank move to
   the chart, as reported. No mathematical node or module is claimed pruned. Read
   sk-prop-av-cube and its realized arrays; the route is unchanged below the unit.
   The pre-existing empty realized arrays are not repaired or bypassed. Verdict: pass.
5. Compared all node statements and Lean records, actual proof steps, proof_deps
   and proof_origin. Each dependency list equals the union of its steps' uses.
   Existing-node changes are only proof, proof_deps and proof_origin. New nodes have
   the required provenance, sources, searches, creation, chapter/unit and Lean
   records. In particular the repaired gluing node names the reused local-immersion
   theorem and no longer names the deleted helper's direct dependencies. Verdict: pass.

This second reading changed only this report and added independent search evidence.
No further Lean or node repair was necessary. Closed one original direct hole and
added one strictly smaller chart hole: decomposition, net zero; no modules pruned.
