## What changed

Proved `AlgebraicGeometry.ProEtale.comparison_pullback_coherent` in
`Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`. Identity and composition
are checked on restriction direct images using injectivity and functoriality of
adjoint conjugation. The specified square follows by pasting the two composition
equations with transport along its actual commutativity equality.

Added proof-only import `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`.
The categorical glue is private and fully proved. The public `ComparisonSquareData`,
`ComparisonSquareComponent`, and `comparisonSquareData` share the canonical square
data; the square clause of `ComparisonPullbackCoherent` uses this definitionally
identical API to prevent expensive repeated kernel conversions. No original
inverse-image construction or theorem signature changes. No other module is
adapted. The change record is
`coord/changes/U2-comparison-pullback-coherence-square-api.md`.

Updated the existing node's proof and Lean attachment to describe the implemented
route. The unit's proper-base-change route is retained.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.comparison_pullback_coherent`
(node `lem-weil-pbc-comparison-pullback`), the item's only sorry.

Added: none. Remaining sorry declarations in the delivery: none.
This is a proof, not a decomposition. The complete module compiled in 14.4 seconds on the project server, and
`#print axioms` of the theorem reports only `propext`, `Classical.choice`,
and `Quot.sound`. The independent reader repeated compilation and the axiom probe on a scratch copy
of the delivered source. Final preflight and delivery are run after this reading.

## No longer needed

Removed the redundant direct proof import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; it remains available through
the public `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar` import.
No DAG node or module is withdrawn; all ten existing proof dependencies remain
used by the canonical constructions or the identity/composition calculation.
The square needs only the supplied commutativity equality after those comparisons
are fixed; no separate square theory or new unproved obligation is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The square step simplifies to a generic cancellation
and equality-transport argument after composition coherence. The initial fully
expanded component predicate caused repeated costly kernel conversions; the
recorded API refactor expands to exactly the original equation and changes no
mathematical statement. Its public construction and the definition's expansion
must be checked by the independent reader.


## Second reading by U2

1. **Interfaces: pass.** Diffed the complete module against the shared repository.
   All fifteen original declaration signatures are byte-for-byte identical. The
   thirteen original inverse-image/adjunction/comparison construction bodies are
   unchanged. The only existing definition body changed is the declared refactor
   of `ComparisonPullbackCoherent`, covered by
   `coord/changes/U2-comparison-pullback-coherence-square-api.md`. Checked each of
   the eighteen fields of `comparisonSquareData`: its four pullbacks, four
   comparison functors, four pro-etale pullbacks, four comparison isomorphisms,
   and the two specified square isomorphisms expand the component predicate to
   the original equation, in the original order and with every original binder.
   No hypothesis, coefficient category, universe or conclusion changes. No other
   module is delivered. Repository-wide search finds no external use of the
   refactored predicate or theorem by name.

2. **Proof and constructions: pass.** Recompiled the repaired complete module
   with `lcompile.py`: clean, 14.4 seconds on the project server. A scratch copy
   of the actual sandbox source, with `#print axioms` appended, reports exactly
   `propext`, `Classical.choice`, and `Quot.sound` for
   `comparison_pullback_coherent`, `comparisonSquareData`, and
   `ComparisonSquareComponent`. There are no `sorry`, axioms, unsafe/opaque or
   replacement-code constructs anywhere in the delivery. The generic pasting
   lemmas cancel actual isomorphisms; equality transport is proved by substitution.
   The identity and composition calculations use injectivity of conjugation and
   finish with the identical underlying restriction maps. The square uses precisely
   `sq.w.symm` between the two composites. All data are explicitly constructed;
   none are arbitrary witnesses selected from an unproved existence statement.

3. **Split statements: pass, none.** The single original hole
   `AlgebraicGeometry.ProEtale.comparison_pullback_coherent` is closed and zero
   holes are added. The three new public declarations only package the existing
   square data and equation; they contain no postponed theorem. Every private
   helper is proved. The proof handles identities, arbitrary composites, and
   any supplied chosen Cartesian square, including degenerate identity squares.
   It does not require a nonempty scheme or nonzero coefficient ring; the zero
   ring and empty scheme are not excluded. Searches through `msearch.py`
   (LeanFinder, Loogle and grep, using adjoint-mate/coherence terminology) and
   `rg` in the upstream comparison modules found the existing adjunction and
   comparison constructions already used, not a theorem closing all three
   clauses for all coefficient categories.

4. **Route and pruning: pass.** Read the imported comparison construction and
   upstream mate laws. The proof uses the existing canonical restriction
   isomorphism and `conjugateIsoEquiv` composition/whiskering/unit laws directly.
   The chosen-square equation then follows by elementary isomorphism pasting;
   there is no reason to add a separate square obligation. The proof-only mate
   import is plain `import`. The redundant direct import of etale
   `UpperLowerStar.Defs` is removed, while its declarations remain supplied by
   the necessary public `Comparison.LowerStar` import. Checked all ten old
   `proof_deps`: each is still used in the public constructions or calculations,
   and their union equals the proof-step uses. No node or module is pruned.
   Read `dag/units/sk-thm-properbasechange.json`; its realized statement and
   three steps are untouched, and this local comparison proof bypasses none.

5. **DAG agreement: pass after metadata repair.** Read the node and every proof
   dependency's statement/Lean attachment. Steps 1--2 describe the unchanged
   canonical construction; step 3 describes the actual restriction calculation;
   step 4 describes composition cancellation and equality transport, matching
   the Lean proof. The node's mathematical statement and statement dependencies
   are unchanged. The Lean declaration list includes the three fully constructed
   square API definitions and the original declarations still present. There
   are no new nodes. Restored the shared repository's `reviewed_lean` field,
   which the first worker's stale copy had inadvertently changed; updated the
   delivery's Lean attachment author/date/branch to U2, 2026-10-16, sheaf-dag.

Changes in this reading: made the local continuity instance `etale_cont` private
so it does not accidentally add public API; repaired only the node metadata just
listed; added this independent reading and current compiler/axiom evidence. The
mathematical proof and the declared square API refactor needed no repair.

The source-only scratch axiom check compiled. A separate scratch check duplicating
the original expanded predicate and asking Lean to compare it with the bundled
predicate exceeded the 60-second limit; it is not used as verification evidence.
Definitional preservation above was checked by reading/substituting all fields.
The expanded predicate's conversion cost is the reason for the declared API
refactor. Scratch files are outside the delivered `lean/` tree.

Final dry run: `deliver3.py U2 Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
--no-push` printed OK (commit `1cd49bc5d6`), with compilation and preflight
passed; review class CODEX for the documented API/definition refactor.
