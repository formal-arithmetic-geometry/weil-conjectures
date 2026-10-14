## What changed

Repaired `lean/Sheaf/Paper/ModuleCupDerivedClassComparison.lean` at the supplied broken tip.
Replaced its public import of `ModuleCupNaiveDerivedCompatibility` with the direct
`ModuleCupKInjectiveTarget` import. Replaced every use of `moduleCup_globalComparison X K`
with its defining expression `(moduleCup_comparisonNatTrans X).app K`, and removed the
now-unused wrapper from the unfolding and local irreducibility lists.

The public structure's cycle formula is definitionally unchanged: the old wrapper is
exactly the new expression. The theorem signature, universes, binders, abbreviation body,
visibility, docstrings and mathematical construction are preserved. The DAG proof and
proof dependencies now record the direct component and omit the unused compatibility
proof dependency. The change record is
`coord/changes/ModuleCupDerivedClassComparisonRestore.md`. No consumer or dependency was edited.

Single-file checks using `lcompile.py`, remote fallback disabled, reproduced the original
combined-import collision and verified the repaired proof with the normalization module
present (35.3 seconds). A further single-file check imported all three dependencies with
`import all` and printed axioms (30.7 seconds). The existence theorem, abbreviation and
structure each use exactly `propext`, `Classical.choice`, `Quot.sound`. All temporary
verification directives were removed from the final source. The final source compiled
cleanly in 32.4 seconds, with no warnings or errors. No build, server compile,
delivery, .check file or second-reading evidence was produced.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.exists_cupDerivedClassComparison` remains completely
proved, as do its existing private helpers. There is no sorry in the repaired module.
Holes closed by this repair: zero (the landed theorem already had a proof).
Holes added: zero. No new statements or definitions are introduced.
The injective-resolution, naturality and cycle-representative argument is unchanged.

## No longer needed

Removed the public import `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` and the proof
dependency `lem-sc-module-cup-naive-derived-compatibility`. The comparison needs its
transparent wrapper's body, not its tensor compatibility theorem or local tensor instances.
`Sheaf.Paper.ModuleCupKInjectiveTarget` supplies the actual comparison natural transformation.
The removed wrapper is no longer unfolded or marked locally irreducible here.
This is pruning from this module's closure, not a claim that the compatibility module is
unused by every project target. All other proof dependencies and the unit route are retained.

## Where the brief, the DAG or earlier work was wrong

The previous restoration correctly named instances in this module and recognized another
instance-name collision, but left that collision unresolved because a standalone compile
passed. The global axiom/sorry probe also loads private proof dependencies, including
`GlobalTensorPullbackMonoidalNormalization`. Its generated local instance names conflict
with those in `ModuleCupNaiveDerivedCompatibility`. A temporary combined import reproduced
that failure. Removing the unnecessary compatibility import fixes the combined environment
without edits outside the allowed module.

The reported self-importer failure has the same underlying import collision, rather than
a changed mathematical contract. The repaired combined environment and private-import
check compile, and the target's axiom output contains no sorryAx. The earlier report's
second-reading section and claims of delivery/preflight success have been removed; this
repair is left for the independent reader and is not delivered or pushed.

## Second reading by XRa0a656f89c54729e

Independent second reader, 2026-10-14. I read request.json, the original delivery.diff,
the repaired Lean file, node, change record and report, and the stage-3 review instructions.
The checkout has transactionally removed this module and node, so I compared the repair
with the exact landed source recovered from delivery.diff as well as the current dependencies.

1. Interface and targets: PASS. The only public-signature edit replaces
   `moduleCup_globalComparison X D.integerComplex` by
   `(moduleCup_comparisonNatTrans X).app D.integerComplex`. I checked the wrapper's
   definition in ModuleCupNaiveDerivedCompatibility: its body is exactly that component.
   This is a definitional unfolding, documented with the old and new interfaces in the
   change record. The existence theorem signature, abbreviation body, hypotheses,
   universes, visibility and docstrings are preserved. No target or dependency is edited.
   A source search found no current importer or external use needing adaptation.
2. Compilation and trust: PASS. With LCOMPILE_REMOTE=0 and WEIL_SERVER_COMPILE=0,
   I compiled the sole touched Lean file through lcompile.py: clean exit 0 in 34.0 s.
   An independent scratch copy of the original landed source with `import all
   Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization` reproduced the duplicate
   generated CommRing-instance failure in 1.4 s. A scratch copy of the repair with the
   same normalization import and separate `import all` directives for all three direct
   dependencies compiled cleanly in 27.6 s. Its #print axioms results for
   exists_cupDerivedClassComparison, cupDerivedSections and CupDerivedClassComparison
   were exactly propext, Classical.choice and Quot.sound, without sorryAx. Static
   inspection found no sorry, axiom, unsafe, opaque, extern, implemented_by or kernel
   checking bypass. The returned probe collision and consequent self-importer failure
   are addressed by removing the unnecessary colliding import, not by a trust workaround.
3. Split statements and mathematics: PASS. No statement or hole was split off or added.
   I read the injective-resolution construction, invertible derived comparison,
   augmentation naturality, extension homology/cycles isomorphisms, transport equation
   and final explicit cycle lift. They prove the same comparison and representative
   formula. The lift uses actual inverse isomorphisms; no unspecified witness is chosen
   from an unproved existence theorem. The formulas include degree zero and zero cycles.
4. Route and pruning: PASS. The repair directly uses the comparison natural transformation
   and the existing Mathlib resolution and homology machinery. Local searches for
   resolution comparison and extension-cycle lemmas revealed supporting machinery
   already used, rather than an exact shorter replacement for this representative formula.
   All three public imports supply names used in public signatures or definitions.
   No longer needed lists the sole removed import and proof dependency. I checked
   dag/units/sk-prop-av-cube.json: its realized route is unchanged; no unit step is bypassed.
5. DAG and report: PASS. The node's proof steps describe the Lean construction, their
   uses union equals proof_deps, and proof_origin identifies the repair. Its mathematical
   statement and statement dependencies are retained; its reference to the old comparison
   wrapper denotes the same natural-transformation component. The change record accurately
   explains the definitional signature edit, import pruning and absence of forced users.
   The report correctly counts this as a red-build repair: zero holes closed or added.

Second-reading changes: appended this independent review and wrote .check. The dry-run
preflight required restoration metadata for the node absent from the current base: corrected
created.group and lean.by from D2 to XRa0a656f89c54729e and added the New nodes entry below.
No Lean or change-record repair was necessary. Scratch verification files are outside the
sandbox and are excluded from delivery. All compilation used lcompile.py with its
60-second single-file limit; no lake build or server compilation was used.

## New nodes

`lem-sc-module-cup-derived-class-comparison` is restored from the failed D2 landing,
not a newly split mathematical statement. Its unchanged existence theorem is completely
proved by the preserved injective-resolution and cycle-transport argument. The restored
node records the repair group in created.group and lean.by, while proof_origin retains
attribution to the landed D2 construction. Its import pruning and definitionally equal
interface edit are documented in `coord/changes/ModuleCupDerivedClassComparisonRestore.md`.
