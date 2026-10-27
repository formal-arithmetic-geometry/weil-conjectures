# Q9 LocalizingInputs: statement setting and rework-scope repair

The upstream archive omits `[LocallyOfFiniteType X.hom]`, `[QuasiCompact X.hom]`
and `[IsSeparated X.hom]` from all three coefficient-specific tensor lemmas.
The unchanged proof `ObjectProperty.prop_tensor hK hL` now needs precisely those
instances through `isMonoidal_boundedConstructible`. The root module docstring
and DAG `lem-sfb-dc-tensor-preserves` already restrict schemes to this setting.
Thirteen successive workers were told by the launcher to restore this broken
text verbatim and repair only Sheaf modules, with no public Sheaf import path.
This was an incompatible assignment, not a compiler or provider failure.

## Statement corrected

The structured `statement_change` is in
`coord/changes/Q9-localizing-inputs-statement_change.json`. It preserves each old
and new effective statement (the section omission plus theorem header).
Restore the three geometric hypotheses in the root's three tensor declarations
and the exact two downstream rational tensor-closure declarations in
`ProjectionFormulaField`. Keep the characteristic-prime omission. No proof body,
import, name, attribute, definition, or DAG statement/plan changes.
The correction is to the overgeneralized Lean signatures, not a claim that the
arbitrary-scheme statements have been independently refuted.

`ProjectionFormulaAdic` is restored byte for byte. Its three uses of the integral
tensor lemma already supply the required hypotheses. The other field-consumer
uses also already do so. A full search of lean/, quarantine/ and DAG Lean
attachments found no other uses of the five corrected declarations.

## Validation

Server `tools/lean_file.sh`, `SHEAF_FILE_TIMEOUT=60`, one file at a time, against
the last green build plus this maintenance group's own compiled root. The root
and both consumers compile. The root keeps its original nine explicit sorry
bodies; neither consumer adds holes. Quarantine archives remain untouched.
Adjacent `.maint-Q9-1792925570.bak` files preserve the original sources; scratch
copies and structured-record `.bak` files are also retained. An inflight landing
keeps the files out of the global build until the validation and commit finish.
The finished interface landings are then verified by the ordinary global build;
only that verification may clear the quarantine/rework records.

## Next worker

Use the repaired canonical lean/ sources, not the old archive or the stale
verbatim-restoration prompt. Normal proof work on the nine remaining holes is
still open. Six earlier proof completions survive in the Q9 sandbox's
`scratchpad/RetainedSixHoleProofs.lean`; revalidate them against the repaired
signatures and do not restore the rejected arbitrary-scheme tensor sorrys.
The dispatcher and generic brief still contain obsolete upstream restrictions.
They are launcher-owned and were not edited. The maintenance REPORT.md names
the exact locations for the launcher owner to correct; this item no longer
requires a verbatim restore once its repaired canonical sources are present.
