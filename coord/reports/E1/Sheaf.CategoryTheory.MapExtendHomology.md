## What changed

Copied the existing `Sheaf.CategoryTheory.MapExtendHomology` module into the E1 sandbox.
The canonical `mapExtendHomologyIso` definition and `mapExtendHomology_nonempty_iso`
theorem are already fully proved; no imports or declarations were changed.

## Proved and sorry left

`mapExtendHomology_nonempty_iso` is proved by packaging
`mapExtendHomologyIso E K q` in `Nonempty`. No `sorry` remains in the module and no
new holes were added.

## No longer needed

None. The two public imports are used by the construction.

## Where the brief, the DAG or earlier work was wrong

No discrepancy found. The DAG node and Lean module agree, and the module was already
proof complete.

## Earlier second reading (a previous round; superseded)

The module and DAG node were checked. The construction proves the unchanged target statement directly, with no new statements or remaining holes.

## Second reading by E1

1. **Visible changes and statements.** Compared the delivered module with the repository
   version. The declarations, definitions, theorem signatures, and imports are unchanged;
   only the proof term for `mapExtendHomology_nonempty_iso` differs (`Nonempty.intro`
   instead of angle-bracket notation). No change record is required.
2. **Compilation and axioms.** Compiled the module with `lcompile.py`; it succeeds with no
   warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by` declarations. `#print axioms` for both declarations gives only
   `propext`, `Classical.choice`, and `Quot.sound`.
3. **Statements and split-offs.** No statement was split off and no new node was added.
   The existing `mapExtendHomology_nonempty_iso` statement is unchanged and is proved by
   packaging the explicitly constructed `mapExtendHomologyIso`; it is exactly as strong as
   the DAG node and has no hollow definition.
4. **Shortest route and pruning.** The proof uses the canonical upstream
   `mapExtendHomologyIso` construction directly. Both public imports provide declarations
   used in the public definition, so neither can be removed. The node's `proof` and
   `proof_deps` agree with the Lean code, and there are no obsolete dependencies.
5. **Unit route.** The DAG node and its unit/chapter metadata agree with the module. The
   route through `HomologicalComplex.mapExtendIso` and `extendHomologyIso` is retained;
   no unit step is bypassed.

No repairs were needed beyond this report entry.
