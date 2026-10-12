## What changed

Replaced the sole `sorry` in `Sheaf.CategoryTheory.RightDerivedPlusCube` with a complete
proof of `CategoryTheory.Functor.rightDerivedFunctorPlusBaseChange_cube` following both
steps of `lem-weil-pbc-right-derived-plus-cube`. Two proved private helpers compose the
existing exact-functor factorization equations and invert the resulting isomorphism equation.
The main proof forms the two natural transformations, applies `rightDerived_ext`, factors
all four faces through their units, identifies the exact edges, and maps the assumed
underived cube equation into the bounded below homotopy and derived categories.

The public statement, universes, visibility, existing docstrings, and imports are unchanged.
No other module, definition, or statement is adapted. The existing DAG route is realized
as written, so no node update is needed. Local compilation is clean and takes about ten
seconds, below the sixty-second single-file limit.

Searches: LeanFinder returned generic localizer comparison and Guitart exactness APIs,
not a cube theorem. Loogle returned the general right-derived API. The launcher grep
search found no cube or inverse-factorization match; repository searches found the
factorization lemmas and the proved homotopy-category composition API used here.

## Proved and sorry left

Closed: `CategoryTheory.Functor.rightDerivedFunctorPlusBaseChange_cube`
(node `lem-weil-pbc-right-derived-plus-cube`), one of one original holes.

Added holes: none. Remaining holes in the delivered module: none.
The explicit `#print axioms` check reports exactly `propext`, `Classical.choice`, and
`Quot.sound` for the cube theorem, with no `sorryAx` or other axioms.

Both private helpers, `exactComparison_factorsh` and `exactComparison_inv_factorsh`,
are fully proved. This is a proof, not a decomposition into new unproved statements.

## No longer needed

None. No import was added or removed; the sole existing public import is required by
both the statement and the proof. No planned dependency, node, module, or unit step is
bypassed. No additional geometric, acyclicity, or injective-preservation lemma is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The formal route described by the existing docstring
and DAG works with the original hypotheses, including noninvertible `a` and `b` and
without preservation of injectives by `U` or `U'`.

## Second reading by G1

1. Compared the delivered module with the repository version. The public theorem signature, hypotheses,
   conclusion, universes, visibility, and existing imports are unchanged; only the proof and private
   helper lemmas were added.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. A scratch `#print
   axioms` check gives only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.
3. The private factorization helpers are direct consequences of the existing composition and natural
   transformation factorization lemmas. They introduce no split-off statements, and repository searches
   found no existing declaration duplicating them or the cube theorem.
4. The proof follows the node route: it compares the two derived natural transformations, applies
   `rightDerived_ext`, factors all four base-change faces through their units, transports the exact
   comparison isomorphisms, and invokes the underived cube equation. The existing public import is
   still needed, and no unused import or old proof dependency was removed.
5. The theorem statement and DAG node agree byte for byte, and the unit route remains the recorded
   `sk-thm-p1` route. No new nodes or change records are needed.

Changed after review: appended this second-reading record only; no Lean or DAG changes were required.
