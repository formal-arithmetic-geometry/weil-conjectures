## What changed

Proved `exists_descend_model_localization` in
`Sheaf.AlgebraicGeometry.DescendModelLocalization`, preserving its public signature,
visibility, public imports, and existing docstring. Added two fully proved private
helpers: `shrink_scalarTower` and `exists_base_element_model_localization`.

The proof uses Mathlib's `IsAlgebraic.exists_nonzero_dvd` to choose the nonzero
base coefficient divisible by `t`. It constructs the actual model as the shrink
of `Localization.Away (algebraMap S0 A0 a)`, proves the base localization is
`A[1/(c0*b)]`, and transports finiteness, étaleness, fraction field, localization,
and scalar towers. Spectrum surjectivity follows from integral lying over for the
injective finite algebra map. All data come from explicit localizations and ring
equivalences; there is no selection from an unproved existence theorem.

Added proof-only imports of Mathlib's algebraic, integral, localization finiteness,
iterated localization, module smallness, and algebra shrink APIs. Updated the
existing DAG node's proof and proof origin to describe this implemented route.
The unit's realized statements and proof steps are unchanged.

Validation: the module compiles without warnings through `lcompile.py`. The
required `deliver3.py --no-push` dry run also checks declaration signatures and
the allowed axioms. No other library modules are adapted.

## Proved and sorry left

Closed: `exists_descend_model_localization`
(node `lem-weil-pbc-descend-model-localization`), the only original hole.

Added holes: none. Remaining holes in the delivered module: none.
Both private helpers are fully proved. This is a complete proof, not a decomposition.

## Second reading by E2

1. **Interface and visibility:** Compared the delivered module with the repository
version. The existing theorem statement, docstring, module header, and public imports
are unchanged byte for byte; the added imports are plain proof-only imports. Verdict:
pass.

2. **Proof and axioms:** Compiled the module with `lcompile.py`; it has no remaining
`sorry`, forbidden declarations, or warnings. A scratch `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. **Statements and helpers:** The private helpers are explicit localization and
`Shrink` constructions, with no data selected from an unproved existence theorem. The
target is proved with its original hypotheses and conclusion, and no new public
statement or split-off node was introduced. Verdict: pass.

4. **Pruning and route:** Checked the proof against the Mathlib APIs and the original
node. All six added imports are used by the proof, no original import is removable,
and the unit `sk-prop-sf-cbc` has no realized statement or steps to alter. Verdict:
pass.

5. **DAG agreement:** Updated the existing node's proof and proof origin to match the
implemented route; its statement, dependencies, unit, and chapter are unchanged.
There are no new nodes or change records. Verdict: pass.

Changed during second reading: added this review section only; no Lean proof or DAG
content required repair.

## No longer needed

No original imports, DAG nodes, or library modules are pruned: the original node
had no proof dependencies. No Sheaf or WeilConjectures proof-dependency imports
are needed. The exploratory `Mathlib.RingTheory.Ideal.GoingUp` import was removed;
the used integral lying-over API is already available through the retained imports.
The exploratory auxiliary module was removed; all helpers reside in the item.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface error was found. The least-degree integral
polynomial argument is already available through Mathlib's
`IsAlgebraic.exists_nonzero_dvd`; reimplementing it is unnecessary.
The assumed original spectrum surjectivity is redundant for this algebraic
construction: finiteness and the subalgebra embeddings give integral lying over.
The original hypothesis remains unchanged in the public theorem.

Searches were run with `msearch.py` (LeanFinder, Loogle, grep), followed by reading
the matching Mathlib declarations. The source blueprint path listed by the node
is absent from this clone; the existing node and declaration contain the full
localization argument used here. The unit record has no realized statement or
steps for this extracted algebraic lemma.
