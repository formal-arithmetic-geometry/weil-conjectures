## What changed

Replaced the sorry in `FormalGlueing.h0_chart_power_lift` by a complete Lean proof
from compatibility of an explicitly constructed localized tuple. The existing signature,
visibility and docstring are unchanged. Added proved private helpers `clear_family`,
`numerator_vanish`, `swap_self`, and `self_overlap`. The proof constructs the tuple through
Mathlib's canonical finite-product localization equivalence; no data is chosen from an
unproved mere-existence theorem. It then clears a numerator denominator and both finite
families of compatibility errors, constructs membership in `h0`, and transports the chart
coordinate back through the self-localization equivalence.

Added `Sheaf.RingTheory.FormalGlueingLocalizedChartTuple`, whose single statement specifies
the canonical tuple by an actual construction and asks only for its two compatibility
families after localization. This isolates steps 1–2 of the existing plan; it neither
produces an `h0` element nor states power lifting. The original module now imports that
module and finite-product localization. The remaining tuple identities follow the square
and cocycle conditions and the canonical swap/tensor comparison formulas.

## Proved and sorry left

Closed `FormalGlueing.h0_chart_power_lift` (node
`lem-weil-pbc-formal-glueing-H0-chart-power-lift`) from one new strictly intermediate
statement. This is a decomposition, not a claim of a sorry-free transitive proof: one
original hole closed and one lower hole added; net zero holes.

The only sorry in the delivery is `FormalGlueing.localized_chart_tuple_compatible`
(node `lem-weil-pbc-formal-glueing-localized-chart-tuple`). It is the entire proof of its
public theorem in its own module. Its docstring and node contain the source and argument.
There are no sorries in the original module or the private helpers. In particular the
all-equal cocycle/self-overlap step and all finite denominator/error clearing are proved.

Both modules compile with lcompile.py. Edge cases checked in the argument: `t=0` has no
index; `f i=0` makes the localized modules zero; zero rings and zero modules require no
extra hypothesis. Flatness is not needed in these local calculations, but the original
flatness binder is preserved unchanged.

## No longer needed

Removed the original module's direct proof import
`Sheaf.Paper.FormalGlueingCanonicalMaps`. Its node
`lem-weil-pbc-formal-glueing-canonical-maps` is no longer a direct proof dependency of
chart power lifting; the new compatibility item retains this dependency for its square
and cocycle argument, so the canonical-maps module is not globally pruned. No other
original planned node or module is pruned. In the new compatibility module, the second
reader narrowed the unused `FormalGlueingH0` public import to `FormalGlueingData`;
the original module still needs and imports `FormalGlueingH0`. All the remaining original public imports
are retained for the unchanged statement.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The finite clearing step marked elementary in the old DAG
requires Mathlib's finite product localization instances, from
`Mathlib.RingTheory.TensorProduct.IsBaseChangePi`; those instances make the combination
shorter and avoid manually taking maxima of exponents. The existing self-overlap step
is now formalized by cancellation of the localized overlap map.

An attempt to finish both canonical tuple compatibility families encountered expensive
elaboration of iterated localizations and restricted tensor scalars; the final delivery
keeps exactly those identities as a standalone public theorem, with no partial proof
or internal sorry. This is below the unit level and leaves the unit route unchanged.

## New nodes

`lem-weil-pbc-formal-glueing-localized-chart-tuple` is stated in
`lean/Sheaf/RingTheory/FormalGlueingLocalizedChartTuple.lean` as
`FormalGlueing.localized_chart_tuple_compatible`. It fixes the tuple using the canonical
finite-product localization equivalence and asserts vanishing of the localized defining
differences. Source: Stacks 05EL conditions (a),(b), 05EP and 05ER second paragraph.
LeanSearch was unavailable (Internal Server Error); LeanFinder/Loogle returned generic
denominator and localization tools, and source/blueprint grep found no existing matching
compatibility theorem. The parent node's proof and dependencies now follow the Lean
construction and combination. No definition, existing statement or interface changed;
no change record or forced adaptation is needed.


## Second reading by G1

1. **Unchanged public contract: pass.** Read the whole repository and delivered
   chart-power-lift modules and their diff. The existing `h0_chart_power_lift`
   signature is byte-for-byte identical, including `hflat`, all universe and
   index binders, and the exact equality `h.val.2 i = (f i) ^ n • x`.
   No existing definition, visibility or docstring changed; the four new private
   helpers are fully proved. No change record or forced adaptation is needed.
2. **Kernel proof and construction: pass with the reported dependency hole.**
   Both modules compile cleanly through `lcompile.py`. Separate scratch copies
   with `#print axioms` showed only `propext`, `Classical.choice`, and `Quot.sound`
   for `clear_family`, `numerator_vanish`, `swap_self`, and `self_overlap`.
   `h0_chart_power_lift` and `localized_chart_tuple_compatible` additionally use
   `sorryAx`, exactly as expected from the one reported new compatibility hole.
   Scanned both delivered modules for forbidden declarations and found none.
   The tuple is explicitly constructed with the canonical localization equivalence;
   numerator and annihilator witnesses come from proved Mathlib localization lemmas.
   No data is chosen from the open compatibility theorem, whose conclusion is a
   proposition about the fixed tuple, and there is no sorry in any definition.
3. **Split statement: pass as a genuine decomposition, not a complete proof.**
   Matched both displayed difference maps against the kernels defining `h0`.
   The square `X.square i j` evaluated on the prime coordinate identifies the
   prime/chart terms after the canonical tensor comparison, which is injective
   by `compare_properties`. The cocycle `X.cocycle i j k` evaluated on the
   twice-localized `x` identifies the chart/chart terms after canonical swaps.
   This holds for an arbitrary ring map: flatness is unnecessary for these
   identities. With one chart, the self-overlap identity and the inverse-alpha
   equation give both equations; with `f i = 0`, zero rings or zero modules,
   the localized targets are zero. With no charts there is no `i`.
   The theorem asserts these identities for a fixed tuple, and contains neither
   an exponent nor an `h0` witness, so it is strictly the compatibility part of
   the argument. Its source and complete prose proof are in its docstring and
   its own node. Independently searched LeanFinder using commuting-square and
   kernel-equation terms, Loogle for finite-product localization, the search
   wrapper's grep, and `rg` over local Sheaf/WeilConjectures sources. Found generic
   localization tools but no existing canonical-tuple compatibility declaration.
   The remaining identity proof is not a short lemma application; it stays open.
4. **Route and pruning: pass.** The new proof uses Mathlib's finite-product
   localization and equality-clearing lemmas directly, then cancels the chart's
   self-localization. Read `dag/units/sk-thm-p1.json`, including `realized`:
   neither item node realizes a unit statement or step, and no unit route is
   bypassed. Compared all old `proof_deps`: only canonical maps ceased to be a
   direct dependency, and it remains under the new compatibility theorem. The
   report states this; no original module is globally pruned. The original
   public imports serve its unchanged signature, and the new module's product
   localization import serves instance synthesis inside its statement.
5. **DAG agreement: pass after repair.** Read both sandbox nodes and the original
   item node. The item's new proof steps follow the tuple, self-overlap,
   numerator, annihilator and chart-cancellation code, and their `uses` union
   equals `proof_deps`. Only permitted proof-related fields changed in the
   existing node. The new node has source, self-contained statement, dependency
   lists, searches, creation/provenance, chapter/unit and Lean records. Replaced
   its flattened `lean.statement` with the exact multiline Lean signature.

Second-reading changes: narrowed the new module's public `FormalGlueingH0`
import to `FormalGlueingData`, made injectivity of the tensor comparison explicit
in the new theorem's prose proof, corrected the new node's verbatim signature,
and added this review and the import clarification above. Existing proof code
needed no repair. Rechecked the source argument against [Stacks 05EL]
(https://stacks.math.columbia.edu/tag/05EL), [05EP]
(https://stacks.math.columbia.edu/tag/05EP), and [05ER]
(https://stacks.math.columbia.edu/tag/05ER), since the cited TeX is absent on this
machine. Closed one original hole, added one strictly intermediate hole: net zero.
