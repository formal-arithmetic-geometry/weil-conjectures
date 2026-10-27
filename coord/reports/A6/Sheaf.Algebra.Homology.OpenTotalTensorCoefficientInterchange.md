## What changed

Replaced the body of `SheafOfModules.OpenTotalTensorCoefficient.interchange_exists`
with a complete Lean reduction. Its signature and all existing public imports are
unchanged. Added proof imports of three new modules; no other existing Lean module
or definition is changed.

The main module proves pure-tensor extensionality through the module
sheafification adjunction. Its source extensionality proof successively uses the
scalar-extension adjunction, the normalized gamma inverse, the extension/restriction
adjunction, total-summand extensionality and tensor induction. This proves the
interchange equation from the two computed generator values.

The target coefficient diagram is constructed by conjugating the source diagram
with the left comparison after scalar restriction. Cancellation proves its strict
identity, composition and naturality laws. The inverse generator formula and
multiplicativity prove that these transported transitions replace both scalar
entries exactly as required. Pointwise equality gives the tower equation, and
functoriality gives its localization. This is a decomposition, not a claim that
the new proof's axiom closure is already sorry-free.

`OpenTotalTensorSourceFamily` constructs and proves the source strict diagram from
the existing normalized tensor-to-scalar-extension transport. In each degree it
uses the flipped curried tensor functor on `algebraModules`, lifts its maps to
complexes, then conjugates by the normalized module comparison. The local pure
tensor formula is the existing `moduleTmul_map` theorem. No arbitrary witness is
used to define a public object, and no data definition contains a hole.

Validation: server single-file compilation through `lcompile.py`, with all four
sandbox modules compiled in import order. The final delivery tool also performs
its required preflight. No local Lake command was run.

## Proved and sorry left

Original holes closed (1 of 1):

- `SheafOfModules.OpenTotalTensorCoefficient.interchange_exists`
  (`lem-sf-open-total-tensor-coefficient-interchange`), proved from the new
  intermediate statements.

New theorem proved without a local hole:

- `SheafOfModules.OpenTotalTensorCoefficient.sourceCoefficientFamily_exists`
  (`lem-sf-open-total-source-coefficient-family`). It uses the existing
  `SliceTensorGenerator.tensorTransport_exists`, which remains a separate item.

New holes added (2), each in its own module with a complete proof in words:

- `SheafOfModules.OpenTotalTensorCoefficient.normalizedComparisons_exists`
  (`lem-sf-open-total-normalized-comparisons`): construct only the three normalized
  comparisons; no interchange equation or coefficient transitions.
- `SheafOfModules.OpenTotalTensorCoefficient.normalized_composite_values`
  (`lem-sf-open-total-generator-calculus`): compute the two forward values, the
  inverse value and complex naturality for already supplied normalized comparisons;
  no equality of the two chain maps or strict coefficient diagram.

The item module itself has zero remaining holes. Overall this delivery closes
one existing hole and adds two: a decomposition, with net minus one hole closed.

## No longer needed

No existing direct import is removed, and no library module is withdrawn. The
original file had only the public coherence-interface import; this stays verbatim.
The new comparison-construction and generator-calculus modules publicly import
only the normalization interface they state their conclusions with.

The direct proof-plan dependency on
`lem-sf-ringed-open-total-tensor-kflat` /
`Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat` is unnecessary: its unnormalized
comparison and K-flatness conclusions are not used. The normalized totalization
construction replaces that route, with no K-flatness assumption. The existing
transitive public imports have not been changed, so this is a removed proof-plan
edge, not a claim that that module has left the whole target import closure.

The main proof no longer directly uses
`lem-sf-ringed-slice-tensor-generators`,
`lem-sf-cbc-slice-tensor-generator-coherence`,
`lem-pur-cochain-pullback-tensor-coherence`, or
`lem-sfb-localized-site-tensor-restriction`: they remain the construction/calculus
lemmas' proof inputs. Corresponding obsolete direct `tool_uses` entries for the
first, third and fourth are removed; the remaining approval is unchanged.

`def-pur-localized-ringed-site`, `def-weil-extension-by-zero-presheaf`,
`def-weil-inverse-system`, `def-pc-sheaf-restrict-scalars` and
`def-weil-abstract-derived-category` need no separate direct proof edge: their
actual operations are packaged in the existing coefficient interfaces. Scalar
restriction and sheafification remain inputs to normalized construction. The
tower equality uses precomposition of actual functors and the existing derived
localization, rather than a separate inverse-system construction theorem.

For constructing the source family, the smaller
`lem-sf-slice-normalized-tensor-transport` suffices in place of obtaining the full
slice tensor coherence package. No unused statement is imported or proved.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface change was found. The original plan correctly
identifies the generator argument, but its assertion that the totalization,
coefficient-linear restriction comparison and the composite generator formulas
are already available directly from the module-level declarations hides substantial
Lean glue. Those two genuine mathematical steps are now isolated explicitly.

The three split nodes were checked conceptually on zero complexes, degree-zero
complexes, negative homogeneous degrees, identity coefficient maps and the zero
coefficient ring. The constructions use only direct sums, ordinary balanced
tensors and unitality; none requires flatness or boundedness. The inverse formula
must multiply both independent coefficient entries; this is retained verbatim.

The current unit realization is preserved. Existing lower-level statements from
other units are used only as general module/totalization tools, as in the original
route. The new source-family proof uses the existing normalized tensor transport
and `moduleTmul_map` as such tools; any required route-approval bookkeeping belongs
to the maintainer, not to a new worker-written `tool_uses` approval.

## New nodes

`lem-sf-open-total-normalized-comparisons` in
`OpenTotalTensorNormalizedComparisons` states the normalized ordinary chain
comparison construction (original proof steps 1 and 5). Its hole has a source and
complete proof in its docstring and DAG node.

`lem-sf-open-total-generator-calculus` in `OpenTotalTensorGeneratorCalculus`
states only the homogeneous composite/inverse calculations and complex
naturality (original proof steps 2, 3, 5 and 7). Its hole has a source and complete
proof in its docstring and DAG node.

`lem-sf-open-total-source-coefficient-family` in `OpenTotalTensorSourceFamily`
is proved from existing declarations and constructs just the source strict
coefficient diagram (part of original proof step 6). The target diagram and both
strict comparison squares are proved in the item, rather than assumed by this node.

All three nodes inherit the item's chapter and unit and name the current
projection-formula coherence blueprint ancestor. Searches were actually run via
`msearch.py` (Lean Finder, LeanSearch and source grep); the results are recorded
in each node. Blueprint searches for coefficient tensor, projection formula and
strict coefficient diagram found no duplicate of these specific refinements.
No change record is needed: no existing statement or definition was changed.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
