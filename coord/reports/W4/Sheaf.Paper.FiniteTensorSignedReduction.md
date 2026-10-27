## What changed

Proved the assembly and uniqueness of
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorLines` with its
original signature. Its proof uses two private imports of new statement modules.
`FiniteTensorSemilinearReduction` isolates the ordinary normalized semilinear
family. `FiniteTensorLineDerivedExistence` isolates unique existence at one signed
exponent, for an already given normalized ordinary family, retaining the actual
adjunction's transpose equation. The proved private generic `existsUnique_family`
chooses only pointwise unique witnesses, assembles their normalization, and proves
family uniqueness by function extensionality. The parent then proves outer
uniqueness from the ordinary normalization. No data is selected from non-unique
unproved mere existence. No existing definition body changes.

Updated the owning DAG proof and added two nodes with sources, full proof plans,
Lean attachments, and logged LeanSearch, LeanFinder, Loogle, and Mathlib grep
searches. The unit route and every existing declaration signature and definition
body are preserved. This is a partial decomposition, not a complete proof of the
finite signed-line reduction construction.

## Proved and sorry left

Closed one of the item's two original holes:
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorLines`.
This is a decomposition into two strictly smaller mathematical statements, with
a complete Lean family-assembly and outer-uniqueness argument.
The previously proved `existsUnique_finiteTensorTwistShiftComparison` is preserved.

The original hole left is
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorCore`, owned by
`def-pur-finite-signed-reduction-comparisons`.

Added two holes:

- `WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorSemilinearReduction`,
  node `lem-pur-finite-tensor-semilinear-reduction`: ordinary signed sheaf maps only.
- `WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorLineDerivedComparison`,
  node `lem-pur-finite-tensor-line-derived-existence`: unique existence for one signed
  exponent and an already given normalized semilinear family, with its full
  prescribed transpose equation.

Total delivered holes: three (one retained, two added). Net closure contribution:
minus one. Neither new theorem restates the parent: neither asserts its nested
existence-and-uniqueness result, and family uniqueness and outer uniqueness are proved in the parent.
Edge cases checked mathematically: r=0, r=1, positive tensor powers, negative dual
powers, m=n, level one, ramified coefficient quotients, and the empty scheme.
Flatness of the quotient is never assumed.

## No longer needed

No modules or nodes are withdrawn; no existing imports are removed. The two new
proof imports are both used. Existing public imports are retained as the module's
published interface. No additional planned mathematical branch is introduced by
this decomposition: the two nodes isolate steps of the original docstring plan.

## Where the brief, the DAG or earlier work was wrong

The source already contains A8's proof of the natural twist/shift comparison,
landed earlier on 2026-10-25; the starting hole count is two, not three. There is
no current quarantine/rework row or W4 return for this item.

The existing `SignedLineScalarTensorTower.exists_signedLineComparison` is a useful
ordinary tool, but assumes a given first-line scalar comparison and has its own
normalization; it is not the prescribed integral-balanced finite-level semilinear
family. `scalarExtensionTateMaps_existsUnique` uses finite-root presentations,
whereas this item's first line is the actual integral-reduced presentation. A
future proof must supply their canonical comparison and transport the equation,
rather than silently identifying the presentations. The derived scalar API also
needs its actual adjunction/representative normalization; arbitrary endpoint
isomorphisms would not prove the required statement. No false statement was found.

An initial explicit inverse-adjunction construction and later pointwise existence
assembly hit the per-file limit. Profiling identified kernel comparisons of the
specialized adjunction types, not slow tactics. Pairing the construction with its
equation and generalizing the assembly did not make runtime reliable. The final
split therefore groups the pointwise existence and adjunction-injectivity step
into one genuine local conclusion, while the parent proves the family and outer
uniqueness. No limit was raised or existing definition changed.

Duplicate searches over all DAG nodes, project Lean, Mathlib, and the current
blueprint found no exact finite-level integral-balanced statement. The existing
completed-integral-to-finite `signedTwistReduction_comparison` is a different
coefficient map and cannot be applied as the finite-to-finite result. New-node
plans reuse the existing signed-line scalar and rank-one scalar-computation nodes.

## New nodes

`lem-pur-finite-tensor-semilinear-reduction`, module
`Sheaf.Paper.FiniteTensorSemilinearReduction`: constructs and uniquely normalizes
ordinary maps, with no derived comparison. The source is finite reduction of
purity Step 2 and the coefficient-twist convention. The existing generic signed
scalar comparison and rank-one local-freeness results supply its planned route.

`lem-pur-finite-tensor-line-derived-existence`, module
`Sheaf.Paper.FiniteTensorLineDerivedExistence`: asserts the unique existence of the
normalized derived isomorphism for one exponent, conditional on an ordinary
normalized family. Its proof is the flat single-complex calculation of the same
source step. It contains no definition or choice.
The parent supplies family packaging, family uniqueness and outer uniqueness
through its proved generic helper. No existing definition or
statement changes, so there is no change record or forced consumer adaptation.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
