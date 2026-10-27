## What changed

Replaced the sole hole in `Sheaf.Paper.SignedTwistSiteTransport` by a complete Lean proof
assembling the source's separate dual-extension, product and geometric results. The private
`root_normalized` lemma proves the remaining degree-one coefficient formula directly: lift
roots along the locally surjective root-tower projection, apply the supplied positive
normalization and theta formula on that cover, then use separatedness. The final inverse-theta
calculation and uniqueness argument are complete.

Moved the original 17 coefficient, section and normalization declarations, verbatim, into
`Sheaf.Paper.SignedTwistSiteTransportData`. The original module publicly reexports this module.
The original theorem's entire signature is byte-identical. The extraction makes the three
separate results importable without a cycle; it changes no object, map, hypothesis or target.
No source-library module was changed. The definition node owns the moved Lean attachments;
the original node keeps the original theorem attachment and its unchanged statement dependencies.

Added three single-theorem modules for the genuine separate results of source Steps 2, 3 and 4:
`SignedTwistEvaluationExtension`, `SignedTwistProductCompatibility`, and
`SignedTwistGeometricCompatibility`. Their exact remaining statements have sources, complete
proofs in words, and matching DAG nodes. The top theorem uses all three, rather than restating
its whole conclusion as one new assumption.

The full five-file server compilation passed without warnings (result
`60ac85a0915524ca7a83cddf`, 2026-10-25). Single-file times were 46.5–54.8 seconds. There are
no hollow definitions or new choices of objects from existence-only statements. The data
block and original theorem signature were compared mechanically with the repository source.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.signedTwistSiteTransport` (1 of 1 original holes).
The private `root_normalized` proof is also complete. The original module now has zero holes.

Added and retained exactly these three public theorem holes, one per new module:

- `WeilConjectures.PurityFiniteSetting.signedTwistEvaluationExtension`, node
  `lem-pur-signed-twist-evaluation-extension`: existence and uniqueness of the dual extension,
  with the actual section evaluation equation; source Step 2 only.
- `WeilConjectures.PurityFiniteSetting.signedTwistProductCompatibility`, node
  `lem-pur-signed-twist-product-compatibility`: the ordered product equation for an already
  evaluation-normalized family; source Step 3 only.
- `WeilConjectures.PurityFiniteSetting.signedTwistGeometricCompatibility`, node
  `lem-pur-signed-twist-geometric-compatibility`: the root/dual pullbacks, their coherence and
  the negative comparison square for that family; source Step 4 only.

This is a decomposition, not a net proof of the item: one original hole closed, three added,
net minus two before any closure-ledger effects. No claim of axiom-free completion is made.
The four statements neither add a hypothesis to the original theorem nor weaken its conclusion.
The data module has zero holes. Scratchpad experiments are not delivered.

## No longer needed

Removed these original direct imports from the item (some are still available transitively
through the unchanged data definitions, and mathematical dependencies of the lower results
remain in their nodes):

- `Mathlib.AlgebraicGeometry.Scheme`
- `Sheaf.Paper.PurityFiniteSetting`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `Sheaf.Paper.PurityFrameClass`
- `Sheaf.Paper.FiniteTateSiteDescent`
- `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison` (now a private proof import using its
  proved section lemmas, and a public dependency of the data module)
- `Sheaf.Algebra.Homology.SignedLineDerivedBaseChange`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Sheaf.Paper.AmbTateRootProjectionReduction`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback`
- `Sheaf.Paper.ComparisonPullbackExact`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.SecSmoothPurity.CochainInverseComparison`

Retained `ProEtaleSiteComparison` and `IntrinsicCoefficientTwistsUnrestricted` as public
imports of the item to preserve the blueprint unit route. The data module retains only its six
required public interfaces. The item retains the public
product-normalization interface and adds private imports of the three separate results and
`RootTowerFiniteTensor`. Its root proof uses the local-surjectivity clause of
`lem-amb-root-tower-finite-tensor`; it needs neither a flatness assumption nor a new root theorem.
The original planned duality and geometric dependencies are retained below the new step nodes;
none is falsely reported as globally unused. No module is withdrawn and no complete DAG branch
is claimed pruned. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false original statement was found. The old proof plan describes the mathematics correctly,
but applying its ringed-site dual-pullback declarations to these fixed-coefficient sheaves
requires a comparison between presentations and their section formulas. This is the remaining
content of the dual-extension result, not a missing theorem that merely restates the full item.
The product and geometric assertions are independently stated consequences with fewer
conclusions and strictly fewer data than the item. They retain the source arguments.

Exploratory server-checked lemmas establish positive-comparison uniqueness from a primitive-root
basis and the root-tower projection, the action of the basis comparison on pulled generators,
and the coordinate formula for pro-etale evaluation. These helpers alone do not finish the
presentation bridge and are left only in the scratchpad, not imported unused into the library.

The new statements were checked at degree zero, positive and negative degrees, equal opposite
exponents, characteristic two, arbitrary ramification and the empty scheme. The use of
predecessor n is unchanged. The original theorem's parameter theta does not enter any of the
three step statements; its exact normalization is proved separately in the item.

`tools/downstream.py` for the coefficient declaration and the item theorem reported zero
current downstream modules. Searching every moved name throughout both Lean roots and the
quarantined sources found only the original item. No consumer needs an adaptation. New
consumers are listed in the change record. Blueprint searches for evaluation, signed and Tate
found no identical fixed-map statement; the generic duality results are cited as dependencies.
The current blueprint frame-independence proof's unit-multiple, permutation and base-change
passages provide the ancestor references, via the original supported-cup node.

## New nodes

`def-pur-signed-twist-site-transport-data` owns the 17 unchanged declarations extracted into
`SignedTwistSiteTransportData`. It adds no mathematical assumption or construction.

`lem-pur-signed-twist-evaluation-extension` records exactly source Step 2: a unique extension
from the prescribed nonnegative maps to the actual signed duals, preserving evaluation.

`lem-pur-signed-twist-product-compatibility` records exactly source Step 3: normalized ordered
products commute with an evaluation-normalized signed comparison for all sign combinations.

`lem-pur-signed-twist-geometric-compatibility` records exactly source Step 4: the root/dual
geometric maps satisfy their laws and the negative comparison-mate square.

Change record: `coord/changes/A6-signed-site-transport-definitions.md`. It records the identical
old and new data block, reexport, consumer audit, and relocation of the owning Lean attachment.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
