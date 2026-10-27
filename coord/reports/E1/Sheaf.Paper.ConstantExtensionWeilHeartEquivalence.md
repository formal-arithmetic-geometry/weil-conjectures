## What changed

Filled the assembly proof of WeilConjectures.constantExtensionWeilHeartEquivalence,
keeping its statement and the already proved constantExtensionCyclicSheets unchanged.
The proof selects the existing local/weight return functor and transfers the equivalence
structure from sheetReturnExactFunctor by a proved natural Weil isomorphism. Four
proved private helpers identify functors satisfying the same sheet specification,
identify every sheet carrier, compare normalized pullback with return, and transport
the restriction specification across a natural Weil isomorphism. The existing
pullback-return and residue-compositum declarations supply exactness, the restriction
formula, the inverse-pullback comparison, and the residue-degree/cardinality formulas.

Added ConstantExtensionRestrictionLocalConjugacy for the remaining strictly narrower
local-power comparison. It does not assert an equivalence, exactness, a degree formula,
or a weight comparison. Its source and complete proof in words are in its docstring
and matching node. The unchanged theorem is assembled by real Lean proof steps from
this comparison and the existing stated dependencies.

Corrected the two reverse public imports in ConstantExtensionReturnData and
ConstantExtensionPullbackReturnResidue to the already existing definition owner,
ConstantExtensionWeilHeartData. This makes the stated dependencies importable by the
parent without a cycle. No declaration in either dependency changes. The change record
is coord/changes/E1-constant-extension-proof-imports.md. Unchanged return-module copies
are included for checking against the relocated data rather than stale compiled
parent exports; they contribute no source changes.

Validation: lcompile.py --all compiled all ten sandbox modules successfully, including
the main theorem, all four private helpers, both import-only adaptations, and the new
local-comparison statement. Both original theorem signatures and the complete
cyclic-sheet proof were compared with the shared source and are unchanged.

## Proved and sorry left

Closed the one original hole in
WeilConjectures.constantExtensionWeilHeartEquivalence
(lem-zl-constant-extension-weil-heart-equivalence), using the existing named dependencies
and one new local-comparison lemma. The item module now has zero sorry occurrences.
This is a decomposition, not a net hole closure: one original hole closed, one new hole
added. No axiom or hollow definition was added. The cyclic-sheet proof is preserved.

The new remaining hole is
WeilConjectures.constantExtensionRestrictionLocalConjugacy
(lem-zl-constant-extension-restriction-local-conjugacy), in its own module.

A concurrent delivery has already proved constantExtensionPullbackReturn by reduction to
WeilConjectures.constantExtensionRestriction_data
(lem-zl-constant-extension-pullback-restriction-data) and
WeilConjectures.constantExtensionRestriction_normalization
(lem-zl-constant-extension-pullback-normalization). This delivery preserves that proof
and both existing holes verbatim; only its module's import changes. The unchanged
compile-only copies also retain the existing sheetReturnExactFunctor,
sheetReturnTransportComparison, sheetReturnLocalSpectra, and
constantExtensionSheetGeometry holes with their existing nodes. These are existing
stated dependencies, not holes added by this delivery.

## No longer needed

No existing direct import was removed from the item; no module is withdrawn or globally
pruned. The direct plan requirements
lem-zl-constant-extension-sheet-heart-coordinates and
lem-zl-cyclic-return-exact-equivalence are now used through the already stated
lem-zl-sheet-return-exact-functor. Their modules remain needed transitively; no claim is
made that they can be deleted. The generic local-pullback theorem is now used through
the new local-comparison node. The two dependency modules no longer import the parent
assembly theorem; their data requirements come from ConstantExtensionWeilHeartData.

## Where the brief, the DAG or earlier work was wrong

H5's data relocation left two dependencies importing the parent theorem module:
ConstantExtensionReturnData and ConstantExtensionPullbackReturnResidue. Neither uses
either parent theorem. Replacing those imports with the data owner is necessary to
use the stated plan without a Lean import cycle. The prescribed downstream scans find
four users of ReturnData and no users of PullbackReturnResidue; no consumer refers to
the parent theorem names through these dependencies.

The DAG's last assembly step does not directly follow by applying
fdWeilPullbackLocalFrobenius: that theorem is stated for a bundled coefficient datum
with coefficient universe tied to the base universe, common-stage cohomology, and
compatible geometric lifts. The requested ConstantExtensionLocalConjugacy quantifies
over independent coefficient universes, arbitrary finite Weil presentations and both
residue embeddings, after changing the finite base-field datum. The new lemma isolates
precisely that presentation/scalar/conjugacy bridge, with the existing generic theorem
and sheet-return comparison as its mathematical inputs. All target signatures, base
models, coefficient categories, return maps, and unit routes are unchanged.

## New nodes

lem-zl-constant-extension-restriction-local-conjugacy records the local Frobenius power
of sheet return of actual pullback, for every functor satisfying the fixed sheet
specification. Its proof composes the generic pullback comparison with the sheet-return
operator comparison and then transports across presentations, scalar extension and
residue embeddings. Edge cases m=1, empty schemes and zero stalks are included. The
existing sfLocalFrobenius_model_conjugacy theorem supplies both presentation independence
and arbitrary residue embeddings; it is used as a generic tool, whose approval can be
recorded by the independent reader. The node makes
no new assertion about weights or the heart equivalence. Change record:
coord/changes/E1-constant-extension-proof-imports.md.

## Forced adaptations

### Sheaf.Paper.ConstantExtensionPullbackReturnResidue
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
