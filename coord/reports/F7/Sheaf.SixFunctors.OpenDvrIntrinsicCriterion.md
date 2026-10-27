## What changed

Proved `WeilConjectures.openDvrIntrinsicCriterion` without changing its signature.
The proof uses the existing integral Roos criterion and the two specified
Koszul reconstruction unit equations. Added
`Sheaf.SixFunctors.OpenDvrRoosCompletionComparison`, identifying quotient
completion with integral Roos completion by an isomorphism preserving the
actual units. Its proof assembles the existing augmented-tower comparison
with the normalized universal right-derived Roos comparison. The argument
never uses level projections to detect equality in a derived inverse limit.

The only existing module changed is the assigned item. Updated its node's
proof route and dependencies; added one node for the new comparison.
All additional imports are private proof imports in the item.

Verification: remote `lcompile.py --all` compiled both modules: 47.2 seconds
for the comparison and 16.3 seconds for the criterion. Development timing
options have been removed. `deliver3.py` performs the final clean compile
and preflight checks. Static checks confirm that the original theorem
signature is unchanged, the node dependencies match their proof steps,
and both files have no holes or lines longer than 100 characters.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.openDvrIntrinsicCriterion`
(node `lem-sf-open-dvr-intrinsic-criterion`).

The new theorem `WeilConjectures.openDvrRoosCompletionComparison`
(node `lem-sf-open-dvr-roos-completion-comparison`) is also proved.
There are no `sorry` declarations in either delivered module, and zero
new holes. This is a proof from existing project declarations, including
the already stated `openDvrAugmentedReductionComparison` still carrying
its own hole; that dependency is not part of this delivery.

## No longer needed

The item's proof does not directly use
`lem-sf-regular-roos-koszul-unit` / `Sheaf.SixFunctors.RegularRoosKoszulUnit`:
the already proved integral Roos criterion supplies the needed equivalence.
It does not directly use
`lem-weil-pbc-completed-constant-sheaf-reduction` /
`Sheaf.Paper.CompletedConstantSheafReduction`: the existing normalized
augmented-tower comparison supplies the coefficient reduction comparison.
These two old proof dependencies are removed from the item's node.
Their declarations and modules remain available and may still be reached
through other consumers; no library-wide withdrawal is claimed.

The original public import `Sheaf.SixFunctors.OpenQuotientKoszulModels`
is retained verbatim. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The original plan
required redoing the normalization between the generic regular-element
criterion and the completed integral coefficients. The existing integral
Roos criterion already performs that work. The replacement route keeps
the unit's coefficient-compatibility step and preserves the specified
completion units; it imposes no extra hypotheses on the scheme or complex.
The new comparison does not assume completeness or the generator equation.
The empty scheme and zero complex use the same formulas throughout.

## New nodes

`lem-sf-open-dvr-roos-completion-comparison` records the normalized
isomorphism from the completed-adic quotient completion of `C(P)` to
`C(IntegralOnSlice.completion(P))`. Its unit equation is established on a
flat-term K-flat representative using the single strict augmentation,
the right-derived universal property, and the defining integral Roos
unit normalization. Naturality transports it to every derived object.
This lemma concerns quotient completion alone and contains neither the
intrinsic Koszul unit nor a completeness predicate. It is proved, with
no split-off hole and no change record required.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
