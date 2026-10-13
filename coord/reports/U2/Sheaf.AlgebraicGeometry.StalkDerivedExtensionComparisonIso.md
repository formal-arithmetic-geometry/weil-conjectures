## What changed

Repaired the saved attempt without changing any existing statement or public import.
`exists_stalkDerivedExtensionComparisonIso` now obtains a natural transformation
with the required K-flat equation, proves it invertible, and bundles it with `asIso`.
Two proof-only imports supply the construction and the proved invertibility lemma.
The inherited unused quantified proof-binder names are preserved; only this theorem
disables the unused-variable linter to avoid changing those names.

The new construction module `StalkDerivedExtensionComparisonIsoCore` states
`exists_stalkDerivedExtensionComparisonTransformation`, which requires the same
representative equation but asserts only a natural transformation, not an isomorphism.
The new module `StalkDerivedExtensionComparisonIsIso` proves
`stalkDerivedExtensionComparison_isIso`: any transformation satisfying that equation
is invertible. It uses the K-flat stalk criterion, the scalar-extension counit theorem,
and existing `nonempty_coordinates` to reduce every component to a K-flat representative.
The original node and the two new nodes record this route without circular dependencies.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.SingleComplexBaseChange.exists_stalkDerivedExtensionComparisonIso`
(node `lem-pc-stalk-derived-extension-comparison-intermediate`).

Also completely proved the new theorem
`AlgebraicGeometry.SingleComplexBaseChange.stalkDerivedExtensionComparison_isIso`
(node `lem-pc-stalk-derived-extension-comparison-is-iso`).

Added exactly one remaining hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_stalkDerivedExtensionComparisonTransformation`
(node `lem-pc-stalk-derived-extension-comparison-core`). Its proof is exactly
`:= by sorry`, in its own module, with the construction, descent argument and source
in its docstring. This is a decomposition: one original hole closed and one added;
it does not establish a decrease in the targets' closure hole count.

The remaining statement omits invertibility, which has been proved independently
from its equation. Thus it is strictly part of the original argument. No definitions,
target statements, axioms or existing signatures were changed.

## No longer needed

No original imports were removed; no existing DAG nodes or modules are claimed
pruned. Roof representation, common refinement and K-flat resolution remain needed
by the construction, and its node retains those dependencies. The original theorem
uses those steps through the construction module rather than directly.

In the saved, unsubmitted attempt, the two holes
`exists_stalkDerivedExtensionComparisonIsoCore` and
`stalkDerivedExtensionComparisonIsoFormula` have been replaced. Its old formula
module and unsubmitted formula node were removed: an arbitrary comparison
isomorphism does not satisfy a canonically specified equation.
The new invertibility proof needs no separate inverse-comparison construction
and no direct K-flat resolution import: `nonempty_coordinates` already supplies
both the representative and the invertible recorded pullback counit.

## Where the brief, the DAG or earlier work was wrong

The saved attempt asserted the equation for every comparison isomorphism. This is
false in general: even in an identity square over a field of characteristic other
than two, postcomposing a canonical comparison with minus the identity changes
its component on a nonzero single complex but leaves the right-hand side fixed.
The repaired statement constructs a transformation with the equation and proves
invertibility from that equation; it never claims every isomorphism is canonical.

The saved new nodes depended on the original theorem, making their proposed
reduction circular, and their Lean records contained prose instead of verbatim
signatures. Both issues are repaired. The unit's route is preserved; its realized
lists do not designate this node as a separate mandatory step to bypass.

Edge cases: zero complexes and zero stalk rings make both sides zero; the
invertibility proof still applies because the sole morphism of a zero object is
invertible. Identity morphisms and arbitrary universal derived pairs are handled
by the same counit and naturality argument. No base-flatness is assumed.

## New nodes

`lem-pc-stalk-derived-extension-comparison-core`, in
`dag/nodes/sec-picard-framework/lem-pc-stalk-derived-extension-comparison-core.json`,
states the existence of the natural comparison with the precise K-flat equation
and leaves only its construction and localization descent open.

`lem-pc-stalk-derived-extension-comparison-is-iso`, in
`dag/nodes/sec-picard-framework/lem-pc-stalk-derived-extension-comparison-is-iso.json`,
is completely proved from the representative equation and the existing K-flat
stalk, scalar-extension counit and coordinate results. It makes no choice of a
comparison and asserts no formula for an arbitrary isomorphism.

No change records or forced adaptations are needed.

## Second reading by U2

1. Compared the delivered existing module with the repository version. The theorem
   signature and visible imports are byte for byte unchanged; the added modules are
   proof dependencies and the new node records match their Lean declarations. Verdict: pass.
2. Compiled all three delivered Lean modules with `lcompile.py`. There is one `sorry`,
   exactly in the named construction theorem; no forbidden declarations or hollow
   definitions occur. The completed invertibility theorem uses only the permitted
   categorical and classical axioms (`propext`, `Classical.choice`, `Quot.sound`).
   The original theorem and the open construction theorem additionally use `sorryAx`,
   exactly as expected from that remaining hole. Verdict: pass.
3. Checked the split statements against the construction route and edge cases. The
   transformation statement is strictly weaker than the original isomorphism statement,
   and the isomorphism theorem derives invertibility from its displayed equation. Neither
   duplicates an existing library declaration. Independent Loogle search confirmed
   `NatIso.isIso_of_isIso_app`; LeanFinder and grep found generic derivability/Guitart
   exactness tools but no result supplying this stalk comparison and its equation.
   The zero and identity cases preserve the displayed equation. Verdict: pass.
4. Read the proofs and dependency imports. The invertibility proof follows the K-flat
   stalk criterion, scalar-extension counit, coordinates, and naturality; proof-only
   imports are plain imports. No unused original proof dependency was removed. Verdict: pass.
5. Checked the DAG node `proof`, `proof_deps`, `proof_origin`, unit, and realized route.
   The unit realized lists are empty and impose no separate step here; no unit route
   is bypassed. The new nodes contain verbatim Lean statements.
   Verdict: pass.

Changed only this report by recording the independent second reading; no Lean or DAG
repairs were necessary.
