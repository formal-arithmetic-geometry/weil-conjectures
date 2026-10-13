## What changed

The existing theorem `AlgebraicGeometry.standardSingleFlatCounitPresentation_union_of_open_presentations` now assembles a bounded flat complex K, its base identification e, and the pullback identification t with the counit equation. Its signature and existing docstring are unchanged. The two new modules are proof-only imports of the item. Each helper publicly imports only the definitions its statement needs; its planned proof dependencies are plain imports.

The first worker's equation helper concluded the whole presentation predicate. The second reader replaced that restatement by existence of t and the factorization equation for the supplied K and e. The construction helper now uses Nonempty for the base isomorphism instead of an existential followed by True. Both helpers use the same standard derived categories as the presentation predicate. Their source docstrings now contain complete proof arguments, and the new-node Lean statement fields contain the actual signatures.

## Proved and sorry left

Closed: `AlgebraicGeometry.standardSingleFlatCounitPresentation_union_of_open_presentations` (the item's one original hole).

Added and still open:
- `AlgebraicGeometry.standardSingleFlatCounitUnionCore`, node `new-pc-standard-single-flat-counit-union-core`.
- `AlgebraicGeometry.standardSingleFlatCounitUnionEquation`, node `new-pc-standard-single-flat-counit-union-equation`.

This is a decomposition, not a completed proof: one upper hole closed, two strictly smaller lower holes added, net -1 for these declarations. The core supplies only a bounded flat base model; the equation supplies only its missing pullback identification and compatibility. No data definition or arbitrary witness chosen into a definition was added. Existing upstream holes remain; closure totals are determined by the maintainer's pinned sorry ledger.

## No longer needed

The item's old proof dependency `lem-pc-derived-mayer-vietoris-triangle` and its module `Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle` are no longer used by this route. Its quasi-coherent triangle statement requires compact opens, which the item does not assume. The lower general sheaf-module short exact presentation `lem-pc-kinjective-mayer-vietoris-presentation` supplies the needed cover argument instead. No actual import line was removed from the repository's item, which originally imported only the presentation definition.

The other old dependency, `lem-pc-flat-complex-derived-pullback`, is retained in the equation helper's plan and imported there. No claim is made that a module is globally unreachable: that is the maintainer's closure check.

## Where the brief, the DAG or earlier work was wrong

The first worker's equation lemma restated the target instead of supplying the claimed t and equation. The new-node statement records were prose rather than verbatim Lean signatures; the item's updated proof route was left in a root-level copy that deliver3.py does not deliver. These are corrected.

The original plan tried to lift a derived arrow between arbitrary flat complexes; flatness alone does not provide that lifting. The core proof now first bounds cohomology via the Mayer--Vietoris triangle and then applies the existing bounded-above flat replacement to a good truncation. This avoids assuming projectivity. The existing qcqs quasi-coherent Mayer--Vietoris refinement also requires compactness not present here; the general K-injective cover presentation does not, and the helper proof describes its use without that refinement.

## New nodes

`new-pc-standard-single-flat-counit-union-core` records just bounded-above flat representability of the union direct image, using the three local bounds, the general K-injective cover presentation, and bounded flat replacement (Stacks 08BV, 0DJ9, 077J).

`new-pc-standard-single-flat-counit-union-equation` fixes the complex and base isomorphism as inputs and records only the ordinary pullback identification and canonical equation. Its argument obtains invertibility of the union comparison through the two relative Mayer--Vietoris triangles and constructs t by composing the inverse of Lg*(e) followed by the pinned counit with that comparison.

No existing statement or definition changed; no change record is needed for the undelivered new helper corrections.

## Second reading by M2

1. Compared the item with the repository file using diff: the sole existing declaration's signature, visibility and docstring are byte-for-byte unchanged. The only item edits are two plain imports and its proof. The helper modules and nodes are new, and no definition changes are delivered. Verdict: unchanged public contract.
2. Read all three modules and checked the completed proof's witness assembly. Both remaining sorries are entire named public theorem proofs. There are no axiom, unsafe, opaque, extern, implemented_by declarations, no hidden sorry in data, and no arbitrary witness inserted into a definition. The local compile and declaration-axiom checks are recorded below. Verdict: valid reduction with explicitly open dependencies.
3. Read Stacks 0DJ9 (https://stacks.math.columbia.edu/tag/0DJ9), the general K-injective presentation, bounded flat replacement, flatComplexDerivedPullback, and the pinned counit's uniqueness argument in SingleComplexBaseChangeStalkCondition. Core is strictly base-model existence; equation now fixes that model and supplies only t and compatibility. Tested the mathematical zero-module, empty-open, equal-open and contained-open cases: the restriction-difference cover sequence still works; no disjointness, nonemptiness, or compactness is silently required. A change of e by an automorphism changes t by the inverse pulled-back automorphism, so the equation is required for every supplied e. Searches through msearch leanfinder, loogle and grep and through lean/ found bounded flat replacement and flat counit comparison but no existing exact gluing helper; these results narrowed the construction route. Verdict: true, strictly smaller statements, not duplicate target predicates.
4. The new proof uses the same K and e throughout; it genuinely combines the two parts. Checked the old dependency list and reported the unused compact-open triangle. The unit sk-thm-picard-coherence has realized.statement = [] and realized.steps = [[]]; this item realizes no recorded unit step, and no unit or chapter route was changed. Verdict: route preserved; decomposition honestly reported.
5. Updated the delivered parent node's proof and dependencies to the actual two-helper assembly. Each new node has a self-contained statement, source, stepwise proof, dependency union, provenance, three search kinds, split status, creation and blueprint records, chapter/unit, and a verbatim Lean declaration signature. Their steps use the general cover presentation rather than the too-restrictive qcqs triangle. Verdict: Lean and DAG agree.

Second reading changed the restating equation interface into fixed-model compatibility, removed the vacuous True witness, pinned derived-category instances, completed both proof docstrings, corrected the DAG route and exact signatures, and replaced the unneeded compact-open refinement in the helper plans.

Validation: all three delivered modules compile locally in import order without warnings. A scratch copy with #print axioms for the target and both helper declarations compiled; each reports only propext, Classical.choice, Quot.sound and sorryAx. The latter is expected from the two recorded helper holes and upstream open declarations. The scratch file was removed before delivery. Existing target signature comparison returned True.

Delivery dry run: deliver3.py --no-push returned OK, including compilation and preflight. Review class CODEX, because the delivery adds the two helper nodes and their modules.
