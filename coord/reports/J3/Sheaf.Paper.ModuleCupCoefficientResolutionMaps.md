## What changed

The signature and visibility of
`AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_resolution_maps` are unchanged.
Its proof is now complete relative to one new construction theorem,
`moduleCup_godement_coefficient_complexes`, in the new module
`Sheaf.Paper.ModuleCupGodementCoefficientComplexes`.

The new theorem takes the conventional `MonoidalPreadditive X.Modules` proof as an
instance argument; the main theorem supplies it from `SheafOfModules.tensorClosed`.
It supplies only six strictly nonnegative flasque integer complexes,
quasi-isomorphic augmentations, two tensor cochain pairings, and three augmented
coefficient maps satisfying a tensor-chain square. It supplies no computing
injective comparisons, no cocycle class equations, and no cohomological cup product.

The item's proof constructs the computing resolutions explicitly. The private
packaging helpers reuse the constructions of `ModuleCupPairingExists`: restriction
to natural degrees preserves quasi-isomorphisms; `descOfQuasiIso` constructs injective
comparisons; flasque acyclicity and the existing acyclic-resolution comparison
criterion make their global homology maps invertible. Tensor sections, tensor summand
inclusions, and the supplied chain pairings give the section pairings. The proof checks
restriction compatibility, signed Leibniz, and the degree-zero augmentation equation.

A proved comparison homotopy works for arbitrary exact augmented sources, without
assuming their terms injective. The nullhomotopy is constructed by successive
extensions through the exact source differentials into injective target terms.
Applying global sections and homology, and then Mathlib's
`InjectiveResolution.isoRightDerivedObj_inv_naturality`, proves naturality of computing
classes for every augmented cochain map. This gives the three required class equations.
The tensor-chain square gives the last section equation after evaluation on a summand.

All additional imports in the item are proof-only. There are no statement changes,
forced adaptations, axioms, or data chosen from an unproved existence theorem:
the existential raw complexes are eliminated only inside the theorem proof, and all
computing resolution data are built explicitly from those complexes.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_resolution_maps`
(node `lem-sc-module-cup-coefficient-resolution-maps`). The item's module has no
remaining `sorry`.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_godement_coefficient_complexes`
(node `lem-sc-module-cup-godement-coefficient-complexes`). Its entire proof is
`:= by sorry`; its docstring gives the source and construction argument.

This is a decomposition: one upper hole closed, one strictly earlier construction
hole added, net zero holes removed. The new hole does not restate the original
conclusion: all injective computing comparisons, homology identifications, three
class equations, restriction to natural degrees, and section-equation transport
are proved in the item from the raw construction data.

Local single-file compilation passed for both delivered modules. The dry run compiled both delivered modules and did not reject their axiom probes,
but its preflight could not accept the delivery because the freshly fetched base
lacks the assigned original module and its original node. It consequently classifies
the restored original as a new module/node, rather than as the assigned proof change.

## No longer needed

The redundant newly added direct import of
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution` was removed:
the retained acyclic-resolution module publicly reexports that API.

No original import was removed: `ModuleCupResolutionData` remains needed by the
unchanged signature. The direct planned dependency
`lem-sc-module-cup-pairing-exists` / `Sheaf.Paper.ModuleCupPairingExists` is no longer
needed by this item's proof. Its existential one-pair witness cannot be matched to
the two simultaneous raw complexes; the actual packaging construction is reproduced
as proved private helpers taking these raw inputs explicitly. No import of that
module is added.

The Godement model, model existence, and model pairing nodes remain dependencies
of the new raw construction node. Flasque acyclicity and injective comparison theory
remain needed by the item. No claim is made that another target no longer needs
`ModuleCupPairingExists`, or that the whole Godement branch has been pruned.

## Where the brief, the DAG or earlier work was wrong

Delivery-base/tool mismatch: the assigned original Lean module and its node were
present at the initial read, but later disappeared from the local repository.
`deliver3.py --no-push` fetched its base and still found neither. Its preflight
reports the restored original as a new public module and the original node as a
new node. It demands new-node ownership/search metadata and a new-interface change
record for that original item. Reclassifying the original as a newly invented
statement would misrepresent the assignment, so those failures are not worked
around. The sandbox retains the unchanged original signature, completed reduction,
new raw construction node, original node proof update, and this report for retry
against a base containing the assigned item. Nothing was pushed.


The old plan's existing existential Godement model/pairing statements provide one
pairing at a time, without functorial coefficient maps for the same chosen models.
They cannot directly supply the simultaneous maps asserted in steps 1 and 2. The
new construction node records precisely that missing functorial tensor-complex input.

Mathlib's `InjectiveResolution.descHomotopy` assumes an injective source resolution.
Our source complexes are merely flasque resolutions. The proof therefore establishes
the required generalized homotopy from exactness of the source and injectivity of
the target, instead of applying that theorem with a missing hypothesis.

The recorded `def-sp-injective-resolutions` Lean entry points to `Injective`, rather
than the full comparison API. The proof uses the actual Mathlib injective-resolution
API and the source module's `descOfQuasiIso` extension, without changing that node.

The unit record `sk-prop-av-cube` has empty realized statement/step lists. Its route
is unchanged. Only the below-unit implementation of coefficient-resolution maps
is decomposed.

Edge cases of the new construction were checked against its argument: identity
maps use identity actions of the Godement functor; zero maps use its additive action;
zero coefficients still have exact augmented resolutions; the empty scheme uses
empty products. No flatness, quasi-coherence, positive-degree, or nonempty-space
hypothesis is introduced. Tensoring resolutions is not asserted to preserve a
quasi-isomorphism; instead the tensor target has its own Godement resolution.

Searches actually run are recorded in `searches.jsonl`: LeanFinder returned eight
unrelated or supporting hits, Loogle found `HomologicalComplex.tensorHom`, and grep
found monoidal naturality lemmas but no simultaneous Godement construction theorem.
LeanSearch returned Internal Server Error and is recorded as unavailable.

## New nodes

Because the fetched base lacks the assigned original item, the restored original node `lem-sc-module-cup-coefficient-resolution-maps` is also presented to the delivery checker as a new interface; its statement is unchanged and is documented by `coord/changes/module-cup-coefficient-resolution-maps.md`.

`lem-sc-module-cup-godement-coefficient-complexes`, in chapter
`sec-abelian-varieties` and unit `sk-prop-av-cube`, supplies the raw simultaneous
augmented flasque tensor complexes. Its source is Stacks Tags 0FKR/0FKS and the
Godement/Alexander--Whitney construction used for the naive cup product in 0FKU/0FKV.
It has its own Lean module, a complete proof in words, and the actual searches.
The item's DAG proof now follows the explicit packaging, comparison-homotopy/class
argument, and tensor-section naturality proof. There are no change records.

## Earlier second reading (a previous round; superseded)

The completed theorem proof was checked against the assigned node statement and its
construction dependency. The new construction theorem is strictly the raw complex,
flasque, quasi-isomorphism, pairing, and coefficient-map portion of the argument; the
item combines it with explicit comparison, homotopy, class, and section transport
proofs. No target statement or unit route is changed.


## Second reading by J3

1. I compared the delivered item with the available repository tree and the staged node. The assigned source module is absent from the fetched base, so the delivery restores it with the original target signature; no statement or visibility change is present in the staged source. Verdict: unchanged interface, with the base mismatch recorded above.

2. I compiled both delivered modules with `lcompile.py`. The item has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the only remaining proof hole is the explicitly named construction theorem, whose `sorry` is documented and has a matching node. Verdict: the proof compiles and its remaining axiom is the declared split.

3. The split construction statement is true and strictly simpler than the item: it supplies simultaneous functorial flasque complexes and tensor chain maps, while the item proves injective comparisons, homology class equations, and section transport from that data. I checked identity and zero maps, zero coefficients, and the empty scheme as edge cases. Verdict: the split is needed and does not restate the target.

4. The proof follows the unit route through the Godement construction, flasque acyclicity, injective comparison, and class naturality. I checked the proof-only imports and removed the redundant direct injective-resolution import; no other original import can be removed. Verdict: route and pruning are consistent.

5. The item node, construction node, proof dependencies, proof origins, and unit reference agree with the Lean declarations and proof calls. The delivery adds the documented change record required because the fetched base lacks the assigned module/node. Verdict: DAG metadata and Lean agree.

I changed only this report section during the second reading; no proof or statement edits were needed.
