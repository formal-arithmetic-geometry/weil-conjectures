## What changed

Proved `CategoryTheory.Sheaf.zariski_torsor_representative_exists` with its signature and
public imports unchanged. Added the proof-only import
`Sheaf.CategoryTheory.Sites.ZariskiTorsorFreeExtension`. Its new module constructs the free
abelian relation pushout and proves short exactness, using the existing pair-difference
and pair-displacement maps of `WeilConjectures.CategoryTheory.Sites.Torsor`.
The original module proves naturality, degree one and equivariance of the generator map,
and applies the already proved `Torsor.Iso.ofHom` to obtain the required isomorphism.
Updated both DAG proofs to match this implementation of Stacks Tag 02FQ.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Sheaf.zariski_torsor_representative_exists`
(node `lem-sc-zariski-torsor-representative-exists`).
Also proved `CategoryTheory.Sheaf.Torsor.FreeExtension.shortExact`
(node `lem-sc-zariski-torsor-free-extension-short-exact`), its inclusion monomorphism,
projection epimorphism and all auxiliary lemmas. No sorry remains in either delivered
module; no hole was added or split off. This is a proof, not a decomposition.
Both modules compiled locally in import order without warnings. The delivery tool runs
its axiom probe as part of the dry run.

## No longer needed

No original import was removed, and no standalone module is claimed to become unreachable.
Removed `def-sc-topological-abelian-cohomology` from the original node's direct proof
dependencies: the proof uses abelian-category kernels and cokernels, without derived
cohomology, resolutions, enough injectives or contracted powers. This node remains in the
original statement dependencies, which were not changed. The enlarged-universe
`ZariskiContractedPowerExtension` route was neither imported nor used.
The new module needs only its two public imports, Torsor and Scheme, plus the proof-only
Mathlib.CategoryTheory.Abelian.CommSq import. Explicit imports of Spaces, Sites.Abelian,
and Pullback.HasPullback were removed after verifying they are already available.

## Where the brief, the DAG or earlier work was wrong

The original plan supplied definitions rather than theorem interfaces for its substantive
steps. The existing Torsor module already proves the pair-displacement kernel relation,
invariant-section gluing and the equivariant-map isomorphism criterion, which permit a
full proof rather than new holes. The relation pushout uses the free sheaf on pairs
instead of first choosing a map from the augmentation kernel; its proved cokernel property
shows this implements the same quotient. No statement, definition, unit realization or
existing visibility was changed.

Read the actual Stacks Tag 02FQ page, including its corrected sign convention
`g + x = y`; local literature payloads are absent on this machine.
The existing contracted-power extension has coefficients in universe u+1, so it does not
specialize to this item's universe u. No false or disputed statement was used.
Edge cases: empty schemes are covered by the sheafification and kernel/cokernel arguments;
no global section of T is assumed. With G zero, the relation quotient still gives the
integer sheaf. Local augmentation surjectivity uses arbitrary signed integers, including
zero and negative integers, and no connectedness or nonempty-space hypothesis appears.

## New nodes

`lem-sc-zariski-torsor-free-extension-short-exact` records the explicitly constructed
same-universe relation pushout and its fully proved short exactness, in
`lean/Sheaf/CategoryTheory/Sites/ZariskiTorsorFreeExtension.lean`. It is strictly the extension
part of the original argument; the generator-map and torsor-isomorphism part is proved in
the original module. All Mathlib searches were actually run and recorded in searches.jsonl;
LeanSearch returned Internal Server Error, recorded as unavailable. Blueprint searches for
"torsor free", "free abelian" and "torsor extension" found no exact canonical-presentation
statement. No change record or forced adaptation is required.


## Second reading by N1

1. Compared both delivered modules with the repository version. The target theorem signature,
existing declarations, and all public interfaces are unchanged; the added import is proof-only.
The new free-extension module is the declared split-off node and introduces its stated interface.
Verdict: pass.
2. Compiled both files in import order with `lcompile.py`; the files contain no `sorry`,
`axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC`. Axiom probes
for the target and `FreeExtension.shortExact` return only `propext`, `Classical.choice`, and
`Quot.sound`. Verdict: pass.
3. Checked the split-off short-exactness statement against its construction and the Stacks
02FQ argument. It is true, same-universe, and strictly the extension part of the target;
searches recorded in `searches.jsonl` found no existing declaration. Verdict: pass.
4. Read the proof top-down. It uses the existing torsor pair maps and `Torsor.Iso.ofHom`,
then the explicit relation pushout; no shorter available library route was found. The unit's
representative-extension route is retained, and no import or proof dependency is unnecessarily
left in the delivered modules. Verdict: pass.
5. Compared both DAG nodes with the Lean declarations and proof dependencies. The target node
points to `FreeExtension.shortExact` and the free-extension node records the construction and
its source; the unit realization remains unchanged. Verdict: pass.

Changed only the delivered proof modules, the target proof metadata, the new free-extension
node, and this report. No statement, definition, or unit route was changed.
