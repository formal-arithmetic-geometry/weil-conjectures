## What changed

Replaced the first worker's invalid Cartesian-existence/reconstruction split with a real
reduction. `AlgebraicGeometry.fpqc_affine_model_transition` retains its existing signature
and docstring byte for byte. Its proof base-changes the fpqc singleton twice, makes `r U`
an effective epimorphism using fpqc subcanonicity, constructs `t` with `EffectiveEpi.desc`,
proves reconstruction with `EffectiveEpi.fac`, and proves its structural equation by epi
cancellation. It then applies the residual Cartesian verification.

The new reconstruction module now proves the overlap equation for `c_i ≫ r B`, retaining
all actual transport compatibility, Cartesian, and invariance hypotheses. The new Cartesian
module now states only that an already reconstructed transition is Cartesian, with a source
and full proof in words. The two imports of new modules are plain proof imports. The
unneeded public Fpqc import was removed from the overlap module. The original module's
plain `FpqcMorphismsDescend` import moves to the residual Cartesian module, where it is the
planned descent input. No existing interface or target meaning changes.

## Proved and sorry left

Closed existing hole: `AlgebraicGeometry.fpqc_affine_model_transition`
(node `lem-galois-fpqc-affine-model-transitions`). Its body is complete, but its axioms still
include `sorryAx` from the residual Cartesian theorem.

Proved new declaration: `AlgebraicGeometry.fpqc_affine_model_transition_reconstruction`
(node `lem-galois-fpqc-affine-model-transition-reconstruction`), the overlap equation;
its axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

Added hole: `AlgebraicGeometry.fpqc_affine_model_transition_cartesian`
(node `lem-galois-fpqc-affine-model-transition-cartesian`). This is the only `sorry` in the
three delivered files, a named theorem with its source and complete docstring proof.

This is a decomposition, not a completed proof of the original item: one old hole closed
and one new hole added (net zero). Compared with the first worker's attempted delivery,
the false overlap/reconstruction hole is replaced by a proved true overlap equation.
There is no choice of arbitrary data from an unproved theorem: `t` is constructed by
`EffectiveEpi.desc`, whose existence and uniqueness are already proved in Mathlib.

## No longer needed

Removed direct import: `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend` from the item;
it remains a proof dependency/import of the residual Cartesian lemma. No module is
claimed pruned from the full targets' closure.

Old direct proof dependencies no longer used directly by the item:
`def-pd-descent-datum` and `lem-galois-fpqc-morphisms-descend`; both remain dependencies
of the auxiliary lemmas. The other old dependencies `def-pc-fibre-product` and
`def-weil-pbc-fpqc-covering` are retained. New direct dependencies include the two
auxiliary nodes, covering base change and representable fpqc descent.

## Where the brief, the DAG or earlier work was wrong

The first worker replaced actual hypotheses by arbitrary unused `Prop` parameters,
passing `True`. Its reconstruction theorem asserted reconstruction for every Cartesian
map, even without the Cartesian hypotheses on r. This is false: take f the identity,
U=B, V and W a scheme with a nonidentity automorphism, and r the identity; a nonidentity
automorphism t gives a Cartesian square but does not reconstruct r. Its Cartesian
existence statement also dropped the necessary compatibility/invariance restrictions.
Both new nodes depended on the original theorem, creating a circular decomposition.
They had no searches, no self-contained statements, no verbatim Lean signatures, and
no complete docstring proofs; the existing item's proof plan was not updated.

All of these faults are repaired. The local Stacks tex is absent on this machine, so
sources were checked at [Tag 02W3](https://stacks.math.columbia.edu/tag/02W3) and
[Tag 02W0](https://stacks.math.columbia.edu/tag/02W0). The former compares nested affine
models using full faithfulness; the latter supplies that full faithfulness. Searches via
leanfinder, loogle and grep found generic pullback APIs and no exact lemma for these
obligations; LeanSearch returned Internal Server Error and is recorded as unavailable.
The searches are logged in the sandbox's `searches.jsonl`.

## New nodes

`lem-galois-fpqc-affine-model-transition-reconstruction`: the true, proved overlap equation.
Compatibility with D and invariance identify transport of g with h through the U-model
pullback, then compare their B-model images by mono cancellation. Its statement needs no
fpqc hypothesis. A private congruence helper handles dependent transport endpoint types.

`lem-galois-fpqc-affine-model-transition-cartesian`: the remaining Cartesian verification,
assuming a map over the inclusion and the reconstruction equation. Its proof descends
an inverse to the induced comparison with `W B ×_B U` using fpqc full faithfulness.
This is a strictly smaller obligation than constructing a compatible Cartesian transition.
No change record is necessary: the first worker's auxiliary declarations were new and
unlanded; every declaration that exists in the repository retains its signature.

## Second reading by W2

1. Compared the item with the repository using diff and exact signature extraction.
   Verdict: existing declaration signatures and docstring unchanged; only proof, local
   elaboration options and plain proof imports changed. There are no definitions to alter.
2. Compiled all three files locally in import order using lcompile.py: no errors or
   warnings. Searched for forbidden declarations and holes. The only hole is the named
   Cartesian theorem. Scratch `#print axioms` confirms the overlap lemma uses only the
   three allowed axioms and the original theorem uses those plus `sorryAx` from Cartesian.
3. Rejected both first-worker auxiliary statements. Retested their replacements: the
   identity-inclusion case requires t to reconstruct r; an empty open gives empty source
   models by their Cartesian squares; no affine-intersection or nonemptiness assumption
   enters. The overlap lemma is kernel-checked; the Cartesian lemma follows by descending
   the inverse of the base-changed comparison. Read the full existing descent theorem and
   searched with different phrases and type patterns before keeping this residual lemma.
4. The original proof now actually constructs the transition by representable descent.
   Only Cartesian verification is split off. Checked dag/units/sk-prop-h2.json: this node
   is not a realized unit statement or step, and no realized route is removed or modified.
   The No longer needed section names all old direct dependencies omitted from the new
   proof, including those that remain transitively necessary.
5. Rewrote both new nodes with self-contained statements, verbatim Lean signatures, actual
   searches, source locations, complete proof steps, creation and blueprint fields. Updated
   the existing item's proof, proof_deps and proof_origin to follow its actual Lean body.
   Removed the circular edges from auxiliaries to the item. Verdict: DAG and Lean agree.

Second reading changed: rejected the false split, proved the overlap lemma, constructed
the descended transition and reconstruction, corrected the remaining Cartesian statement,
repaired all node metadata and proof dependencies, and made the accounting a decomposition.
