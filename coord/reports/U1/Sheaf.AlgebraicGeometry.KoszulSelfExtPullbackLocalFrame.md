## What changed

Reduced `AlgebraicGeometry.koszulRegularImmersion_self_ext_pullback_local_frame`
without changing its signature, visibility, universes or public imports. Its proof
obtains the quotient-module frame on U and applies the proved tensor descent
comparison.

Added `Sheaf.AlgebraicGeometry.KoszulSelfExtQuotientFrame` for the affine
zero-differential Hom calculation before tensor pullback. This is strictly a part
of the original argument: its conclusion concerns G over U on Y and contains no
pullback or free structure module on Z.

Added `Sheaf.AlgebraicGeometry.ClosedImmersionQuotientFramePullback`, with a
complete proof. It is independent of Koszul regularity, derived categories and
cohomology. The proof uses the invertible closed-immersion counit, preservation
of coproducts, canonical pullback composition, and the over-site equivalence.
The private restriction comparison is proved by uniqueness of left adjoints.
No definition or existing interface changed; no forced adaptations are needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.koszulRegularImmersion_self_ext_pullback_local_frame`
(node `lem-sc-koszul-self-ext-pullback-local-frame`). This is a decomposition,
not completion of the affine Koszul calculation.

Also proved the new theorem
`AlgebraicGeometry.closedImmersion_quotient_frame_pullback`
(node `lem-u1-closed-immersion-quotient-frame-pullback`) and its private
`tensorPullbackRestrictIso` comparison.

One hole is added and left:
`AlgebraicGeometry.koszul_self_ext_quotient_frame`
(node `lem-u1-koszul-self-ext-quotient-frame`). Its proof is exactly `by sorry`.
No sorry remains in the assigned module or the tensor-descent module. Original
holes closed: 1; new holes added: 1; net reduction: 0.

Edge cases: n=0 gives the empty wedge and one quotient summand; n>m gives an
empty coproduct and zero self Ext; m=0 resolves A/(0); a zero quotient gives zero
modules. The tensor theorem covers any J, including empty J, and any open,
including an empty inverse-image chart. All constructions in its proof are
categorical isomorphisms and require no rank, finiteness or nonemptiness.

## No longer needed

Removed these direct proof imports from the assigned module, moving them into
`KoszulSelfExtQuotientFrame`, where the remaining chart argument needs them:

- `Sheaf.RingTheory.KoszulProjectiveResolution`
- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`

Their nodes (`new-j3-koszul-projective-resolution`,
`lem-sc-affine-quotient-resolution-sheafification`,
`lem-sc-derived-internal-hom-restrict-open`,
`lem-sc-derived-hom-finite-free-model`) remain needed by the new quotient-frame
node. No module is globally pruned. No existing public import was removed. In the new quotient-frame module, the
second reader removed the unused public TensorPullback import and replaced the
public ExteriorPower.Basis import with public Data.Set.PowersetCard plus a private
ExteriorPower.Basis proof import. Searches found
that the self Ext exterior and stalk-basis modules depend on this item, so they
cannot serve as a shortcut.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The dry run requires a
LeanSearch search record beyond the three searches named in the machine brief;
LeanSearch was run for each new node and returned an internal-server error,
recorded as unavailable. The original node treated
tensor descent and over-site transport as one elementary final step without a
reusable declaration. The delivery supplies and proves that step. The affine
chart computation is still a larger remaining obligation; its existing resolution
and derived Hom interfaces do not directly state the zero-differential quotient
frame. The retained natural-language proof specifies that computation and its
localization and derived-universe comparisons.

Checked `dag/units/sk-thm-picard-duality.json`: this item is not itself a realized
unit statement or step. The split preserves the original affine Koszul route.
The already-proved closed-immersion full-faithfulness node is used as a tool;
it supplies precisely the counit isomorphism, rather than a new hypothesis.

## New nodes

`lem-u1-koszul-self-ext-quotient-frame`: the quotient-valued affine self Ext frame
on Y before tensor pullback. Its separate module has the only new sorry, the
source and complete proof sketch, and the original four proof dependencies.

`lem-u1-closed-immersion-quotient-frame-pullback`: the proved general transport of
a quotient-module frame across ordinary tensor pullback. It has no derived or
regularity assumptions. Its proof dependencies record the closed-immersion
counit theorem, module pullback and module sheaves. No change record is needed.

## Second reading by U1

1. **Interfaces: pass.** Diffed the assigned module against the repository and
   compared the original theorem signature byte for byte: identical. All original
   docstrings, definitions, universes and public imports are unchanged. The other
   two modules are new, with no existing declarations altered. No change record
   or forced adaptation is needed.
2. **Proofs: pass.** Compiled all three modules with lcompile.py, without errors
   or warnings. Inspected every proof and construction: the sole sorry is the
   whole proof of koszul_self_ext_quotient_frame, a public named theorem with its
   source, natural-language proof and node. No hollow definition or forbidden
   axiom, unsafe, opaque, implemented_by or extern occurs. The private restriction
   isomorphism uses the proved uniqueness of left adjoints; it chooses no
   arbitrary witness from a holed existence assertion. Checked axioms in scratch
   copies for both public proved declarations, the open quotient-frame theorem,
   and the private restriction comparison (results below).
3. **Split statements: pass.** Read Stacks Tags
   [0BQY](https://stacks.math.columbia.edu/tag/0BQY) and
   [08KS](https://stacks.math.columbia.edu/tag/08KS), and all four original
   dependency interfaces. The open theorem is the zero-differential affine Hom
   computation on Y before tensor pullback, strictly a part of the original
   argument. The separate proved transport theorem requires neither regularity
   nor derived Hom and supplies the remaining step. Checked n=0 (one quotient
   summand), n>m (zero summands), m=0 (the identity quotient), zero quotient,
   empty opens and empty indexing types. These require no added hypothesis.
   Independently searched LeanFinder for cohomology of Hom from a Koszul
   resolution into its quotient, Loogle for the coproduct preservation
   isomorphism, Mathlib for quotient frames and counit isomorphisms, and both
   Lean library roots for self Ext and quotient frames. No existing independent
   quotient-frame theorem was found. The nearby exterior and stalk comparisons
   depend on this item. Closing the remaining affine sheaf/derived comparison
   is substantial work, not a small omitted lemma.
4. **Route and pruning: pass.** The main proof opens the original hole, obtains
   the quotient frame, then applies the proved transport theorem. Its four old
   direct proof dependencies are all named under No longer needed and retained
   for the unresolved affine computation. No module is globally pruned. Checked
   sk-thm-picard-duality.realized: this item is not a realized unit statement or
   step; the original affine Koszul route is preserved. Public imports of the
   existing module remain intact. Removed an unused public TensorPullback import
   from the new quotient-frame module; its exterior-basis import is now private,
   with the actual subset-index definition imported publicly instead.
5. **Nodes: pass.** Compared all three node Lean statements with their source
   signatures and checked that proof_deps is exactly the union of proof-step
   uses. The original node changes only proof, proof_deps and proof_origin.
   New nodes supply chapter, unit, source, proof, origin, recorded searches,
   status, creation metadata, blueprint ancestry and Lean records. Their proofs
   match the actual reduction and categorical transport construction.

Second-reading changes: import cleanup in KoszulSelfExtQuotientFrame and this
review report. No statement, definition, proof body or hole count changed.

Axiom probes: closedImmersion_quotient_frame_pullback and the private
tensorPullbackRestrictIso use only propext, Classical.choice and Quot.sound.
The original local-frame theorem and koszul_self_ext_quotient_frame additionally
use sorryAx, exactly from the one documented affine calculation still open.
Scratch copies are kept outside the delivered lean directory.
