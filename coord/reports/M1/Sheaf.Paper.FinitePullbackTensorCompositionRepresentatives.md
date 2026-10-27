## What changed

The unchanged statement of
`WeilConjectures.finitePullbackTensor_composition_representatives` is reduced to the
ordinary signed total-tensor composition calculation. Its proof pastes the three
single-pullback representative squares, identifies the actual intrinsic derived
compositor with its ordinary representative coordinates, uses naturality of the
specified tensor-model comparisons, and cancels the computation isomorphisms.

The new module `Sheaf.Paper.FinitePullbackTensorRepresentativeData` packages the existing
coordinate maps. One total-tensor functor supplies both objects and maps, and large
comparison definitions have an explicit interface to avoid expensive unfolding.
`Sheaf.Paper.FinitePullbackTensorRepresentativeSquare` proves the
single-pullback square directly from `proEtaleCanonicalTensorPullback`. The proof
explicitly transports through all five factors of `finitePullbackTensorConstruction`.
The auxiliary definitions are compositions or specializations of existing functors
and maps. They introduce no chosen object, alternative tensor, or alternative pullback.
The ordinary compositor is the conjugation of the prescribed intrinsic compositor by
the three unique unit-normalized finite realization comparisons.

The proved `Sheaf.Paper.FinitePullbackTensorCompositorFactors` supplies the exact-derived
compositor equation used in the reduction. Its generic categorical helpers are private
and proved. The complex pullback and large comparison definitions have explicit types
and are kept folded in consumers, so checking coherence does not expand their objects.

The new module `Sheaf.Paper.FinitePullbackTensorChainComposition` states the remaining
identity between ordinary chain maps for arbitrary complexes. It contains no derived
category, tensor-model comparison, or flatness restriction in its theorem. This is
Step 2 of the original plan followed by totalization. The other parts of the original
plan are carried out by the proved Lean glue in this delivery. Generic square-pasting
helpers are private proved specializations of the categorical calculations in
`FiniteTensorComparisonProofSupport`; that larger presentation is not imported.

Only the item, four new modules, and their five node records are changed.
No existing definition, signature, instance, attribute, or public import changes.

Validation: all five modules compile through lcompile.py within 60 seconds each
(Data 55.5 s, ChainComposition 45.2 s, CompositorFactors 11.6 s,
RepresentativeSquare 23.3 s, item 51.6 s). The original theorem signature is
verbatim unchanged; every new node dependency list agrees with its proof steps.

## Proved and sorry left

Closed in the item:
`WeilConjectures.finitePullbackTensor_composition_representatives`
(node `lem-pur-finite-pullback-tensor-composition-representatives`).

New proved theorems:
`WeilConjectures.FinitePullbackTensorRep.compositor_fac`
(node `lem-pur-finite-pullback-tensor-compositor-factors`), and
`WeilConjectures.FinitePullbackTensorRep.square`
(node `lem-pur-finite-pullback-tensor-representative-square`).

One new hole remains, and it is the entire proof of:
`WeilConjectures.FinitePullbackTensorRep.chain_composition`
(node `lem-pur-finite-pullback-tensor-chain-composition`).

Thus the item's original one hole is closed by decomposition, with one strictly
earlier chain-level hole added. This is a decomposition, not a net hole-closing proof.
There are zero direct holes in the item, the coordinate-data module, the compositor
factor module, and the representative-square module, and
one direct hole in the chain-composition module. Existing imported holes are unchanged.

## No longer needed

No existing import is removed and no whole module is claimed pruned. The original
ordinary total-tensor and intrinsic pullback dependencies remain needed in the
chain-composition calculation. The general independent-universe ringed-topos theorem
need not be imported separately: its published small-pro-etale representative square
is already available through the construction layer. The separate
`FiniteDerivedComparisonNormalization` / `CochainPullback.CompositePresentation` route
is not used; it would require identifying a different generalized-element-normalized
comparison with the specified finite one. No nodes of the unit's own route are bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The listed dependencies give the canonical
comparison, its representative square and the definitions of the compositor. They do
not directly state the composition equation for the specified finite chain comparison.
That ordinary calculation is now isolated explicitly, rather than leaving the entire
localization and realization transport under a single sorry.

The remaining chain identity was checked on zero complexes, degree-zero complexes,
empty schemes, identity morphisms, and arbitrary unbounded degrees: it reduces to the
ordinary unit-section formula and introduces no sign or boundedness hypothesis.
For the representative square, every preservation witness comes from the existing
canonical theorem, rather than assuming that an arbitrary complex stays K-flat.

## New nodes

`def-pur-finite-pullback-tensor-representative-data` records the concrete coordinate
API in its own module. This separation keeps both that API and the proved square
within the per-file compilation limit. It introduces no hole or new choice.

`lem-pur-finite-pullback-tensor-representative-square` records the proved single-pullback
normalization using the ordinary-coordinate API. Its source is Stacks 07A4, with the
existing uniquely unit-normalized realizations from 00YV. The proof is the canonical
representative square followed by explicit naturality and inverse cancellations.

`lem-pur-finite-pullback-tensor-compositor-factors` records the proved exact-derived
computation equation. Its source is exact termwise localization and adjunction
composition; the Lean proof uses the existing exact-derived coherence API.

`lem-pur-finite-pullback-tensor-chain-composition` records the remaining ordinary
chain-map equality. Its docstring and node describe the unit-section calculation,
adjunction/tensor extensionality, and equality after all total coproduct injections.
It is strictly a part of the original proof: it does not mention the finite derived
tensor or its representative realizations, and the localization/transport argument
combining it with the single-pullback squares is fully written in the item.

No change record is needed: only new declarations and proofs of the assigned item
are added, with every existing public interface retained.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
