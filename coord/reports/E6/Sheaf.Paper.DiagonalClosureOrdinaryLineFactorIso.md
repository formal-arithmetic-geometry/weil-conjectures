## What changed

Restored the assigned quarantined source of
`Sheaf.Paper.DiagonalClosureOrdinaryLineFactorIso` and replaced its only sorry
with a proof of `diagonalClosure_ordinaryLine_factor_isIso`, preserving its
signature and public import. Added proof imports for the rational root diagram
basis, normalized slice scalar extension, monoidal colimits and local detection
of sheaf isomorphisms. Two proved private helpers transport compatible linear
bases through colimits and retain their leg equations. Updated the item's node
to record the proof actually written.

Validation: the item compiled cleanly through `lcompile.py` in 14.4 seconds,
with no warnings. Both added Sheaf imports were checked for import cycles.
All added proof imports supply APIs used in the proof. Only the item's proof
and its own node route were changed; no consumer adaptation is needed.

On the compatible-root cover, the finite basis diagram gives a normalized linear
basis of the closure colimit. The scalar-extension basis and the colimit basis
identify the given map by comparing their values on one. Cover descent and the
conservative forgetful functor prove invertibility globally. This also treats
empty schemes and slices: all arguments are categorical universal properties;
no point, nonzero section, or nonempty cover is selected.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalClosure_ordinaryLine_factor_isIso`
(node `lem-diagonal-closure-ordinary-line-factor-iso`). Original holes: 1;
remaining holes in the item: 0; holes added: 0. Both private colimit helpers have
complete proofs. No decomposition or new node is introduced.

## No longer needed

The planned dependency `lem-sfb-regular-scalar-extension-multiplication`
(`Sheaf.CategoryTheory.RegularScalarExtensionMultiplication`) is not used or
imported: `spSliceNormalizedScalarExtensionBasis` gives the required normalized
basis on each slice directly. The colimit comparison is proved in the item.
No existing import was removed, no module is withdrawn, and no assertion is made
that the regular multiplication lemma has no other consumers.

## Where the brief, the DAG or earlier work was wrong

The source was initially absent from lean/ because coord/rework.tsv records its
quarantine following the false-tail import repair; its preserved source was used,
with its declaration and attachment intact. The old one-step plan omitted the
normalization needed to identify an arbitrary factor f with the local basis
comparison. The proof now retains the colimit-leg equations and compares on one
using regular-module hom extensionality. It does not assume arbitrary sections of
a sheaf tensor are pure tensors and introduces no extra hypotheses.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
