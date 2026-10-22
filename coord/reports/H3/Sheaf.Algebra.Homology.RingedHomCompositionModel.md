## What changed

Constructed sign-free Hom-complex composition by the existing chain tensor–Hom
adjunction. Evaluation is inverse transposition of the identity; composition
transposes the associator followed by two evaluations. Proved the component
formula on homogeneous pure tensors, including restriction to arbitrary slice
objects, and uniqueness by tensor summands and Hom-product projections.

For the derived comparison, normalized uncurrying against the fixed augmentation
identifies the chain and derived pairings. A triple-pairing comparison handles
K-flat inputs, and auxiliary K-flat resolutions plus source naturality give the
stated one-K-flat model. Public signatures, public imports and definition bodies
are unchanged. The existing proof of derived naturality is preserved.

Private proof imports expose the existing chain adjunction, tensor constraints,
generator calculus and sheafification universal property. Updated the item's
proof plan and proof dependencies to this route. The private
proof setup and unchanged consumer are recorded in
coord/changes/ringed-hom-composition-private-model.md.

Validation: the full item and its unchanged direct consumer
Sheaf.Paper.RingedPullbackHomEvaluationComparison compiled together through
lcompile.py --all without errors or warnings (59.3 s and 29.9 s). The consumer
copy was used for compatibility checking only and is not part of the delivery.
All seven public signatures, all four public definition bodies and all public
imports were compared against the repository and remain verbatim. Every Lean
line is at most 100 characters.

## Proved and sorry left

Closed both original holes, from the existing declared adjunction and model APIs:

- CategoryTheory.ringedHomComposition_existsUnique
- CategoryTheory.ringedHomComposition_model

Closed: 2 of 2. Added: 0. No sorry remains in the item, and no statement was split
off. The existing proof of CategoryTheory.ringedHomComposition_naturality remains
unchanged. All new private lemmas are proved; there are no new nodes.

## No longer needed

The new comparison argument does not use the separate Hom quasi-isomorphism
invariance node lem-pur-rhom-well-defined: it uses normalized uncurrying and
source naturality of the fixed representative map. Its proof import
WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap can therefore be removed.
This is pruning of this item's proof dependency only; no existing source-library
declaration or module is withdrawn. The blueprint unit and its route are
unchanged.

The direct proof imports Sheaf.Algebra.Homology.RingedDerivedTensorNative and
Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses were also removed:
the retained adjunction import supplies their APIs transitively. Their modules
and nodes remain dependencies; this removes redundant direct imports only.

## Where the brief, the DAG or earlier work was wrong

The planned direct differential construction is valid but unnecessary: the
already available chain adjunction produces a chain map and its homogeneous
formula immediately supplies the desired characterization. The derived
comparison can also be proved without inverting Hom representative maps, so
separate Hom quasi-isomorphism invariance is unnecessary for this proof.

No statement dispute, public-interface repair, forced consumer adaptation, or
new DAG node is proposed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
