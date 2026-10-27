## What changed

Completed `CategoryTheory.ringedExtendedCech_complete_implies_unit_isIso` in
`Sheaf.Paper.ExtendedCechCompleteImpliesUnitIso`, preserving its signature and
all three public imports. Added only proof imports and proved private helpers.
Updated its node's proof route to the ordered tensor induction implemented in Lean.

For one localization factor, the canonical degreewise split stupid-truncation
sequence has kernel isomorphic to the localization in degree one. The other
truncation maps isomorphically to the ring complex, compatibly with the specified
augmentation. Contravariant exactness of derived
internal Hom, its source-shift comparison, and the stipulated vanishing show that
precomposition by that factor's augmentation is invertible. Natural K-flat
currying combines two such augmentations, and induction handles the actual
ordered tensor defining extended Cech. This only requires vanishing for the
individual generators, rather than a separate product-localization filtration.
The specified local augmented isomorphism and the natural restriction comparison
transport that invertibility to the given augmentation. Homology and the sheaf
cover criterion descend it, and the canonical invertible evaluation-at-one map
converts it into invertibility of the actual completion unit.

The one-factor sequence uses the proved generic truncation API in
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.ComplementaryTrunc`. Its
concentrated kernel is identified by a canonical isomorphism constructed from
Mathlib's single-complex morphisms and the specified degree-one term isomorphism.
The proof reuses proved private constructions through `import all` from
`RingedCechCompletionUnitIdempotence` (factor/Cech/ring K-flatness and the
canonical derived Hom unit isomorphism). No declarations of that module change.
The homology-based cover-detection helper generalizes the proved private helper
in `ExtendedCechReflectorCore` to an abstract sheaf of rings and explicitly given
exact restriction functors; importing that parent here would create a cycle.
This abstraction avoids repeated expansion of the concrete coefficient sheaf.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.ringedExtendedCech_complete_implies_unit_isIso`
(node `lem-weil-pbc-extended-cech-complete-implies-unit-isIso`).
One original hole closed, zero holes added, zero split off, zero holes remaining
in the delivered module. All new private helpers have complete proofs.

## No longer needed

No original imports or declared proof dependencies were removed. No module or
node is withdrawn or claimed globally pruned. The planned separate argument
using the positive Cech filtration and every product localization is unnecessary:
the actual ordered tensor construction supports induction using vanishing at
each individual generator. Both original substantive dependencies, finite
ideal-generating covers and internal-Hom restriction, are still used.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no mathematical defect was found. The DAG's one
large proof step concealed the shorter tensor induction. The replacement uses
existing declarations and proved auxiliary constructions and introduces no
further obligation. The empty list is the identity augmentation, so the argument
also covers empty generating lists, zero rings, zero objects, and empty covering
families without additional hypotheses.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
