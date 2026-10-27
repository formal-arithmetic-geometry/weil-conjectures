## What changed

Decomposed `Profinite.DiscreteLattice.CubicalMultiplication.lattice_cubical_multiplication_roof`
into three strict mathematical steps: normalized map construction, the multiplication/unit
numerator calculation, and the augmentation denominator/K-flat tensor calculation.
The parent proves the assembly, including localization cancellation in an arbitrary category,
the triangular-number sign identity, rank-zero and rank-one Koszul product coordinates, and the
two-term singleton diagonal. It derives the second supported coefficient from the chain-map
numerator equality rather than adding another hole for it.

To make the three proof steps importable without a cycle, relocated the original definitions,
instance aliases and coordinate constructions verbatim to the new public data module. All
existing names are reexported by the item with their original types and bodies. Added only two
Prop-valued abbreviations for the exact normalization and tensor clauses. See
`coord/changes/H2-lattice-cubical-roof-proof-components.md`.

Validation: all five delivered modules compile separately through `lcompile.py`. The shared
data module took 35.5 seconds, the three split statements took 5.7, 13.9 and 7.2 seconds,
and the completed parent took 36.3 seconds with no diagnostics. All files meet the 100-character
line limit. A source comparison confirms that every original declaration signature and every
original non-theorem body is preserved verbatim across the relocation. There are no direct
existing Lean importers requiring adaptation.

## Proved and sorry left

One original hole is reduced: the parent declaration
`Profinite.DiscreteLattice.CubicalMultiplication.lattice_cubical_multiplication_roof`
contains a complete combining proof, conditional on the following three new statements.
This is a decomposition, not a net reduction in holes and not a sorry-free proof of the item.

The three new holes, each exactly `:= by sorry`, are:

- `Profinite.DiscreteLattice.CubicalMultiplication.exists_normalized_roof` in
  `Sheaf.CategoryTheory.LatticeCubicalNormalizedRoof`.
- `Profinite.DiscreteLattice.CubicalMultiplication.normalized_roof_numerators` in
  `Sheaf.CategoryTheory.LatticeCubicalNumeratorComparison`.
- `Profinite.DiscreteLattice.CubicalMultiplication.normalized_roof_tensor_representatives` in
  `Sheaf.CategoryTheory.LatticeCubicalTensorRepresentatives`.

No definition contains a hole or chooses arbitrary data from an unproved existence theorem.
The normalized construction theorem pins its maps on the coproduct/tensor generators, and its
witness is eliminated only inside the parent theorem proof. Existing imported input theorems
remain untouched. Holes closed: 1; holes added: 3; net: -2; split off: 3.

## No longer needed

No mathematical node or module is pruned. The original three public input imports move with the
unchanged definitions to the public data module and remain publicly visible through the item.
The node's original six-step route is retained: the three strict statements realize construction,
finite numerator comparison, and homological tensor comparison. Localization cancellation,
signs, second coefficients and low-rank normalization are proved in the parent. The current
unit's statement and proof route are unchanged. No upstream source declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The stage-2 augmentation-evaluation theorem chooses its own cubical model; the item quantifies
over every cubical model. Its construction step therefore also needs transport along the unique
cell-preserving isomorphism of the recorded coproduct complexes. This is explicit in the new
construction theorem's proof plan and docstring. Likewise the derived lemma must assume the
roof normalization; the bare `Roof` structure does not impose any augmentation or diagonal laws.
The delivered homological statement includes that hypothesis.

Searched Mathlib using LeanFinder, LeanSearch, Loogle and grep, and searched both project roots.
The results contain augmentation constructions, total differential identities and general
isomorphism cancellation, but no internal cubical/Koszul multiplication comparison. The generic
cancellation is implemented directly using Mathlib's isomorphism API. The search records and
actual results are retained in each new node. The current blueprint is read through
`literature/blueprint/latest/`; its paragraph (3) supplies the direct-image route, while the
specific lattice calculation is the existing agent-written DAG expansion.

## New nodes

- `def-sfb-lattice-cubical-multiplication-data`: the relocated constructions and the exact
  normalization/tensor predicates; no holes.
- `lem-sfb-lattice-cubical-normalized-roof`: normalized augmentation, diagonal and evaluation;
  excludes multiplication compatibility, denominator quasi-isomorphisms and localization.
- `lem-sfb-lattice-cubical-numerator-comparison`: multiplication/unit numerators for an already
  normalized roof, plus the first coefficient formula; asserts no roof existence or localization.
- `lem-sfb-lattice-cubical-tensor-representatives`: the common denominator, its quasi-isomorphisms
  and K-flat tensor words; excludes multiplication and the localized evaluation roof equality.

These are distinct genuine steps of the existing proof, strictly smaller than the item.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
