## What changed

Completed `lean/Sheaf/Paper/EtaleCETotalizeAugmentedComparison.lean`, preserving the
signature and docstring of `AlgebraicGeometry.Etale.etaleCE_totalize_augmented_comparison`.
Invert `Functor.cartanEilenberg_mapped_total_iso`, extend the supplied bicomplex map,
flip, and totalize. The total-map inclusion formula proves the required summand equations;
resolution degree zero and the supplied augmentation equation prove the strict square.

The private, fully proved helper `etaleCE_filtration_restrictions` uses those summand
equations. Naturality of `ceSectionsUnit` and the two `totalSectionsIso_formula` equations
show that the conjugated sections lift preserves each diagonal generating image. A private
finite-supremum factorization proof (the argument already used privately in
`Sheaf.CategoryTheory.DoubleComplexTotal`) combines the generators using pullback and
`Finset.sup_le`. Convert the resulting image-subobject factorizations to factors through
the actual degree components of the target subcomplex. Monicity and the chain-map equations
prove that these components form a chain map. Empty intervals and negative total degrees
are covered by the same finite-supremum argument; no first-quadrant assumption on the
complex degree is added.

Added proof-only import
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap` for the extension-map
component equation. No definitions, existing public signatures, or public imports changed.
The proof follows all three steps of the existing node, with the same proof dependencies;
there is no new route or unproved intermediate statement requiring a node change.

Validation: the launcher single-file compile succeeded without warnings (about 20 seconds).
The delivery dry run checks the signatures, import cycle, and axioms of all declarations.
The source places were read at [Stacks 015J](https://stacks.math.columbia.edu/tag/015J)
and [Stacks 015K](https://stacks.math.columbia.edu/tag/015K), because the local literature
checkout does not contain `derived.tex`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.etaleCE_totalize_augmented_comparison`
(node `lem-weil-pbc-ce-totalize-augmented-comparison`).

No `sorry` remains in the delivered module, and no holes are added elsewhere. Both
private helpers are proved. This is a proof, not a decomposition into new holed statements.

## No longer needed

Removed the redundant direct proof import `Sheaf.CategoryTheory.CartanEilenbergMappedTotal`:
`Sheaf.Paper.EtaleCETotalSections` already publicly imports it. Its declaration is still
used, so its module and node `lem-sp-cartan-eilenberg-mapped-total` are not pruned from the
target closure. No planned dependency node or module is eliminated: the proof uses the
mapped-total comparison, termwise-presentation fields, sections comparison and naturality,
and the second-filtration definition from `def-sp-double-complex-total`.

The earlier sandbox's proposed public `etaleCE_filtration_restrictions` with `sorry` is
replaced by a proved private helper; it needs no new module or node.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt did not compile: its two adjacent declaration docstrings caused a
parse error, and its filtration helper used unbound `K` and `L` with `autoImplicit = false`.
More seriously, that helper asserted filtration preservation for an arbitrary map `u`,
without the summand condition. An arbitrary total chain map can mix complex degrees.
The replacement helper explicitly takes the summand condition and proves preservation
from it. The old claim that a new holed finite-supremum lemma was necessary is resolved by
a complete private proof using Mathlib subobject pullbacks and image factorizations.

No error was found in the assigned statement or the DAG's three-step plan. The unit record
`sk-prop-h2` has empty realized statement/step lists; this delivery changes none of its
statements or steps.

## Second reading by U4

1. **Comparison with the repository.** I diffed the delivered module against the repository version. The theorem statement, declaration visibility, docstring, and all existing declarations are unchanged; the only source change is the proof and a proof-only import of `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap`. No definition or target statement changed.

2. **Proof and axioms.** The module compiles cleanly with `lcompile.py` and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or `debug.skipKernelTC`. A probe reports that the target and both private helpers use only `propext`, `Classical.choice`, and `Quot.sound`. The sole original hole, `AlgebraicGeometry.Etale.etaleCE_totalize_augmented_comparison`, is closed and no hole is added.

3. **Statements and split-offs.** There are no new public statements, split-off nodes, or change records. The private finite-supremum helper is a proved proof-local construction, and the filtration helper includes the necessary summand hypothesis; it does not assert preservation for arbitrary total maps. The theorem statement remains exactly the DAG statement and is unchanged.

4. **Route and pruning.** The proof follows the DAG's three steps: invert the finite-diagonal comparison and totalize the extended map; verify the augmentation square in resolution degree zero; then use the summand equations, section naturality, finite suprema, and monicity to construct filtered chain-map restrictions. Empty intervals and negative total degrees are handled by the same finite-supremum argument. The redundant direct import of `Sheaf.CategoryTheory.CartanEilenbergMappedTotal` is removed because `Sheaf.Paper.EtaleCETotalSections` already publicly imports it; the mapped-total declaration remains used. All four DAG proof dependencies remain used.

5. **DAG agreement, search, and edge cases.** I searched the local library and Mathlib for an existing public factorization or filtration-map theorem; the only matching finite-supremum proof is private in `DoubleComplexTotal`, so duplicating the short local proof is necessary. I checked that the construction does not assume a first-quadrant complex and that `Finset.Icc` empty and negative-degree branches are covered. The existing node’s `proof`, `proof_deps`, and `proof_origin` accurately describe the Lean argument and its source, so no node edit is needed. The unit route is unchanged (its realized lists are empty).

I changed only the extra proof spacing noted during review and appended this second-reading report. No mathematical repair was needed.
