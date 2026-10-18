## What changed

Proved `AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_residueField_isIso` in
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeResidueIso`, preserving its complete signature and
all public imports. A proved private helper refines the pointwise constant-rank neighbourhoods
into finite free charts and assembles the varying-rank finite-local-freeness instances.
The theorem obtains finite free stalks, reflects the given scalar-extension isomorphisms along
the residue local homomorphisms, and applies the existing stalkwise isomorphism criterion.

Added proof-only imports of `Sheaf.AlgebraicGeometry.StalkFiniteFree` and
`Sheaf.AlgebraicGeometry.LocalFreeBaseChangeReflectsIso`; both imported results are proved.
Updated the existing node's proof, proof dependencies and proof origin to match this route.
No definitions, public statements, or other modules changed. No new nodes or split-offs.
The final file compiled through `lcompile.py` in 5.4 seconds with no errors or warnings.
The theorem-of-the-cube unit has no realized node replaced by this local algebra shortcut.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_residueField_isIso`
(node `lem-sc-finite-locally-free-residue-isomorphism`).
Added 0 holes. There are no remaining `sorry` declarations in this delivery.
The private helper `isFiniteLocallyFree_of_pointwise` is proved in full.

## No longer needed

Removed the redundant proof-only import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`: the public module
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` already exports its declarations.
No public imports were removed.

The proof no longer needs `lem-weil-pbc-nakayama-local-generators` as a dependency, nor the
planned construction of cokernel and kernel, their finite generation, tensor exactness and
splitting, or either application of Nakayama. Removed that obsolete entry from `tool_uses`.
No standalone Sheaf module for Nakayama was imported originally. The node is pruned from this
proof route; other consumers may still need it. No other module is withdrawn or claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original mathematical statement and plan are correct. The library already proves the
finite-free local-hom reflection theorem and finite-free stalk theorem, making the longer
Nakayama argument unnecessary here. The explicit local-hom instance for the scheme residue map
is needed because typeclass search does not unfold `Scheme.residue` automatically.

Source checked: `literature/stacks-project/algebra.tex`, lemma-cokernel-flat, part (3)
(Tag 00O0). The existing local reflection theorem implements its finite-free matrix argument.
The construction handles empty schemes (no pointwise obligations) and rank zero (empty finite
frames); ranks may vary between neighbourhoods, and no equal-rank hypothesis is added.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
