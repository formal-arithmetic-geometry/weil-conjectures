## What changed

Proved three existing theorems in `Sheaf.Paper.ClassicalLocalFrobeniusData` without
changing their statements, any definition, or any import:

- `WeilConjectures.ClassicalLocalFrobenius.positiveIso_hom`: induction matches the
  isomorphism recursion with the morphism recursion.
- `WeilConjectures.ClassicalLocalFrobenius.positivePower_blocks`: a proved private
  helper identifies `localPositivePower g n` with `(End.of g) ^ (n + 1)`, and
  Mathlib's `pow_mul` proves the block identity.
- `WeilConjectures.ClassicalLocalFrobenius.positiveIso_blocks`: isomorphism
  extensionality reduces to the two preceding public theorems.

The endomorphism multiplication order matters: the private helper uses
`pow_succ'`, since endomorphism multiplication reverses categorical composition.
The proofs include the boundary values m = 0 and n = 0, without assumptions on g
beyond being an endomorphism (respectively an isomorphism). No new mathematical
hypotheses, public declarations, or postponed proof obligations were introduced.

This is a partial proof delivery, not a decomposition. The existing definition
node has no proof steps or proof dependencies to replace; the elementary power
arguments use only definitions already in that node and Mathlib monoid laws.
The unit route is preserved.

Validation: the sandbox module compiled successfully through `lcompile.py`
(19.6 seconds, exit code 0), with no diagnostic messages.

## Proved and sorry left

Closed 3 of the module's original 7 holes, by the three declarations above.
Added 0 holes; split off 0 statements. The private helper `positivePower_eq_pow`
is fully proved.

The following four existing holes are unchanged, all attached to
`def-zl-classical-local-frobenius-data`:

- `WeilConjectures.ClassicalLocalFrobenius.classicalComposition_existsUnique`
- `WeilConjectures.ClassicalLocalFrobenius.transport_blocks`
- `WeilConjectures.ClassicalLocalFrobenius.sfWeil_blocks`
- `WeilConjectures.ClassicalLocalFrobenius.classicalWeil_blocks`

They retain their source citations and complete prose proofs. In particular,
`classicalComposition` still selects the uniquely germ-normalized compositor
specified by the existing existence-and-uniqueness theorem; this delivery does
not introduce or alter any such choice.

## No longer needed

None. All three existing public imports are retained: the normalized realization
supplies statement data, the large-coefficient local Frobenius interface supplies
statement data, and PathTransport supplies the classical transport construction.
No node or module is withdrawn. The search found the holed `positivePower_eq`
in `Sheaf.Paper.LocalFrobeniusTransportNormalization`, but importing that larger
normalization module is unnecessary: the needed elementary identity is proved
privately here from the recursion, without importing its postponed results.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The definition node also owns seven auxiliary
proof obligations; its `proof` and `proof_deps` are empty. No alternative declared
proof plan for the remaining four obligations was present there.

The search located integral pullback associativity in
`Sheaf.Paper.IntegralPullbackComposition`, but this is not directly a coherence
API for the prescribed `LocalFrobeniusLarge.composition` or the classical
finite-germ compositor. The remaining block theorems require those coherence
arguments, not only the arithmetic identity proved here. They are explicitly
left unchanged rather than counted as proved or renamed into new holes.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
