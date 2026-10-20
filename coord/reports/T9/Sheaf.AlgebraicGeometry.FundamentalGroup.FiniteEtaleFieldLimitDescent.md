## What changed

Proved `AlgebraicGeometry.Scheme.FiniteEtale.finiteEtale_fieldLimit_descent`, with its
public signature and both public constructions unchanged. The proof constructs the
specified finite-field diagram and cone, establishes its limit from the already
proved `FiniteIntermediateField.isLimitSpecCone`, using Mathlib’s theorem that
pullbacks commute with connected limits, then uses all three clauses of
finite-presentation descent. Finiteness and etaleness descend separately and persist
at a common larger finite field. The comparison isomorphisms come from pullback
pasting and satisfy the two required projection equations.

Updated the proof import of `DescendFinite` to its current upstream
`WeilConjectures.AlgebraicGeometry.DescendFinite` module after the library migration.

Private helpers establish the diagram laws, limit, affine transitions, qcqs stages,
and canonical cover comparisons. General projection and naturality lemmas, with local
irreducibility for the comparison-isomorphism constructions, prevent expensive
unfolding. No public definition, statement, or consumer is changed.
The node proof and dependencies reflect the implemented argument. The complete
module compiled through lcompile.py; deliver3.py performs the final checks. The unit has
empty realization lists, and its route is preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.FiniteEtale.finiteEtale_fieldLimit_descent`
(node `lem-wf-finite-etale-field-limit-descent`). No holes added, no split-off
statements, and no `sorry` remains in the delivered module.

## No longer needed

Removed proof imports:

- `Sheaf.FieldTheory.AlgebraicSeparableSmooth`, node
  `lem-kun-algebraic-separable-smooth`: the existing proved finite-intermediate-field
  limit supplies the exact indexing fields and inclusions directly.
- `Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyOfFinitePresentation`,
  node `lem-trf-finite-morphism-finite-presentation`: existing Mathlib instances
  supply local finite presentation, quasi-compactness and quasi-separatedness.

Their obsolete tool approvals are withdrawn from the node copy. The finiteness and
etaleness descent imports remain used. No public import or module is withdrawn.
Pruning concerns this proof; other parents may still use these nodes.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The original plan's existential filtered-smooth
presentation does not directly identify the specified intermediate fields; the
source library already proves the exact required finite-field spectrum limit.
Finiteness and etaleness can descend from the same original model independently,
then be combined at a common upper bound; no sequential tail restriction is needed.

Checked Stacks `pione.tex`, label `lemma-limit` (0BTV), and `limits.tex`, labels
`lemma-descend-finite-presentation` (01ZM),
`lemma-descend-finite-finite-presentation` (01ZO), and `lemma-descend-etale` (07RP).
The proof retains empty schemes, `L = K`, the bottom stage, and unchanged indices.

Change record: `coord/changes/FiniteEtaleFieldLimitDescentProofHelpers.md` records
the private instances and local transparency commands flagged by preflight.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
