## What changed

Reduced `completedCoefficientRealization_exists` to two strictly smaller coefficient
comparisons, and wrote the complete Lean construction combining them. The composite
functor restricts scalars along the coefficient-ring isomorphism and then applies the
inverse internal/sectionwise module equivalence. Its scalar-restriction inverse and
round-trip isomorphisms are constructed explicitly. Additivity is checked on sections;
finite limits and colimits are preserved because the composite is an equivalence.

The underlying-sheaf comparison is the section-reconstruction counit. The inverse
coefficient-ring map gives the regular-module comparison, including its linearity and
naturality. Full faithfulness lifts this and the root-line comparison to internal module
isomorphisms. A proved categorical cancellation lemma identifies their underlying maps
with the supplied sectionwise maps and proves both required normalizations.

The assigned module adds private proof imports of
`Sheaf.Paper.CompletedCoefficientRingComparison`,
`Sheaf.Paper.CompletedCoefficientRootLineComparison`, and
`Sheaf.Paper.DiagonalIntegralRootMap`. The new statement modules publicly import
only their statement dependencies.

Only the assigned module, its node, and two new modules and nodes are changed. No shared
interface, target, adopted source declaration, or existing public import is changed.

## Proved and sorry left

Original holes: 1. The proof body of
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedCoefficientRealization_exists`
contains no `sorry` after this change. This is a decomposition, not a net proof: it uses
the following two new named public theorem holes.

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedCoefficientRingComparison_existsUnique`
  in `Sheaf.Paper.CompletedCoefficientRingComparison`
  (`lem-diagonal-completed-coefficient-ring-comparison`): the coefficient-ring isomorphism,
  fixed by all positive finite reductions. This asserts no module equivalence, underlying
  functor comparison, or Tate-line comparison.
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedCoefficientRootLineComparison_exists`
  in `Sheaf.Paper.CompletedCoefficientRootLineComparison`
  (`lem-diagonal-completed-coefficient-root-line-comparison`): linearity and invertibility
  of the already specified root-limit map for one module, after the ring comparison is
  given. This asserts no equivalence of categories or regular-module normalization.

Thus one original hole is replaced by two smaller holes; the net hole change is +1.
There is no `sorry` inside a definition or a private declaration. The ring isomorphism is
unique with its projection equations. The root-line isomorphism is determined by its
underlying map, since forgetting module structure is faithful; neither witness is an
arbitrary object selected from an undetermined existence statement.

All three Lean modules compiled cleanly together in import order with development
profiling options removed. The final delivery check also verifies the import cleanup.

The existing `diagonalIntegralRoots_exists` and internal/sectionwise module equivalence
are used directly. The scalar-restriction equivalence, regular-module isomorphism,
counit cancellation, and assembly are proved here.

## No longer needed

No existing module or declaration is withdrawn, and no global pruning is claimed.
The original public import `Sheaf.Paper.DiagonalCoefficientReference` is preserved.
The new ring module uses the coefficient-reduction and completion definitions rather
than importing the entire reference module. The new root module imports the diagram
definitions; the ring-comparison and proved root-map theorems are imported privately
only by the parent.
These remove unnecessary trial imports, not previously landed dependencies.

The assigned node no longer directly uses
`sk-prop-sfb-qlbar-colimit-x` or
`det-prop-sfb-qlbar-colimit-x-integral-limit`: its general inverse-limit calculation is
replaced at this level by the fixed-projection ring comparison. This does not establish
that its module is globally unused. The general completed-condensed-coefficient limit
remains below the new ring-comparison obligation; the root-map and section-module
comparison remain direct dependencies. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is retained. The previous plan described the limiting-ring
and root-limit identifications in words, but its declared dependencies did not themselves
supply the two fixed comparison maps needed by the record. In particular,
`diagonalIntegralRoots_exists` supplies a normalized additive-sheaf map, not its scalar
linearity or its invertibility. A non-normalized finite-level comparison is insufficient
for the required projection identities. The new nodes isolate those precise missing
parts while the functorial reconstruction and normalization glue are now Lean proofs.

The two comparisons have been checked mathematically on the empty scheme, on positive
finite root levels, and against the inverse orientation of the ring isomorphism. The
positive coefficient tower omits only the terminal exponent-zero ring. No hypotheses
are added to or removed from the assigned theorem.

## New nodes

- `lem-diagonal-completed-coefficient-ring-comparison`: the unique coefficient-ring
  isomorphism with its finite reduction equations. Its source is the integral coefficient
  limit in `sk-prop-sfb-qlbar-colimit-x`, as used in paragraph (1) of diagonal tower
  coefficient changes. Its proof reconstructs the two limiting cones, matches their
  finite projections, and uses uniqueness of limits.
- `lem-diagonal-completed-coefficient-root-line-comparison`: the prescribed root map is
  a linear isomorphism after this ring identification. Its source is the integral
  root-limit identification in the same paragraph. Its proof checks scalar linearity
  after finite projections and invertibility on the compatible primitive-root cover.

Each new module has one public theorem hole, with a source, complete proof in words,
blueprint identifier, exact Lean signature, and matching DAG record. The original node's
proof and proof dependencies now describe the implemented assembly.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
