## What changed

Proved both existence-and-uniqueness theorems in
`Sheaf.Paper.ExceptionalDerivedSiteRealization`, preserving all existing public
signatures, visibility, docstrings, and public imports. The two normalization
predicates now specialize general formulas that are definitionally equal to their
original equations; this avoids expensive unfolding on concrete sheaf categories.

The inverse comparison lifts the ordinary inverse comparison through
`DerivedCategory.Q`, using the specified exact factorization isomorphisms. Its
component square and localization extensionality give normalization and uniqueness.

The direct comparison constructs the two composite cochain units with their exact
component formulas. Additive functors invert quasi-isomorphisms between K-injectives
because those maps are homotopy equivalences. Exact realization preserves the
prescribed invertible unit; the realization equivalence also preserves K-injectives.
The K-injective derivability structure therefore gives both right-derived universal
properties. `Functor.rightDerivedNatIso` produces the comparison, cancellation of the
factorization isomorphisms gives the stated unit square, and `rightDerived_ext` gives
uniqueness. All private helpers are proved, including the cochain-unit naturality and
invertibility statements. No auxiliary result is assumed or split off.

The proof-only import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` supplies
preservation of K-injectives by an additive equivalence. The existing node now records
the two proofs and the actual dependencies. The predicate factorizations and
proof-context command changes are recorded in
`coord/changes/cochain-right-unit-is-iso.md`; all attributes are local and no
consumer is adapted. The unchanged direct consumer compiled against the sandbox
module. A separate normalization probe timed out and is not counted as a
successful check; the normalization formulas were compared directly.

## Proved and sorry left

Closed 2 of 2 original holes, both belonging to
`def-pur-adic-derived-site-realization`:

- `WeilConjectures.integralExceptionalSiteDerivedInverse_existsUnique`
- `WeilConjectures.integralExceptionalSiteDerivedRight_existsUnique`

Added 0 holes; split off 0; 0 `sorry` remain in the delivered module. The proofs use
the existing ordinary comparisons and exact-realization property declarations; their
remaining dependencies are outside this item. This is a proof, not a decomposition.

## No longer needed

No original imports, nodes, or modules are pruned. The original sole public import
`Sheaf.Paper.ExceptionalSiteRealization` remains required by the public statements.
The earlier packet's direct import of
`WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives`
is redundant: it is already publicly available through the retained right-derived
functor definitions. The definition node had no original proof dependencies to prune.
The proof uses ordinary site realization, both exact realizations, and the
`CoefficientDerivedImage` inverse factorization, direct unit, and computation property.
No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The interrupted packet claimed completion but retained diagnostic options, compile
errors and timeouts. The resumed work repaired the inverse square's associativity and
replaced the direct composite units with explicit component formulas and proved
naturality. This avoids repeatedly simplifying their identity transports.

The original node had no numbered proof plan; its two new steps formalize the exact
localization and universal right-derivation arguments of the original docstrings.
The original apparent opposite orientation of `quotientCompQhIso` in the fixed unit
is harmless: its hom and inv components are identity maps, as checked by Lean.
No statement or mathematical definition correction was needed. The two
normalization predicates were factored without changing their meaning. No file or
proof was split to avoid the single-file compile limit.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
