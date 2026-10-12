## What changed

Added `Sheaf.RepresentationTheory.FinitePrimaryDecomposition`, a strictly smaller
intermediate statement for finite discrete representations. The target module now
transports this decomposition through `abelianSheaves_equiv_discreteGModules`; the
transport proof is complete. The representation theorem remains the sole sorry.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.exists_finite_primary_sheaf_decomposition`
by a complete transport proof. This is a decomposition: one hole closed, one hole added;
net hole reduction zero.
The new theorem `Rep.exists_finite_primary_decomposition` remains `sorry`, with node
`lem-sc-finite-discrete-rep-primary-decomposition`.

## No longer needed

No stated imports were removed. The direct group-theoretic construction in the blueprint
is isolated in the new representation module; no additional DAG dependencies were needed.

## Where the brief, the DAG or earlier work was wrong

The DAG treated the Chinese-remainder decomposition and its equivariant transport as one
step. The decomposition is substantially simpler and is now isolated as a finite
representation theorem; the sheaf theorem is proved by the existing equivalence.

## New nodes

`lem-sc-finite-discrete-rep-primary-decomposition` records the remaining finite
representation theorem and its source.

The new statement was checked on the zero representation (empty decomposition), a
primary group (one summand), and a group with two distinct primary parts. Restricted
stabilizers remain open, including when the acting group is infinite. Blueprint search
for `primary decomposition` found only the broader constructible reduction, not this
finite representation statement.

## Second reading by U2

1. Compared the delivered sheaf module with the repository version. The theorem signature and all
   existing declarations are unchanged byte for byte; the added representation module and node are
   the only new artifacts.
2. Compiled both sandbox modules with `lcompile.py --all`; both compile without errors or warnings.
   The sheaf theorem has no remaining sorry. The representation theorem is the single explicitly
   named sorry and has the matching node; no definitions contain sorry or forbidden declarations.
3. Checked the split statement against the zero representation, a single primary component, and
   two distinct primary components. It is strictly below the sheaf target and exactly supplies the
   transport input; no existing Mathlib or Sheaf declaration duplicates it.
4. The proof follows the stated route through the existing sheaf/G-module equivalence and the new
   finite representation theorem. The unit route is preserved. The proof-only AdditiveFunctor
   import in the representation module was changed from `public import` to plain `import`.
5. The DAG proof, proof dependencies, origin, Lean declaration, and unit/chapter fields agree with
   the source. No old proof dependency is unused; no pruning beyond the import visibility change
   was possible.

Changed the representation module import visibility and recorded this second reading.
