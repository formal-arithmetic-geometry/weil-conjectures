## What changed

Replaced the proof of `AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal` with a direct application of `AlgebraicGeometry.dimension_at_point_components`. The maximal ideal hypothesis forces the maximal ideal occurring in that theorem's attained localization clause to equal `m`, using `Ideal.IsMaximal.eq_of_le`. The finite-type hypothesis is obtained from the supplied MvPolynomial-surjection hypothesis via `Algebra.FiniteType.iff_quotient_mvPolynomial''`.

The proof import was changed to `Sheaf.RingTheory.DimensionAtPointComponents`. The item's DAG node proof dependencies were updated to this theorem and the Mathlib lemmas used in the short argument.

## Proved and sorry left

Proved and closed: `AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal`.

No `sorry` remains in this module. No new statements or nodes were added. The existing dependency `AlgebraicGeometry.dimension_at_point_components` remains unproved in its own module (node `lem-weil-pbc-dimension-at-point-components`); the delivery closes one upper hole and adds zero lower holes. Single-file local compilation passed without warnings.

## No longer needed

Removed direct proof import: `Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRing`.

Removed direct proof dependencies:

- `def-weil-affine-spectrum`
- `def-weil-pbc-noetherian-ring`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-noetherian-finitely-many-minimal-primes`
- `lem-weil-pbc-spec-irreducible-closed-subsets-primes`
- `def-kun-topological-krull-dimension`
- `lem-weil-pbc-irreducible-closure`
- `lem-weil-pbc-localization-dimension-chains-below-prime`
- `lem-weil-pbc-prime-contains-minimal-prime`
- `def-weil-pbc-krull-dimension-ring`
- `lem-weil-pbc-finite-type-domain-dimension-local-ring`
- `def-kun-topological-dimension-at-point`

These are unnecessary as direct proof dependencies of this item. Several remain used transitively by `DimensionAtPointComponents`, including `FiniteTypeDomainDimensionLocalRing`; no claim is made that they leave the targets' global closure. The existing public imports remain required for the statement.

The item is not in `dag/units/sk-thm-p1.json`'s realized statement or steps; the shorter route bypasses no unit realization.

## Where the brief, the DAG or earlier work was wrong

The DAG's long six-step Stacks 00OT proof is valid but unnecessary for this specialized maximal-point statement: the already stated `dimension_at_point_components` theorem includes the needed attained localization dimension for every maximal ideal above the point. No statement was changed.

## Second reading by N2

1. PASS: compared the sole delivered module with the repository using `diff -u` and
   checked the existing theorem signature byte for byte. Only the proof body and its
   non-public proof import differ. No definition, declaration signature, public import,
   or target statement changed; no change record is required.
2. PASS: compiled the module locally through `lcompile.py` without errors or warnings.
   A scratch copy with `#print axioms` reports exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The last comes from the existing unproved
   `AlgebraicGeometry.dimension_at_point_components`, not from a new hole. The delivered
   module has no `sorry`, forbidden declaration, or data construction from an unproved
   existence statement. Its existential witness is eliminated entirely inside a theorem
   proof. This closes the item's one hole, but is not an axiom-free target proof yet.
3. PASS: no statements or nodes were split off. Read the existing component-dimension
   theorem: its attained localization clause is precisely what this specialization uses.
   At a maximal prime the containing maximal ideal must be the same ideal. The zero ring
   supplies no maximal ideal, so creates no exceptional case; fields and zero-dimensional
   finite algebras give dimension zero, consistent with the argument. Independent
   LeanFinder search for local spectrum dimension versus maximal localization returned
   height/localization lemmas, not this topological local dimension equality. Repository
   and upstream searches found no proved shorter equality; Mathlib search found no
   `topologicalKrullDimAt`, `dimAt`, or `krullDimAt` declarations.
4. PASS: the proof specializes an existing broader theorem and uses the finite-type
   equivalence and maximality, with no new lower hole. The replacement import is private
   to the proof; the public imports supply the original signature. Checked that
   `## No longer needed` lists every old proof dependency absent from the new list.
   The removed domain-dimension import remains reachable through the new dependency, so
   no module is claimed pruned from the target closure. Read `sk-thm-p1.json`: none of its
   realized statement or step nodes is bypassed; its realization is unchanged.
5. PASS: compared both node files. Only `proof`, `proof_deps`, and `proof_origin` differ.
   The two steps match the finite-type conversion, component-dimension specialization,
   maximal-ideal equality, and equality composition actually compiled. The dependency
   list equals the union of the steps' uses. No new-node fields are needed.

Second reading changed only this report, adding the independent checks and the explicit
axiom/dependency limitation. The Lean proof and DAG update required no repair.
