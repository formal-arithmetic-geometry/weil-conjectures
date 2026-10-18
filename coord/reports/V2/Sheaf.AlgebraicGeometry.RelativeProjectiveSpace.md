## What changed

Filled all seven original holes in
`lean/Sheaf/AlgebraicGeometry/RelativeProjectiveSpace.lean`. All original public
signatures, public imports, definition bodies and docstrings are preserved.

The main construction uses the actual symmetric algebra sheaf, with its existing affine
comparison. On each affine open the finite-free section coordinates and Mathlib's
symmetric-algebra polynomial equivalence identify the monomial maps with the polynomial
monomial basis. Partitioning that basis by total degree makes the affine finite-sum map
bijective. Its inverse extends any family of homogeneous-sheaf maps on affine opens;
restriction compatibility and sheaf gluing give the global coproduct universal property.
This handles arbitrary base schemes and arbitrary opens without assuming a global bound
on the degrees of a section.

The coproduct property produces the decomposition isomorphism. Multiplication is an
explicit bilinear map sending two monomial basis vectors to the vector indexed by the
sum of their exponents; the unit is the zero-exponent basis inclusion. The injective
homogeneous inclusions reduce naturality and the graded algebra laws to the corresponding
ring laws. Those inclusions also determine the decomposition, multiplication and unit
uniquely, proving equality of the entire input datum.

The other proofs establish monomial naturality, the chosen algebra equality, coordinate
homogeneity, existence and uniqueness of the affine polynomial equivalence, its agreement
with the homogeneous submodule, and the restriction of the global standard opens. For the
last assertion, coordinate naturality identifies the local basic opens under transition
maps; affine refinements inside intersections prove the union has exactly the desired
restriction. Affine intersections are not assumed to be affine.

Updated the proof steps, proof dependencies and proof origin of the existing node
`def-nagata-relative-projective-space` to record this construction. No new nodes, modules,
change records or forced adaptations were needed.

## Proved and sorry left

Closed all seven original holes, by declaration name:

- `AlgebraicGeometry.RelativeProjectiveSpace.monomial_naturality`
- `AlgebraicGeometry.RelativeProjectiveSpace.existsUnique_symmetricInput`
- `AlgebraicGeometry.RelativeProjectiveSpace.algebra_eq`
- `AlgebraicGeometry.RelativeProjectiveSpace.coordinate_mem`
- `AlgebraicGeometry.RelativeProjectiveSpace.existsUnique_affinePolynomialEquiv`
- `AlgebraicGeometry.RelativeProjectiveSpace.affinePolynomial_homogeneous`
- `AlgebraicGeometry.RelativeProjectiveSpace.standardOpen_restrict`

Zero holes remain in this module; zero holes added or split off. All private helpers and
their constructions are proved. Existing imported declarations are used with their
unchanged statements, including the older relative-Proj existence theorem.

## No longer needed

Removed these unused proof imports and their corresponding proof dependencies:

- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`, node
  `lem-weil-pbc-symmetric-algebra-graded`: the grading is constructed explicitly from
  exponent addition and the finite-free monomial bases.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`, node
  `lem-weil-pbc-quasi-coherent-symmetric-algebra-core`: no comparison of universal pairs
  is needed.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`, node
  `lem-weil-pbc-quasi-coherent-symmetric-algebra`: the direct comparison for the actual
  constructed sheaf supplies both quasi-coherence and its affine section isomorphism.

The replacement is `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine`, node
`lem-weil-pbc-quasi-coherent-symmetric-algebra-affine`, together with Mathlib's
`SymmetricAlgebra.equivMvPolynomial`. The old nodes remain cited in the unchanged
mathematical statement, but none of their Lean declarations or modules is needed by
this module's proofs. No module is withdrawn, and no claim is made that unrelated
parents stop using these nodes elsewhere in the project.

## Where the brief, the DAG or earlier work was wrong

The original node had no numbered proof steps (`proof` was empty); the detailed plans
were in the seven theorem docstrings. The delivery fills those plans and records the
actual direct-comparison route in the node.

The current `def-nagata-relative-proj` and `lemma-nagata-relative-proj-exists` dependency
records point to the upstream `Scheme.GradedAlgebraData` implementation, whereas this
module's existing public interface uses the older `RelativeProjAlgebra` and
`RelativeProjData` records. This delivery preserves that interface and uses the existing
`Sheaf.AlgebraicGeometry.RelativeProjExists` declaration. A migration to the upstream
interface would require a separate coordinated change, and is unnecessary here.

The supplied affine comparison already proves quasi-coherence for the actual sheaf,
so constructing a second universal pair and comparing the two is unnecessary. The
coproduct argument must still be sheaf-theoretic: its affine section calculation does
not justify a direct-sum formula for sections on arbitrary opens.

Validation: the complete cleaned source, with axiom probes appended, compiled through
the required remote single-file compiler in 32.7 seconds without warnings. The first six
completed declarations listed above use only `propext`, `Classical.choice` and `Quot.sound`.
`standardOpen_restrict` additionally inherits `sorryAx` through the existing relative-Proj
data/existence dependencies; its own proof has no holes. Those existing dependencies are
not changed by this delivery. A separate static check confirms the original public
definition bodies and docstrings are unchanged, every Lean line is at most 100 characters,
and the updated DAG proof dependencies introduce no cycle back to this item.

The required delivery dry run compiled the item and passed the preflight. Its review
class is CODEX because the existing DAG node is updated.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
