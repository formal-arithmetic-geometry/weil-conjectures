## What changed

Proved `Algebra.exists_augmented_firstOrder_polynomial_coordinates` in
`Sheaf.RingTheory.Smooth.AugmentationFirstOrderCoordinates`, with its original signature,
visibility and docstring unchanged. Added only the proof import
`Mathlib.RingTheory.LocalRing.Module` and two proved private helpers.

Updated the existing node’s proof and proof-origin records during second reading
to match the actual Mathlib retraction and coefficient argument.

The augmentation section of C/I² supplies a retraction of the conormal map through
Mathlib's `retractionKerCotangentToTensorEquivSection`. After restricting scalars to B,
I/I² is a direct summand of the finite projective module B tensor[C] Ω[C/B]. It is
therefore finite projective and, by `Module.free_of_flat_of_isLocalRing`, finite free.
Lift its finite basis to I and construct f by polynomial evaluation. A coefficient
calculation gives each polynomial's constant-plus-linear normal form modulo J².
The augmentation and basis independence prove injectivity; basis expansion of
`a - algebraMap B C (ε a)` proves surjectivity. This implements the node's split
conormal/basis-lift/square-zero argument without constructing explicit square-zero
extension equivalences. All lifts occur inside a proved theorem, and no definition
chooses data from an unproved existence statement.

## Proved and sorry left

Closed the one original hole:
`Algebra.exists_augmented_firstOrder_polynomial_coordinates`
(node `lem-sbc-smooth-augmentation-first-order-coordinates`).

Both private helpers, `augmented_cotangent_finite_free` and `firstOrder_remainder`,
are fully proved. No `sorry` remains in the module, no holes were added, and no
statements were split off. The Lean proof covers n = 0 using empty sums and an empty
basis, and does not assume that B or C is Noetherian.

Validation: the single-file compile passed. The delivery dry run performs the final
compile and axiom probe. All original public imports and the public theorem signature
are preserved.

## No longer needed

No original imports, DAG nodes or project modules were removed. The DAG has no
stated proof dependencies to prune. The tentative proof import
`Mathlib.RingTheory.TensorProduct.Finite` was removed because
`Mathlib.RingTheory.LocalRing.Module` already imports it transitively.
There are no new modules or nodes.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's single prose proof step supplies no lower
nodes, but the needed conormal splitting, finite/projective descent to a direct
summand, and local freeness are already available in Mathlib. Its stronger conormal
isomorphism assertion is valid; constructing just its retraction is sufficient for
the finite-freeness step. The existing mathematical route and unit route are retained.

## Second reading by N4

1. Compared the entire module with the repository using `diff -u`, and checked the
   existing theorem signature byte for byte. Its hypotheses, conclusion, visibility,
   and original public imports are unchanged. Restored the accidental replacement of
   `B[X]` by `B[MvPolynomial.X]` in its docstring; the original docstring is now identical.
2. Read both private helper proofs and the entire public proof. The conormal retraction
   is constructed from the actual augmentation section; finite projective base change,
   restriction of scalars, and local freeness are applicable. Basis lifts use the proved
   surjectivity of `Ideal.toCotangent` inside a theorem. No definitions were added, no
   forbidden declarations occur, and no `sorry` remains. Compilation passed without warnings. An explicit `#print axioms` probe
   of all three declarations passed, showing exactly `propext`, `Classical.choice`,
   and `Quot.sound`, with no `sorryAx`.
3. No statements were split off and no holes were added. Checked the coefficient
   remainder for degree zero and one, including the empty variable set; the higher
   monomials are exactly those in J². For C = B with identity augmentation, I = 0
   and the rank-zero construction reduces to constants. The argument works over
   rings with zero divisors and uses no Noetherian assumption.
4. Searched the current Sheaf and upstream RingTheory sources with `firstOrder`,
   `first_order`, augmentation coordinates, and ideal-power terminology, and searched
   Mathlib's conormal and polynomial ideal APIs. The existing power-series comparisons
   impose different hypotheses; the similar Taylor expansion is private. The proof
   already uses the direct Mathlib conormal retraction, local freeness, and coefficient
   criterion, with no missing shorter public result found. The added local-ring module
   import is proof-only and supplies local freeness. No old proof dependency exists to
   prune. The unit `sk-prop-input-spreading` and its recorded route are unchanged; this
   argument supplies its first-order step in the completion chart.
5. The original node has empty `proof_deps` and the proof uses no project theorem
   dependencies. Updated its `proof` and `proof_origin` to describe the actual three
   steps: conormal retraction and finite freeness, basis lifting and the polynomial
   remainder, and injectivity/surjectivity. The statement and Lean signature are
   unchanged; there are no new nodes.

Second reading changed only the accidental docstring edit, the existing node's proof
record, and this report. The Lean proof required no repair. Checked the cited source,
[Stacks Project Tag 05D5](https://stacks.math.columbia.edu/tag/05D5), through its
first-order quotient argument; the polynomial quotient implements the same constant
and linear coordinates as the power-series quotient at this order.
