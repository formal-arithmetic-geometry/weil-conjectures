## What changed

Replaced the sole sorry in `Algebra.exists_popescu_denominator_basis_enlargement`
with a complete Lean reduction. Its signature and all existing public imports stay
unchanged. Added `Sheaf.RingTheory.PopescuUnscaledUnitBasis`, with one geometric
intermediate theorem, `Algebra.exists_popescu_unscaled_unit_basis`.

The remaining geometric statement constructs an admissible extension, an unscaled
basis, and a unit that inverts a positive power of the denominator modulo nilpotents.
It has no numerator family and asserts neither an actual denominator power in A nor
a differential basis lifted from Λ. It is strictly the geometric part of the argument.
The parent proves the missing steps: Frobenius capture, vanishing of the differential
of the captured power, explicit numerator lifts, unit scaling of the basis, and finite
reindexing. The private `Algebra.capture_unit_power` is fully proved for arbitrary
commutative-ring homomorphisms in prime characteristic.

Updated both DAG proof routes to match. The geometric route uses Mathlib's
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`, through the existing node
`lem-weil-pbc-separable-algebraic-differentials-base-change`, and the existing theorem
`henselianLocalRing_of_maximalIdeal_le_nilradical`. No existing statement, definition,
public import or unit-level route was changed. No forced adaptations are needed.

## Proved and sorry left

Closed: `Algebra.exists_popescu_denominator_basis_enlargement`
(node `lem-weil-pbc-popescu-denominator-basis-enlargement`), by reduction to the
geometric intermediate theorem. The private `Algebra.capture_unit_power` is proved
without a sorry dependency. It returns an explicit p-th power of a unit.

Added and left: `Algebra.exists_popescu_unscaled_unit_basis`
(node `lem-weil-pbc-popescu-unscaled-unit-basis`), in its own module, with proof exactly
`:= by sorry`. This is the only delivered sorry. It contains the polynomial-localization
and finite-étale geometric constructions, with a complete proof in its docstring and DAG.

Accounting: one upper hole closed, one lower hole added; this is a decomposition,
not a completed proof of the mathematical enlargement theorem. The delivered declarations
have net zero holes; any additional effect of closure pruning is left to the maintainer's
sorry ledger. The combining proof, including the Frobenius argument, is complete Lean. Both delivered
modules compile with no warnings through `lcompile.py --all`.

Edge cases checked in the mathematics and the Lean proof: t₀ = 0, no extra vectors
(m = 0), the transcendental extra vector (m = 1), n = 1, positive powers Q = 1 and
N = 1, and p = 2. Sum indexing and reindexing require no nonempty basis. The
nilpotent-error lemma is valid even with a zero error; its exponent is chosen as
p^(r+1), so its unit witness is explicitly a p-th power. In the geometric theorem,
the transcendental case takes Q = 1 and an actual inverse, while the algebraic case
only needs the residue inverse of α^Q. No data definition is extracted from an
unproved existential theorem.

## No longer needed

Removed these direct proof imports from the parent:

- `Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue`
- `Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian`
- `Sheaf.RingTheory.HenselianEtaleRetraction`
- `Sheaf.RingTheory.HenselianFiniteEtaleEquivalence`
- `Sheaf.RingTheory.JacobiZariskiHomologySequence`
- `Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`
- `Sheaf.RingTheory.LocalDimensionZeroHenselian`
- `WeilConjectures.Mathlib.RingTheory.Etale.Field`

Six of these remain needed by the new geometric module; they are moved dependencies,
not global pruning. Two are removed from this route entirely:
`Sheaf.RingTheory.JacobiZariskiHomologySequence` and
`Sheaf.RingTheory.LocalDimensionZeroHenselian`.

The new geometric proof no longer uses nodes
`lem-weil-pbc-jacobi-zariski-homology-sequence`,
`lem-weil-pbc-etale-ring-map-iff-etale-affine`, or
`lem-weil-pbc-local-dimension-zero-henselian`. The first two are replaced by the
already stated Mathlib differential-base-change node; the last is replaced by the
smaller existing nil-maximal-ideal henselian theorem. These nodes may still have
other users in the whole library; this report only prunes their use on this route.
All other former geometric proof dependencies are retained under the new node.
No unit's realized statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan invoked the entire Jacobi–Zariski homology sequence for the finite
separable residue-field extension, although Mathlib already provides exactly the
canonical differential isomorphism needed. Its Tor conditions and leftmost terms
are unnecessary here. Likewise the full dimension-zero henselian theorem, including
its idempotent-lifting assertion, is unnecessary for Artinian rings with nil maximal
ideal. The existing smaller theorem suffices. Neither issue requires an interface
change or a disputed statement.

The geometry and the final denominator arithmetic were combined in one former hole.
This delivery separates them and proves all the arithmetic and basis manipulation.
The common-denominator hypothesis is genuinely used in the explicit lift equation,
and the characteristic hypothesis is genuinely used in both Frobenius and d(c) = 0.

Searches: LeanFinder found only local-ring/cotangent statements for the enlargement.
Loogle supplied the basis unit-scaling API; local Mathlib and library searches found
no enlargement theorem. LeanSearch returned Internal Server Error, recorded as
unavailable without a verdict. A further LeanFinder query found the exact Mathlib
formally-étale differential isomorphism, already represented by an existing DAG node.
The Stacks proofs at https://stacks.math.columbia.edu/tag/07FI and
https://stacks.math.columbia.edu/tag/07FH were read directly because this clone lacks
the untracked `literature/stacks-project/smoothing.tex` file.

## New nodes

`lem-weil-pbc-popescu-unscaled-unit-basis` records just the geometric enlargement
before the Frobenius capture and denominator clearing. Its new module is
`Sheaf.RingTheory.PopescuUnscaledUnitBasis`; its only declaration with sorry is
`Algebra.exists_popescu_unscaled_unit_basis`. The statement introduces every ring,
ideal, basis, lift and unit independently. Its proof follows the original geometric
steps and the Stacks cases, with the smaller existing differential-base-change and
nil-maximal-ideal henselian dependencies. No change record is necessary: all existing
interfaces and target statements are identical.

## Second reading by N4

1. **Visible changes and statements.** Compared the delivered parent module with the repository version. The existing theorem signature is byte-for-byte unchanged; the only new public declaration is the explicitly split geometric theorem in `PopescuUnscaledUnitBasis`. No definitions or target statements were changed.

2. **Compilation and proof audit.** Compiled both delivered modules individually and together with `lcompile.py --all`; both compile without errors or warnings. The parent theorem and its private Frobenius helper contain no `sorry`; the sole remaining `sorry` is the named geometric theorem, with a matching node and proof docstring. No forbidden declarations or hollow definitions occur.

3. **Truth and strength of split statement.** The unscaled theorem is a strict geometric reduction: it asserts an admissible enlargement, a residue inverse modulo nilpotents, and the corresponding differential basis, while omitting numerator families and actual denominator-power capture. Its statement is strictly weaker than the parent and is needed by the parent proof. Edge cases (empty basis and added family, Q = 1, and n = 1) are covered by the indexed formulation.

4. **Shortest route and pruning.** The proof uses the existing geometric node, Mathlib Frobenius and basis-scaling lemmas, and the smaller nil-maximal-ideal henselian theorem. The former Jacobi–Zariski and local-dimension-zero dependencies are removed from this route; moved geometric dependencies remain imported by the new module. No unit-level route is bypassed.

5. **DAG and route consistency.** Updated node proof routes and dependencies match the Lean proof, and the new node has source, proof, searches, Lean record, chapter, and unit metadata. The unit `sk-thm-p1` remains realized through the parent and geometric split.

I changed only the report by adding this second-reading record; no Lean repair was necessary.
