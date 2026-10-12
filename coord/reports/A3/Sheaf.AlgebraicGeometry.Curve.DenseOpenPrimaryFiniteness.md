## What changed

Replaced the draft's pair/proper projection split with a real reduction. The existing
`AlgebraicGeometry.IsCurve.dense_open_primary_finiteness` signature and docstring are
unchanged. Its proof establishes constructibility and r-annihilation of G, uses the
existing dense-open higher-cohomology comparison, treats the two prime-torsion cases,
and applies an unconditional cohomology-finiteness equivalence.

Added three modules, all under `Sheaf.AlgebraicGeometry.Curve`:
`PrimeAnnihilatedPrimaryCases`, `PrimeAnnihilatedInvertibleCases`, and
`DenseOpenCohomologyFiniteness`. The first two are fully proved using additive geometric
stalks, Mathlib's coprime-annihilator lemma, ΓSpecIso, and stalk conservativity.
The last isolates the finite-boundary five-term argument, without any prime-annihilation,
primary/invertible-order predicate, or properness condition.

All additional imports of the original module are plain proof imports. The new invertible
cases module imports TorsionSheaf rather than the larger curve-assertions interface; the
unconditional finiteness module imports only the curve, constructibility, cohomology and
open-extension interfaces needed by its statement.

## Proved and sorry left

The original module has no direct `sorry`:
`AlgebraicGeometry.IsCurve.dense_open_primary_finiteness` is proved as a reduction.
The new `AlgebraicGeometry.Scheme.prime_annihilated_primary_cases` and
`AlgebraicGeometry.Scheme.prime_annihilated_invertible_cases` are proved without `sorry`.

The only new `sorry` is
`AlgebraicGeometry.IsCurve.dense_open_cohomology_finiteness`, node
`lem-pbc-a3-dense-open-cohomology-finiteness`. Its docstring gives the full finite-boundary
and five-term argument. The main theorem also uses the existing open
`AlgebraicGeometry.IsCurve.dense_open_high_cohomology` (node
`lem-pbc-s2-dense-open-high-cohomology`); it is therefore not claimed axiom-clean yet.

## No longer needed

Removed the draft-only modules and nodes
`DenseOpenPrimaryFinitenessPair` / `lem-pbc-s2-dense-open-primary-finiteness-pair` and
`DenseOpenPrimaryFinitenessProper` / `lem-pbc-s2-dense-open-primary-finiteness-proper`.
No original public import is removed, and no existing module is globally pruned.

The following old proof dependencies are no longer used directly by the item's Lean proof:

- `def-weil-pbc-etale-constructible-sheaf`
- `def-weil-pbc-primary-torsion`
- `lem-weil-pbc-closed-point-residue-field-base`
- `lem-weil-pbc-cohomology-pullback-derived-unit`
- `lem-weil-pbc-extension-by-zero-stalks`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `lem-weil-pbc-noetherian-finitely-many-components`
- `lem-weil-pbc-open-closed-short-exact`
- `lem-weil-pbc-pullback-cohomology-long-exact-ladder`
- `lem-weil-pbc-zero-dimensional-cohomology`
- `lemma-weil-pbc-finite-direct-image-exact`
- `lemma-weil-pbc-geometric-stalk-conservative`

These arguments are retained below the reduction in the appropriate new generic or
unconditional-finiteness node, or below the existing higher-cohomology node. Their modules
are not asserted to be globally unreachable. The finiteness and generic nodes have no
back-edge to the item.

## Where the brief, the DAG or earlier work was wrong

The first draft's component nodes depended back on their parent, making a cycle. They
contained placeholder Lean signatures, empty search records, and docstrings without sources
or proofs. The parent's `proof_deps` also disagreed with the steps in `proof`. A projection
split did not formalize the actual torsion-case and five-term reductions. These defects
were repaired, and both elementary torsion-case reductions were proved outright.

The existing higher-cohomology declaration is present in the repository but initially
absent from the last-green compiled library. The reader waited for publication rather
than adding a duplicate theorem. A temporary scratch copy checked the rest of the assembly;
that scratch file is not delivered.

Source checked against [Stacks Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA): the
finite-boundary and five-term comparison is the source's argument. Its remark (a) concerns
invertible torsion and remark (b) constructibility; the Bezout prime-case supplements are
written out by A3, not attributed as verbatim source statements.

## New nodes

`lem-pbc-a3-prime-annihilated-primary-cases`: a generic prime-annihilation/primary-torsion
lemma, with no curve or finiteness hypotheses; proved by exponent one and coprime
annihilators followed by geometric stalk conservativity.

`lem-pbc-a3-prime-annihilated-invertible-cases`: a generic prime-annihilation/invertible-order
lemma over a field, with no curve or constructibility hypotheses; proved by ΓSpecIso,
coprime annihilators, and geometric stalk conservativity.

`lem-pbc-a3-dense-open-cohomology-finiteness`: the unconditional finiteness comparison,
strictly the finite-boundary portion of the original argument. It has its complete source
proof in the docstring and remains the one newly open statement. Each new node records
leansearch (attempted, service unavailable), leanfinder, loogle, and grep searches and the exact Lean signature. No change record is
needed: no existing statement, definition, or public import is changed.

## Second reading by A3

1. **Interface:** PASS. Compared the delivered original module with the repository using
`diff` and the declaration parser. The existing theorem signature, hypotheses, conclusion,
definitions, docstring and public imports are byte for byte unchanged. The only original
module changes are its proof and plain proof imports. No change record is required.

2. **Proof:** PASS. All four delivered modules compile locally. The two generic
prime-torsion case theorems compile without `sorry` and
`#print axioms` shows only `propext`, `Classical.choice`, and `Quot.sound`. The only new
open proof is the named unconditional cohomology-finiteness theorem. There are no forbidden
axiom/unsafe/opaque/implemented_by/extern declarations or hollow definitions. The real main module and its `#print axioms` scratch copy now compile with the published
higher-cohomology module. The main theorem and open finiteness theorem additionally show
only the expected `sorryAx`. Temporary scratch files are not delivered.

3. **New statements:** PASS. The primary and invertible-order case lemmas are generic,
proved facts, not copies of the item. The remaining split-off statement is unconditional
finiteness for all cohomology, strictly the finite-boundary portion of the geometric argument.
It has a complete source proof and matching node. Checked empty X, zero F, U=X, degree
zero, degree one, higher degrees, equal/different primary primes, characteristic zero,
and noninvertible annihilating prime. In particular no converse equivalence of the torsion
hypotheses is assumed. Independent leanfinder/loogle/grep searches and rg of the project
found no existing replacement. LeanSearch was also attempted and returned Internal Server
Error, which is recorded without a mathematical verdict. The useful Mathlib coprime and
zero-cohomology lemmas were
used, and the existing upstream constructibility results were used rather than restated.

4. **Route and pruning:** PASS. The proof now genuinely combines prime cases, zero
cohomology, the existing canonical higher-cohomology bijection, and the unconditional
finiteness comparison. `dag/units/sk-thm-p1.json`'s `realized` statement and steps are
unchanged; this node and all new intermediates are below that unit route. Removed the
faulty draft-only component modules. All old direct dependencies absent from the new
`proof_deps` are listed under No longer needed, with the distinction between a delegated
argument and a globally pruned node made explicit.

5. **DAG:** PASS. Read all three new nodes and the repaired item node alongside the Lean.
Each new `lean.statement` is the exact parsed declaration signature; required source,
proof, search, creation, blueprint, chapter, unit and Lean records are present. The parent
and each new node have `proof_deps` exactly the union of their proof steps' `uses`, and
`proof_origin` describes the source-based reduction. The draft's parent back-edges are
removed. The only new sorry's docstring points to its own new node.

**Second-reading changes:** Removed the pair/proper projection split; proved both generic
prime-torsion cases; isolated only unconditional cohomology finiteness; wrote the main
conditional proof; repaired all node records and pruning documentation; minimized the new
modules' statement imports. No existing mathematical interface changed.

**Delivery checks:** The first dry run passed compilation and axiom checks but required
an attempted LeanSearch record in addition to Loogle/LeanFinder and grep. LeanSearch was
attempted, its service error recorded, and the search records were repaired. No mathematical
or Lean change was needed for that preflight repair.
