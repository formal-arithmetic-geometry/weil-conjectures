## What changed

Prove both holes in `Sheaf.Paper.FiniteSystemPullbackCoherence`. The first proof
specializes the existing varying-ring evaluation comparison and proves that its
categorical unit normalization is equivalent to the assigned section formula.
The coherence proof computes right-adjoint comparators sectionwise, transfers
associativity through adjunction, and descends the resulting identities to
complexes and the ordinary unbounded derived category. The derived evaluation
identity follows from composition of exact localization squares and the
published canonical module comparison. The argument specializes the equality
of natural isomorphisms before taking components; this avoids expensive kernel
conversion between presentations of concrete localization morphisms.

Three new modules prove the general helper results described below. No source
library declaration is edited. The finite-system operations use explicit aliases
of their existing varying-ring specializations, and the derived evaluation
operations explicitly select the canonical coefficient category structures;
see `coord/changes/m3-finite-system-pullback-aliases.md`. The existing theorem
statements and all existing declaration docstrings are preserved.

## Proved and sorry left

Closed the two original holes, both attached to
`lem-pod-finite-system-pullback-coherence`:

- `WeilConjectures.finiteSystemPullbackEvaluation_existsUnique`.
- `WeilConjectures.finiteSystemPullbackCoherence`.

Final verification through `lcompile.py --all` compiled all four delivered
modules and these four unchanged direct consumers: `IntegralSystemReductionFullyFaithful`,
`IntegralPullbackSystemComparison`, `IntegralSystemPullbackLiftAssociativity`, and
`IntegralPullbackComposition`. The assigned module took 22.2 seconds, and the
slowest delivered file took 25.6 seconds. No consumer adaptation was needed.
The three new public helper theorems are also proved. Holes added: zero. Holes
remaining in the delivered modules: zero. No unfinished lemma is split off.
The proof uses existing declared dependencies in accordance with stage 3;
this does not assert that every transitive dependency is already axiom-free.

## No longer needed

Removed these seven direct proof imports from the assigned module:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.CategoryTheory.GeometricModuleTransport`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.

The new proof does not construct independent K-flat representatives, so its
explicit proof dependency on `lem-pc-kflat-resolution` is removed. Ordinary
adjunction coherence and exact-functor localization replace its direct uses of
`lem-trf-constant-coefficient-composition`,
`lem-weil-pbc-geometric-module-transport`, and
`lem-weil-pbc-ringed-topoi-module-adjunction`. The canonical finite-coefficient
comparator is handled by the new module-localization bridge, replacing a direct
proof edge to `lem-weil-pbc-proetale-derived-pullback-composition`.

The constant-sheaf, semilinear-system, and constant-ring-map nodes remain
statement dependencies and dependencies of the existing varying-ring API;
their duplicate proof-dependency entries are removed. Exactness is still used
through the existing instances. None of these modules is withdrawn: they have
other uses and several remain transitively imported. Globally pruned modules:
none. No maintainer tool-use approval is removed.

## Where the brief, the DAG or earlier work was wrong

The existing varying-ring API already constructs the system adjunction and
unit-normalized evaluation comparison. Repeating those constructions was
unnecessary; the missing work is identification of their normalizations and
coherence of their specified comparators. The proof follows this shorter route
without bypassing the unit's finite-system reassociation step.

Lean's competing abelian and derived-category instances can describe the same
category by substantially different data terms. The explicit specializations
and category-structure choices avoid expensive kernel comparisons of those
presentations. No false mathematical statement or changed target was needed.

## New nodes

`lem-pod-canonical-module-adjunction-unit`, module
`Sheaf.AlgebraicGeometry.ProEtaleCanonicalAdjunctionUnit`, declaration
`AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction_normalized`: the canonical
module adjunction sends a section to the sheafified tensor unit section. This is
proved from the existing canonical transpose formula, including arbitrary ring
maps and the identity/zero-ring cases; no faithful-section assumption is used.

`lem-pod-constant-comparison-module-localization`, module
`Sheaf.AlgebraicGeometry.ProEtaleConstantModuleComparisonLocalization`, declaration
`AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition_eq_mapModuleComparison`:
the canonical finite-coefficient derived comparison is the localization of the
specified ordinary module comparison. Unit normalization and uniqueness identify
the ordinary comparisons; the existing canonical localization formula then
identifies their derived realizations. The coefficient ring need only satisfy
the already specified finiteness assumption, which includes the zero ring.

`lem-pod-derived-exact-square-composition`, module
`Sheaf.CategoryTheory.DerivedExactSquareComposition`, declaration
`CategoryTheory.Functor.mapDerivedCategorySquareIso_comp`: a specified composition
equation between exact ordinary squares descends to an equality of the
pasted derived natural isomorphisms. Localization extensionality, invertible
factorization maps and cancellation give the proof. It applies to all objects, including zero objects, without boundedness,
conservativity, or resolution hypotheses.

All three nodes have sources and complete proofs in words and Lean. Definition
change record: `coord/changes/m3-finite-system-pullback-aliases.md`.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
