## What changed

Proved both original holes of Sheaf.Paper.ECoefficientSmoothBaseChange. The arithmetic
helper identifies each finite quotient cardinality as a power of l by excluding every
other prime divisor using units and the l-adic norm. The proof applies the published
adic theorem, localizes its actual integral mate, and proves presentation independence
by naturality and cancellation. For conditional constructible landing it transports
all four finite witness systems, applies the adic theorem's landing clause, and
rationalizes the isomorphism in the full constructible subcategory.

Added Sheaf.Paper.SbcFiniteWitnessRealization and Sheaf.Paper.SbcFiniteConstructibility.
Both are fully proved. The first compares the fixed-coefficient witness operations
with the actual finite ringed operations. The second transports the given intrinsic
finite stratification and finite local models through canonical quotient realization.
The helpers include no new hypotheses on schemes, etale origins, or cohomological bounds.

All existing definitions and theorem conclusions are retained. The unit route remains
integral adic smooth base change followed by central localization and the four-system
constructible-landing clause. The new lemmas make its coefficient-presentation glue
explicit. No existing module outside the assigned item is adapted.

## Proved and sorry left

Closed 2 original holes:
- WeilConjectures.sbcPrimeUnitOnSource.
- WeilConjectures.eCoefficientSmoothBaseChange.

Added 0 holes. No sorry remains in any delivered Lean module. Both new public theorems
WeilConjectures.sbcFiniteWitnessRealization and
WeilConjectures.sbcFiniteRealization_constructible are proved, as are all private helpers.
This is a proof from the stated library dependencies, not a decomposition into new holes.
Existing imported results may still have their own holes; no claim of closure-wide
axiom elimination is made.

## No longer needed

Removed these proof-only imports from the assigned module:
- Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral.
- Sheaf.Paper.ProEtaleCanonicalTensorPullback.
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived.
- Sheaf.Paper.IntegralUniformCoefficient.
- Sheaf.Paper.PbcRationalCategory.

The assigned proof no longer directly uses def-pc-perfect-ring-complex or
lem-weil-valued-dvr-finite-quotients: the published coefficient datum already provides
its finite/perfect instances. The quotient order proof uses the unique-prime-divisor
criterion instead of separately counting residue-field filtration factors. Neither
node is asserted globally unreachable; other modules and the adic coefficient datum
still need them.

Removed obsolete direct tool-use approvals from this node for
lem-weil-valued-dvr-finite-quotients, prop-weil-pbc-direct-image-limits,
lemma-weil-pbc-completed-pullback-reduction, lem-weil-pbc-constant-completion-equivalence,
lem-weil-pbc-normalized-constructible-local-effectivity,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
prop-weil-pbc-site-comparison-finite-level, and thm-weil-pbc-site-comparison.
These underlying operations and comparisons are consumed through adicSmoothBaseChange;
this proof does not reprove that theorem or bypass it. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old final proof step called the two four-output conditions identical. Their
coefficient presentations differ: admissibility uses fixed-coefficient witness
operations, while the adic theorem uses actual ringed finite operations and restricted
cohomology. The two new proved bridges supply this missing comparison, including
intrinsic constructibility and its unchanged vanishing interval. Merely applying the
adic theorem to the original condition would leave this step unproved.

The continuation note progress.md was stale: the three retained proof modules already
had no literal holes, but no report or node packet existed. Current-source compilation
also exposed incorrect slice-site annotations in the constructibility helper. These
were corrected to use the original ambient topology, retained before sieve
membership destructuring introduces shadowing variables. Diagnostic scratch files
are outside lean/ and are not part of the delivery.

## New nodes

lem-sbc-finite-witness-realization records the proved natural comparisons of finite
witness direct image and inverse image with canonical quotient realization. Its module
is Sheaf.Paper.SbcFiniteWitnessRealization. It refines the final four-system clause,
not a restatement of the assigned theorem.

lem-sbc-finite-realization-constructibility records preservation of intrinsic finite
constructibility by that realization and restriction to the constant coefficient
sheaf. Its module is Sheaf.Paper.SbcFiniteConstructibility. It retains the same strata
and finite local models, including the empty scheme. Both nodes are in
sec-smooth-base-change/sk-rem-rest. The module-environment change record is
coord/changes/ECoefficientSmoothBaseChange-imports.md.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
