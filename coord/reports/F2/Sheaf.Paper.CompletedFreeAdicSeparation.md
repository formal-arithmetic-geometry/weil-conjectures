## What changed

Repaired the false unrestricted intermediate separation statement by restricting
`completedFree_adicSeparated` to representables whose structure morphism satisfies
`proAffineEtale`. It now has a complete proof from local-dual detection and the
actual finite coefficient limit. The private coefficient annihilation,
coefficient separation, and restriction-of-local-functionals lemmas are proved.

Added `Sheaf.Paper.CompletedAffineFreeLocalDual`, containing the geometric
finite-support local-dual detection step. It contains no divisibility condition
or equivalent reformulation of the separation assertion. Its source, complete
proof in words, edge cases, and dependency/search records are in its docstring
and node. The proof uses clopen graphs at finite affine etale stages and a finite
closed-stratum covering, rather than a countable intersection of covering sieves.

Adapted the unclaimed `Sheaf.Paper.CompletedCoefficientFreeGenerator`: its
`completedFreeCell_automaticLinearity` helper receives the same hypothesis and
passes it to separation. All free-presheaf, free-cell, distinguished-generator
and generator-to-section constructions are unchanged.

Adapted the unclaimed `Sheaf.Paper.CompletedCoefficientSectionAction`: its public
statements and definitions are unchanged. The old free-generator argument now
works first on the pro-affine etale basis. A new private action-restriction lemma
and the existing cover-density instance for `Scheme.AffineProEt.toProEt X` descend
the identity to every pro-etale object. In particular no affineness hypothesis on
X or U reaches the public section-action theorem or any target.

The free-generator module replaces the broad public DiagonalCoefficientReference
import by the three modules its declarations need: DiagonalTowerLimitInterface,
ProEtaleCompletedCoefficients, and InternalAbelianSheafModuleEquivalence. Its sole
direct importer SectionAction already publicly imports DiagonalCoefficientReference.

The two corrected statement modules publicly import the definition of
`proAffineEtale`. The new detection lemma is a private proof import of the item,
and the basis comparison is a private proof import of SectionAction. Updated the
three existing proof records, and the two changed statements with complete
`statement_change` histories and their sole citers. No adopted source-library
file or unit route is changed. Change record:
`coord/changes/F2-completed-free-pro-affine-generators.md`.

Validation: all four delivered modules compile cleanly through lcompile in
dependency order, including both direct consumers of changed interfaces. The
standard per-file Lean acceptance limit is enforced by that tool; its displayed
elapsed figures also include service setup before Lean starts. No profiler or
transparency-debugging option remains. The statement-change records pass their
format/history checks, and the new structural node introduces no dependency cycle.

## Proved and sorry left

Original item: one sorry, `completedFree_adicSeparated`. Its old unrestricted
statement is false and is not proved. This packet is a statement repair and
geometric decomposition, not a claim of one original theorem proved or positive
net sorry progress.

The corrected `completedFree_adicSeparated` has zero local sorries and a complete
combination proof. Its three private helpers `finiteCoefficient_nsmul`,
`coefficient_adicSeparated` and `localDual_zero` are fully proved. The modified
automatic-linearity proof and the unchanged general section-action statement are
fully proved from their existing dependencies plus the corrected helper.

One new sorry remains:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedAffineFree_localDual_detect`,
node `lem-sfb-completed-affine-free-local-dual` in
`Sheaf.Paper.CompletedAffineFreeLocalDual`. It is strictly the geometric detection
step: it does not assume infinite divisibility, and it does not prove coefficient
annihilation, coefficient-limit separation, or the linear-functional calculation,
which are implemented in the parent. This is one split-off obligation, not another
copy of the assigned adic-separation assertion. There are no sorries in data,
private declarations, or either adapted consumer. Actual packet hole count: one
new structural theorem; zero holes in the corrected item.

## No longer needed

The corrected proof does not use `det-pe-replete-epimorphism` or the source module
`WeilConjectures.AlgebraicGeometry.ProEtaleReplete`. Removed that dependency from
the item's proof record. It had not been imported by the original file, so no
original import of repleteness is removed. The broad public import
`Sheaf.Paper.DiagonalCoefficientReference` is removed from FreeGenerator and replaced
by the three statement dependencies named above; its sole consumer already imports
that reference directly. No declaration or module is withdrawn: that
repleteness theorem remains available for its other users.

The former countable common-refinement step is discarded. The new proof uses
finite local linear tests, coefficient projections, and finite closed refinements.
No unit statement or realized unit step is bypassed. No other planned dependency
is pruned, and the existing coefficient/sheafification imports remain needed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old unrestricted statement): non-quasi-separated etale
representables give nonzero infinitely divisible free-sheaf sections. M8 had
already documented this before this assignment. Independently checking the
finite-support proof exposed precisely the same problem: repleteness applies to
sheaf epimorphisms, and does not make countably many arbitrary presheaf-equality
sieves have a covering intersection.

For a concrete counterexample, let X be the Boolean spectrum of eventually
constant F2 sequences (the convergent sequence N union infinity). Double X along
E=N, and take l=3. The resulting etale X-scheme U has sections s,t agreeing exactly over E.
The continuous p-adic coefficient a(n)=l^n, a(infinity)=0 gives
x=a([s]-[t]). For every m, its continuous divided tail b_m is zero on the finite
initial segment and l^(n-m) on n>=m, with value zero at infinity. Thus l^m b_m
agrees with a off the initial segment, where [s]-[t] already vanishes. Hence x is
globally infinitely divisible. The zero sieve of its free-presheaf representative consists of maps lying in E or
{infinity}; no finite family of quasi-compact images of this form covers X, so
it is not a pro-etale covering sieve and x is nonzero. The corrected hypothesis
excludes this doubled non-affine representable.

The repair is explicit, not a silent weakening: both intermediate statements and
their sole parent uses are adapted together, and the parent's general conclusion
is recovered by descent. The existing basis node is stated for affine X, but its
attached source cover-density instance `Scheme.AffineProEt.isCoverDense_toProEt`
is already proved for arbitrary X and is the declaration used here. No source
signature needs changing. The nearest blueprint source remains coefficient
identification paragraph (1) of `det-prop-diagonal-tower-coefficients`.
The existing separation node points its blueprint ancestry at a created helper,
rather than the imported blueprint node; that maintained field is preserved.
The new structural node records the actual blueprint ancestor explicitly.

## New nodes

`lem-sfb-completed-affine-free-local-dual` states local R-linear dual detection for
the sheafified free module on a pro-affine etale representable. Its finite-support
proof uses the existing affine presentation, profinite connected-component and
canonical closed-localization nodes. Empty objects and empty support are included;
finite stages need only be etale and separated, not finite etale. The statement
has no quotient-power, infinite-divisibility or realization hypotheses.
The statement correction and complete consumer list are recorded in
`coord/changes/F2-completed-free-pro-affine-generators.md`.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
