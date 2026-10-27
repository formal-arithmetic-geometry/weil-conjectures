## What changed

Replaced the sole `sorry` in
`WeilConjectures.BalancedFiniteTower.balanced_finite_tower_generator_comparison`
by a complete Lean combination of three genuine parts of its recorded argument.
The theorem's statement, existing public imports, definitions and universes are unchanged.
No source-library module or existing consumer is changed.

The new scalar-comparison module isolates the coefficient-square construction of lambda.
The quotient-comparison module isolates C, its quotient-unit formula, the ordinary
finite evaluations, their normalized source comparison r and literal compatibility
with the published comparison across independent universes. The Koszul module takes
any supplied normalized lambda and C and asserts their augmentation compatibility
through a normalized theta. Thus neither the existence of lambda nor that of C or
the ordinary comparison is smuggled into the Koszul statement's conclusion.
The main proof instantiates that compatibility with the two independently supplied
comparisons and assembles all original clauses.

Each new theorem is public, has its entire proof `by sorry`, a source, a detailed
proof in words, and its own DAG node. All new modules import only the existing
strict-tower definition owner. Existing generic proof dependencies remain on the
new nodes that need their specialization; they have not been duplicated.

This is a decomposition, not a completed mathematical proof of the comparisons.
The first remote compile of all four files passed without errors or warnings:
Koszul 53.0 s, quotient 51.5 s, scalar 51.2 s, item 59.5 s. Since the item
was near the compile limit, its proof was changed from repeated tactic
elimination to direct existential elimination, and its two inherited
respectTransparency=false options were removed. No definition or theorem
statement is changed by that elaboration cleanup. The final item compile passed cleanly in 11.0 s using the compiled new modules.
The delivery preflight validates the final packet again.

## Proved and sorry left

Input: one hole. The body of
`WeilConjectures.BalancedFiniteTower.balanced_finite_tower_generator_comparison`
is now complete from the three statements below. One upper hole is closed and
three strictly smaller holes are added: net minus two holes closed. This is a
decomposition and claims no net proof progress.

Every remaining hole in this packet is listed here:

- `WeilConjectures.BalancedFiniteTower.balanced_scalar_comparison`
  (`lem-a1-balanced-finite-tower-scalar-comparison`).
- `WeilConjectures.BalancedFiniteTower.quotient_comparison_with_ordinary_evaluations`
  (`lem-a1-balanced-finite-tower-quotient-comparison`).
- `WeilConjectures.BalancedFiniteTower.koszul_augmentation_compatibility`
  (`lem-a1-balanced-finite-tower-koszul-augmentation`).

Edge cases checked mathematically against each extracted statement: P=0,
empty source scheme, identity g, n=0 (exponent one), arbitrary unbounded P,
nonflat completed coefficient map, and different coefficient and scheme universes.
The scalar and Koszul statements do not require good P; the quotient theorem
retains the original good-P quantifier for its identification clause. None needs
scheme-level invertibility of l: these are ordinary coefficient/tensor constructions.
No global lifting of quotient sections is assumed. In the Koszul statement the
negative basis vector is retained, and its augmentation is zero. The positive
basis calculation uses pi_n(b), with no division or sign adjustment.

## No longer needed

Removed the following six proof imports from the item, because the main proof
uses only the three extracted interfaces:

- `Sheaf.SecSmoothPurity.StrictCoefficientComparisonCalculus`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `Sheaf.SixFunctors.CompletedCoefficientFreeResolution`
- `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`
- `Sheaf.Paper.RingedTopoiTensorSections`

These are not claimed as globally pruned modules. Their statements remain needed
by the extracted nodes, and the exact generic-dependency plans are recorded there.
The item's existing public imports are retained as its public interface.

The old proof's good-complex quasi-isomorphism and localization step is unnecessary
for deriving the current Lean conclusion, which asks for a strict augmentation
square and a termwise ordinary evaluation identity. Therefore this proof no longer
uses `lem-a1-pulled-koszul-tower-chain-comparison` or its module
`Sheaf.Paper.PulledKoszulTowerChainComparison`. This is a local dependency removal;
no claim is made that all other parents cease to need it, and no module is withdrawn.
The normalized ordinary evaluation theorem remains a dependency of the quotient node.
The generic cochain coherence remains a dependency of the Koszul node.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The existing generic declarations do
not directly state the needed specialization to these concrete independent-universe
coefficient functors, strict transition maps and section formulas. In particular,
the published ordinary comparison alone does not immediately give
PublishedCompatibility: its two uniquely normalized additive section transports
must actually be constructed. The quotient node now records that argument rather
than treating universe transport as an unproved identification.

The original proof step 8 includes a quasi-isomorphism claim stronger than the
current Lean conclusion needs. Its ordinary evaluation and published-normalization
part is retained; localization is not used to prove an equality already asserted
at the strict-complex level. The chapter and unit route are unchanged. The new
nodes extract steps of this same scalar/Koszul argument. Their off-unit generic
tools are precisely those already approved on the parent; no substitute weight,
purity or proper-base-change route is introduced.

An overlay dependency audit found no missing dependency and no cycle containing
any of the four changed/new nodes. It also encountered a pre-existing reachable
cycle outside this packet:
`lem-pc-ring-hom-extension-differential` has a proof dependency on
`lem-pc-ring-hom-extension-differential-adjacent`, whose statement dependency
points back to it. This is reported for maintainer reconciliation; neither record
is changed here.

## New nodes

`lem-a1-balanced-finite-tower-scalar-comparison`, module
`Sheaf.Paper.BalancedFiniteTowerScalarComparison`, extracts original steps 2, 3,
and 5. Its sole conclusion is lambda with its balanced generator formula; it
asserts neither C nor theta nor an augmentation square nor ordinary evaluations.

`lem-a1-balanced-finite-tower-quotient-comparison`, module
`Sheaf.Paper.BalancedFiniteTowerQuotientComparison`, extracts original steps 1,
2, 4, 5 and the ordinary-evaluation part of step 8. Its conclusion is C and its
ordinary evaluation data. It does not assert lambda, theta or an augmentation
square. The proof explicitly retains the actual sheaf quotient hypothesis,
local lifting, tensor-to-ordinary reduction, and normalized published transports.

`lem-a1-balanced-finite-tower-koszul-augmentation`, module
`Sheaf.Paper.BalancedFiniteTowerKoszulAugmentation`, extracts uniformizer
preservation and original steps 6 and 7. Its hypotheses supply lambda and C
with their formulas. Its conclusion constructs theta and proves the square,
without asserting existence of either supplied map or any ordinary evaluation.
The main proof applies this conditional calculation to its actual witnesses.

A full latest-blueprint search for balanced tower/generator, quotient-unit,
Koszul augmentation and ordinary finite evaluation phrases found no existing
blueprint statement duplicating these refinements. DAG candidates on normalized
scalar realization and quotient-expression towers concern good representatives
and derived systems; they do not supply the all-complex strict interfaces here.
The ordinary ring Koszul augmentation theorem concerns ModuleCat rather than
the actual sheaf pullback and its independent-universe coefficient transports.

Each node records the three searches actually run through msearch.py (LeanFinder,
Loogle and grep); the hits concern ordinary module tensor/quotient constructions,
completion or the generic totalization, not the extracted strict comparisons.
The main node's proof, proof_deps and proof_origin follow the Lean combination.
No change record is needed: no existing declaration signature, definition,
public import or consumer changed.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
