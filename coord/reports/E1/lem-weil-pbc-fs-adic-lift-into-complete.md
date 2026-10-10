# Stage 1 report: `lem-weil-pbc-fs-adic-lift-into-complete`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-fs-adic-lift-into-complete.json`
- `coord/reports/E1/lem-weil-pbc-fs-adic-lift-into-complete.md`

## Split

The statement was checked against More on Algebra Lemma Tag `07NJ`
(`lemma-lift-continuous`, source lines 9257--9319) and remains unchanged. Its
six proof steps follow the source's finite quotient grid: identify
`A/J = lim A/(J + I^b)`, prove the maps from each southeast grid entry to the
fiber product of its northern and western neighbours are surjective with
square-zero kernel, construct compatible lifts by induction, take the
`(bt,b)` diagonal and its inverse limit, verify agreement modulo `J`, and prove
the bound `f(n^(rt)) subset I`.

The calculations omitted in the source are included. In particular, the
inverse-limit identification uses a recursive adjustment of representatives;
the grid surjection and its square-zero kernel are checked directly with
ideals; every intermediate map is shown to kill a power of `n`, so the precise
lifting property in `def-weil-pbc-formally-smooth-adic` applies; and diagonal
compatibility is obtained by reducing in both grid indices.

## Dependencies and searches

No new node was needed. The proof uses exactly the existing nodes
`def-weil-pbc-formally-smooth-adic`,
`def-weil-pbc-algebra-hom-quotient`, and
`def-weil-pbc-adically-complete-ring`. The first and third are respectively a
reviewed split definition and a Mathlib leaf; the second records the elementary
algebra conventions used in the calculations.

The node already records LeanSearch, LeanFinder, Loogle, local-search, and
Mathlib-source grep results. The closest declaration is
`Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`, which assumes
discrete formal smoothness and lifts modulo the completeness ideal itself; it
does not cover adic formal smoothness or a separate closed ideal `J`.

No Lean was written or built. No prior node or import became unnecessary, and
I found no error in the statement, unit route, or source.

## Review by E1

I read More on Algebra Lemma 07NJ (`lemma-lift-continuous`) and its proof in `more-algebra.tex`. The item has precisely the source's adic formal smoothness, complete target, closed ideal, containment J^t in I, and continuous quotient map; the explicit r and t in its conclusion express the source's final continuity argument. There are no new nodes, so B1-B7 and C5 have no new-node case. The three cited definition statements were opened and match the notions used.

Step 1 uses the quotient and completeness definitions: closedness gives injectivity, and representative adjustment followed by completeness gives surjectivity of A/J to the inverse limit. Step 2 writes the fiber-product ideal calculation and checks the kernel square using b>=1. Step 3 uses exactly the square-zero lifting property in `formally-smooth-adic`; the square of a killed power is killed by each lift, so the maps remain eligible for the next lift. The prescribed first row and constructed first column make the induction on a+b well-founded. Step 4 uses J^t in I to identify each diagonal quotient with A/I^b and completeness to take the limit. Step 5 checks equality modulo J by the injectivity from step 1. Step 6 expands (I+J)^t and obtains f(n^(rt)) in I, including t=1. These are the source's steps with its omitted ideal calculations made explicit, and no step borrows an uncited lemma or a node proof. I found no A-F issue to return to the worker; no mathematical revision was needed.
