## What changed

Proved `RingTheory.flat_polynomial_local_quotient_of_finiteType_subrings` with its signature
unchanged. Added two proved private helpers in the same module: `finite_polynomials_stage`
constructs a finite coefficient subring by adjoining finitely many scalars and polynomial
coefficients; `finite_relation_stage` clears denominators and detects a finite relation modulo
the equations in that subring. The main proof uses the forward and backward Mathlib equational
criterion and explicitly constructs the induced quotient map and checks scalar compatibility.
All constructions are proved; no definition chooses data from an unproved existence theorem.

Added proof imports `Mathlib.RingTheory.Flat.EquationalCriterion`,
`Mathlib.RingTheory.Localization.Integer`, and `Mathlib.RingTheory.Localization.Ideal`.
Updated the existing node's proof, proof_deps, and proof_origin to match this direct version
of the finite-coefficient argument. The node is below the unit's realized steps, so no unit
statement or required unit step is bypassed.

## Proved and sorry left

Closed the only original hole, `RingTheory.flat_polynomial_local_quotient_of_finiteType_subrings`
(node `lem-weil-pbc-polynomial-local-flat-quotient-descent`). Both private helpers are fully proved.
No sorry remains in the delivered module, and no new hole or module is added.
This is a complete proof, not a decomposition. Local single-file compilation succeeds without
warnings. The argument includes empty finite relations and equation lists, arbitrary prefix
lengths, zero quotients, and coefficient rings with zero divisors; it never assumes the
localized coefficient inclusion is injective.

## No longer needed

Removed proof import `Sheaf.RingTheory.DirectedUnionSubringsFlatModule` and the corresponding
proof dependency `lem-weil-pbc-directed-union-subrings-flat-module`. The general directed index,
transition maps, representation and eventual-zero interfaces are unnecessary for this item:
the proof detects each finite relation in a single explicitly constructed stage instead.
The Mathlib leaf `lem-weil-pbc-flat-equational-criterion` replaces that dependency.
All original public imports remain because they form the existing statement interface.
No other project module or node is newly required. Whether the removed module remains reachable
through other targets is for the global import-closure calculation to determine.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original directed-system plan can be shortened
to direct finite-relation descent, using the same equational criterion as the already proved
05UU (2) lemma. Search via LeanFinder found only fixed-ring localization flatness tools;
Loogle found no combined polynomial-map/localization declaration; source grep found the
common denominator, localized ideal membership, and equational criterion lemmas used here.
The finite-polynomial adjoin argument follows the proved helper in
`Sheaf.RingTheory.PolynomialLocalIdealRelationFiniteStage`, generalized here to include scalar
coefficients; that unrelated module is not imported. There are no forced adaptations or new nodes.

## Second reading by M2

1. Compared the complete delivered module against the repository with `diff` and compared
   the extracted existing signature byte for byte: unchanged. No existing definition,
   visibility, hypothesis, universe, equation list, or conclusion changes. The only new
   declarations are two private, fully proved helper theorems. No change record is required.
2. Read the entire proof and compiled it with `lcompile.py`: no errors or warnings.
   Checked the source for sorry, axiom, unsafe, opaque, implemented_by, extern and kernel
   checking bypasses: none. Scratch `#print axioms` checks cover both private helpers and
   the public theorem; each depends only on propext, Classical.choice and Quot.sound.
   The finite subring is explicitly Algebra.adjoin; all representative choices come from
   proved surjectivity, common-denominator or polynomial coefficient-range theorems.
3. No statement is split off and no hole is added. Checked both helper statements against
   their proofs: finite sets can be empty, the relation index can be Fin 0, the prefix can
   be empty or longer than the equations, and the quotient can be zero. The contracted
   prime remains prime without any additional hypothesis; denominator avoidance follows
   from its definition. The only injectivity used is MvPolynomial.map of B.subtype,
   which follows from subtype injectivity, not injectivity of a localization map.
4. Read [Stacks 00SV](https://stacks.math.columbia.edu/tag/00SV), second proof paragraph,
   [05UU (2)](https://stacks.math.columbia.edu/tag/05UU), and
   [00HK](https://stacks.math.columbia.edu/tag/00HK), and the pinned Mathlib equational
   criterion. The code directly realizes finite-coefficient descent: common denominator,
   polynomial ideal membership, finite adjoin, quotient map, scalar compatibility, then
   stage trivialization and transport of its matrix equations. Independent LeanFinder
   search for descent of finite linear relations and grep for flat finite-type/subring
   results found no shorter applicable theorem. Repository search and reading
   PolynomialLocalIdealRelationFiniteStage found only a single multiplicative relation
   lemma, insufficient for simultaneous finite linear relations. Imports for the criterion,
   common denominators and localized ideal membership are proof-only; public imports
   supply the unchanged statement interface, including Ideal.ofList. The only removed
   old proof dependency is DirectedUnionSubringsFlatModule, already reported above.
   Opened dag/units/sk-thm-p1.json: neither this node nor the removed general directed-union
   helper realizes a required unit statement or step. The unit route is preserved.
5. Compared the node JSONs: exactly proof, proof_deps and proof_origin change. Read every
   updated proof step and checked its cited declaration or Mathlib match. Their union is
   the recorded proof_deps. The flat-equational-criterion leaf names both directions used
   here; finite-type, polynomial and localization nodes supply the other recorded notions.
   The public node statement and its stored Lean signature agree with the unchanged theorem.
   No new node is required and no new-node metadata is introduced.

Changed the public theorem's stale natural-language proof: it described applying the
removed directed-union theorem. It now describes the actual common-denominator,
finite-relation and equational-criterion argument. No proof term or statement was changed
by the second reading. Closed one original hole, added zero holes, split off zero statements.
