## What changed

Replaced the proof of `MvPolynomial.ideal_coefficients_monomial_map` without changing
its signature or the public imports. Added proof imports
`Mathlib.LinearAlgebra.DFinsupp`, `Mathlib.LinearAlgebra.Isomorphisms`, and
`Sheaf.Paper.PolynomialIdealCoefficientsMonomialMembership`.

The polynomial coefficient linear equivalence, followed by
`finsuppLequivDFinsupp`, identifies polynomials with the constant dependent direct
sum. `DFinsupp.mapRange.linearMap` applies each ideal quotient map componentwise.
The coefficient formula is definitional. Surjectivity follows from
`DFinsupp.mapRange_surjective`, component quotient surjectivity, and the coefficient
equivalence. The existing membership theorem identifies the kernel by checking
each quotient coefficient is zero. Scalar restriction, quotient congruence, and
`LinearMap.quotKerEquivOfSurjective` give the requested equivalence; its formula on
quotient representatives is definitional.

This implements both existing DAG proof steps, using exactly its existing proof
dependency `new-polynomial-ideal-coefficients-membership`. The route and node need
no change. The item's node is below the unit's realized statements and steps, so
this does not bypass a unit step. The direct-sum description matches the paragraph
of [Stacks Tag 07DW](https://stacks.math.columbia.edu/tag/07DW) beginning with the
polynomial quotient as an R-module. The local literature file is absent on this
machine; that paragraph was read on the Stacks website.

## Proved and sorry left

Closed the sole local hole, `MvPolynomial.ideal_coefficients_monomial_map`
(node `new-polynomial-ideal-coefficients-map`). No holes added or split off, and no
`sorry` remains in the delivered module.

The proof still depends on the existing, undelivered theorem
`MvPolynomial.ideal_coefficients_monomial_membership`
(node `new-polynomial-ideal-coefficients-membership`), which contains `sorry`.
Thus this is a proof from the stated dependency, not an axiom-free completion of
the full import closure.

The construction works also when `i = 0`, all generators vanish, or a coefficient
ideal is the unit ideal: component quotient surjectivity and the membership
criterion handle all those cases without additional assumptions.

## No longer needed

None. No original imports, nodes, or modules are pruned. All three added proof
imports are used. Removing `Mathlib.LinearAlgebra.Isomorphisms` was tested and
made `LinearMap.quotKerEquivOfSurjective` unavailable; it was restored.

## Where the brief, the DAG or earlier work was wrong

The module originally lacked its DAG proof-dependency import; this delivery adds
it. Otherwise the statement and proof plan fit unchanged. No interface changes,
forced adaptations, or new nodes were necessary.

## Second reading by T1

1. Compared the delivered module with the repository using `diff -u` and an exact
   text assertion on the theorem signature: byte-for-byte unchanged. Only the
   proof and three private proof imports differ. No definitions, public imports,
   existing signatures, change records, or other modules are changed. PASS.
2. Compiled the delivered module locally with `lcompile.py`: no errors or
   warnings. Scanned for forbidden declarations and holes: none. A scratch copy
   with `#print axioms MvPolynomial.ideal_coefficients_monomial_map` reports
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last
   comes from the existing membership theorem, as disclosed above. The
   coefficient map is constructed explicitly, not chosen from an unproved
   existence theorem. The quotient equivalence uses the identified kernel and
   the proved surjectivity, which determine its action on every representative. PASS.
3. No statements were split off or new nodes added. Read the existing membership
   dependency and checked its relevance and edge cases: with no generators, or
   all generators zero, both ideals are zero; a unit generator kills exactly
   the coefficients whose exponent involves that variable. This existing hole
   is not duplicated, altered, or delivered. PASS.
4. Read the proof from coefficient construction through surjectivity, kernel
   identification, and the first isomorphism theorem. Searched the library with
   coefficient/ideal and quotient/coefficient terms and inspected Mathlib's
   monomial-ideal lemmas: those concern monic generators and do not replace
   the arbitrary scalar coefficient criterion here. Confirmed the componentwise
   surjectivity API with an independent Loogle query for
   `DFinsupp.mapRange_surjective`. The three private imports supply used APIs;
   a scratch compile without `Mathlib.LinearAlgebra.DFinsupp` fails on
   `finsuppLequivDFinsupp`, and the first reader's Isomorphisms removal check
   agrees with its defining the quotient equivalence API. The sole old
   proof dependency is still used, so `No longer needed: None` is complete.
   Read `dag/units/sk-thm-p1.json`: neither this node nor its dependency is a
   realized unit statement or step; the local reduction preserves the route. PASS.
5. Read both existing DAG nodes: the map node's first step is the concrete
   coefficient/direct-sum construction, and its second step uses exactly
   `new-polynomial-ideal-coefficients-membership` followed by the module
   isomorphism theorem. Its `proof`, `proof_deps`, and `proof_origin` already
   agree with this proof; no node edit is necessary. PASS.

Second reading changed only this report by adding the review record. No Lean
repair was needed. One existing local hole closed, zero holes added, zero
statements split off, and no modules or nodes pruned.
