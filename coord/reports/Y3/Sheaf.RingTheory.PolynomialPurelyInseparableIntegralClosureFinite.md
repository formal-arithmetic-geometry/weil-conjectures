## What changed

Replaced the one sorry in
`finite_polynomial_purelyInseparable_integralClosure` by a complete Lean reduction.
Its signature, universe, visibility and existing docstring are unchanged.

Added the proof-only import `Sheaf.RingTheory.PurelyInseparablePolynomialCover` and
`Mathlib.RingTheory.Polynomial.IsIntegral`. Added the proved private helper
`finite_adjoin_coefficients_and_integral`: finite coefficient algebras and one integral
element generate a finite algebra over the larger Noetherian base.

The new cover theorem gives a finite coefficient field E, a positive integer q, and a
ring embedding into `FractionRing (Polynomial (integralClosure R E))`, with the exact
coefficient map and substitution X ↦ T^q. It assumes neither Japanese finiteness,
Noetherianity, nor normality of R, and asserts no module-finiteness conclusion. Thus it
is strictly the geometric field-cover part of the argument, not a renamed restatement.

The main proof now proves the rest: it applies the Japanese hypothesis to E, constructs
the substitution algebra structure, proves the variable integral using
`IsIntegral.of_pow`, proves polynomial-cover finiteness using finite integral algebra
generators and polynomial induction, identifies the normal cover's integral closure
using `IsIntegralClosure.equiv`, and descends finiteness along an injective linear map.

Updated the original DAG node's proof, proof_deps and proof_origin to match this proof;
added one DAG node and module for the cover theorem. No definitions, existing
statements, target declarations or other modules were changed. No forced adaptations.

Both modules compile with no warnings using lcompile.py. Proof imports were minimized:
separate imports of FiniteType, Polynomial.Basic and Noetherian.Basic were tested and
removed because Polynomial.IsIntegral already supplies their required declarations.

## Proved and sorry left

Closed the original hole in `finite_polynomial_purelyInseparable_integralClosure`
(node `lem-weil-pbc-polynomial-purely-inseparable-closure-finite`). Its proof is complete
and its module contains no sorry. The private helper
`finite_adjoin_coefficients_and_integral` is also fully proved.

Added one hole, `exists_purelyInseparable_polynomial_cover`, in the new module
`Sheaf.RingTheory.PurelyInseparablePolynomialCover`, node
`lem-weil-pbc-purely-inseparable-polynomial-cover`. This is the only sorry left by this
delivery. It has its source and a complete proof in words in both its docstring and node.

This delivery is a decomposition, not a proof free of all sorry dependencies:
one original hole closed, one strictly smaller geometric cover hole added; net zero.
All normality, integral finite generation and Noetherian descent are proved from Mathlib.
No data definition chooses an arbitrary witness from the unproved cover theorem;
the existential fields are used only inside the proposition's proof.

Edge cases checked mathematically: for L=F use E=Frac(R), q=1 and the canonical
fraction-field embedding; imperfect coefficient fields require only roots of finitely
many coefficients, not their entire perfect closure; a field R causes no obstruction;
q=0 is excluded and q=1 is supported by the integral-power argument. The cover's
commutation equation explicitly preserves the given R[X]-algebra structure on L.

## No longer needed

No original import was removed. No whole module is claimed pruned.

The rational-function, algebraic-closure, Frobenius, purely-inseparable and
finite-dimensional-domain-is-field dependencies of the old node now belong to the
new coefficient-root cover node, rather than to the main theorem's combining proof.
They remain needed transitively, so moving these edges is not counted as pruning.
The remaining main dependencies are Japanese finiteness, normality of integral
closures and polynomials, finite integral generators, finite-module transitivity,
and Noetherianity/submodule finiteness. The definition of normality remains in the original signature; the other removed
main-node edges are needed in the cover argument. Pruned modules: none. No unit statement or realized unit step is bypassed.

For completeness, these are every old `proof_deps` entry removed from the main node:
`def-weil-rational-function-field`, `def-weil-pbc-finite-purely-inseparable-extension`,
`def-weil-algebraic-closure`, `def-weil-ring-frobenius`,
`lem-weil-pbc-finite-dimensional-domain-is-field`, `def-weil-algebraic-element`, and
`def-weil-pbc-normal-ring`. The first six now occur in the cover node's `proof_deps`;
normality is an existing statement dependency and is implemented by the retained
integral-closure and polynomial-normality lemmas in the combining proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature mismatch was found. The original plan's main theorem
is too large for a short direct proof, but its final three steps can be completed using
Mathlib once the coefficient-root embedding is exposed with a precise substitution map.
The generator step uses the finite-integral-generators theorem rather than an explicit
list of generators a_j T^r. This is the same finiteness argument below the unit level.

Existing CoefficientRootExtension and FiniteRootedExtension results were inspected.
They root coefficients/constants and independent variables at exponent p, but do not
state the arbitrary-exponent field-cover embedding needed here. The new node does not
repeat either statement; those results may help its future proof.

LeanSearch returned Internal Server Error; this is recorded as unavailable, with no
absence verdict. LeanFinder, Loogle and source searches found no direct cover theorem.
The named literature file is absent in this read-only checkout. The source was read
from the official Stacks page https://stacks.math.columbia.edu/tag/032O.
WANTED: literature/stacks-project/algebra.tex, Tag 032O, for the new cover node.
The source itself omits the coefficient-root details; the new docstring and node expand
these details, including finite coefficient extension, nonzero denominator, Frobenius
injectivity, transcendence, fraction-field identification, and universe preservation.

## New nodes

`lem-weil-pbc-purely-inseparable-polynomial-cover`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-purely-inseparable-polynomial-cover.json`,
states the coefficient-root embedding as
`exists_purelyInseparable_polynomial_cover` in
`lean/Sheaf/RingTheory/PurelyInseparablePolynomialCover.lean`.
It is exactly the cover portion of the original node's first step, with the fraction-field
identification from its second step, and makes no normalization-finiteness assertion.
The normality calculation and finiteness are handled by the complete main Lean proof.
There are no change records because no existing statement, definition or public import changed.


## Second reading by Y3

1. **Existing interfaces: PASS.** Compared the main module with the repository using
   `diff -u`. Its existing theorem signature is byte for byte unchanged, as are its
   universe, visibility and docstring. Its five original public imports are unchanged.
   Only a private proved helper, two plain proof imports and the proof body were added.
   The cover is a new module; no existing definitions or target statements changed.
   The existing node differs only in `proof`, `proof_deps` and `proof_origin`.

2. **Proof and trust: PASS, with the reported open cover dependency.** Both modules
   compiled cleanly in import order through `lcompile.py`. Scratch-copy `#print axioms`
   checks give only `propext`, `Classical.choice`, `Quot.sound` for the private helper;
   the main theorem and the cover additionally use `sorryAx`, accounted for by the
   single named cover theorem. Text inspection finds exactly that one `sorry`, and
   no forbidden declarations or data definitions. Existential coefficient fields and
   their structures are eliminated inside a theorem proof, not used to define data.
   Reviewed the scalar towers, the substitution map, the integral-power argument,
   finite adjoin, polynomial induction, normal integral-closure equivalence and the
   injective linear descent. They establish the original conclusion.

3. **Split-off statement: PASS.** The cover is a strictly smaller geometric part of
   the source proof: it assumes neither Noetherianity, normality nor the Japanese
   property and asserts no module finiteness. Checked the trivial extension with
   q=1, field bases, imperfect coefficient fields and nonnormal domains. For the latter,
   the fraction-field property of the integral closure still follows by scaling an
   algebraic element by a nonzero coefficient denominator; normality of R is unnecessary.
   A finite basis gives a common p-power; finitely many rooted coefficients give finite
   E, and Frobenius injectivity embeds L in E(t). The docstring and node explain these
   steps and denominator nonvanishing. Read Stacks Tag 032O directly at
   https://stacks.math.columbia.edu/tag/032O and checked the matching Mathlib
   fraction-field lemma. Independent LeanFinder query about an algebraic function field
   and finite extension of constants, Loogle `RatFunc, IsPurelyInseparable`, and grep
   `RatFunc|FunctionField` in Mathlib's purely-inseparable directory found no direct cover.
   Inspected the proved CoefficientRootExtension and FiniteRootedExtension statements:
   they supply one-step root constructions, not this arbitrary-exponent embedding.
   Closing the cover would require a substantial new field-construction proof, rather
   than a short application of those declarations.

4. **Route and pruning: PASS after report repair.** The combining proof uses Mathlib
   for every part after the field cover. The five original public imports supply
   signature notions; the two added imports are plain proof imports. Narrowed the new
   cover's public integral-closure import from `IntegrallyClosed` to `Algebra.Basic`
   and `Localization.FractionRing`, which provide only the required statement notions.
   Listed all seven old dependency edges removed from the main node under
   `No longer needed`, with their continuing roles. No whole module is pruned.
   Read `dag/units/sk-thm-p1.json`: neither the item nor the cover is a realized unit
   statement or step, and the unit's required route is retained.

5. **DAG correspondence: PASS.** The main node's four steps follow the written Lean
   reduction, and its `proof_deps` equals their union. The new node has its source,
   complete proof plan, searches, `split` status, creator, blueprint, chapter, unit and
   exact Lean signature. Its proof-dependency union matches its steps. No dependency
   of the main combining proof silently moved into an unreported hole.

Second reading changed only the new cover's imports and this report: narrowed the
integral-closure import, made the removed dependency list explicit, and recorded the
independent checks. No proof body or existing signature required repair. This remains
one hole closed and one strictly smaller hole added, a decomposition with net zero.
