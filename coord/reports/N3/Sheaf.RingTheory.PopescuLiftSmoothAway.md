## What changed

Proved `Algebra.popescu_lift_smooth_away` in
`Sheaf.RingTheory.PopescuLiftSmoothAway` without changing its signature or docstring.
The proof explicitly substitutes the auxiliary variables by pi inverse times the original
relations, descends through the defining ideal and ULift, extends both maps to principal
localizations, and verifies both composites. Mathlib supplies polynomial smoothness,
principal-localization smoothness, composition, and transport across the resulting equivalence.
Added the proof-only import `Mathlib.Tactic.Ring`.

Updated the existing node's proof steps to describe the implemented substitution argument.
Its source, statement, unit route and proof dependencies are unchanged. No definitions,
interfaces, target statements, or other modules were changed.

## Proved and sorry left

Closed the single original hole: `Algebra.popescu_lift_smooth_away`
(node `lem-weil-pbc-popescu-lift-smooth-away`). There are no remaining holes in the item
and no holes added elsewhere: this is a complete proof, not a decomposition.
The proof uses only `hd.relation` from the prepared data; it does not use the unproved
existence theorem `Algebra.exists_popescu_lift_preparation`.

Local compilation passes with no errors or warnings. The argument also covers pi=0
(the localizations are the zero ring), the zero base ring, zero original variables,
zero auxiliary variables, and an empty collection of charts: no cancellation assumes
that pi was a nonzero divisor before localization, and all sums are finite.

## No longer needed

No original imports, nodes or modules were pruned. All original proof dependencies
remain appropriate: preparation, polynomial smoothness, smooth principal localization,
and the smoothness definition. A trial direct import of
`Mathlib.RingTheory.Localization.Away.Basic` was removed as redundant; the existing
statement import already makes its API available.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The source file
`literature/stacks-project/smoothing.tex` is absent from this clone; the proof of
Stacks Tag 07CP was read at https://stacks.math.columbia.edu/tag/07CP.
The node's key-equality step is implemented equivalently by substituting first and
multiplying the cleared relation by the canonical inverse of pi.
Broad simplification using commutativity on the concrete localization expressions
caused excessive unfolding; explicit rewrites eliminated it without changing definitions.
Searches through the launcher used LeanFinder for the quotient-localization statement,
Loogle for `Algebra.Smooth.of_equiv`, and grep for principal-localization equivalences.
They found the supporting APIs but no ready-made result for this prepared quotient.

## Second reading by N3

1. PASS: Compared the complete delivered module and node against the repository with
   `diff -u`. The sole existing declaration's signature and docstring are byte for byte
   unchanged. The only Lean changes are its proof and the private proof import
   `Mathlib.Tactic.Ring`. There are no changed definitions, visibility changes, new
   declarations, change records, or forced adaptations.
2. PASS: Independently compiled the module through `lcompile.py` with no errors or
   warnings (35.9 seconds). Compiled a scratch copy with
   `#print axioms Algebra.popescu_lift_smooth_away`; it reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. No sorry or forbidden declaration is present.
   Checked the substitution, ideal descent, ULift transport, localization extensions,
   both composites, and the orientation of the final smoothness transport. All data
   are explicit; the unproved preparation existence theorem is never invoked.
3. PASS: No statements were split off and no holes were added. Checked the existing
   statement and argument in the cases pi=0, the zero ring, n=0, m=0, r=0 and empty
   E_k. Inverting zero produces the zero ring; the proof never cancels pi in R.
   The only needed prepared condition is the cleared relation, with the correct
   sign and pi squared remainder.
4. PASS: Read the original proof plan, the preparation module and the three Mathlib
   leaf dependencies. Independently searched the library and Mathlib by quotient,
   evaluation-equivalence and localization terminology, and repeated LeanFinder
   with "Localizing a polynomial quotient with relations c times y_i minus f_i at c
   is isomorphic to the localization of the polynomial ring in the remaining variables".
   The closest result, `IsLocalization.Away.mvPolynomialQuotientEquiv`, presents a
   localization by one inverse variable; it does not replace this multiple-relation
   elimination argument. Checked the substitution route against Stacks Tag 07CP,
   key equality and property (b): https://stacks.math.columbia.edu/tag/07CP.
   The public preparation import is needed by the signature, and the ring tactic
   import is proof-only and used. No original dependency is unused; the No longer
   needed list is complete. Read `dag/units/sk-thm-p1.json`, including `realized`:
   this is a component below the unit steps, and no unit step or route is bypassed.
5. PASS: The existing node's four proof steps accurately describe the Lean argument.
   Their uses union equals proof_deps: preparation data, polynomial smoothness,
   principal-localization smoothness and the smoothness definition. The Mathlib
   leaf matches are precisely the instances and smoothness lemmas used at the end.
   The document proof_origin remains correct. All fields outside stage-3 ownership
   are unchanged, and no new nodes need validation.

Second reading changed only this report, adding the independent review and its
verification evidence. No mathematical repair was necessary; the proof and node
were retained unchanged. Holes closed: `Algebra.popescu_lift_smooth_away` (1).
Holes added: none (0). Split off: none. Pruned: none.
