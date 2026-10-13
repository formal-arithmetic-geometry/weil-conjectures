## What changed

Completed the proof of
`FieldTheory.triangularFieldModelEquations_isWeaklyRegular` in
`Sheaf.FieldTheory.TriangularFieldModelWeakRegularity`, with its signature unchanged.
The saved private helpers `monic_mul_mem_extended_ideal` and
`fresh_monic_mul_mem_extended_ideal` are now used by the main proof.
The proof-only imports are `Mathlib.Algebra.MvPolynomial.Equiv` and
`Mathlib.RingTheory.Polynomial.Basic`; all original public imports are preserved.
Updated the existing node's proof, proof_deps and proof_origin to the implemented route.

For each positive index, the prefix ideal is the extension of its comap to the
polynomial ring in earlier variables. Every prefix generator has an explicit
preimage, verified by polynomial evaluation and composition of renamings.
Isolating the fresh variable turns the next monic equation into a monic polynomial
whose coefficient ring can be reduced modulo the prefix ideal. Monic cancellation
then proves the required injectivity on the quotient. The first equation is
nonzero because evaluating all variables at zero gives -1; domain cancellation
handles the empty prefix. No localization presentation is needed.

## Proved and sorry left

Holes closed: one, `FieldTheory.triangularFieldModelEquations_isWeaklyRegular`
(node `lem-weil-pbc-triangular-field-model-weak-regularity`).
Holes added: zero. Sorries left in the delivery: none.
Both private helpers are fully proved. The assigned module compiles through
lcompile.py without errors or warnings. The required deliver3.py --no-push dry run printed OK: compilation, the
axiom probe and preflight passed except for the second reading, which the
independent second reader writes. Nothing was pushed.

The proof covers r=0 and d=0, constant monic equations equal to one, and zero
successive quotients. The generic cancellation helpers allow the unit ideal,
zero coefficient rings, and noninjective variable maps that avoid the fresh
variable. No objects are chosen from an unproved existence theorem.

## No longer needed

Removed imports: none; the original module did not import the localization plan.
The proof no longer needs the following nodes, removed from proof_deps:
`lem-weil-pbc-localization-away-polynomial-quotient` (Mathlib localization quotient
presentation) and `def-weil-ring-localization-away` (Localization.Away).
Their proof imports `Mathlib.RingTheory.MvPolynomial.Localization` and
`Mathlib.GroupTheory.MonoidLocalization.Away` are not added. No Sheaf module is
pruned by name: both nodes already refer to Mathlib. All other original proof
nodes remain used. The unit sk-thm-p1's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The prior attempts were blocked by the missing compiled dependency
`Sheaf.FieldTheory.TriangularFieldModelEquations`. That dependency is now available
in the shared build, and the assigned module compiles normally. No dependency was
copied, recreated or compiled as a workaround.

The DAG's localization quotient route was mathematically valid but unnecessary.
Direct cancellation modulo extended ideals is shorter and avoids the isomorphism
glue. The hypothesis hh (h nonzero) is stronger than this particular proof needs:
hT-1 is nonzero even when h=0. The original hypothesis and full signature are
preserved. No statement, definition, target, or other module was changed.

## Second reading by A3

1. Interface: PASS. Diffed the sole delivered Lean module against the repository.
   The existing theorem signature is byte for byte identical, including `Field k`,
   both natural-number parameters, the dependent coefficient rings of `p`, `hh`,
   `hp`, and the full `IsWeaklyRegular` conclusion. No definition, visibility,
   original public import, or existing docstring changed. Both added helpers are
   private proof lemmas; both added imports are plain proof-only imports. There
   are no change records or adaptations because there is no interface change.
2. Proof: PASS. Independently compiled the module with `lcompile.py`, without
   errors or warnings. A scratch copy with `#print axioms` for both helpers and
   the main theorem reports exactly `propext`, `Classical.choice`, `Quot.sound`
   for each, with no `sorryAx`. Checked the entire delivered module: no `sorry`,
   forbidden trust construct, or hollow definition. The first helper passes to
   the polynomial coefficient quotient using `Polynomial.ker_mapRingHom`, then
   applies `Monic.mul_right_eq_zero_iff`. The second explicitly isolates `t`
   through `optionSubtypeNe` and `optionEquivLeft`, transports the extended
   ideal and evaluated equation, and transports cancellation back. The main
   proof constructs preimages of every prefix generator and uses the resulting
   map-comap equality; no arbitrary witness is taken from an unproved theorem.
3. Split statements: PASS, none. Both private helpers are fully proved and
   strictly intermediate. Checked their generality: the unit ideal and zero
   coefficient ring cause no exception, and a noninjective variable map is
   permitted because only avoidance of `t` is needed. For the main theorem,
   `r=0` leaves only the nonzero first equation; `d=0` still has variable `T`;
   `p_i=1` makes a later quotient zero, which weak regularity permits. The
   retained `hh` is unused mathematically but has not been dropped.
4. Route and pruning: PASS. Searched Mathlib and both Lean roots with the
   alternate phrases `monic.*ideal`, `Monic.*regular`, and polynomial weak
   regularity; also ran Loogle through `msearch.py` with
   `Polynomial.Monic, Ideal.map`. Its four results concern Eisenstein bounds,
   integral equations, and maximal polynomial ideals, not this cancellation
   argument. Inspected the upstream tensor diagonal theorem and polynomial
   local descent theorem: their flatness/localization hypotheses do not give
   this arbitrary triangular list. The proof already uses Mathlib's monic
   cancellation and polynomial-map kernel lemmas. The two added imports supply
   the fresh-variable equivalence and kernel theorem. Original public imports
   supply the equation definition, monicity in the signature, and weak
   regularity. The no-longer-needed section lists exactly the two removed old
   proof dependencies. Inspected `dag/units/sk-thm-p1.json`: neither removed
   dependency realizes a unit statement or step; the realized route stays.
5. DAG: PASS. Diffed the existing node: only `proof`, `proof_deps`, and
   `proof_origin` changed. The union of the steps' `uses` equals `proof_deps`.
   Step 1 matches evaluation at zero and domain cancellation; step 2 matches
   the explicit prefix-generator preimages; step 3 matches the fresh-variable
   and coefficient-quotient cancellation helpers; step 4 matches the quotient
   regularity criterion. The original statement and Lean record are unchanged.
   No new nodes or new open statements need metadata.

Changes by this second reading: added this independent review and ran the
signature, line-width, node-field, dependency-union, compilation, search, and
axiom checks. No correction to the Lean proof or DAG was needed. Confirmed net
holes closed in this delivery: one; holes added: zero.
