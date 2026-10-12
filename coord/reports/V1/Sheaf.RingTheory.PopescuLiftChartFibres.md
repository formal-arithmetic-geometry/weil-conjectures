## What changed

Replaced the sorry in `Algebra.popescu_lift_chart_fibres` with a complete proof combining
two structural polynomial-chart identifications. The existing declaration's signature,
visibility, and docstring are unchanged. Its proof imports two new modules privately:
`Sheaf.RingTheory.PopescuSpecialChartPolynomial` and
`Sheaf.RingTheory.PopescuZeroBaseChartPolynomial`.

The proof lifts the chart element through the quotient projection, proves pi belongs
to the contracted prime and vanishes in its residue field, and constructs the compatible
R/(pi squared)-algebra structure on that field by the quotient universal property.
The inverse law for `PrimeSpectrum.preimageEquivFiber` identifies contraction of the
fibre prime, so the image of the chart lift avoids it. The arbitrary-base polynomial
model, `Prepared.smooth`, smooth base change, polynomial smoothness, and smooth composition
then supply the fibre localization witness. Independently, principal localization and
polynomial smoothness applied to the C0-algebra model supply the special-fibre clause.
Every smoothness combination and every prime-membership argument is written in Lean.

Added one statement per new module and its DAG node, with a source and a complete
substitution proof in words. Updated the original node's proof and proof dependencies
so its route agrees with the Lean proof. No existing statement, definition, public
import, target, or other group's module was changed. The unit record `sk-thm-p1`
contains no realization by this item, and its statement and steps remain intact.

Source read: Stacks Project Tag 07CP, especially the displayed calculation of
(D_k/pi D_k)[1/a_k], the coefficient comparison of charts, and the residue-field
base change in the following paragraph. Searches included LeanFinder, Loogle,
Mathlib/source-library/Sheaf grep, and the blueprint search. LeanSearch returned
Internal Server Error; this is recorded as unavailable, not as an absence verdict.

## Proved and sorry left

Closed the original hole `Algebra.popescu_lift_chart_fibres`
(node `lem-weil-pbc-popescu-lift-chart-fibres`). No sorry remains in the item's module.

Added exactly two holes, each the entire proof of a named public theorem:

- `Algebra.popescu_special_chart_polynomial`, node
  `lem-weil-pbc-popescu-special-chart-polynomial`, module
  `Sheaf.RingTheory.PopescuSpecialChartPolynomial`.
- `Algebra.popescu_zero_base_chart_polynomial`, node
  `lem-weil-pbc-popescu-zero-base-chart-polynomial`, module
  `Sheaf.RingTheory.PopescuZeroBaseChartPolynomial`.

This is a decomposition: one original hole closed and two structural holes added,
net minus one. It is not an unconditional proof of the mathematical theorem.
Both new statements identify explicit algebras and have no IsSmoothAtPrime conclusion;
the special model has no prime or nonmembership hypotheses, and the scalar-extension
model concerns every commutative base killing pi, with no field or prime hypothesis.
The actual smoothness deductions and residue-prime witness are proved in the original
module rather than delegated to a restatement of either smoothness clause.

All three sandbox modules compile through lcompile.py. No proof in a definition,
private sorry, axiom, or interface adaptation was introduced. Quotient representatives
and isomorphisms are eliminated only in proofs of propositions; no definition chooses
arbitrary data from an unproved existence theorem.

## No longer needed

Removed the redundant private import `Sheaf.RingTheory.SingularIdeal`: the presentation
module already publicly imports it. The presentation module is needed by the statement,
and the residue-field fibre module is needed by both statement and proof.
No existing module is pruned. The original node's direct computational dependence on
`def-weil-pbc-module-localization-away` moves into the two structural model nodes;
it remains needed there and is not claimed as global pruning. All other original
proof dependencies remain needed in the main proof or the new models.

Removed the initially redundant public fibre import from both new modules; their
statements elaborate using the presentation module's existing public dependencies.
No extra generic Mathlib or source-library imports were retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original node's first three steps
were a plan for a substantial quotient calculation, rather than existing declarations
identifying that quotient. That is the work now exposed by the two polynomial-model
items. The source's later annihilator argument concerns lifting the chart comparison
back from modulo pi; it is not required for either of these modulo-pi models.

Edge cases checked before stating the models: E_k empty gives a polynomial algebra on
an empty type (the coefficient ring); m=0 gives the same coefficient chart with no
auxiliary variables; r=0 supplies no k and hence makes no assertion; a_k=0 yields
zero localizations on both sides; pi a unit forces the coefficient quotient and every
base killing pi to be zero. Neither statement excludes these cases or imposes
nontriviality. The normalized coefficients and the conormal basis are essential to
eliminating the complementary variables and proving redundancy of other charts.

The blueprint ancestor script reported None for this newly created module-backed
node. The new nodes retain the explicit existing blueprint ancestry recorded on the
item (`thm-weil-pbc-finite-etale-lifting`), with this item prepended to the via chain.
No blueprint or unit route is changed.

## New nodes

`lem-weil-pbc-popescu-special-chart-polynomial` identifies D0 localized on chart k,
as a C0-algebra through the specified cmod, with the polynomial algebra on E_k over
C0 localized at the coefficient a_k. Its proof is the elimination of complementary
z variables and the conormal coefficient calculation of Tag 07CP, including the
compatibility checks hc and hcmod. It enables the special-fibre smoothness conclusion
using principal-localization, polynomial, and composition smoothness.

`lem-weil-pbc-popescu-zero-base-chart-polynomial` identifies the localized scalar
extension B tensor_R D, for any compatible R/(pi squared)-algebra B killing pi,
with the polynomial algebra on E_k over B tensor_{R/(pi squared)} the prepared
reduced coefficient chart. Its proof makes explicit why any lift s of the specified
chart element has the same image after scalar extension, and repeats the quotient
calculation after killing pi. It enables direct use of `Prepared.smooth` and smooth
base change without introducing another smoothness or prime statement.

Both nodes record the searches; none of the search results identifies the quotient
with all chart relations. There are no change records or forced adaptations.

## Second reading by V1

1. Interface: compared every delivered module with the repository. The only existing
   module differs in its proof and private imports; the existing signature and docstring
   are byte for byte identical. Neither new module exists in the repository. No definition,
   public import, target statement, or forced adaptation changes. Verdict: pass.
2. Proof: independently compiled the three modules in import order using lcompile.py.
   The main theorem contains no sorry; the only delivered holes are the two named public
   model theorems listed above, with complete docstring arguments. Explicit #print axioms
   checks show only propext, Classical.choice, Quot.sound and sorryAx. No forbidden
   declaration or data-producing definition was added. Quotient representatives and model
   equivalences are eliminated inside a proposition proof. Verdict: valid conditional
   reduction, not an unconditional proof.
3. Split statements: read Prepared, its explicit quotient equations, and the calculation
   and coefficient comparison in [Stacks Tag 07CP](https://stacks.math.columbia.edu/tag/07CP).
   The cleared relations give sum b_j f_j = 0 in the reduced conormal module. Its specified
   basis forces the localized coefficients b_j to vanish; clearing denominators puts them
   in (f_l, pi squared). After killing pi, substitution for complementary z_l therefore
   kills all other charts' relations. Surjectivity and kernel of epsilon identify the
   coefficient algebra, and hc and hcmod identify its structural map. For arbitrary B,
   pi=0 also kills the difference between s and the original a_k lift; the same substitution
   survives scalar extension without a flatness assumption. Empty E_k and m=0 give the
   coefficient ring; r=0 has no k; a_k=0 makes both localizations zero; pi a unit forces
   every base killing pi to be zero. Both statements are true structural parts of the
   argument, rather than renamed smoothness conclusions. Repeated LeanFinder search for
   algebra equivalences after eliminating dependent generators, Loogle `MvPolynomial,
   AlgEquiv`, and source grep using variable elimination and conormal terminology.
   Presentation.quotientEquiv, renameEquiv, and mapAlgEquiv provide generic ingredients,
   not either prepared-chart calculation. Read the nearby desingularization inverted
   quotient and linear-equation localization formula: neither matches these relations.
   No split can be closed in a few minutes using these results. Verdict: pass.
4. Route and pruning: checked the actual nonmembership witness, quotient base map,
   Prepared.smooth, polynomial smoothness, base change, composition and transport through
   the two equivalences. Imports are needed for signatures or these two structural steps.
   The old proof dependency def-weil-pbc-module-localization-away is the only removed
   direct dependency and is explicitly reported as moving to the new nodes. The redundant
   SingularIdeal import removal is now recorded; that module remains transitively needed.
   sk-thm-p1.realized does not name this item, and no realized node or unit step is bypassed.
   Verdict: pass; no globally pruned module.
5. DAG: verified all three verbatim Lean statement records, proof_deps as the union of
   proof-step uses, unchanged source-based proof_origin, new-node source/search/creation/
   ancestry records and shared chapter/unit. The existing node changes only proof and
   proof_deps. Its proof steps follow the Lean reduction; the new nodes contain exactly
   the two remaining structural calculations. Verdict: pass.

Second-reading repair: corrected the inaccurate claim that no original import was
removed. No Lean proof, signature, split statement, or node required modification.
This delivery closes one of one original holes and adds two; its net is minus one and
it is a decomposition.
