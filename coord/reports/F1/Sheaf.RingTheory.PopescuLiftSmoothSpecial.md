## What changed

Reduced `Algebra.popescu_lift_smooth_special` to two strictly smaller intermediate
arguments in new modules `Sheaf.RingTheory.PopescuLiftChartFibres` and
`Sheaf.RingTheory.PopescuLiftChartFlat`. Its signature, visibility, and existing
docstring are unchanged. There are no changes to existing definitions or interfaces.

The Lean proof first rewrites the two universally quantified implications as a
pointwise conjunction. `Prepared.cover` chooses a chart avoiding the given prime.
The first intermediate theorem supplies the smooth residue-field fibre and a smooth
principal localization of the special fibre, without an annihilator hypothesis.
The second supplies flatness of the canonical local ring map, using the annihilator
hypothesis but asserting no smoothness of the lifting algebra. The proved
`PopescuLiftPresentation.finitePresentation` supplies finite presentation; localization
at 1 supplies the neighbourhood required by `flat_smooth_fibre_smooth_at_prime`.
Applying that existing criterion proves the first clause. The explicit chart element
and the first intermediate theorem's smooth localization witness the second clause
with exactly `cmod.toAlgebra`. Thus the upper proof contains actual composition of
flatness, fibre smoothness and finite presentation, rather than applying a renamed
copy of the original statement.

The new statements are the two unfinished chart calculations from Tag 07CP. Their
modules each contain one public theorem with its full natural-language proof and node.
The node of the original theorem now records the combination used by Lean. The new
flatness node retains the differential-rank and equation-count route of the original
plan, but needs only the local comparison of D_k with D. The new fibre node performs
the extra-relation calculation directly modulo pi, where it needs no annihilator
argument. No unit statement or realized unit step has been bypassed.

## Proved and sorry left

Closed the one explicit hole of the original module:

- `Algebra.popescu_lift_smooth_special`, node
  `lem-weil-pbc-popescu-lift-smooth-special`.

Added these two explicit holes, each exactly `:= by sorry` in its own new module:

- `Algebra.popescu_lift_chart_fibres`, node
  `lem-weil-pbc-popescu-lift-chart-fibres`.
- `Algebra.popescu_lift_chart_flat`, node
  `lem-weil-pbc-popescu-lift-chart-flat`.

This is a decomposition: one upper hole closed, two lower holes added, net minus one
before accounting for pruning. It is not an axiom-free proof of the original theorem.
There are no remaining explicit holes in the original module, no new definitions,
and no changed signatures of existing declarations. Other imported pre-existing holes
are unchanged. All three delivered modules compile together with `lcompile.py`.

Edge cases checked mathematically before stating the new theorems:

- If pi is a unit, D/pi D is the zero ring and has no primes, so both statements are
  vacuous. Neither theorem asserts the existence of a prime or a nonzero ring.
- If pi is zero, the annihilator equality is automatic. Modulo pi, the construction
  on a chart is a polynomial algebra over the smooth coefficient chart, so both the
  fibre smoothness statement and the flatness statement have the expected meaning.
- If there are no charts, there is no `k : Fin d.r`; the original theorem is vacuous
  at a smooth pullback by `Prepared.cover`. There is no hidden nonempty-chart assumption.
- If E_k is empty, all auxiliary variables are eliminated; if E_k contains all
  relations, no complementary variables are eliminated. The equation count is m
  in both cases. The differential-rank computation uses `Prepared.card_le`.
- A zero chart element cannot satisfy `hk`. The statements make no false smoothness
  or flatness claim on an empty basic open.

## No longer needed

Removed these five proof imports from the original module:

- `Sheaf.RingTheory.AnnihilatorElementFlatBaseChange`
- `Sheaf.RingTheory.EquationCountFibreDimensionFlat`
- `Sheaf.RingTheory.ExistsAnnihilatorOfSubsingletonLocalizedModule`
- `Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`
- `Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension`

Four remain needed inside the unfinished chart-flat argument and are imported by
`PopescuLiftChartFlat`; this relocation is not global pruning. The annihilator-of-a-finite-
localized-module import is not reintroduced. Its node
`lem-weil-pbc-finite-module-localization-zero-annihilator` is no longer needed by
this proof or either new subargument. We transfer only local flatness from D_k to D,
and obtain smoothness of D from its own smooth fibre by the existing criterion, so
there is no need to annihilate the finite kernel on a principal neighbourhood.

The old planned uses of `lem-weil-pbc-smooth-ring-map-flat`,
`lem-weil-pbc-localization-flat`, and `lem-weil-pbc-flat-ring-map-comp`
are also unnecessary here: equation-count flatness
already supplies flatness of the chart local ring directly; transport by an algebra
equivalence and restriction along localization require no flat-map composition.
These Mathlib facts may
still be imported transitively or needed elsewhere. All other old dependencies remain
in either the upper proof or the two intermediate arguments. No claim is made that a
module unused here is unreachable from every project target.

For completeness, the following old direct `proof_deps` leave the upper node but
are retained in the two lower chart arguments (relocation, not pruning):

- `def-weil-pbc-flat-ring-map`
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-module-localization-away`
- `def-weil-pbc-smooth-ring-map`
- `lem-weil-pbc-annihilator-element-flat-base-change`
- `lem-weil-pbc-equation-count-fibre-dimension-flat`
- `lem-weil-pbc-kahler-differentials-base-change`
- `lem-weil-pbc-kahler-differentials-localization`
- `lem-weil-pbc-kahler-differentials-polynomial-extension`
- `lem-weil-pbc-polynomial-ring-smooth`
- `lem-weil-pbc-smooth-over-field-dimension-differentials`
- `lem-weil-pbc-smooth-ring-map-base-change-composition`
- `lem-weil-pbc-smooth-ring-map-principal-localization`


## Where the brief, the DAG or earlier work was wrong

The supplied imports state generic ingredients, not the explicit chart quotient,
its local comparison with D, or its special-fibre polynomial description. In particular,
applying equation-count flatness directly to D would count the redundant equations
from every chart, instead of the m equations of D_k. The split preserves this necessary
chart argument and does not pretend the generic imported statements already prove it.

The local copy of `literature/stacks-project/smoothing.tex` is absent. I read the
complete proof of Stacks Tag 07CP (lemma-lifting) at
https://stacks.math.columbia.edu/tag/07CP. The new proofs cite its chart computation,
coefficient comparison and final annihilator argument. No source statement was changed.

`blueprint_refs.py ancestor` prints None for the original item because its `created.item`
is a Lean module name. Its immediate blueprint.from.node also points to another created
node. The new nodes record the actual imported ancestor
`thm-weil-pbc-finite-etale-lifting`, following the existing parent's blueprint metadata,
with the intermediate nodes included in `via`. Existing ownership-restricted blueprint
fields were left untouched. Whole-blueprint searches for the chart construction and
Tag 07CP found no duplicate imported statement.

The required LeanSearch calls returned Internal Server Error; the records say
unavailable, not absence. LeanFinder and Mathlib grep searches ran for both new nodes,
with their actual queries recorded in the sandbox search log and copied into the nodes.
They found generic smoothness, flatness and standard-smoothness ingredients, not the
explicit prepared-quotient statements.

One temporary compile timeout was caused by an underspecified `Ideal.Quotient.mk _`
inside the finite-presentation witness. Giving its contracted prime an explicit type
and avoiding a duplicated pointwise signature resolved it; the final original module
compiled in 11.4 seconds. No timeout limit or existing definition was changed.

## New nodes

`lem-weil-pbc-popescu-lift-chart-fibres`:
`lean/Sheaf/RingTheory/PopescuLiftChartFibres.lean`, declaration
`Algebra.popescu_lift_chart_fibres`. This is the calculation modulo pi on one prepared
chart, including redundancy of the relations from other charts. It supplies smoothness
of the residue-field fibre and a specified smooth principal localization over
Cbar/pi Cbar. It assumes neither the annihilator equality nor Noetherianity. Its JSON
records the polynomial elimination, conormal coefficient comparison, compatibility of
cmod, and the residue-field base change as separate proof steps.

`lem-weil-pbc-popescu-lift-chart-flat`:
`lean/Sheaf/RingTheory/PopescuLiftChartFlat.lean`, declaration
`Algebra.popescu_lift_chart_flat`. This supplies only flatness of R_p to D_qD on a
prepared chart. Its proof records the equation count for D_k, the rank and dimension
calculation, the key equality, divisibility and annihilation of the remaining relations,
flat base change of annihilators, and the local-ring comparison. It does not state either
smoothness conclusion of the original theorem. No change records are required because
no existing interface was changed.

## Second reading by F1

1. **Visible declarations:** compared the original module with the repository using
   `diff -u`. Only five plain imports and the theorem body change. The existing
   signature, universes, visibility and docstring are byte-for-byte identical.
   The new modules declare only the two reported theorems, with no definitions.
   No change record is needed. Verdict: pass.

2. **Lean proof:** compiled all three modules in import order with `lcompile.py`:
   no errors or warnings. In a removed scratch copy, `#print axioms` for each of
   `Algebra.popescu_lift_smooth_special`, `Algebra.popescu_lift_chart_fibres`, and
   `Algebra.popescu_lift_chart_flat` returned exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The only two explicit holes are the named chart
   theorems, both exactly `:= by sorry`; there are no forbidden declarations or
   data chosen from an unfinished existence theorem. Verdict: valid decomposition,
   not an axiom-free proof or positive net hole reduction.

3. **Split statements:** independently read Stacks Tag 07CP, including the
   coefficient comparison and annihilator calculation. Modulo pi the extra chart
   equations already vanish after inverting a_k, so the chart-fibres theorem needs
   neither Noetherianity nor the annihilator equality. Local chart flatness does
   use Ann(pi)=Ann(pi^2), exactly as stated. Both conclusions are genuine proper
   parts of the upper proof, not renamed copies. Checked pi=0, pi a unit, empty
   chart sets, and empty/full E_k. Also checked n=m=0: the canonical localization
   is the identity where a chart meets the prime. The polynomial description and
   all maps remain compatible with hc and hcmod. Each hole has a source, complete
   verbal proof and matching node. Searches with new phrases via LeanFinder
   (flatness after lifting modulo a square; elimination of auxiliary variables),
   Loogle (`Algebra.Smooth, MvPolynomial`), and rg on Mathlib and both library roots
   found generic ingredients only. An initial Loogle query containing
   `Ideal.Quotient` was rejected as an unknown identifier and was replaced.
   Neither hole can be closed in a few minutes without formalizing the explicit
   quotient isomorphism and chart comparison. Verdict: pass.

4. **Route and pruning:** read the existing finite-presentation proof, the
   flat-with-smooth-fibre criterion, equation-count flatness, differential dimension
   and annihilator-base-change declarations. The upper proof composes the required
   three ingredients and explicitly witnesses the special-fibre neighbourhood.
   Its plain imports are exactly the three proof ingredients; the new public imports
   support their statements. The two lower plans retain the chart/equation-count
   argument. Inspected `dag/units/sk-thm-p1.json`: this item is below its realized
   steps; none is bypassed or changed. Expanded the pruning list to account for
   every old direct dependency, distinguishing relocation from removal. Verdict: pass.

5. **DAG agreement:** the existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Checked that each `proof_deps` is precisely the union of step
   uses, and that the new nodes have all required provenance, source, search,
   blueprint, chapter/unit and Lean fields. Their recorded signatures match their
   Lean statements. The upper node follows the actual Lean composition; lower
   nodes record the unfinished chart calculations. Removed the unused flat-map
   composition dependency from the lower flatness plan. Verdict: pass.

Second reading changed the flatness docstring and node to specify topological
dimension at the fibre point (not the dimension of its local ring), removed
`lem-weil-pbc-flat-ring-map-comp` from the lower plan, and made the pruning report
exhaustive. No Lean statement, definition, proof body or hole count changed.
