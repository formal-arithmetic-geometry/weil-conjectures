## What changed

Reduced zero_base_single_chart_presentation to the unlocalized coefficient presentation.
The localization part is proved: tensor localization, polynomial localization, quotient
localization, equality of the mapped linear ideal, and transport through the coefficient-compatible
equivalence. Added a proof-only import of PopescuZeroBaseSingleChartUnlocalized and Mathlib's
localization modules. All existing signatures and definitions are unchanged.
Completed the previous attempt by caching the coefficient-ring and quotient-ring instances
before elaborating the localization equivalence. This prevents repeated unfolding of the
explicit linear ideal. The polynomial algebra instance is local to each private proof.

## Proved and sorry left

Closed Algebra.PopescuLiftPresentation.zero_base_single_chart_presentation (one original hole).
Added one hole: Algebra.PopescuLiftPresentation.zero_base_single_chart_unlocalized,
node lem-weil-pbc-popescu-zero-base-single-chart-unlocalized. This is a decomposition, not a
net decrease in holes. Both private localization helpers are fully proved. The new hole
contains only scalar extension and quotienting the coefficient ring, with no localization.
No data is chosen from the unproved theorem in a definition.

## No longer needed

No existing imports removed. The original direct proof dependencies
`def-weil-pbc-algebra-hom-quotient`, `def-weil-pbc-module-tensor-product`, and
`def-weil-pbc-mv-polynomial-ring` are now carried by the unlocalized node instead of
being direct dependencies of the presentation calculation. They remain needed there,
so no node or module is pruned from the transitive closure. No variable-elimination,
normalization, conormal-basis, or smoothness lemma is used by this presentation calculation.

## Where the brief, the DAG or earlier work was wrong

The general universal-property dependencies do not directly state the unlocalized chart
isomorphism. It needs polynomial/tensor/quotient glue. Mathlib directly provides the entire
localization part, so no new localization theorem with sorry is needed. LeanSearch was
unavailable (HTTP Internal Server Error); Loogle, LeanFinder and local searches ran.
The existing module imports only its statement dependency, rather than the listed proof
dependencies, as allowed in the dispatcher brief. The previous attempt did not compile:
elaborating the quotient ring instance after the coefficient-compatible equivalence exhausted
400000 heartbeats. Establishing its ambient ring instances before the maps resolves this.
The new node now records the actual universe-polymorphic ULift signature verbatim.

## New nodes

lem-weil-pbc-popescu-zero-base-single-chart-unlocalized records the unlocalized coefficient
reduction in Tag 07CP. Edge cases checked: empty original or auxiliary variable sets, zero
rings, vanishing chart element, and arbitrary nonnormalized h. No invertibility of a_k is
needed before localization; a zero chart element simply gives a zero localization afterwards.
The existing unit's own statements and realized steps are retained.

## Second reading by P3

1. Compared the existing delivered module with its repository version and confirmed that
   the unlocalized module is new. The existing target and
   all existing declarations retain byte-for-byte identical signatures; the presentation
   change is confined to proof code and proof-only imports. Verdict: pass.
2. Compiled the unlocalized and presentation modules with `lcompile.py --all`. The target
   compiles without errors, and the only remaining `sorry` is the named unlocalized theorem
   recorded above. The presentation proof introduces no forbidden declarations or hollow
   definitions. Scratch copies with `#print axioms` show exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` for both public theorems.
   Verdict: pass, with the documented split hole.
3. Checked the split-off unlocalized statement against its node and source calculation.
   It is a strict coefficient-only reduction before localization, with the same hypotheses
   and coefficient compatibility conclusion; its docstring gives the construction and
   generator checks, and its node records the declaration and proof route. Checked empty
   variable sets, the zero ring, vanishing a_k, and arbitrary h: none requires division or
   smoothness. Independent LeanFinder, Loogle, and local searches found general
   `Presentation.baseChange_relation`, `MvPolynomial.ker_map`, `sumAlgEquiv`, and
   tensor-quotient equivalences, but no exact chart theorem. The reduction still needs
   the coefficient-ideal quotient and generator compatibility glue, so it cannot be closed
   by a direct application of those search hits. Checked Tag 07CP online. Verdict: pass.
4. Read the proof top-down. It uses the unlocalized reduction, tensor-product localization,
   polynomial localization, quotient localization, and the mapped-generator equality; the
   private localization helpers are fully proved. The unit's realized route is retained and
   all old direct dependencies are accounted for under No longer needed. Verdict: pass.
5. Checked the two node records against the Lean declarations, including proof dependencies,
   proof origin, module paths, and the universe-polymorphic unlocalized signature. The new
   node is needed by the target proof and is not a restatement of the target. Verdict: pass.

Changed after reading: added this second-reading record and clarified the disposition of
all old direct proof dependencies under No longer needed. No Lean code or node statement
was altered.
