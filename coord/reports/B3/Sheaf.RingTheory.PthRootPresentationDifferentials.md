## What changed

Proved `KaehlerDifferential.pthRootPresentation_differentials` in
`Sheaf.RingTheory.PthRootPresentationDifferentials`, with its signature and visibility unchanged.
The proof uses only Mathlib. Added three proved private helpers:
`relative_relation_zero`, `relative_basis`, and `coefficient_exact`.

Ideal-span induction proves that the relative conormal differential vanishes. The conormal
sequence then gives a bijective map on differentials, through which the base-changed polynomial
basis is transported. For the coefficient kernel, use Mathlib's connecting map for the actual
quotient presentation. Compute its image on relation cycles and use ideal-span induction to
identify its range with the range of the stated linear combination map. Mathlib gives the final
two exactness claims directly.

Replaced the proof import `Sheaf.RingTheory.JacobiZariskiHomologySequence` with
`Mathlib.RingTheory.Kaehler.JacobiZariski`. All public imports stay unchanged.
Updated the item's proof route, proof dependencies, and proof origin in its node copy.
Recorded the already proved presentation-level Mathlib API as a new Mathlib-backed node.
No new Lean module, definition, public statement, or interface change was necessary.

## Proved and sorry left

Closed the only original hole: `KaehlerDifferential.pthRootPresentation_differentials`
(node `lem-weil-pbc-pth-root-presentation-differentials`). All four conjuncts are proved.
The three private helpers are also proved. No `sorry` remains and no hole was added or split off.

Single-file compilation through `lcompile.py` succeeded without warnings after import pruning.
The proof handles the empty family (`n = 0`), the zero coefficient ring, zero or repeated
coefficients, and dependent coefficient differentials: no nontriviality or coefficient
independence is assumed or introduced. In particular the relative basis argument uses no
nonzero-coefficient hypothesis. The characteristic computation uses the algebra map from
`ZMod p`, so it also works for a zero ring.

The quotient section uses `Ideal.Quotient.mk_surjective`, a fully proved Mathlib theorem.
It is local proof data, not a public definition chosen from an unproved existence assertion.

## No longer needed

Removed import: `Sheaf.RingTheory.JacobiZariskiHomologySequence`.
This proof no longer needs node `lem-weil-pbc-jacobi-zariski-homology-sequence` or its full
six-term sequence and Tor base-change comparison. The needed presentation-level connecting
map and exactness are already in Mathlib and are recorded by the new node below.

Removed from this item's proof dependencies:
`lem-weil-pbc-polynomial-ring-kahler-basis` (the arbitrary-variable basis node suffices),
`lem-weil-pbc-nl-presentation-h1-functoriality`, and `def-weil-pbc-smooth-ring-map`.
There is no comparison with the canonical presentation and no smoothness argument.

The removed import's entire project-module subtree is unnecessary for this proof:
`Sheaf.RingTheory.JacobiZariskiHomologySequence`,
`Sheaf.RingTheory.TwoTermKernelBaseChange`,
`Sheaf.Paper.TorLongExactFirstVariable`,
`Sheaf.Algebra.TorDimensionShiftFree`,
`Sheaf.Algebra.TorDimensionShiftNatural`, and
`Sheaf.Algebra.Homology.FreeResolutionSesSplit`.
Their associated nodes, also unnecessary for this proof, are
`lem-weil-pbc-jacobi-zariski-homology-sequence`,
`lem-weil-pbc-two-term-complex-kernel-base-change`,
`lem-weil-pbc-tor-long-exact-first-variable`,
`lem-weil-pbc-tor-dimension-shift-free`,
`lem-sc-p1-tor-dimension-shift-natural`, and
`lem-weil-pbc-free-resolution-ses-split`.
These may remain needed by other targets or modules; this report makes no claim of global
unreachability. Temporary explicit Mathlib polynomial-basis and tensor-basis imports were
removed because the single Jacobi-Zariski import already supplies their public APIs.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had the unchanged original hole and no proof.
The original DAG's canonical-presentation comparison is unnecessary: Mathlib's
`Algebra.Generators.H1Cotangent.exact_δ_map` and `δ_eq_δAux` work with any chosen polynomial
presentation. This shortens the route below the unit level; no unit statement or realized
unit step is bypassed (`sk-thm-p1` does not list this auxiliary node as a realized step).

The local Stacks `.tex` files are absent. Read the sources online:
[07E5, proof of (2) implies (4)](https://stacks.math.columbia.edu/tag/07E5) and
[00S2, chosen-presentation Jacobi-Zariski sequence](https://stacks.math.columbia.edu/tag/00S2).
The connecting map gives the negative coefficient differential with Mathlib's convention;
using negative relation cycles gives exactly the positive generators in the statement.

LeanSearch returned HTTP 500 for the new API-node search; recorded as unavailable, not as
absence. Loogle found the exact chosen-presentation API, and LeanFinder and source grep
confirmed the coefficient formulas. Every applied signature was read in pinned Mathlib.
No statement was disputed or changed.

## New nodes

`lem-weil-pbc-presentation-connecting-map-exact` records existing Mathlib declarations in
`Mathlib.RingTheory.Kaehler.JacobiZariski`: presentation-level `exact_δ_map`, cycle formula
`δ_eq_δAux`, and coefficient formulas `δAux_monomial`, `δAux_C`, and `δAux_mul`.
It states the generic chosen-presentation ingredient, not a restatement of the p-th-root
result. It adds no module or hole. The item uses it for the coefficient-image computation
and exactness at the first tensor term. No change record is needed.

## Second reading by B3

1. **Interfaces: pass.** Compared the delivered module with the repository version.
   The complete `pthRootPresentation_differentials` signature, section parameters,
   notations, visibility, and all three public imports are byte-for-byte unchanged.
   The only existing-node fields changed are `proof`, `proof_deps`, and `proof_origin`.
2. **Proof and axioms: pass.** Independently compiled the module through `lcompile.py`
   without warnings (8.5 seconds). A scratch copy prints axioms for all three private
   helpers and the public theorem: exactly `propext`, `Classical.choice`, `Quot.sound`.
   No `sorry`, forbidden declaration, or hollow definition occurs. The quotient section
   is chosen from Mathlib's proved surjectivity; no unproved existence data is used.
3. **New statements: pass.** No statement or hole was split off. Read the new API node
   against Mathlib `JacobiZariski.lean` lines 233–263, 370–383, and 396–418.
   Its generic chosen-presentation exactness and coefficient formulas agree clause by
   clause, with compatible algebra structures and no flatness assumption. Read
   [Stacks 00S2](https://stacks.math.columbia.edu/tag/00S2),
   `lemma-exact-sequence-NL`: this is its chosen-presentation connecting map, with
   explicit formulas supplied by Mathlib. Empty variable sets and zero rings satisfy
   these formulas; there is no finite-generation or nontriviality restriction.
   Independently searched Loogle for `"δAux_mul"`, Mathlib grep for
   `pthRootPresentation|δAux_monomial|δ_eq_δAux`, and project Lean/DAG sources for
   chosen presentations, connecting maps, and root differentials. Existing project
   results concern canonical presentations or stronger full sequences; none supplies
   this entire generic API node. Corrected its two erroneous source line references.
4. **Route and pruning: pass.** Read
   [Stacks 07E5](https://stacks.math.columbia.edu/tag/07E5), proof (2) implies (4),
   and followed each helper. Span induction uses the vanishing of the quotient image
   in the Leibniz scalar case. Conormal exactness and surjectivity transport the
   polynomial basis with the required vector formula. All conormal representatives
   are cycles; coefficient differentiation sends each relation to negative `1 ⊗ da_j`.
   Span induction proves one range inclusion; negative relation cycles prove the other.
   This works for `n = 0`, the zero ring, repeated or zero coefficients, and dependent
   coefficient differentials. The two final conjuncts use the general first fundamental
   sequence. The report lists all four removed old dependencies and the removed import.
   `dag/units/sk-thm-p1.json` has neither this auxiliary node nor the bypassed comparison
   among its realized steps; the fixed unit route is preserved. The sole proof import
   supplies both the connecting map and polynomial-basis APIs; no shorter existing
   p-th-root theorem was found in project sources.
5. **DAG: pass after repair.** The first two steps match `relative_relation_zero` and
   `relative_basis`; the next two match the coefficient-map computation and the two
   range inclusions in `coefficient_exact`. Their cited definition, conormal, basis,
   and new presentation-API nodes state precisely those inputs. The final step had
   incorrectly cited the quotient conormal node 00RU for general transitivity.
   Replaced that citation with the existing Mathlib leaf
   `lem-weil-pbc-kahler-differentials-first-exact-sequence` (00RS), and added it to
   `proof_deps`. New-node fields, searches, source, creation, blueprint origin, and
   Mathlib-backed Lean record were checked. No new module or hole is needed.

Second reading changed only the new node's Mathlib line references and the item's final
DAG citation/dependency, plus this report. The Lean proof needed no repair.
