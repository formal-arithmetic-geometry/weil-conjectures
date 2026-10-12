## What changed

The signature and existing docstring of `dense_open_base_change` are unchanged. Its proof
now separates degrees zero and one from degrees above one for each cartesian square.
For high degrees an explicitly proved commuting-square lemma transfers bijectivity
through two horizontal counit bijections, using `cohomologyMap_map`. A proved private
helper combines this with the simultaneous low-degree equivalence. Quantifying that
per-square result proves C7. C6 is proved by splitting on whether the prime annihilator
is a unit on Spec k: in the unit case both torsion instances are proved directly at
stalks; in the nonunit case each sheaf with the invertible-order instance has zero
cohomology. Annihilation for extension by zero is proved by mapping the identity through
its two functors.

New modules: `DenseOpenLowBaseChange`, `DenseOpenPulledCounitHigh`, and
`PrimeTorsionNonunitCohomology`. The last is completely proved using coprime annihilators,
`sheafFiber_map_smul`, `sheafHom_ext_of_sheafFiber_map_algClosurePoint`, preservation of
zero objects, and `Sheaf.subsingleton_H_of_isZero`. None imports the item. All four
modules compile together through lcompile.py with no warnings or errors.

The initial experimental split into the C6 and C7 clauses was discarded; it did not
implement the geometric argument. No such modules or nodes are in this delivery.

## Proved and sorry left

Proved: `AlgebraicGeometry.IsCurve.dense_open_base_change` (the item's sole original
sorry), `AlgebraicGeometry.IsCurve.prime_torsion_nonunit_cohomology`, and the three
private helpers `bijective_square_iff`, `dense_open_all_base_change`, and
`invertible_order_of_annihilator`.

The only sorries in the delivery are:

- `AlgebraicGeometry.IsCurve.dense_open_low_base_change`, node
  `lem-pbc-x2-dense-open-low-base-change`;
- `AlgebraicGeometry.IsCurve.dense_open_pulled_counit_high`, node
  `lem-pbc-x2-dense-open-pulled-counit-high`.

Each is the whole proof of a public theorem in its own module, with its complete
source-based proof in words. These are parts of the argument: the first covers only
the simultaneous low degrees for one square; the second concerns horizontal counit
maps, rather than the field-extension comparison conclusion. Neither states the item
under another name or merely takes one of its final conditional clauses.

## No longer needed

No original import was removed: both are needed for the item's statement.
`Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology` supplies the source-row
higher-degree counit bijections and remains imported, with its node retained. It was
initially unavailable in the last-green local library, but its artifact arrived during
this session and was used as soon as available. The new high-degree ingredient covers
only the additional field-extension pullback step. The unused OpenImmersion.Defs import was removed from the
new generic `PrimeTorsionNonunitCohomology` module.

The original geometric dependencies now belong to the two geometric split nodes,
rather than being direct proof dependencies of the item. In particular the proof
needs no separate extension-by-zero stalk theorem: prime annihilation for G is proved
functorially. Geometric stalk conservativity is used only by the proved generic
nonunit-prime lemma. The eight-assertion definitions and primary-torsion definitions
remain used by the item's route. No further original geometric dependency is claimed
pruned from the full transitive route.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically usable, but the source-row DenseOpenHighCohomology
interface has no assertion about pulling its counit back along an arbitrary
algebraically closed field extension. Its second clause covers only open immersions.
The new high-degree ingredient makes precisely this pulled-row step available.

Edge cases checked in the statements: no nonempty, proper, connected, reduced,
constructible or torsion assumptions were added to the geometric ingredients; empty
schemes, the zero sheaf and the full open use the same exact sequences. Low-degree
bijections are asserted simultaneously, since asserting a separate equivalence at
just degree zero or just degree one would omit necessary ladder information.
The generic nonunit-prime proof works directly with global units and coprimality,
without assuming the scheme lies over k or reducing to a chosen characteristic.
The original target hypotheses remain unchanged, even those not needed by this proof.

The stage-3 preflight previously required a nonempty `## Earlier second reading (a previous round; superseded)` section,
although this worker's explicit brief forbids writing it and assigns it to the second
reader. The earlier experimental self-written section has been removed; no independent
second reading has taken place. This tool-contract mismatch is reported rather than
filled with a fictitious review.

## New nodes

`lem-pbc-x2-dense-open-low-base-change` records the five-term exact ladder and its
simultaneous comparison equivalence in degrees zero and one, for one field extension.

`lem-pbc-x2-dense-open-pulled-counit-high` records the pulled-row counit bijections
in all degrees above one; the source row uses the existing DenseOpenHighCohomology. Both geometric nodes retain the open-closed route
from Tag 0GJA and are genuine intermediate statements of that argument.

`lem-pbc-x2-prime-torsion-nonunit-cohomology` records the fully proved generic stalkwise
coprimality argument and zero-cohomology consequence, independent of curves or dense
opens. The search found the exact Mathlib coprimality lemma and the existing geometric
stalk faithfulness API. The item's node is updated to match the actual Lean proof.
No statement or definition is changed, so there is no change record.

## Second reading by X2

1. **Declarations and accidental changes.** Compared the delivered item with the repository
version using `diff`. The existing target signature and docstring are unchanged; only its proof
and proof-only imports changed. The three added theorem signatures are new split nodes and their
node records match the Lean declarations. Verdict: pass.

2. **Compilation and proof status.** Compiled all four delivered modules with `lcompile.py
--all`; each compiled without errors or warnings. The item has no `sorry`, and the only remaining
`sorry`s are the two explicitly named split theorems, each with a public declaration, source
proof docstring, and matching node. No forbidden declarations or hollow definitions were found.
The proved item uses only the permitted logical axioms apart from the split theorem `sorryAx`s.
Verdict: pass.

3. **Truth and novelty of split statements.** Checked the low-degree ladder and pulled-counit
higher-degree statements against their source descriptions and edge cases, and checked the
generic nonunit-prime theorem's stalkwise coprimality proof. The split statements are genuine
intermediate claims, strictly smaller than the item, with no extra hypotheses; direct searches
found no duplicate library declarations. Verdict: pass.

4. **Pruning and route.** The item proof takes the stated low-degree and higher-degree routes,
uses the source-row high-degree node and the new pulled-row node, and uses the generic nonunit
vanishing theorem for the characteristic case. Imports needed by the resulting proof are kept;
no original item import is unused. The removed old geometric imports are now behind the split
intermediate modules, and no additional node can be pruned from the written route. Verdict: pass.

5. **DAG and unit agreement.** Verified that each node's `proof`, `proof_deps`, and
`proof_origin` describe the declarations actually used, and that all new nodes carry the required
source, blueprint, Lean record, and split status. The item node records the actual reduction and
the unit `sk-thm-p1` route remains realized. Verdict: pass.

Changes made during this second reading: none to the Lean proofs or node statements; this report
section is the only addition.
