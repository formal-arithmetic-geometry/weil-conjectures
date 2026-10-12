## What changed

Proved `AlgebraicGeometry.Scheme.essSurj_pullback_finiteEtale_of_henselianRing` in
`Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity`, with its original
signature unchanged. Retained the proof-only imports of
`Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent` and
`Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation`, and removed the redundant
direct import of `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete`. The lambda supplies the
universal G-ring lifting hypothesis by the approximation theorem; limit descent
then gives exactly the required lift and isomorphism over the closed fibre.
Updated the item's node proof, proof_deps and proof_origin to this assembly.

The proof follows Stacks 0GS2, label
`lemma-finite-etale-on-proper-over-henselian-pair`, Noetherian G-ring and General
case paragraphs. Read the available Stacks source at
`/home/ubuntu/c1-stacks-review/pione.tex`, lines 1749–1878, because the repository's
literature copy is absent on this machine. Checked the unit `sk-thm-p1` and its
realized steps: no unit statement or realized step is bypassed. The complete
Noetherian case remains a dependency of the approximation argument.

Searches: LeanFinder returned etale composition and ring-level etale lemmas, with
no matching lifting theorem; Loogle returned HenselianRing/root-lifting facts;
launcher grep returned no match. Source grep found the upstream equivalence
already importing this item, so it would be circular to use that equivalence.
The two existing stated lemmas give the shortest noncircular assembly.

Local single-file compilation passed without warnings.

## Proved and sorry left

Proved the one original sorry:
`AlgebraicGeometry.Scheme.essSurj_pullback_finiteEtale_of_henselianRing`
(node `lem-weil-pbc-finite-etale-lifting-essential-surjectivity`).
No sorry remains in the item's module. No new theorem or sorry was introduced.

The existing dependencies still have their original sorries:
`AlgebraicGeometry.Scheme.exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting`
(node `lem-weil-pbc-finite-etale-lifting-limit-descent`) and
`AlgebraicGeometry.Scheme.exists_finiteEtale_lift_of_henselianPair_of_isGRing`
(node `lem-weil-pbc-finite-etale-lifting-approximation`). They are the next proof
items, not newly split-off lemmas. This is a complete reduction to those existing
statements, not an axiom-free completion of their transitive proofs.

## No longer needed

Removed the proof-only import
`Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete`. No module is eliminated from
the transitive proof route. This module does not need a direct import of
`Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete` or a direct proof edge to
`lem-weil-pbc-finite-etale-lifting-complete`: the approximation lemma uses that
case internally. The finite-etale category node
`def-weil-pbc-finite-etale-category` remains a statement dependency; its direct
proof edge is unnecessary because limit descent already returns the exact
Over-category isomorphism required by the conclusion. These are redundant direct
edges, not claims that either node is globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original DAG lists the complete case
as a separate step at this node, but the existing approximation and conditional
limit-descent interfaces already package that route. They fit without any
signature changes or extra glue statements. The repository's cited literature
file is absent locally; an existing read-only local Stacks copy supplied it.


## Second reading by J1

1. **Visible declarations unchanged: PASS.** Diffed the sole delivered Lean module
   against the repository: the existing theorem signature and docstring are byte
   for byte unchanged; there are no new declarations or definitions. Only its
   proof and private imports differ. All public imports are unchanged. There is
   no statement change requiring a change record.
2. **Proof and axioms: PASS as a reduction.** Local compilation passed without
   warnings. The module contains no `sorry` or forbidden trust construct.
   A scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.essSurj_pullback_finiteEtale_of_henselianRing` compiled
   and printed exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The last is expected from the existing, still-open approximation and
   conditional limit-descent theorems; this delivery does not close their proofs.
   The lambda supplies every argument of H, including the ring instance,
   `IsGRing`, henselian-pair instance, proper scheme morphism and cover. The
   returned lift and Over-isomorphism have exactly the target's types.
3. **Split statements: PASS (none).** No new statement or split-off sorry exists.
   Read both imported lifting declarations and `IsGRing`: its definition
   includes Noetherianity, so the approximation theorem has the required
   Noetherian hypothesis. Conditional limit descent is the general-case step,
   not an unconditional restatement of the item. Empty covers, zero rings,
   I = 0, and empty schemes are not excluded or changed by the assembly.
4. **Shortest route and pruning: PASS.** Searched the library, Mathlib's
   algebraic-geometry sources, and the upstream henselian finite-etale module
   using essential-surjectivity and lifting terms. The upstream equivalence is
   itself `sorry`; the project's equivalence imports and applies this item, so
   it cannot give an independent shorter proof. Read Stacks' available local
   `pione.tex`, lines 1749–1878: the Noetherian G-ring and general-case paragraphs
   are the two steps used here, with the complete case retained transitively.
   The removed old direct proof edges are exactly
   `lem-weil-pbc-finite-etale-lifting-complete` and
   `def-weil-pbc-finite-etale-category`; both are accounted for above, and the
   latter remains a statement dependency. Checked `dag/units/sk-thm-p1.json`
   and its realized steps: this is below its strictly henselian comparison
   step, with no realized unit statement or step bypassed. The unit source file
   is absent locally, but its statement and steps are recorded in that JSON.
   The remaining explicit proof imports name the two declarations actually used.
5. **Nodes match Lean: PASS.** Diffed the delivered node: only `proof`,
   `proof_deps`, and `proof_origin` changed. The two proof steps match the lambda
   invoking approximation and the application of conditional limit descent;
   `proof_deps` is exactly their union. Statement, statement dependencies, Lean
   signature record, chapter and unit are unchanged. No new node fields arise.

**Second-reader changes:** corrected the report's stale claim that proof imports
were added and none removed: the current repository already imports both used
lemmas, and the sandbox removes the redundant complete-case import. The Lean
proof and DAG assembly required no repair. Section I of
`coord/delivery-errors.md` is not yet present; the stage-3 brief was followed.
