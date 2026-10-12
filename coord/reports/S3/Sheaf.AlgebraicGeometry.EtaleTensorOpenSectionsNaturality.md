## What changed

Completed `Sheaf.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality` without changing
any existing signature, visibility, or definition. The proof compares conjugates of
adjunction isomorphisms, uses the unit equation and unit naturality, evaluates on top
sections, and identifies over-scheme morphisms with inclusions by cancellation.
Private proved helpers carry these steps. The local elaboration commands are documented
in `coord/changes/etale-tensor-open-sections-proof-elaboration.md`; no existing
public interface or downstream module needs adaptation. Added the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique` for the conjugates of
`leftAdjointUniq`. Updated the core and naturality nodes to match the Lean argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.etaleTensorOpenSectionIso_component_core`
(node `new-etale-tensor-open-section-core`).
`AlgebraicGeometry.Scheme.Modules.etaleTensorOpenSectionIso_naturality` remains proved
by its existing assembly from that core theorem. No holes added, no decomposition,
and no `sorry` left in any delivered module. All private helpers are fully proved.
The proof uses the existing tensor-pullback adjunction and the existing definitions
of normalized tensor section restrictions; their dependencies remain in scope.

## No longer needed

Removed the redundant direct import
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`: it is already publicly imported
by `Sheaf.AlgebraicGeometry.EtaleTensorSections`, and its adjunction theorem is still
used. The naturality node no longer directly uses
`lem-pc-module-pullback-adjunction`, `lem-sc-etale-qcoherent-presheaf-functorial`, or
`lem-weil-pbc-open-immersion-module-pullback-restriction`: its proof now uses
`new-etale-tensor-open-section-core` and `new-etale-tensor-open-section-iso`.
All three removed direct dependencies remain used by the component core, so no
module or dependency is pruned from the import closure. Removed
unused private exploratory helpers from the earlier sandbox attempt; none had landed.
The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt contained private partial proofs and a trace command;
these are replaced by complete proofs. The existing core node omitted the explicit
adjunction and open-restriction ingredients; its proof dependencies now record them.
The naturality node now records its actual assembly from the component core.
No statement or definition correction was required. Empty opens, identity inclusions
and zero modules are covered without extra hypotheses by the same adjunction and
presheaf equations. Broad rewriting and elementwise elaboration at the concrete
open inclusions were expensive; targeted expansion and a general open-immersion
section calculation keep the tensor construction folded.

## Second reading by S3

1. Compared the complete module with the repository version using `diff` and the
   declaration scanner. Every existing signature and visibility is byte for byte
   unchanged; both public definitions have identical bodies. The only existing proof
   replaced was the component core's `sorry`. Local elaboration options and the local
   irreducibility attribute are covered by the existing change record; they introduce
   no public instances or rewrite rules. Verdict: pass.
2. Compiled the delivered module locally without errors or warnings. Inspected all
   proof steps from restriction-adjunction conjugacy down to the Over-morphism
   cancellation. No forbidden declarations or commands and no textual `sorry` occur.
   A scratch copy prints axioms for all sixteen declarations: the new private
   construction and every private helper use only `propext`, `Classical.choice`,
   `Quot.sound`; the transported public isomorphism and the two public theorems also
   use inherited `sorryAx` from `etaleTensorSectionsPresheaf` and its existing
   composition-law hole. The tensor adjunction is pinned by its explicit unit, and
   the new private comparison uses the existing canonical adjunction, rather than
   arbitrary data from mere existence. Compiled scratch copies of both direct importers,
   `EtaleTensorOpenSections` and `EtaleTensorDirectImageIdentification`, against the
   sandbox's compiled module overlay; both originals compile unchanged.
   Verdict: pass, with inherited holes only.
3. No statement is split off and no new hole is introduced. Checked empty opens,
   identity inclusions, and zero modules: the same presheaf and unit equations apply
   with no nonemptiness assumptions. Searched with LeanFinder for canonical-adjoint
   composition compatibility, Loogle for conjugates, and `rg` for restriction
   naturality and composition equations in Mathlib and the library. These provide
   the ingredients already used, not a direct replacement of the core. Verdict: pass.
4. The argument follows adjunction uniqueness, then evaluates on sections, then
   transports to arbitrary Over objects. The added import is proof-only; the removed
   direct adjunction import is redundant through `EtaleTensorSections`. Checked the
   unit `sk-prop-cd`, its `realized` record, and the Mathlib restriction leaf: this
   argument changes no unit step or realization and bypasses no unit result. The
   three former direct naturality dependencies remain necessary through the core.
   Verdict: pass after completing the pruning report.
5. Compared both delivered nodes with the originals. Their statements and statement
   dependencies stay unchanged. Their proof steps and dependency unions describe
   the conjugate/unit calculation and the final assembly as written. Found that
   `lean.statement` had literal Unicode escape strings; restored the original
   Unicode statements in both records. No new nodes need validation. Verdict: pass
   after metadata repair.

Second reading changed only the two node `lean.statement` strings and this report
(including the complete list of removed direct proof dependencies). The Lean proof
needed no repair. Closed one original hole, added zero, split off zero; no module
is pruned from the targets' import closure.
