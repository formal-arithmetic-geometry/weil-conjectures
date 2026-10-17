## What changed

Repaired the post-sync finite-presentation proof in
`Sheaf.AlgebraicGeometry.CoherentStalkMapExtends`. The former
`import all Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian` now sees
only a re-export wrapper. Import the helper's actual upstream module instead:
`import all WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`.
Use its proved private `Scheme.Modules.isFinitePresentation_of_generators_kernel`
after choosing finite local generators and applying the coherence kernel clause.
Glue these local finite presentations with `IsFinitePresentation.of_coversTop`.
This closes the repository's outstanding private-helper proof without duplicating
upstream's generator-kernel construction. The retained sandbox's duplicate local
helper and its two direct API imports were removed.

All existing signatures, visibility, docstrings, and the public stalk-map proof
are unchanged. Updated the node's proof description and origin to identify the
actual upstream module. No definition or statement repair, new node, or consumer
adaptation is needed.

Validation: the repaired module and all five unchanged direct consumers compiled
against the repaired sandbox module: `CoherentOpenMapTensorExtension`,
`CoherentIntegralGenericFreeNeighbourhood`, `CoherentGenericLocalFreeModel`,
`CoherentIntegralGenericIdealMap`, and `GenericIdealStalkEmbeddingExtension`.
Each file compiled within the unchanged 60-second limit, with no errors or warnings.

## Proved and sorry left

Closed: `AlgebraicGeometry.isFinitePresentation_of_coherent` (the single `sorry`
in the current repository version), supporting
`AlgebraicGeometry.exists_open_hom_of_coherent_stalk_map`
(node `lem-weil-pbc-coherent-stalk-map-extends`).
Holes closed: 1 of 1. Holes added: 0. Holes left in the delivery: 0.
The second reader's axiom check confirms that both the private helper and the
public stalk-map theorem depend only on `propext`, `Classical.choice`, and
`Quot.sound`; neither depends on `sorryAx`.

## No longer needed

Replaced the retired wrapper import
`Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian` with the direct
upstream import. The retained sandbox's separate proof imports of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` are
unnecessary because the upstream module provides these APIs. Removed the retained
private `AlgebraicGeometry.isFinitePresentation_of_generators_kernel_local` copy.
No DAG dependency is pruned: `pqf-lem-coherent-ft-locnoeth` still supplies the
proved private generator-kernel helper. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The retained report incorrectly said that upstream removed the private helper.
It still exists, but in the upstream module; `import all` of the retired wrapper
does not expose the upstream module's private declarations. The repair therefore
uses `import all` directly on that module, as the upstream
`CoherentAffineSectionsFinite` module already does. The earlier duplicate
construction is unnecessary. The return's sync incompatibility is repaired by
this proof change, not by a rebase alone. No target statement changed.

## New nodes

None.

## Second reading by K2

1. Compared the delivered Lean module and node with the current shared versions
   using `diff -u`. Both existing declaration signatures are byte for byte
   unchanged, including the private helper's visibility. The public theorem's
   proof and every existing docstring are unchanged. The only Lean changes are
   the private helper's proof and its proof-only import. No definition, target,
   public import, or other module is changed. Verdict: pass.
2. Compiled the delivered module with `lcompile.py`: no error or warning
   (7.9 seconds). Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.isFinitePresentation_of_coherent`,
   `AlgebraicGeometry.exists_open_hom_of_coherent_stalk_map`, and the imported
   `Scheme.Modules.isFinitePresentation_of_generators_kernel` (6.9 seconds).
   Each uses exactly `propext`, `Classical.choice`, and `Quot.sound`, with no
   `sorryAx`. Read both proof bodies and the upstream helper: there is no
   forbidden declaration, hidden hole, or data chosen from an unproved theorem.
   Verdict: pass.
3. No statement is split off and no declaration is added. The finite-generator
   argument includes the empty family (`n = 0`); no nonempty index set or nonzero
   module is assumed. The empty scheme is handled by cover locality, and the
   public theorem has a given point. There is no statement requiring a new
   Mathlib search or new node. Verdict: pass.
4. Searched the shared Lean sources by finite presentation, coherence, and stalk
   Hom terminology; read the upstream generator/kernel helper and its existing
   use in `CoherentAffineSectionsFinite`. Reusing this proved helper avoids a
   duplicate construction and proves the private theorem without adding a
   locally Noetherian hypothesis. The two proof imports are needed for that
   helper and the internal-Hom stalk equivalence. All old `proof_deps` remain
   used, so no node is newly pruned. Read `dag/units/sk-thm-p1.json`, including
   `realized`: this local repair changes none of its statement or step
   realizations and keeps the same stalk-Hom route. Verdict: pass.
5. Compared the node's three proof steps with the Lean: finite local generators
   and coherence give finite presentation; the stalk-Hom equivalence supplies
   a representative germ; restriction-stalk isomorphisms prove the displayed
   equality. `proof_deps` is exactly the union of the steps' uses and is
   unchanged. `proof_origin` and the first proof step correctly identify the
   actual upstream helper module. No new node fields or change record are
   needed. Verdict: pass.

Second-reading changes: report only. Recorded the independent checks and
replaced the report's uncertainty about imported holes with the successful
axiom audit. The Lean proof and DAG update required no repair.
