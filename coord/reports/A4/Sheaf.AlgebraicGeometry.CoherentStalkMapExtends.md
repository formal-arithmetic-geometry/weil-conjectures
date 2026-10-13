## What changed

Proved `AlgebraicGeometry.exists_open_hom_of_coherent_stalk_map` with its signature
and four public imports unchanged. A proved private helper
`AlgebraicGeometry.isFinitePresentation_of_coherent` constructs finite presentations
locally, then the main proof represents the given stalk map by an internal-Hom germ
and verifies the induced map on germs using the restriction stalk isomorphisms.

Repair of the returned delivery: removed the duplicate private theorem
`AlgebraicGeometry.isFinitePresentation_of_generators_kernel` and its entire proof.
Added the proof-only import
`import all Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian` and applied
its existing private theorem
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_of_generators_kernel`.
Lean's `import all` exposes that private theorem locally without changing its source
module or exporting it to this module's importers. No other module was edited.
The direct Generators and Quasicoherent proof imports are no longer necessary.
The item's DAG now records this reuse and retains `pqf-lem-coherent-ft-locnoeth`.

Sources remain the original Stacks Tags 01Y4, 01XZ and 01CP. The unit route is unchanged;
the finite-presentation construction is below the realized unit statements and steps.
The repaired module compiled cleanly through `lcompile.py` in 38.4 seconds.
The delivery dry run and import-pruning check are run before handoff.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.exists_open_hom_of_coherent_stalk_map`
(node `lem-weil-pbc-coherent-stalk-map-extends`).

No sorry remains in the item. Zero holes added and zero statements split off.
The remaining private helper `AlgebraicGeometry.isFinitePresentation_of_coherent`
is fully proved. The existing internal-Hom theorem
`AlgebraicGeometry.RingedSpace.exists_stalk_internalHom_linearEquiv_of_finitePresentation`
(node `lem-weil-pbc-stalk-internal-hom-finite-presentation`) remains a holed dependency
outside this delivery. This is a proof from existing stated dependencies, not a claim
that the transitive closure has no holes.

## No longer needed

Removed original proof import `Sheaf.Topology.PresheafModuleStalkFunctor`:
Mathlib already supplies the germ representation and map-on-germs facts.
The mathematical node `def-weil-pbc-module-stalk` remains used through its Mathlib match.

Removed original direct proof import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
`StalkInternalHomFinitePresentation` publicly imports it. Node `def-pur-sheaf-hom`
remains used transitively.

Compared with the returned delivery, removed the duplicate helper and the direct imports
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
Their needed declarations arrive through the retained coherence module.
Contrary to the previous report, `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
and node `pqf-lem-coherent-ft-locnoeth` are retained, since their existing private
finite-presentation helper is used. No other original proof node is pruned.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated an existing theorem because it incorrectly treated its
private visibility as preventing reuse. The repair uses `import all`, removes the duplicate,
and calls the original theorem directly, exactly as the return requested.
The previous second reading also missed this reuse mechanism; its stale review has been
removed so the independent second reader can review the repaired version.

No statement, definition, target, universe or declaration visibility was changed. No new
nodes, modules, forced adaptations or change records are needed. Finite generator families
may be empty, and the stalk equality is proved for every element, including zero.

## Second reading by A4

1. Compared the only delivered module with the repository using `diff`, and checked
   its existing theorem signature as an exact string: byte-for-byte unchanged.
   The four public imports and existing visibility are unchanged. Only the proof,
   proof documentation, private proved helper and proof-only imports differ.
   No definition or change record is added. Verdict: pass.
2. Independently compiled the module with `lcompile.py` (41.8 seconds, no errors or
   warnings). Scanned the delivered Lean for sorry and forbidden declarations:
   none. Compiled a fresh scratch copy with `#print axioms` for the reused helper,
   the coherent finite-presentation helper and the item. The two helpers use only
   `propext`, `Classical.choice`, `Quot.sound`; the item additionally uses `sorryAx`
   through the reported existing internal-Hom dependency. The equivalence's formula
   on all germs determines it, and no public definition selects arbitrary data from
   an unproved existence theorem. Verdict: pass with that existing open dependency.
3. No statement is split off, no new sorry or node is added. Checked the private
   coherent-to-finite-presentation argument, including empty finite generator
   families: reindexing by `ULift (Fin n)` and the coherence kernel clause apply
   also for n = 0. For an empty scheme the item has no point x; the displayed stalk
   calculation includes zero and every other element. The reused private helper
   is genuinely proved in the coherence module. Verdict: pass.
4. Read the proof top down: finite generators and relations provide finite
   presentation; the existing canonical internal-Hom theorem represents psi;
   Mathlib's germ and restriction-stalk formulas prove the required equality.
   Repeated LeanFinder with the query "coherent sheaf finite presentation morphism
   from stalk extends locally", and searched Mathlib and both library roots by
   finite-presentation, coherent, hom and stalk terminology. No shorter proved
   extension theorem was found. The existing generators/kernel helper is reused,
   rather than duplicated. Both remaining proof imports are used; the removed
   presheaf-stalk import is unnecessary and internal Hom arrives transitively.
   All original proof dependency nodes remain used, so there is no node pruning.
   Read `dag/units/sk-thm-p1.json`: its realized statement and steps remain intact;
   this construction lies below those unit steps. Verdict: pass.
5. Compared the node JSON: only `proof`, `proof_deps`, `proof_origin` change.
   Checked that proof_deps is exactly the union of step uses. The finite-presentation
   step records the helper reused from the retained coherence node; the next steps
   match the canonical equivalence and the explicit restriction-stalk calculation.
   The statement, statement dependencies, source and Lean record stay unchanged.
   No new node fields are required. Verdict: pass.

Changes by this reader: appended this independent review and made a fresh axiom
probe in scratchpad; no repair to the delivered Lean or DAG was needed.
