## What changed

Proved AlgebraicGeometry.Etale.tailOpenCohomologyArrow_laws with its exact original
signature, universes and visibility. Use the existing tailOpenDiagram, tailOpenSheaf
and tailOpenCoefficient definitions, specialize openSquareCoefficient_diagram_identity,
and prove the coefficient composition calculation from squareUpperStarIso_paste_vert_hom
and naturality. Private, proved cohomology transport and arrow calculations combine these
coefficient equations with cohomologyPullbackFunctorial and cohomologyMap_map.

Added proof-only imports of Sheaf.AlgebraicGeometry.EtaleLimitOpenRestrictedSystem,
Sheaf.AlgebraicGeometry.EtaleOpenSquareDiagramIdentity,
Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial, and
WeilConjectures.SixFunctors.BaseChange.Pasting. The original public import remains.

The public arrow definition is unchanged, including its body. The pointwise private
composition calculation avoids repeating the cohomology argument at restricted-scheme
types; the complete module compiled cleanly in 39.8 seconds. No statement, definition,
public import or visibility changes, and no downstream adaptation or change record is
needed.

Updated the item's DAG proof, proof_deps and proof_origin to name the actual identity,
square-pasting, restricted-system definitions and cohomology-functoriality dependencies.
No unit statement or step is bypassed. No cone, cocone or continuity theorem is used.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Etale.tailOpenCohomologyArrow_laws
(node lem-weil-pbc-tail-open-cohomology-arrow-laws).

Holes closed: 1. Holes added: 0. Split off: 0. No sorry remains in the delivered module.
All private helpers are fully proved. This is a proof from existing named dependencies,
not a decomposition into new holed statements.

The proof applies the existing named
AlgebraicGeometry.Etale.openSquareCoefficient_diagram_identity
(node lem-weil-pbc-open-square-diagram-identity); it adds no replacement for that dependency.
The second reader's scratch-copy #print axioms check confirms that both the public
arrow definition and the laws theorem use only propext, Classical.choice and Quot.sound;
no sorryAx occurs. The delivery dry run also checks all declarations.

## No longer needed

No original import or module is pruned. All five final imports serve the statements,
constructions or proof. The original direct proof dependency on
lem-weil-pbc-inverse-image-composition is replaced by the more specific identity and
square-pasting dependencies; its module is still needed transitively, so no global
pruning is claimed for it.

Only the tail diagram and stage coefficient definitions of
Sheaf.AlgebraicGeometry.EtaleLimitOpenRestrictedSystem are used. Its limit cone,
restricted limit diagram, cocone legs and full coherence theorem are not invoked.
This does not remove that module from the import closure.

## Where the brief, the DAG or earlier work was wrong

The plan describes the right argument, but its inverse-image-composition dependency
alone does not expose the required diagram identity law or vertical square pasting.
The more specific existing nodes now appear in proof_deps. The private square coefficient
composition calculation is the one already proved privately in the restricted-system
module; it cannot be imported by name, so it is reproduced from the public pasting theorem.
No statement error was found. Empty opens, zero coefficients, identity singleton systems
and repeated indices need no exceptional argument: the equations are purely functorial,
and all original hypotheses remain in the public theorem.

The local literature TeX and unit Markdown files referenced by the nodes are absent in
this clone. Read the unit's realized route in dag/units/sk-thm-p1.json and the actual
Stacks statements at https://stacks.math.columbia.edu/tag/01F7 and
https://stacks.math.columbia.edu/tag/09YQ. Tag 09YQ supplies the coherent-system application;
its continuity or affine-transition hypotheses are not imported into these arrow laws.


## Second reading by A2

1. Compared the delivered module with the repository using diff and the declaration
   parser. Verdict: the existing signatures, universes, visibility, docstrings and
   definition body are unchanged. The definition-local transparency setting affects
   elaboration only. No change record or forced adaptation is required.
2. Compiled the delivered module without errors or warnings, then compiled a scratch
   copy with #print axioms for tailOpenCohomologyArrow and
   tailOpenCohomologyArrow_laws. Verdict: each uses only propext, Classical.choice and
   Quot.sound. No sorry, forbidden declaration mechanism, or hollow definition exists
   in the delivered module. The private helpers are proved.
3. No statements were split off and no holes or public declarations were added.
   Verdict: there is no restatement masquerading as a reduction. Read the private
   transport and coefficient calculations: they prove equality transport, vertical
   pasting and cohomology functoriality separately. Identity transitions, repeated
   indices, empty opens and zero coefficients obey the same universal equations.
4. Read the imported identity and cohomology functoriality declarations and searched
   lean/Sheaf and lean/WeilConjectures for composition and identity alternatives.
   The matching square calculation in EtaleLimitOpenRestrictedSystem is private;
   TailOpenCohomologyLegNaturality also contains private calculations and imports this
   item, so importing it would cycle. The full restricted-system coherence theorem
   additionally requires cone and limit-coefficient data absent from this item.
   Verdict: the direct reduction is appropriate; each added import is proof-only and
   supplies a used declaration. The original import stays public for the signature.
   No longer needed names the sole removed old proof dependency, inverse-image
   composition, and correctly makes no claim of global module pruning. The unit
   sk-thm-p1 realized statement and steps are unchanged and none is bypassed.
5. Compared old and delivered node records, and read each dependency's Lean record.
   Verdict: only proof, proof_deps and proof_origin changed; proof_deps is the union
   of the recorded steps. The square-pasting node includes vertical as well as
   horizontal pasting. The node accurately distinguishes using the restricted-system
   constructions from applying its full coherence theorem. No new nodes are needed.

Second reading changed only this report: recorded the completed axiom check and this
independent review. No Lean or DAG repairs were needed. Holes closed: 1; holes added:
0; split off: 0; modules pruned: none.
