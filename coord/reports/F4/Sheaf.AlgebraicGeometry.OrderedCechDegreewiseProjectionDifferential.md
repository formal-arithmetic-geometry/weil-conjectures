## What changed

Completed `Sheaf.AlgebraicGeometry.OrderedCechDegreewiseProjectionDifferential`.
The public theorem `AlgebraicGeometry.Scheme.Modules.orderedCech_degreewise_projection_comm`
keeps its original signature and docstring. The original sectionwise route is now a
complete Lean proof: construct actual intersections on each base open, prove their
maps to the categorical products are isomorphisms, transport the signed projection
and the alternating differential, and conclude by section and morphism extensionality.
All nine local helper declarations are private and proved; no public interface changes.

Added the proof-only import `WeilConjectures.Topology.Sheaves.CechComparison`,
which supplies the already proved `TopCat.Presheaf.cechComplexFunctor_d_π`; no copy of its proof or new statement
is needed. Retained the signed-extension import and original public import.
Updated the existing node's proof, proof_deps and proof_origin to describe the Lean proof,
including the explicitly used intersection model `def-weil-pbc-site-cech-complex`.
The unit's realized route is unchanged.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Modules.orderedCech_degreewise_projection_comm`
(node `lem-pc-ordered-cech-degreewise-projection-differential`).
Added 0 holes and split off 0 statements. No sorry remains in the delivered module.
This is a proof, not a decomposition.

The filtered-sum helper handles injective tuples by uniqueness of sorting and repeated
tuples by injectivity of strict increase. The signed-projection helper checks all faces
of every increasing tuple. The transport construction uses `Fin (p + 1)`, which is
nonempty even in degree zero; an empty cover has no full tuples and is covered by
product extensionality. Neither nonempty opens nor any cover hypothesis is assumed.

The completed module compiles through lcompile.py with no warnings. An independent
scratch copy with #print axioms reports only propext, Classical.choice and Quot.sound.

## No longer needed

Removed the redundant added proof-only import
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`: the file compiles without it.
None of the original imports or proof-dependency nodes is removed: all are used as
constructions, coordinate formulas, or the signed-extension theorem. No new postponed
coordinate-transport module is needed; the earlier draft is replaced by proved private
helpers. There are no new dependency items to dispatch.

## Where the brief, the DAG or earlier work was wrong

The previous attempts were blocked by the unpublished OrderedCechDegreewiseProjection
compiled artifact. It is now present in the shared build, and the original module and
completed proof compile. No dependency artifact or tool was rebuilt or changed by this
worker. Earlier scratch proofs of sorting and intersections were reused and completed.

The planned differential-transport step has an existing proved source-library formula,
`TopCat.Presheaf.cechComplexFunctor_d_π`, which was found by direct repository search.
Lean Finder returned generic Dold-Kan results; Loogle did not recognize the local
cechComplexFunctor identifier, and msearch grep returned no match. Direct rg found the
needed source declaration. The source module has no textual sorry.

The Stacks sources were checked at [01FJ](https://stacks.math.columbia.edu/tag/01FJ),
[01FK](https://stacks.math.columbia.edu/tag/01FK), and
[01FM](https://stacks.math.columbia.edu/tag/01FM). The first is the signed-extension
cochain-map lemma, the second ordered restriction, and the third the homotopy statement
for their composite. Their omitted compatibility verification is supplied here by
explicit transport and the already proved signed-extension theorem.

No statement correction, forced adaptation, change record, or new node is needed.

## Second reading by F4

1. Compared the delivered module with the repository using diff. The only existing
   declaration, `orderedCech_degreewise_projection_comm`, retains its signature and
   docstring byte for byte. Its proof replaces the original sorry; the nine added
   helpers are private. No public definition, statement, hypothesis or visibility
   changes, and no change record is required. Verdict: pass.
2. Compiled the module locally with lcompile.py, without warnings. An independent
   scratch copy of the delivered source with `#print axioms` for the public theorem
   reports exactly propext, Classical.choice and Quot.sound. No sorry, axiom, unsafe,
   opaque, implemented_by or extern appears in the delivered module. The intersection
   site uses explicit infima and universal maps, and the cochain is actual restriction
   of the supplied coordinates; neither chooses data from an unproved existence
   theorem. Verdict: pass.
3. There are no split-off statements or new nodes. Read each private helper:
   sorting uniqueness reduces the filtered sum to its single increasing permutation;
   noninjective tuples contribute zero; increasing faces give the differential
   identity from signedCechExtension_differential. The intersection/product map is
   an isomorphism by both containments. Fin (p+1) has its zero element also for p=0;
   r=0 gives an empty tuple product whose extensionality still applies. No cover,
   affineness or nonempty-open assumption enters any step. Verdict: pass.
4. Read SignedCechExtension and the source-library cechComplexFunctor_d_π proof.
   Repository searches for signed/ordered projection and differential compatibility
   found no shorter matching public theorem; AdditiveAlternatingCechCoordinates
   concerns an additive functor and ordered terms, not the supplied all-tuple
   identifications. The proof reuses the existing differential and signed-extension
   results and closes the target from section extensionality. A scratch compilation
   without ConcreteCategory.Basic passed, so that redundant added import was removed.
   The original public coordinate import and proof-only signed-extension import
   remain necessary; CechComparison supplies the differential expansion. All original
   proof_deps are used, so no original node is pruned. The unit record
   sk-thm-picard-coherence and its realized fields are unchanged, and the original
   sectionwise signed-projection route is kept. Verdict: pass after import pruning.
5. Compared the node JSON with the repository. Only proof, proof_deps and
   proof_origin change. Their five steps follow the intersection construction,
   signed-projection transport, differential expansion, signed-extension identity
   and extensionality actually used in Lean. The added dependency
   def-weil-pbc-site-cech-complex records the SiteCechComplex construction; all old
   dependencies remain used. No statement, source, unit, lean signature or review
   fields were altered. Verdict: pass.

Changed only the redundant added ConcreteCategory.Basic import, two blank lines within helper signatures,
and this report. No proof repair or additional hole was necessary. Closed 1 of 1
original holes; added 0 holes; split off 0 statements.
