## What changed

Proved `ChainComplex.scalarCone_iso_of_coordinates` in
`Sheaf.Algebra.Homology.ChainConeCoordinatesIso`, with the existing signature and
visibility unchanged. The proof follows all three steps of
`lem-pc-chain-cone-coordinates-iso`: construct degreewise isomorphisms, check
both differential projections, and assemble with
`HomologicalComplex.Hom.isoOfComponents`.

The private helpers construct actual isomorphisms, using `extendXIso`, the supplied
linear equivalences, `LinearEquiv.prodComm`, `ModuleCat.biprodIsoProd`,
`biprod.mapIso`, and `homotopyCofiber.XIsoBiprod`. Degree zero uses
`isoZeroBiprod`; positive degrees use the unique isomorphism of zero objects.
The negative-degree first projection is the second coordinate of `e`; its
second projection is the first coordinate. Applying `mappingCone.d_fst_v`
and `mappingCone.d_snd_v` reduces compatibility to `Prod.snd` and `Prod.fst`
of `hd`. The boundary differential reduces to `h₀`; differentials into positive
degrees vanish. No cancellation or division by the scalar is used.

No imports, statements, definitions used by other modules, or DAG routes changed.
All new helpers are private and fully proved. The unit's route is preserved.

Searches were run through msearch.py: LeanFinder for scalar cone coordinates,
Loogle for `CochainComplex.mappingCone, CategoryTheory.Iso`, and grep for
`scalarCone|isoOfComponents|extendXIso`. They found the generic cone and complex
assembly APIs but no exact existing result. Direct searches covered both source
roots and Mathlib's homology and ModuleCat files.

Validation: the complete module compiles through lcompile.py with no errors or
warnings. The required delivery dry run also checks declaration signatures and
axioms. The construction includes zero rings, zero modules, and zero scalar:
only linear equivalences and zero-object properties are used.

## Proved and sorry left

Closed the one original hole:
`ChainComplex.scalarCone_iso_of_coordinates`
(node `lem-pc-chain-cone-coordinates-iso`).

No `sorry` remains in the item. No holes were added or split off, and no other
modules were changed. This is a complete proof, not a decomposition.

## No longer needed

None. The original DAG has no proof-dependency nodes and the proof uses exactly
its planned Mathlib APIs. All four original public imports are retained:
extension to integer cochain complexes, linear structure on complex morphisms,
mapping cones, and ModuleCat biproduct instances. The biproduct instances are
also needed to elaborate the mapping-cone expression in the statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The local copy of
`literature/stacks-project/more-algebra.tex` is absent; the cited sources were
read online at https://stacks.math.columbia.edu/tag/0628 and
https://stacks.math.columbia.edu/tag/0629. They provide the scalar cone matrix
and its Koszul application; the present generic coordinate assembly is the
explicit extension-by-zero argument already recorded in this item's DAG.

## Second reading by K3

1. Interface: PASS. Read the complete repository/sandbox diff and compared the
   existing header, imports, theorem docstring and signature byte for byte.
   The only additions are private helpers and the replacement proof body.
   There are no changed public definitions, signatures, or change records.
2. Proof: PASS. Compiled the delivered module with lcompile.py without errors
   or warnings. Compiled a scratch copy with
   `#print axioms ChainComplex.scalarCone_iso_of_coordinates`: exactly
   `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   Scanned the delivered source for sorry and forbidden declarations: none.
   The four private isomorphism definitions construct their data explicitly
   from supplied equivalences, canonical biproduct isomorphisms, and zero-object
   isomorphisms; none chooses an undetermined witness of an unproved theorem.
3. Split statements: PASS, vacuous. No statements or holes were split off.
   Read every private helper, including both coordinate projections and their
   commutation equations. At degree -2 to -1 the first cone projection is
   the negative L differential of the second supplied coordinate; the other
   projection is the L differential of the first coordinate plus its scalar
   term. At -1 to 0, h₀ gives the second projection and the first has zero
   target. At 0 to 1 and all higher degrees the cone target is zero. These
   arguments also cover zero scalar, zero modules and the zero ring, without
   scalar cancellation or a nontriviality hypothesis.
4. Route and pruning: PASS. Read the original node's three planned steps and
   the unit `sk-thm-picard-duality` with its unchanged `realized` field. The
   component construction, projection checks and isoOfComponents assembly
   realize those steps without bypassing a unit. Independently searched the
   library and Mathlib for cone coordinate and degreewise-splitting results,
   including an msearch.py grep query with different terminology. Inspected
   mappingConeHomOfDegreewiseSplitIso: it needs a short complex, degreewise
   splittings and identification of its shifted connecting morphism, so it
   does not provide a shorter direct application here. All four public
   imports support the existing statement: extension and embedding, scalar
   multiplication on complex morphisms, mapping cones, and ModuleCat
   biproduct instances. No proof-only public import was added; no original
   proof_deps node or module can be pruned.
5. DAG: PASS. The existing node `lem-pc-chain-cone-coordinates-iso` already
   records precisely the degreewise construction, cone projection equations,
   boundary cases and Mathlib assembly used by this proof. Its empty
   proof_deps and agent-expanded source attribution remain accurate: only
   Mathlib APIs and the theorem's own hypotheses are used. No new nodes are
   required and no existing node field needs correction.

Changes by the second reader: appended this independent review and recorded
an additional search. No Lean, import, signature, definition or DAG repair
was necessary. Holes closed: ChainComplex.scalarCone_iso_of_coordinates;
holes added: none. One of one original holes is proved, with zero split off.
