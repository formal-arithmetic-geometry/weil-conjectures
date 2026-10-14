## What changed

Repair of reviewer X-dcde2: removed the duplicate private declaration
`topRestriction_mate_naturality`. Its sole use is now a local `have` specialized
explicitly to this commuting scheme square and its coefficient morphism. There is
no new library declaration of the generic mate-naturality statement. Public
signatures and definition bodies are unchanged.

An attempted import of `DerivedBaseChangeOpenUnit`, using its public
`mate_naturality`, compiled but the delivery gate reported an import cycle through
`DerivedBaseChangeMayerVietorisMaps` and the standard top-restriction theorem back
to this item. Therefore the final repair keeps the calculation local and introduces
no new import or DAG dependency.

The underlying delivery constructs the pullback-apex isomorphism and its coefficient
and direct-image comparisons, reducing compatibility to coefficient coherence.

## Proved and sorry left

Closed `AlgebraicGeometry.standardSingleBaseChange_topRestriction_compatibility`.
Added one hole: `AlgebraicGeometry.topRestriction_coefficient_coherence`
(node `lem-pc-top-restriction-coefficient-coherence-y3`). This is a decomposition:
one upper hole closed, one strictly smaller coefficient hole added, net zero.
No sorry remains in the item module. The supporting declarations
`AlgebraicGeometry.derivedSourceRestriction_unit_naturality` and
`AlgebraicGeometry.picardTermwiseSingleMap_isIso_of_iso` are proved.
This repair adds no further holes.

## No longer needed

Removed the duplicate private `topRestriction_mate_naturality` declaration.
No original import is removed. The new proof import `PicardSingleMapIso` was already
removed; its module remains needed through coefficient coherence. No original node
or module is pruned. The open restriction data node `def-pc-single-complex-open-restriction-data`
remains a direct dependency: the proof constructs `a` from it. The two old direct
proof dependencies `lem-pc-ringed-spaces-derived-pullback-composition` and
`lem-sc-picard-termwise-single-map-composition` are no longer direct dependencies;
they remain needed through the supporting nodes. Their modules are not pruned.

## Where the brief, the DAG or earlier work was wrong

The previous delivery duplicated the existing generic `mate_naturality` declaration.
Importing that declaration is impossible because it closes an import cycle, as
verified by deliver3.py. The calculation is now a local, fully proved identity with
explicit scheme-square binders, not a duplicate module-level statement.

## New nodes

The delivery retains three nodes from the earlier decomposition:
`lem-pc-derived-source-restriction-unit-naturality-y3` (proved),
`lem-pc-picard-single-map-iso-y3` (proved), and
`lem-pc-top-restriction-coefficient-coherence-y3` (the remaining coefficient hole).
No nodes were added in this repair. Change record:
`coord/changes/top-restriction-local-proof-attributes.md`.

## Second reading by Y3

1. Compared the complete item module with the repository using `diff -u`.
   All four existing declaration signatures, their visibility, and the source
   isomorphism definition body are unchanged. Only private helpers, proof imports,
   local proof attributes/options, and the compatibility proof are added. The
   local-attribute change record describes the only static interface classification.
2. Read all four delivered modules and compiled them in import order with
   `lcompile.py --all`: all pass. The only textual hole is the named public theorem
   `AlgebraicGeometry.topRestriction_coefficient_coherence`; there are no forbidden
   declarations or hollow definitions. The pullback apex, coefficient isomorphism,
   and direct-image comparison are explicit constructions. Choices of adjunctions
   and derived comparisons use their uniqueness/factorization properties; no new
   object is chosen from arbitrary unproved existence. A scratch import check with
   `#print axioms` on all four original declarations and three new declarations
   reports only propext, Classical.choice and Quot.sound for the source/unit and
   both proved support lemmas; compatibility and coefficient coherence also have
   the expected sorryAx from the one documented hole. An initial scratch copy
   recompiling the full item hit 60 seconds; the import-only check passed in 1.6 s.
3. Read the three new nodes against their Lean statements and proofs. The source
   unit identity is a proved mate/triangle calculation for any commuting square.
   The single-map invertibility theorem is proved by exactness of an equivalence
   and the left-derived uniqueness factorization. The one remaining hole is only
   the coefficient identity: it has no direct-image or base-change conclusion and
   is strictly smaller than the original compatibility claim. Its docstring gives
   the composition-factorization reduction and normalization of the exact open
   comparison. Checked zero modules, empty schemes and identity isomorphisms:
   nothing needs a nonempty scheme, flatness of r or r', or inversion of q_r or
   q_r'. Independent leanfinder, loogle and grep searches with derived single
   coherence and restriction terminology found constituents, not an exact match.
   Read PicardTermwiseSingleMapComposition, SingleComplexOpenRestrictionData,
   IsomorphismPullbackCounit and the isomorphic-single transport counit equation;
   the latter two concern different coefficient/counit presentations and do not
   close this hole by a short application. Stacks 08HY supplies the base-change
   mate and 0D5S composition; 08DW mentions open compatibility in its proof rather
   than stating the exact-restriction calculation itself.
4. The proof follows the canonical-source restriction route and uses existing
   composition results below the unit level. The unit record
   `sk-thm-picard-coherence.json` has no realized node replaced by this reduction;
   the unit and chapter route are unchanged. Original public imports are needed
   by unchanged signatures or the source definition. Both new item imports are
   proof-only. Supporting public imports supply symbols in their statements;
   PointwiseLeftDerived is already a plain proof import. No original module is
   pruned. The report now explicitly names both former direct dependencies moved
   below support nodes.
5. Compared the original node fields and all three new records with the Lean.
   Existing-node changes are confined to proof, proof_deps and proof_origin.
   New nodes contain statement, source, searches, complete proof steps, creation,
   blueprint and Lean records, and their proof_deps equal their steps' uses.
   Corrected the compatibility node to retain the directly used open-restriction
   data dependency. Statements and new-node signatures were not changed.

Second-reading changes: repaired that missing DAG dependency and made the
no-longer-direct dependency list explicit; retained the checked Lean proofs.
The delivery remains a decomposition (one original hole closed, one new hole,
net zero), with two proved supporting theorems.
