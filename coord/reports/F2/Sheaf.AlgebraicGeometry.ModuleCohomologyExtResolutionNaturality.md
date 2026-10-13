## What changed

Fully proved the original coefficient naturality theorem by constructing its explicit
common-resolution natural isomorphism. Generic resolutionSectionsObjIso and
resolutionSectionsNatIso package exact forgetting, the identity section-complex
identification and the acyclic-resolution comparison. The original Ext.precompAddEquiv handles the terminal source change,
with its naturality supplied by Mathlib Ext.comp_assoc_of_third_deg_zero; identity natural isomorphisms identify its
Ext functor with the existing evaluated cohomology and Sheaf.functorH.
The original equivalence now reads the same component maps from this construction.
Its public signature and the theorem's signature are unchanged. The definition
refactor is recorded in coord/changes/moduleCohomologyExtResolutionEquiv-section-identification.md.

Removed the first worker's equivalent function-equality hole and its proposed node.
Added a plain proof-only AcyclicComparisonNatural import. All public imports
remain needed by definition data, including Ext.Basic for extSourceNatIso.
No downstream module is delivered or adapted.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.Modules.moduleCohomologyExtResolutionEquiv_naturality.
One of one original holes proved; zero holes added; zero split off; no sorry remains
in the item. All new constructions have explicit data and proved laws.
The proposed moduleCohomologyExtResolutionEquiv_naturality_hom hole is removed,
not moved or counted as a second baseline hole closed.


## No longer needed

No original dependency or module is pruned. All three original proof_deps remain
used: acyclic comparison naturality, forgotten-injective acyclicity and
injective-resolution lift naturality. The unit's realized route is unchanged.
The unlanded equivalent-restatement node
new-module-cohomology-ext-resolution-naturality-hom is removed.

## Where the brief, the DAG or earlier work was wrong

The first worker's function-equality square was equivalent to the original theorem
by funext/congrFun. Moving its entire hole there was not a strictly simpler
reduction and did not prove the item. Removed it and completed the actual
common-resolution argument. Generic construction and Mathlib's functorial Ext
source map resolve the elaboration timeout without introducing any new hole.

## Second reading by F2

1. Compared the entire delivered item against the repository. All 18 existing declaration signatures are unchanged; the equivalence
and theorem signatures are also byte-for-byte identical. Earlier declarations stay
unchanged. The equivalence data refactor preserves each component function and
inverse as explained in the change record; no hypothesis or target meaning changes.
No downstream module is edited.
2. Compiled the complete item locally without errors or warnings, below 60 seconds.
No sorry, axiom, unsafe, opaque, implemented_by, extern or hollow definition occurs
in it. Scratch #print axioms checks cover the original theorem/equivalence and the
new natural comparison and generic resolution construction: each uses only
propext, Classical.choice and Quot.sound; no sorryAx. The final axiom scratch (including extSourceNatIso)
compiled cleanly in 59.7 seconds. The delivery probe checks every declaration
and the dry run passed.
3. Removed the equivalent-restatement split rather than accepting it. No split-off
statement remains. Alternative searches used mapHomologyIso naturality,
isoRightDerivedObj naturality and acyclic-resolution terms through loogle,
leanfinder and grep; the existing primitive results are used directly. The generic
argument covers degree zero, zero objects/morphisms and empty schemes and adds
no scheme or coefficient assumptions.
4. Read the proof from the target downward. The concrete common-resolution route
is retained; terminal-source naturality is Mathlib Ext associativity rather than a
new associativity lemma. Checked the imports, all original proof dependencies,
and sk-thm-p1's realized route. No old proof dependency is unused.
5. The existing node's proof, proof_deps, proof_origin and declaration list now
match the completed Lean construction. Statement/dependencies and unit realization
remain unchanged; there are no new nodes. All new definitions contain real maps
and proved naturality, with source docstrings.

Second reading replaced the bogus split with a complete proof, retained the
resolution-normalized comparison, and packaged the original precompAddEquiv
component using Mathlib's Ext.comp_assoc_of_third_deg_zero.


The first dry run exposed a deliver3.py diagnostic-parser fault: after a trial
removal of Ext.Basic, the normalization file correctly failed with
error(lean.unknownIdentifier), but forced_adaptations recognizes only error: or
error[. No script is modified. The final construction instead uses the original
precompAddEquiv in extSourceNatIso's data, so Ext.Basic is needed and retained;
there is no adaptation to classify or deliver. Its final naturality proof uses
Ext.comp_assoc_of_third_deg_zero directly after extensionality.
