## What changed

In Sheaf.CategoryTheory.MapExtendHomology, expose mapExtendHomologyIso as the
explicit composite of homologyFunctor.mapIso applied to the upstream
HomologicalComplex.mapExtendIso and Mathlib extendHomologyIso. The existing
mapExtendHomology_nonempty_iso packages this data, with its signature unchanged.
Publicly import ExtendMap for the public data construction. Update the existing
node's lean.declarations, proof and proof_origin. No caller adaptation is needed.
Change record: coord/changes/map-extend-homology-canonical-iso.md.

Validation: the repaired module compiles without warnings. Both declarations'
#print axioms lists contain exactly propext, Classical.choice and Quot.sound.
The unchanged direct caller Sheaf.Paper.FreeRepresentableHomotopyHomology
compiles against the sandbox overlay (52.7 seconds). The delivery dry run passes;
the independent second reading below confirms the construction.

The duplicate mapExtendTermIso/mapExtendComplexIso are already absent from the
supplied base and from all callers. This completes the same upstream review's
request to expose the canonical isomorphism behind the existence statement,
without reintroducing either duplicate or choosing a witness.

## Proved and sorry left

mapExtendHomology_nonempty_iso remains completely proved.
mapExtendHomologyIso is a direct, fully implemented data construction.
Both belong to lem-weil-pbc-map-extend-homology. Zero original holes; zero holes
closed; zero holes added; zero holes remain. This is an API repair, not new net
proof progress or a decomposition. The construction covers q = 0 via
extendHomologyIso and does not require E to be exact.

## No longer needed

No additional imports, nodes or modules are pruned by this delivery. The former
duplicate mapExtendTermIso and mapExtendComplexIso are unnecessary: use upstream
HomologicalComplex.mapExtendX and mapExtendIso. Their removal was already in the
base. Both retained imports are used. The unit sk-thm-p1 route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous attempt interpreted this as a request to close a sorry and stopped
because the base already had a complete proof. The item is instead an explicitly
listed repair of upstream review #1424. Its duplicate-removal point was already
satisfied, and its related canonical-data API suggestion is completed here.
The existing DAG's mathematical statement is correct and stays unchanged.


## Second reading by W4

1. Compared the delivered module with the repository using diff. The sole existing
   declaration, mapExtendHomology_nonempty_iso, keeps its signature byte for byte,
   docstring and public visibility. The new data definition and the newly public
   ExtendMap import are explicitly declared in the change record. No target or
   existing definition changes. Verdict: pass.
2. Independently compiled the delivered file with lcompile.py, without warnings.
   Compiled its scratch copy with #print axioms for mapExtendHomologyIso and
   mapExtendHomology_nonempty_iso: each lists exactly propext, Classical.choice,
   Quot.sound. No sorry, axiom, unsafe, opaque, extern or implemented_by occurs in
   the delivered Lean. The data is an explicit composite, not an arbitrary witness
   selected from an unproved existence theorem. Verdict: pass.
3. No statement is split off and no new hole or node is added. Read upstream
   HomologicalComplex.mapExtendIso and Mathlib extendHomologyIso: the first uses
   preservation of zero morphisms (supplied by Additive), and the second applies
   to embeddingUpNat with the degree equality rfl. In particular q = 0 is covered;
   the zero complex and identity functor also require no extra hypotheses.
   Searched the local CategoryTheory and upstream homology sources for homology
   extension comparisons: the construction is precisely the two existing APIs,
   with no duplicate component or complex isomorphism. Verdict: pass.
4. The proof retains the shortest existing route, packaging its explicit composite
   as data. Both imports are needed: ExtendHomology for the signature and comparison,
   ExtendMap for the exposed definition body, so the public import is justified.
   Old proof_deps is empty and stays empty; no dependency is omitted from No longer
   needed. Read sk-thm-p1 realized: this helper is below the unit route and changes
   none of its realized nodes or steps. Verdict: pass.
5. Compared the node diff: only lean.declarations, proof and proof_origin change;
   the mathematical statement, recorded theorem signature, proof_deps, chapter and
   unit are unchanged. Both declaration names are recorded. The two proof steps
   match mapIso of mapExtendIso followed by extendHomologyIso. Verdict: pass.

Second-reading changes: no Lean or node edits were needed. Expanded the change
record's Old section with the verbatim original import and theorem, and recorded
this independent review. This remains an API repair with zero holes closed or
added, not new proof progress.
