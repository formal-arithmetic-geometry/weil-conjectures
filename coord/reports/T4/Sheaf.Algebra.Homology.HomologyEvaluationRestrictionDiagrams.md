## What changed
Replaced the rejected duplicate core theorem with three strictly simpler comparison
statements. The assigned theorem now proves its five squares by combining the
Hom-cycle projection/quotient comparisons with the internal-Hom inclusion/quotient
transport comparisons. `map_three_square` is a proved private categorical helper:
Functor.map_comp and associativity combine the projection and source-cycle squares.
The six isomorphisms are then inserted as existential witnesses. The assigned
statement, universe and public imports are unchanged.

New proof imports are OpenOverInternalHomComparison,
OpenOverHomComplexCycleProjectionComparison and OpenOverInternalHomCycleHomologySquares.
No data definition, axiom, target statement or other existing module is changed.
The term proof avoids expensive tactic normalization of the dependent existential
motive. The assigned file compiles within 60 seconds without increasing the time limit.
Its command header has no added local attributes or instance definitions.

## Proved and sorry left
Closed the original hole in
`CategoryTheory.homologyEvaluation_restriction_diagrams` by a genuine decomposition.
The private helper `CategoryTheory.map_three_square` is proved without sorry.

Added three named holes, one per new module:
- `CategoryTheory.openOver_internalHom_comparison`
  (new-t4-open-over-internal-hom-comparison): natural comparison for module objects only.
- `CategoryTheory.openOver_homComplex_cycle_projection_comparison`
  (new-t4-open-over-hom-complex-cycle-projection-comparison): the Hom-cycle projection
  and quotient squares, without internal-Hom transport of T and J cycles/homology.
- `CategoryTheory.openOver_internalHom_cycle_homology_squares`
  (new-t4-open-over-internal-hom-cycle-homology-squares): the four internal-Hom
  transport squares, without any Hom-complex product or differential comparison.

This is a decomposition, not a sorry-free proof: 1 upper hole closed and 3 lower
holes added. Every remaining proof is exactly `by sorry`, with its source,
complete proof in words, edge-case discussion and matching DAG node. There is no
sorry in the assigned module or in any definition.

## No longer needed
No existing library proof-dependency module is pruned globally: the original
projection and exactness ingredients remain in the lower comparison plans.
The original assigned module had only its public definitions import, which stays.
Removed the earlier sandbox-only duplicate HomologyEvaluationRestrictionDiagramsCore
and its import, and replaced the earlier sandbox-only
OpenOverHomComplexProjectionComparison with the strictly partial cycle/projection
comparison. The earlier direct DerivedHomMayerVietoris import is absent from the
assigned module; its exactness API is needed by the lower comparison plans.
These discarded sandbox scaffolds were never landed and are not counted as
library pruning.

## Where the brief, the DAG or earlier work was wrong
The previous core statement repeated the assigned statement verbatim and closed
nothing by reduction; it is removed. The compile limit is not a tool failure.
The actual argument has two independent sets of squares joined by a categorical
composition identity, now written in Lean.

The new statements work on empty opens, zero complexes and unbounded integer
complexes. The natural comparison e is required to be an isomorphism in every
pair of objects and natural in both arguments, so its induced product comparison
commutes with both signed differential summands. Exactness supplies cycle and
homology comparisons without an acyclicity or boundedness hypothesis. No new
statement asserts evaluation on homology or assumes it already exists.
The unit route is unchanged: these are subdivisions of steps 1 and 2 of the
parent restriction plan, below the local finite-duality calculation.

Searches were run with msearch: LeanFinder returned complex-index restriction
lemmas, Loogle did not index ShortComplex.mapCyclesIso, and grep located the
exact-functor cycle/homology comparison API. LeanSearch returned an Internal
Server Error, recorded as unavailable. Whole-blueprint searches found no existing
node stating either new collection of squares. The abstract restriction-isomorphism
modules lack the fixed product-projection identities needed here.

## Earlier second reading (a previous round; superseded)
The assigned theorem has the exact target statement and combines two strictly partial
comparison statements plus the natural internal-Hom statement. The first lower node
contains only the Hom-cycle projection and quotient squares; the second contains only
the four internal-Hom transport squares. The three lower signatures preserve all
opens, empty cases, integer indices and category objects. Their `sorry`s are named,
documented, and recorded in matching DAG nodes.

## New nodes
new-t4-open-over-internal-hom-comparison states the natural module-object comparison
through the open-site equivalence and the two localization comparisons.

new-t4-open-over-hom-complex-cycle-projection-comparison states only the projection
square on Hom cycles and its cycle-to-homology quotient square, for a supplied
natural internal-Hom comparison e.

new-t4-open-over-internal-hom-cycle-homology-squares states only the internal-Hom
transport squares for source and target cycles/homology, for the same supplied e.
It contains no Hom-complex object or product projection.

The parent node proof/proof_deps/proof_origin now follow the Lean assembly of
these three steps. No change record is needed: existing statement signatures and
public imports are unchanged.

## Second reading by T4

1. Compared the assigned module with the repository version. All existing declaration signatures and definitions are byte-for-byte unchanged; only proof imports, a private helper, and the target proof changed. The three added modules contain the documented split statements.
2. Compiled all four delivered modules with `lcompile.py`; the three split declarations remain the only `sorry`s, with no forbidden declarations or hollow definitions. The assigned theorem itself is sorry-free. Its axioms are inherited only through the split comparison theorems.
3. Checked each split statement against the target and library search results. The internal-Hom comparison, Hom-cycle projection comparison, and internal-Hom cycle/homology squares are strictly smaller than the target and retain the stated hypotheses and conclusions; their docstrings give complete constructions and edge cases, and matching DAG nodes are present.
4. The proof uses the three split comparisons and the private categorical composition lemma. The public import remains the definitions module; proof-only imports are private. No prior proof-dependency module is unused or pruned, and the unit route through restriction, cycle, and homology comparisons is preserved.
5. Checked the DAG node proofs, dependencies, origins, and realized unit route against the Lean proof. They match the decomposition and the three new nodes have the required metadata.

Changed during second reading: added this review section only; no Lean or DAG changes were needed.
