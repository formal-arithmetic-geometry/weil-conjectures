## What changed

Constructed increasing-tuple cochains, their signed differential, and degree restriction
in Sheaf.AlgebraicGeometry.AlternatingCechComputes. Proved restriction commutes with the
differential and is surjective by extension by zero. Epimorphism cancellation reduces
its differential-squared identity to SiteCechComplex.differential_squared. Constructed
A and r with CochainComplex.of/ofHom, proved both coordinate formulas, and used the
homotopy inverse lemma plus Mathlib HomotopyEquiv.toHomologyIso for the last clause.
All original signatures and existing docstrings are unchanged. New proof-only imports:
Mathlib.Algebra.Category.Grp.EpiMono and
Sheaf.AlgebraicGeometry.AlternatingCechRestrictionHomotopy.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.Scheme.alternatingCechComputes by a compiling
reduction. There are no sorries in its module. Added one lower hole:
AlgebraicGeometry.Scheme.alternatingCechRestrictionHomotopy, node
lem-pc-alternating-cech-restriction-homotopy. Its whole proof is `:= by sorry` in its
own new module. This is a decomposition: one hole closed, one added, net zero holes.
The construction of A, its square-zero differential, r, and both formulas are proved
independently of the new lemma. The remaining lemma assumes those objects and asserts
only the signed-extension homotopy inverse; it neither constructs A nor repeats the
target's conjunction of existence and coordinate formulas.

The new statement was checked on empty I (zero complexes), singleton I (the full
alternating constant complex contracts to degree zero), empty opens and arbitrary
presheaves, infinite I, degree zero, and arbitrary degree identifications e. Restriction
is degreewise surjective, so its chain-map equation forces A's differential in those
coordinates; no extra differential hypothesis is missing. No cover hypothesis is
needed for the new lemma. Both modules compile locally without warnings.

## No longer needed

No original imports removed and no modules pruned. Second reading removed the newly
added redundant proof import Mathlib.Algebra.Homology.HomologicalComplexAbelian; the
needed homology instances are already available through the remaining imports. The parent's direct proof edge to
def-sc-zariski-site is moved into the homotopy lemma, where the poset property identifies
permuted/repeated intersections. This does not prune it from the transitive argument.
The existing SiteCechComplex module remains required. No Dold-Kan, normalized Moore,
Čech-computes-sheaf-cohomology or spectral-sequence modules are imported.

## Where the brief, the DAG or earlier work was wrong

The DAG steps 2 and 3 were labelled elementary despite containing signed extension and
two substantial homotopy calculations. These are now the explicit remaining theorem,
with a sourced natural-language proof and its own node. Step 1 and square-zero do not
need any sorting argument: restriction, surjectivity, and cancellation suffice.
The local repository has no literature/stacks-project/cohomology.tex; read the primary
Stacks pages at https://stacks.math.columbia.edu/tag/01FJ,
https://stacks.math.columbia.edu/tag/01FK and https://stacks.math.columbia.edu/tag/01FM.
Current Tag 01FK is Lemma 20.23.4, rather than the old section-number label in the
existing docstring. Tags remain stable. LeanSearch returned Internal Server Error;
recorded unavailable, not absence. LeanFinder and grep found no comparison theorem.
The unit route is unchanged: full Čech to increasing-tuple Čech still uses signed
extension and the two 01FM homotopies.

## New nodes

lem-pc-alternating-cech-restriction-homotopy records
AlgebraicGeometry.Scheme.alternatingCechRestrictionHomotopy in
Sheaf.AlgebraicGeometry.AlternatingCechRestrictionHomotopy. It isolates the homotopy
inverse argument for a supplied complex and supplied restriction map, for arbitrary
families of opens. The signed extension and both homotopies are described in its
docstring and proof steps. Searches covered LeanSearch (unavailable), LeanFinder,
Loogle and Mathlib grep; blueprint searches for 01FM and homotopy Cech found no node.
No change record is needed: existing public signatures and public imports are unchanged.

## Second reading by E2

1. PASS. Compared both delivered modules with the repository: the homotopy module is
   new, and the sole existing declaration alternatingCechComputes has a byte-for-byte
   unchanged signature and docstring. All existing public imports stay unchanged.
   The added definitions and verification lemmas are private. No change record is needed.
2. PASS as a decomposition. Independently compiled both modules in import order using
   lcompile.py. Scratch copies with #print axioms show only propext, Classical.choice,
   Quot.sound and sorryAx. The only textual hole is the whole proof of the named public
   theorem alternatingCechRestrictionHomotopy. No forbidden declarations or hollow
   definitions occur. A, its differential, and r are explicit constructions; the proof
   chooses an inverse map only locally to prove a proposition, never to define data.
3. PASS. The new lemma supplies only the homotopy inverse for an already supplied
   restriction chain map; it does not supply the complex, the differential construction,
   or the coordinate formulas. Degreewise surjectivity of restriction forces the supplied
   differential, so no missing hypothesis permits a counterexample. Reviewed empty and
   singleton index types, degree zero, repeated opens, empty opens, arbitrary presheaves,
   arbitrary coordinate isomorphisms and infinite index types. Verified both cited
   homotopy formulas as integer coefficient identities on 510 tuples with index sizes
   0 through 3 and output degrees 0 through 4. These finite checks supplement the
   natural-language cancellation proof; they do not close the Lean hole. Read Stacks
   Tags 01FJ, 01FK and 01FM independently. New LeanFinder and Loogle queries using
   deformation retract, permutation signs and repeated-index deletion returned general
   homotopy, mapping-cone and simplicial-splitting results, not this comparison. Mathlib
   grep found no semi-ordered or ordered-Cech theorem. Searched both Lean roots and
   inspected the upstream MonomialCech special-case contraction and the downstream
   QCohComplexAlternatingCechDerivedSections statement; neither proves this lemma.
4. PASS after import pruning. The shortest available construction uses restriction and
   epi cancellation for square-zero, then Mathlib HomotopyEquiv.toHomologyIso. The new
   hole is the genuine remaining signed-extension and homotopy step. Removed the
   redundant newly added HomologicalComplexAbelian proof import and checked compilation
   without it. No original module is pruned. The old direct edge def-sc-zariski-site
   is explicitly accounted for under No longer needed and retained transitively in the
   new lemma. Read sk-thm-picard-pn.json: its realized statement and step lists are empty;
   no realized node is bypassed, and the full-to-increasing Cech route is preserved.
5. PASS. Checked both node files against the Lean signatures, constructions and proof
   calls. Each proof_deps is precisely the union of its proof-step uses. The new node
   has its source, complete proof steps, search records, creation fields, blueprint
   ancestry, chapter, unit and matching Lean record. Existing node changes concern only
   the actual proof route. One original hole is closed by reduction and one new hole is
   added: net zero, expressly a decomposition, not a completed comparison proof.

Changes: removed one redundant proof-only import; corrected the new lemma's citation
of 20.23.5 to 20.23.4 (Tag 01FK), and clarified which identity uses the zero homotopy.
No theorem statement or construction changed. Added this independent review and clarified
import pruning in the report. The remaining homotopy lemma requires substantial formal
sorting and sign calculations, so it was not claimed closed by these finite checks.
