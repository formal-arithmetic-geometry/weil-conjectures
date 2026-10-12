## What changed

Completed the inherited sandbox attempt. The item now proves independence of all resolution
choices and the restriction square, preserving all six existing theorem signatures and visibility.
The two naturality clauses and pullback composition keep the library's existing proofs.
General composition remains open.

Added the proved module `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapComparison`, providing
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMapData_comparison`.
Its two private helpers extend natural-indexed complexes by zero and use Mathlib's
K-injective localization bijection for existence and the existing homotopy-uniqueness
lemma for uniqueness. The public theorem simultaneously compares lambda and beta;
it makes no assertion about cohomology. The item's independence proof applies sections
and homology to those homotopies, proves naturality of the sections and resolution
comparison isomorphisms, and cancels the invertible homology maps.

Restriction constructs the restricted module map by transposing across the restriction
adjunction. Its unit square follows by inverse cancellation, and the cohomology square
follows from the existing composition clause and equality transport in the scheme map.
This is an actual adjunction construction, with no witness taken from an unproved existence
statement. Updated the item's DAG proof, dependencies, and proof origin accordingly.

Proof imports added to the item: `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapComparison`
and `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`. The new comparison module
publicly imports the choice-data module (which already exports Homotopy), and
privately imports Mathlib KInjective and the existing LiftToInjectiveUniqueUpToHomotopy
module for its proofs.

Validation: both modules compile in import order with lcompile.py --all, without warnings.
The independent-delivery dry run also checks signatures and axioms. No target or definition
was changed. Source passages read: Stacks Cohomology section-functoriality,
lemma-functoriality (01F8) and remark-explain-arrow (01FB); Derived
lemma-morphisms-lift (013P) and lemma-morphisms-equal-up-to-homotopy (013S).
The local literature mirror supplied these passages because this clone lacks the tex files.

## Proved and sorry left

Closed two of the item's three original holes:

- `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_independent`
  (node `lem-weil-pbc-module-cohomology-fmap-functorial`).
- `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_restriction`
  (the same node), from the still-open composition clause.

Remaining hole, unchanged:

- `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_comp`
  (node `lem-weil-pbc-module-cohomology-fmap-functorial`). Its docstring retains the
  complete common-injective-complex composition argument. Unlike independence,
  composition must compare pushed complexes across two scheme morphisms;
  pushforward of lambda is not assumed quasi-isomorphic, so the independence
  lifting argument alone does not close this clause.

Added holes: none. The new comparison theorem and every private helper are proved.
No sorry is present in a definition. The existing source/target naturality and
pullback composition proofs are preserved and depend on the composition clause.
The closure-hole decrease is two; this is not a claim that restriction's transitive
axioms are sorry-free.

## No longer needed

Removed imports: none. Globally pruned nodes or modules: none claimed.
The shorter independence route needs no degreewise-monic replacement and does not
import ComplexInjectiveResolutionMono, LiftAlongInjectiveQuasiIso,
InjectiveResolutionLiftExists, DerivedFunctorMapViaLift, or
HomotopicMapsEqualCohomology solely for independence. Their facts needed here are
proved directly using Mathlib and the existing uniqueness theorem. These were not
imports of the item's current baseline, and the still-open composition argument
may need further comparison machinery, so no global pruning of them is claimed.
The unit sk-thm-p1's realized statement and proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The inherited attempt was compilable but had neither a report nor DAG records for
its new public comparison theorem. This delivery supplies both and accurately
records that composition remains open. It does not relabel composition as a new
hole. No mathematical statement error or forced adaptation was found.

Mathlib searches found resolution comparison and K-injective localization machinery,
not an existing theorem on these scheme-module cohomology maps. The logged LeanSearch
query returned an Internal Server Error and is recorded as unavailable, not as a
negative mathematical result.

## New nodes

`lem-weil-pbc-module-cohomology-fmap-comparison` records the proved simultaneous
homotopy comparison theorem in ModuleCohomologyFMapComparison. Its proof is the
013P(1) existence argument followed by 013S uniqueness, using Mathlib's K-injective
Hom computation as a tool. It is strictly below independence: it concerns maps
and homotopies of complexes only, with no cohomology inverses or resolution transports.
No hypothesis requires lambda to be monic. The identity-choice case, arbitrary
quasi-isomorphic auxiliary injective complexes, and empty schemes introduce no
extra condition. Restriction also covers empty and full opens because its construction
uses only the supplied adjunction and comparison isomorphisms. Blueprint searches
for comparison/injective material found no existing exact statement of this simultaneous
choice-data comparison; its ancestor and unit agree with the item's. No change records
are necessary.

## Second reading by V2

1. Interface: diffed the entire item against the repository version. All six existing
   theorem signatures, visibility, and docstrings are byte-for-byte unchanged; only
   proof bodies, private helpers, and proof-only imports differ. The comparison module
   is new. No existing public definition, target, or statement changed. Verdict: pass.

2. Kernel and holes: compiled both modules in import order with lcompile.py, without
   errors or warnings. Scratch-copy `#print axioms` checks show exactly propext,
   Classical.choice, and Quot.sound for moduleCohomologyFMapData_comparison and
   moduleCohomologyFMap_independent. Composition, both naturality clauses, pullback
   composition, and restriction additionally use sorryAx. There is precisely one
   textual sorry, the unchanged named moduleCohomologyFMap_comp; no new holes,
   forbidden declarations, or holed definitions occur. In restriction, psiV is the
   explicitly written adjunction transpose, not an arbitrarily chosen witness.
   Verdict: pass as a partial proof; two of three original holes closed.

3. New comparison statement: read Derived lemma-morphisms-lift (013P), part (1),
   and lemma-morphisms-equal-up-to-homotopy (013S), and Cohomology
   lemma-functoriality (01F8) and remark-explain-arrow (01FB), in the local source
   mirror /home/ubuntu/weil-launcher/maint/bp/work/literature/stacks-project/.
   Kprime is termwise injective and bounded below after extension by zero; lambda
   is quasi-isomorphic, with no unsupported monicity hypothesis. The first square
   is 013P(1); the second follows by precomposition with the quasi-isomorphic J
   augmentation and 013S. Checked the degree-zero augmentation equations explicitly.
   Identity choices permit e=identity and reflexive homotopies; zero complexes and
   empty schemes do not invalidate any hypothesis. This theorem is strictly below
   independence: it asserts only chain maps and homotopies, with no cohomology
   identification or inversion. It is fully proved, not a split-off hole. Fresh
   LeanFinder search for lifting a chain map across a quasi-isomorphism into a
   bounded below injective complex, Loogle search for Homotopy and QuasiIso, and
   rg searches in lean/Sheaf and the source library found generic resolution and
   K-injective machinery, not this simultaneous comparison. The existing uniqueness
   theorem is used directly. Verdict: pass; no duplicate exact statement found.

4. Route and pruning: read the independence cancellation proof from its target
   equality downward. It uses the two comparison homotopies, the canonical sections
   square (pinned by C.sections), and Mathlib resolution/homology naturality;
   it does not assume pushed identity descents are quasi-isomorphisms. Restriction
   cancels the two comparison isomorphisms after adjunction transposition, then uses
   composition and scheme-map equality elimination. The old proof_deps consisted
   only of the choice-data definition and basic-properties node, both still used;
   none was omitted from No longer needed. Read sk-thm-p1.json realized: neither
   this item nor the new helper replaces a realized unit statement or step, and
   the unit route remains unchanged. Removed the redundant direct public Homotopy
   import from the new module after a successful scratch compile without it.
   The choice-data import already exports the required Homotopy type. Other imports
   supply statement types, K-injective localization, uniqueness, basic properties,
   or the enough-injectives instance actually used. Verdict: pass.

5. DAG: compared the old and delivered item node. Only proof, proof_deps, and
   proof_origin changed; the union of step uses agrees with proof_deps. The new
   comparison node's verbatim Lean statement matches the theorem, its steps match
   the private lifting/uniqueness helpers and augmentation argument, and its
   chapter, unit, source, created, blueprint, search, and lean records are present.
   Read the K-injective Mathlib leaf and the existing uniqueness theorem: they
   provide exactly the localization bijection and homotopy cancellation used.
   No new unresolved statement or change record is required. Verdict: pass.

Second-reading changes: removed one redundant public Mathlib Homotopy import from
ModuleCohomologyFMapComparison; corrected the import description above and appended
this review. The mathematical proofs and node records needed no repair.
