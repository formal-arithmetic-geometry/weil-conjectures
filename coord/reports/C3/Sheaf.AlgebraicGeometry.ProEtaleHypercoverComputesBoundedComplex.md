## What changed

The existing signature of
`AlgebraicGeometry.Scheme.ProEt.hypercover_computes_boundedBelow_complex` is unchanged.
Its proof now constructs the derived comparison from the actual restriction augmentation
and proves the stated naturality equation, including the supplied homotopy. The final
quasi-isomorphism-invariance conjunct is also proved.

Nine new modules contain the constructions and comparisons used by this proof:

- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverAugmentation`: actual restriction maps,
  the row map, and the natural chain augmentation into total sections; no chosen data.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact`: exact evaluation
  proved from module-to-abelian sheaf forgetting, local surjectivity and the given
  weak-contractibility hypothesis.
- `Sheaf.Algebra.Homology.BoundedBelowTotalComparison`: integer-indexed column and row
  total comparison, proved by stupid truncation, the source library's proved
  finite-column theorem, and signed total-flip symmetry.
- `Sheaf.Algebra.Homology.BoundedBelowAugmentation`: total comparison for a single-column
  augmentation, with its explicit chain isomorphism to the augmenting complex.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverQuasiIso`: exact section columns, including
  restriction of scalars, and preservation of bounded-below coefficient quasi-isomorphisms.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverInjectiveRow`: applies the existing ringed
  hypercover injective-augmentation theorem after transporting the site and module sheaf
  through `ULiftHom`; converts the exact alternating sequence into the natural-degree
  quasi-isomorphism and then extends by zero to integer degrees.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverInjectiveComparison`: identifies the
  single-column row maps and applies the proved bounded-below augmentation comparison.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverLocalLifting`: the actual underlying slice
  augmentation and a complete proof of the fan/multicospan matching construction,
  face compatibility, and factorization of every lower-simplex operator through a face.
- `Sheaf.AlgebraicGeometry.ProEtaleRepresentableEpiLocalLifting`: the one remaining
  single-morphism represented-sheaf epimorphism/local-lifting criterion.

The finite-column comparison uses the existing proved source declaration recorded by
`lem-sc-integer-finite-column-total-comparison`; this dependency adds no hole.

The DAG now follows these exact steps. No existing definition or theorem signature was
changed, and no held module was adapted. All new proof imports are non-public. New public
imports are restricted to the declarations needed by their signatures and definitions.
The public affine-hypercover import is retained: the direct caller
`ProEtaleModuleCohomologyCoproducts` uses its exported existence theorem. It also supplies
the matching-diagram definitions, so the redundant direct source matching import was
removed during the second reading. The previous public K-injective import is replaced
by derived-category Basic. In the new exact-evaluation module, the general abelian Exact
API is proof-only; only its narrower PreservesHomology API is publicly imported.

Validation: `lcompile.py --all` compiled all ten modules without warnings, each within the
60-second per-file limit. The slowest is the injective-row transport (about 31 seconds);
the item itself compiles in about 12 seconds. The statement was checked against the
original declaration, and every new definition is a concrete construction. The local
lifting statement was checked on degree zero (no lower simplices), degree one (two
vertices), positive degrees (proper-face compatibility), and empty test schemes/sieves.
The total-comparison arguments allow negative bounds and degrees with empty diagonals.
No target statement or blueprint unit realization was changed. The current direct callers are `ProEtaleModuleCohomologyCoproducts` and
`CondensedQcqsPushforwardContinuity`; their unchanged source copies are checked against
the delivery overlay in the scratchpad and are not delivered.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.Scheme.ProEt.hypercover_computes_boundedBelow_complex`
(node `lem-weil-pbc-proetale-hypercover-computes-bounded-complex`).

The new public theorem proofs are complete:
`weaklyContractible_evaluation_preservesHomology`,
`HomologicalComplex₂.quasiIso_totalMap_of_boundedBelow_columns`,
`HomologicalComplex₂.quasiIso_totalMap_of_boundedBelow_rows`,
`HomologicalComplex₂.quasiIso_of_boundedBelow_row_augmentation`,
`hypercoverTotal_map_quasiIso_of_weaklyContractible`,
`hypercoverRowAugmentationComplex_quasiIso_of_injective`,
`hypercoverAugmentation_quasiIso_of_injective_rows`, and
`hypercover_matching_local_lifting`, together with the restriction
augmentation equations and naturality lemmas. The private bounded-below cylinder
argument proving homotopy invariance is complete as well.

One new hole remains:
`AlgebraicGeometry.Scheme.ProEt.representable_epi_local_lifting` in
`Sheaf.AlgebraicGeometry.ProEtaleRepresentableEpiLocalLifting`
(node `lem-weil-pbc-proetale-representable-epi-local-lifting`). It concerns one morphism
of the pro-etale site: if its represented map is epic, every morphism into its target
lifts on a covering sieve. It mentions neither simplicial objects, matching limits,
module coefficients, injectivity, cohomology, bounded complexes, totalization nor derived
categories. The previous all-degree geometric local-lifting split is now fully proved
from this narrower criterion, not merely renamed: the proof constructs matching cones
in the given slice limits, checks the face-pair identity, transports local lifts over
the augmentation, and proves the equality for every smaller simplex operator by finite
cardinality and face factorization.

The remaining theorem's main task is the value-universe justification. The standard
image-sieve argument is available in Mathlib if sheafification exists in the same value
universe. Here representables are `Type u`-valued while the ready-made pro-etale
sheafification instance uses `Type (u+1)`. The docstring and node explain the size route:
fix bounded affine weakly contractible refinements, use finite clopen partitions on
those compact projective objects to obtain small refinement diagrams, and descend to
small associated sheaves. This construction, or another proof that epic represented
maps have covering image sieves in this precise universe, still needs to be formalized.
Do not replace the input by a larger-universe epi assumption. The existing bounded
weakly contractible cover node is a planned dependency of this size argument; it is
not claimed obsolete by the import-closure list below.

Thus this delivery closes one original hole and adds one new hole: it is a decomposition,
not an axiom-free proof of the target. It also uses the existing
`CategoryTheory.ringedHypercover_injective_augmentation_exact`; D2 has now supplied a
proof in the current repository, so the earlier report calling that theorem open was stale. No claim is made that imported dependencies are sorry-free
or that item-only import counts equal the project's pinned target-closure ledger counts.

## No longer needed

Removed direct imports:

- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`: resolutions and their
  quasi-isomorphisms are inputs.
- `Sheaf.Algebra.Homology.FirstQuadrantTotalComparison`: integer truncation and the
  existing finite-column theorem replace reindexing to the first quadrant.
- `Sheaf.CategoryTheory.DoubleComplexTotal` and
  `Sheaf.CategoryTheory.RingedSiteModules`: redundant direct imports through
  `ProEtaleHypercoverTotal`.
- `Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentation`: the new injective-row
  module imports and applies it instead.
- `Mathlib.CategoryTheory.Sites.EpiMono` and
  `Mathlib.CategoryTheory.Sites.LocallySurjective`: used in the exact-evaluation module.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`: replaced by Basic;
  a bounded-below cylinder proves the required homotopy invariance.

`Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover` remains a public import for
its downstream user. The new direct source matching-object import was redundant and
has been removed. In the new exact-evaluation module, `Mathlib.CategoryTheory.Abelian.Exact`
is a plain proof import, with `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
providing the signature's public API. The sheaf-module Abelian import remains public:
its instance dependencies are required for the signature's PreservesZeroMorphisms instance.

Every old direct proof dependency removed from the item's node is listed below.
Several remain indirect dependencies or supply the unchanged statement's vocabulary;
this list does not claim they leave the targets' closure.

```text
def-pur-kinjective-complex
def-sp-double-complex-total
def-weil-sheaf-of-modules-category
def-weil-size-convention
lem-sc-bounded-below-injective-resolution
lem-sc-first-quadrant-total-column-comparison
lem-sc-kinjective-quasi-iso-comparison
lem-weil-pbc-proetale-affine-acyclic-hypercover
lem-weil-pbc-ringed-hypercover-injective-augmentation
lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective
lem-weil-pbc-site-sheaf-sets-epi-locally-surjective
```

The abelian/set-sheaf epi criteria and ringed injective augmentation are used through
new lower nodes; the size convention remains relevant to the remaining hole.
Module-sheaf and total-complex definitions remain in the statement and constructions.
Resolution existence, K-injective comparison, first-quadrant reindexing, and matching
object existence are unused: resolutions, homotopies and limiting cones are inputs.
The affine-hypercover existence theorem is unused by this proof but re-exported for
its caller. The unit's realized statements and steps remain intact.

The complete project-module import-closure difference for this item alone is:

```text
Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
Sheaf.Algebra.Homology.FirstQuadrantTotalComparison
Sheaf.Algebra.Homology.FirstQuadrantTotalComparisonFinite
Sheaf.Algebra.Homology.FirstQuadrantTotalExtension
WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
WeilConjectures.Mathlib.Algebra.Homology.ExactSequence
WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic
WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
```

Nodes attached to those modules:

```text
lem-sc-bounded-below-injective-resolution
lem-sc-finite-row-total-column-comparison
lem-sc-first-quadrant-total-column-comparison
lem-sc-total-extension-nat-arrow-iso
lem-sp-first-quadrant-spectral-object-abutment
lem-weil-pbc-ring-sheaves-grothendieck
thm-sp-double-complex-spectral-sequences
```

These are eleven modules absent from this item's new import closure. A separate current
source-graph traversal from TargetsCheck finds no project module removed from the global
target closure, so globally pruned modules are none. Progress figures remain those of
the pinned sorry ledger. No files are deleted.
The earlier list of 661 modules was computed before the affine-hypercover import was
restored; the second reader recomputed it against the delivered imports.

## Where the brief, the DAG or earlier work was wrong

The planned selection of injective resolutions and K-injective representatives is
unnecessary for this Lean signature: it quantifies over resolutions and assumes the
comparison map and homotopy. Constructing them would prove unused obligations.

The planned first-quadrant reindexing obscures total signs and shifts. The source library
already proves finite-column comparison; an integer stupid truncation and three-term
homology comparison prove exactly the bounded-below statement needed here.

The generic ringed-hypercover theorem assumes a `SmallCategory`, while the pro-etale
site has objects in `Type (u+1)` and morphisms in `Type u`. The implementation resolves
this by `ULiftHom`, pulling back the precoverage and transporting module sheaves and
injectivity along an explicit equivalence. No change to D2's held theorem was needed.

There is a separate universe issue in the geometric lifting step: the target's represented
matching epimorphisms are maps of `Type u`-valued sheaves, whereas the readily available
pro-etale sheafification instance is for `Type (u+1)`. Mathlib's epi/local-surjectivity
criterion requires sheafification in the same value universe. This is recorded in the
remaining represented-epi node and its docstring rather than concealed in a typeclass
assumption. The matching-cone and simplex-factorization part has now been proved.
No counterexample was found and the statement has not been marked disputed.

## New nodes

`def-weil-pbc-proetale-hypercover-augmentation` (Sheaf.AlgebraicGeometry.ProEtaleHypercoverAugmentation): Restriction augmentation into total hypercover sections. Its construction and/or proof is complete in Lean.

`lem-weil-pbc-bounded-below-row-augmentation` (Sheaf.Algebra.Homology.BoundedBelowAugmentation): Comparison of a row augmentation with a bounded-below total complex. Its construction and/or proof is complete in Lean.

`lem-weil-pbc-bounded-below-total-column-comparison` (Sheaf.Algebra.Homology.BoundedBelowTotalComparison): Column and row comparison for uniformly bounded-below integer bicomplexes. Its construction and/or proof is complete in Lean.

`lem-weil-pbc-proetale-hypercover-injective-complex-comparison` (Sheaf.AlgebraicGeometry.ProEtaleHypercoverInjectiveComparison): Injective row descent implies descent for bounded-below injective complexes. Its construction and/or proof is complete in Lean.

`lem-weil-pbc-proetale-hypercover-injective-row` (Sheaf.AlgebraicGeometry.ProEtaleHypercoverInjectiveRow): An injective module sheaf has a quasi-isomorphic hypercover section row. Its construction and/or proof is complete in Lean.

`lem-weil-pbc-proetale-hypercover-local-lifting` (Sheaf.AlgebraicGeometry.ProEtaleHypercoverLocalLifting): Matching-map epimorphisms imply local lifting of all lower simplex data. Its matching-diagram and simplex-factorization proof is complete in Lean; it uses the narrower represented-epi criterion.

`lem-weil-pbc-proetale-hypercover-total-quasi-iso` (Sheaf.AlgebraicGeometry.ProEtaleHypercoverQuasiIso): Weakly contractible sections preserve bounded-below total quasi-isomorphisms. Its construction and/or proof is complete in Lean.

`lem-weil-pbc-proetale-weakly-contractible-evaluation-exact` (Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact): Exact module-sheaf evaluation at a weakly contractible pro-etale object. Its construction and/or proof is complete in Lean.

`lem-weil-pbc-proetale-representable-epi-local-lifting`
(`Sheaf.AlgebraicGeometry.ProEtaleRepresentableEpiLocalLifting`): local lifting along one
represented epimorphism in its actual value universe. This is the only new sorry;
its universe-small associated-sheaf or equivalent image-sieve argument is described above.

Change record: `coord/changes/C3-proetale-hypercover-proof-imports.md` records the
public-import pruning and its unchanged effect on all five current downstream modules. No
existing signature or definition was changed.


## Second reading by C3

1. **Existing interface: PASS.** Compared every delivered module with the repository:
   nine modules are new, and only the assigned existing module is changed. Compared the
   raw source span of `hypercover_computes_boundedBelow_complex` through its signature,
   byte for byte: identical. No existing definition, binder, universe or conclusion
   changed, and no held or unheld client was adapted. The public KInjective-to-Basic
   replacement is declared in `coord/changes/C3-proetale-hypercover-proof-imports.md`.

2. **Proof and trust: PASS as a decomposition.** Read all ten modules (1,460 original
   lines), including the cylinder proof, total-sign convention, zero extension, matching
   cone construction and ULiftHom transport. Compiled all ten cleanly via lcompile.py;
   the slowest took 29.8 seconds. Recompiled the two import edits. A scratch file prints
   axioms for the item, all main comparison results and the explicit augmentation:
   only propext, Classical.choice and Quot.sound occur, with sorryAx additionally on
   the represented-epi theorem and the results depending on that hole. Scanned parsed
   Lean declarations for forbidden axioms/unsafe/opaque/extern/implemented_by and for
   hollow definitions: none. Every construction is explicit; no data is extracted from
   the unproved mere existence statement. The sole delivered sorry is exactly the body
   of the public named theorem `representable_epi_local_lifting` with its source,
   natural-language proof and matching node. One original hole closed, one new hole
   added: net zero holes closed by this delivery.

3. **Remaining statement: PASS, still open.** The new represented-epi statement is the
   single-morphism image-sieve criterion, strictly below matching data, injective rows
   and derived evaluation; it does not restate the item. Checked identity morphisms
   (top sieve), arbitrary base change of a lift, and empty schemes; the matching proof
   handles no lower simplices at zero, the two vertices at one, and arbitrary proper
   simplices by the finite-cardinality argument and face factorization. Integer total
   truncation also handles negative lower bounds and empty diagonals. Independently
   searched with msearch leanfinder, loogle and grep using epic representables, large
   sites, image sieves, value universes and balanced sheaves, and read Mathlib's actual
   epi criterion. The general theorem requires HasSheafify in the same value universe;
   the available larger-universe instance does not discharge this input. No shorter
   applicable proof or counterexample was found. The docstring describes the small
   associated-sheaf construction still to formalize; the statement is left unchanged.

4. **Route and pruning: PASS after corrections.** The top proof uses the supplied
   resolutions and homotopy rather than proving unused existence/comparison theorems.
   Its reductions are genuine constructions and proved comparisons, including the
   already proved finite-column library result. Read the unit's realized statement
   and three steps in `dag/units/sk-thm-properbasechange.json`; none is bypassed or
   edited. Removed the redundant direct matching-object public import; retained the
   affine-hypercover re-export required by ProEtaleModuleCohomologyCoproducts. Made
   Mathlib.CategoryTheory.Abelian.Exact proof-only in the new evaluation module and
   publicly imported its signature's narrower PreservesHomology API. Retained the
   public sheaf-module Abelian import, whose instance dependencies are needed to
   elaborate the signature (removing it fails PreservesZeroMorphisms synthesis). Corrected the
   obsolete 661-module closure list to the actual eleven, listed every removed old
   direct proof dependency, and distinguished indirect uses and global pruning (none).
   Both current direct clients, ProEtaleModuleCohomologyCoproducts and
   CondensedQcqsPushforwardContinuity, compile unchanged against the delivery overlay
   in 8.9 and 8.3 seconds respectively.

5. **DAG and records: PASS.** Checked all ten node records against the actual declarations
   and proof steps: proof_deps is exactly the union of the steps' uses; the only existing
   node changes proof, proof_deps and proof_origin. All nine new nodes have their source,
   searches, split status, created record, blueprint provenance, chapter, unit and Lean
   declaration record. The local-lifting node records the proved fan/multicospan and
   lower-simplex argument; its one dependency isolates the value-universe epi criterion.
   Added the independent leanfinder/grep results to that remaining node. Corrected the
   change record's old claim that affine-hypercover re-export was removed and refreshed
   its users to the five current downstream modules. The report now also reflects D2's
   landed proof rather than describing the ringed augmentation theorem itself as open.

Second-reading changes: import visibility and redundancy cleanup, refreshed the remaining node's search
record, and corrected the report and change record. No theorem proof or statement
required replacement. Scratch sources and logs remain outside the delivery's lean/ tree.

Final validation: deliver3.py --no-push returned OK after the second-reading repairs,
including all per-file compiles, declaration axiom probes and stage-3 preflight.
