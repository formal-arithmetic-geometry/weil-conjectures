## What changed

Repaired reviewer X-c13ba's E5/H3 and C4 findings. The corrected object-cohomology
signature of AlgebraicGeometry.etaleCohomologyOverOpen is retained, and the prose node
statement is byte-identical to the clone. The false global-cohomology signature is not
restored. The public existence theorem remains proved from the exact Ext adjunction.

Moved the concrete representing-isomorphism and Ext-comparison constructions into the
new module Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison, with a matching data
node. Its public etaleCohomologyOverOpenEquiv specifies one comparison for every coefficient
sheaf and open; it does not choose an equivalence from Nonempty. Its coefficient naturality
is proved using mapExtCounit_comp_mk₀ and Ext associativity. The existing etaleOpenFreeSheaf
is reused by abbreviation. Global-cohomology restriction is independently constructed from
cohomologyMap and the canonical inverse-image/restriction and composition isomorphisms.

Repair of landing return X-e5dd8 (head e5dd88cac): removed the three duplicate
wrapper declarations etaleCohomologyOverOpen_naturality,
etaleCohomologyOverOpen_restriction, and etaleCohomologyOverOpen_quasiCoherent.
The clauses are available through public imports under their original names:
- AlgebraicGeometry.etaleCohomologyOverOpenEquiv_naturality, in
  Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison;
- AlgebraicGeometry.etaleCohomologyOverOpenEquiv_restriction, in
  Sheaf.AlgebraicGeometry.EtaleOpenCohomologyRestrictionCompatibility;
- AlgebraicGeometry.etaleTensorSectionsSheaf_openIdentification, in
  Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentification.

The item's sole public theorem uses etaleCohomologyOverOpenEquiv directly. The
restriction compatibility import is now public to expose that clause without a wrapper.
Updated the item's proof text and lean.declarations to agree; the prose statement and
all clause signatures in their defining modules are unchanged. No adaptation is needed.

The two remaining
obligations have separate modules, nodes, sources, complete proof docstrings and edge-case
checks. The quasi-coherent sheaf lives in AddCommGrpCat.{u}; its restriction therefore uses
the continuous site functor directly, preserving its section data and coefficient universe.
No arbitrary sheaf-isomorphism witness is used to define data.

Restored the original clone proof[4] as proof[3] (step 4), adjusted its reference to the new
restriction-identification step, and restored all five uses to proof_deps. Replaced
proof[2]'s unencoded-clauses disclaimer with the names of the declarations and obligations
covering every clause. Added lem-weil-pbc-etale-inverse-image-restriction to proof[0].uses
and proof_deps, as required by C4. Change record:
coord/changes/etaleCohomologyOverOpen-object.md.

## Proved and sorry left

The original single hole AlgebraicGeometry.etaleCohomologyOverOpen
(lem-weil-pbc-etale-cohomology-over-open) is closed after its documented signature correction.
It compares Ext from the free sheaf on the open object with cohomology on that open.
This is not a proof of the old false global-cohomology proposition.

Newly proved, with no direct or transitive sorry: AlgebraicGeometry.etaleCohomologyOverOpenEquiv
and AlgebraicGeometry.etaleCohomologyOverOpenEquiv_naturality. The representing and sections
helpers are also proved, and all data constructions are real definitions.

Two holes added, each the whole proof of a named public theorem in its own module:
- AlgebraicGeometry.etaleCohomologyOverOpenEquiv_restriction
  (lem-weil-pbc-etale-open-comparison-restriction), in
  Sheaf.AlgebraicGeometry.EtaleOpenCohomologyRestrictionCompatibility.
- AlgebraicGeometry.etaleTensorSectionsSheaf_openIdentification
  (lem-weil-pbc-etale-open-qcoherent-identification), in
  Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentification.

No direct sorry remains in the item's module. The two publicly imported obligations
are not claimed to be sorry-free proofs. They supply strictly smaller clauses than the
full prose node, whose concrete comparison and coefficient naturality are proved.
One original hole is closed after its signature correction and two holes are added:
this remains a decomposition with net minus one, not a proof of the old false statement.
The removed wrappers contributed no additional proof and no holes.

Validation for this repair: all four delivery modules compile without errors or warnings.
The unchanged current direct importer Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
also compiles against the repaired sandbox overlay. deliver3.py --no-push with server
compilation explicitly enabled printed OK: the single commit was based on current
origin/sheaf-dag, local/server compilation and axiom checks passed, and the preflight
passed except for the pending independent second reading. Nothing was pushed. The direct import_prune_check.py check against the refreshed
library also exits successfully with no findings.
The earlier second reading was removed because it describes the refused wrapper version;
the second reader must review this repair independently. No delivery will be pushed here.

Edge cases: identity inclusions give
the usual composition/unit comparisons; degree zero gives the actual sections at j and
restriction along k; empty opens and zero sheaves give zero groups. The quasi-coherent
component formula applies on the empty or identity open and to the zero module, without
an affine, finite-type or separation hypothesis. The independent reader must check the two
obligations as mathematical statements; they have not been proved here.

## No longer needed

Removed duplicate wrapper declarations (no replacement aliases):
- AlgebraicGeometry.etaleCohomologyOverOpen_naturality;
- AlgebraicGeometry.etaleCohomologyOverOpen_restriction;
- AlgebraicGeometry.etaleCohomologyOverOpen_quasiCoherent.

Their original clause modules remain necessary and publicly imported; this repair
removes no further module or node dependency.

The following original node dependencies are not used by the repaired route:
- lem-weil-pbc-etale-site-localization-open
- lem-weil-pbc-cohomology-over-object-localization
- lem-weil-pbc-etale-cohomology-invariance-under-site-equivalence
- lem-weil-pbc-bounded-below-injectives-kinjective
- def-weil-pbc-global-sections-functor

Removed original imports still unused throughout this route:
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
- Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
- Sheaf.CategoryTheory.Sites.CohomologySiteEquivalence

EtaleTensorSectionsSheaf, EtaleTensorSections and TensorPullback are needed again for the
quasi-coherent clause and are imported through the new identification module. They are
not pruned. In particular lem-weil-pbc-etale-inverse-image-restriction is retained for the
exactness argument and the canonical restriction comparisons, and all five original
quasi-coherent-step uses are retained. Removed redundant explicit imports from the new
comparison-data module after compiling: SheafCohomology.Basic, LowerShriek.OpenImmersion.Defs,
Grp.AB, GrothendieckCategory.EnoughInjectives, GrothendieckAbelian.Sheaf, and Ext.Basic;
these are already public dependencies of EtaleOpenObjectCohomologyMap. No claim of global
unreachability is made. The unit sk-prop-cd has empty realized arrays for this item; its
statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

X-e5dd8 correctly identified duplicate clause statements. Applying the original theorem
inside a newly named wrapper still restated the same fact and failed import_prune_check.py.
The repair removes those declarations entirely and uses their defining modules' public API.

E5/H3 was a real omission: the earlier delivery proved the pointwise comparison but
explicitly left three clauses of the unchanged prose node unencoded. The repair now
encodes all three. Coefficient naturality is proved for the same constructed comparison;
smaller-open compatibility uses that comparison and independently specified restriction
maps; the quasi-coherent clause includes the original prescribed composition/restriction
component formula. Neither the prose statement nor the corrected object-cohomology
signature has been weakened.

C4 was a missing dependency citation: the exactness proof uses
localizationRestrictionLowerStarAdjunction, recorded under
lem-weil-pbc-etale-inverse-image-restriction. That node is now in proof[0].uses and
proof_deps and is removed from the pruning list.

The original stage-2 signature's global-cohomology left side remains false, as the
preserved degree-zero obstruction demonstrates. Mathlib H' still has the wrong coefficient
universe for the existing binders, so the corrected theorem retains the explicit
large-universe Ext/free-representable formulation.

## New nodes

- def-weil-pbc-etale-open-comparison-data: the concretely constructed comparison,
  representing/sections helpers, coefficient naturality, and independently specified
  global restriction map; module Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison.
- lem-weil-pbc-etale-open-comparison-restriction: precisely the smaller-open commutative
  square, with one public sorry obligation and its full proof plan.
- lem-weil-pbc-etale-open-qcoherent-identification: precisely the quasi-coherent sheaf
  identification and specified sectionwise components, with one public sorry obligation.
- lem-sc-ext-exact-adjunction: retained from the first delivery; records the existing
  proved source Adjunction.extAddEquiv and adds no hole or module.

For the new nodes LeanSearch was run and returned an Internal Server Error (unavailable).
Loogle found the degree-zero H naturality tools, and LeanFinder found module-restriction
formulas, but no missing-clause theorem. Local rg found the exact Ext coefficient
naturality theorem used here. The search-service grep returned no match for the queried
combined names. Blueprint searches found no duplicate; the three new nodes point to the
item's ancestor lem-sc-artin-schreier-dimension, via this item and its original ancestor
chain. Source arguments were checked at [Stacks 03F3](https://stacks.math.columbia.edu/tag/03F3)
and [Stacks 03DR](https://stacks.math.columbia.edu/tag/03DR). Change record:
coord/changes/etaleCohomologyOverOpen-object.md.


## Second reading by F2

1. **Visible declarations and statements.** Compared the delivered item with the repository copy. The
item's changed signature is exactly the Old/New change record, while all unchanged declarations retain
their signatures. The three added clause declarations occur only in their new modules; no duplicate
wrapper remains. Verdict: pass, with the documented target correction reviewed as a CODEX change.

2. **Proof and axioms.** Compiled all four delivered modules with `lcompile.py --all`; compilation is
clean. Sorries occur only in the two named public split theorems, with matching nodes and docstrings;
no definitions contain sorry and no forbidden declarations occur. The closed comparison and naturality
proofs use the explicit representing isomorphism and exact Ext adjunction. Verdict: pass subject to the
two declared obligations, which are intentionally split and therefore carry `sorryAx` transitively.

3. **Split statements.** Checked both split statements against their node text, component formulas,
hypotheses, coefficient universes, and edge cases (identity and empty opens, zero coefficients, and
q = 0). The restriction square uses the concrete free-sheaf map and independently defined restriction;
the quasi-coherent clause specifies every component rather than choosing an arbitrary isomorphism. Local
search found no existing declarations duplicating either statement. Verdict: pass; both are strictly
smaller clauses needed by the item.

4. **Route and pruning.** The item uses the concrete comparison, the existing exact Ext adjunction,
coefficient naturality, and the two named clause obligations. Removed duplicate wrappers and the listed
localization/site-equivalence imports and nodes; retained inverse-image restriction and all dependencies
needed by the quasi-coherent step. Verdict: pass; the unit route and `realized` data are preserved.

5. **DAG agreement.** Checked the item and three new node JSON records against declaration names,
verbatim statements, proof steps, proof dependencies, sources, and split status. The report's proved/
sorry-left accounting and pruning list agree with the files. Verdict: pass.

Changed during this reading: no Lean declarations or node statements; only this independent-review
section was appended. The delivery dry run initially hit temporary filesystem exhaustion; generated local
build artifacts were cleared before rerunning delivery.
