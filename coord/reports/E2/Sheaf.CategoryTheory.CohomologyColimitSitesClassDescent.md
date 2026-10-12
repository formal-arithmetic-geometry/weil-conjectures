## What changed

Replaced the sorry in `Sheaf.CategoryTheory.CohomologyColimitSitesClassDescent`
with induction on the degree, generalizing the coefficient system, its inverse-image
diagram, its colimit cocone and the cohomology comparison diagram. Degree zero uses
`cohomology_colimit_sites_degree_zero_descent`. In degree n+1 the connecting ladder
lifts the target class to the degree-n cokernel system; the induction hypothesis
represents the lift at a stage, and evaluating the commuting square proves that the
stage connecting image represents the original class.

Added two statement modules and their nodes. The ladder constructs lower-degree
data independently of the induction hypothesis: it does not assert descent in the
original degree or even descent for the returned cocone. The zero lemma is confined
to degree zero. Their sources and detailed proof plans are in their docstrings and
nodes. Updated the original node's proof, proof_deps and proof_origin to match the
Lean induction. All original public imports and the original elaborated signature
are preserved; no definition or existing statement changed.

All three modules compile locally in import order, with no errors or other warnings.
The interface comparison reports no changed signature and no changed public interface.
The delivery dry run also checks compilation on the server, declaration axioms and
preflight; its final result is recorded by the delivery tool.

## Proved and sorry left

`CategoryTheory.cohomology_colimit_sites_class_descent` is proved from the two
intermediate statements, with no sorry in its body. This is a reduction, not a claim
that its transitive dependency closure is already free of sorry.

The only sorries left by this delivery are:

- `CategoryTheory.cohomology_colimit_sites_degree_zero_descent`, node
  `lem-weil-pbc-colimit-sites-degree-zero-descent`, in
  `Sheaf.CategoryTheory.CohomologyColimitSitesDegreeZeroDescent`.
- `CategoryTheory.cohomology_colimit_sites_connecting_ladder`, node
  `lem-weil-pbc-colimit-sites-connecting-ladder`, in
  `Sheaf.CategoryTheory.CohomologyColimitSitesConnectingLadder`.

Both are public named theorems with proof exactly `by sorry`, source references,
complete proof plans and matching DAG signatures. No new definition is introduced.

Edge cases checked: at n=0 the ladder is the usual section-to-H1 connecting map;
for a zero coefficient system both comparison groups are zero. A one-object index
reduces to ordinary injective dimension shifting on one site. Empty covering
families remain allowed. J and Under i are nonempty by filteredness and the identity
arrow; no extra nonemptiness assumption was added. The formal nonunital cocycle is
handled by normalizing identity idempotents in the ladder proof plan. The diagram
identity laws ensure this preserves the groups to which the induction is applied.

## No longer needed

Removed the following direct proof imports from the item's module:

- `Sheaf.CategoryTheory.ColimitSiteCechComplex`.
- `Sheaf.CategoryTheory.ColimitSiteSections`.
- `Sheaf.CategoryTheory.SiteCechVanishingCriterion`.
- `Sheaf.CategoryTheory.SiteInjectiveCechAcyclic`.
- `Sheaf.Paper.ColimitSitesInjectiveSystem`.
- `Sheaf.CategoryTheory.SiteCechComplex`.

Their roles are deferred to the two new nodes: the section comparison belongs to
the degree-zero node, and the injective/Cech argument belongs to the connecting-ladder
node. Those modules' unfinished theorems need only the two public statement imports
to typecheck; their planned proof dependencies are recorded in the DAG. No unused
proof import remains in a delivered file. No global pruning of those six modules
is claimed, and no unit statement or realized unit step is bypassed.

The original plan's explicit stage-injective higher-cohomology vanishing and its
source right-exact colimit row are unnecessary for class existence: only the target
connecting map must be surjective. Stage connecting maps need not be surjective.
No global pruning of `lem-weil-pbc-derived-functor-injective-vanishing` is claimed,
since it can still be reached through other proofs. Exact filtered group colimits
remain needed for the Cech acyclicity part of the ladder.

The complete old direct `proof_deps` replaced by the two new nodes are:

- `lem-weil-pbc-colimit-of-sites`
- `def-weil-pbc-sites-and-cohomology`
- `def-weil-pbc-category-colimit`
- `lem-weil-pbc-site-cohomology-pullback`
- `lem-weil-pbc-colimit-of-sites-sections`
- `lem-weil-pbc-colimit-of-sites-injective-system`
- `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`
- `lem-weil-pbc-colimit-of-sites-cech-complex`
- `lem-weil-pbc-site-injective-cech-acyclic`
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`
- `def-weil-pbc-site-cech-complex`
- `lem-weil-pbc-site-cech-vanishing-criterion`
- `lem-weil-pbc-derived-functor-injective-vanishing`

The first twelve remain in the planned proofs of the split nodes (and the
statement dependencies still describe the signatures); only the last is no
longer needed by this class-existence argument. This is direct dependency
replacement, not a claim that these modules are globally unreachable.


## Where the brief, the DAG or earlier work was wrong

`ColimitSiteSections` states a comparison for a fixed diagram of sheaves on the
colimit site, not the inner inverse-image section formula or the entire varying-site
comparison. Applying it directly would not prove the degree-zero case. The new
zero node explicitly includes the inner-colimit/reindexing step from 0A35 and 09YN.
`exists_colimit_site` supplies section data for the site it constructs; using it for
an arbitrary specified object-and-arrow colimit V also requires transporting that
data through the colimit equivalence.

The cocycle hφ contains no explicit identity law. The new ladder proof plan first
splits its identity idempotents, then uses the supplied diagram identity equations
to transfer the ladder back. It does not silently assume unital stage transitions.

The source's generic right-derived long-exact sequence uses rightDerived functors,
whereas these signatures use H' = Ext from the free representable. The ladder plan
requires the object-cohomology long exact sequence and its naturality. This can be
obtained directly from Mathlib's Ext exact sequence, or by the existing bridge; the
new theorem isolates this work rather than pretending the signatures coincide.

The local Stacks tex and blueprint folders are absent on this machine. Read the
online primary-source pages 09YP, 0739, 09YN and 0EXZ, and the unit record
`dag/units/sk-thm-p1.json`. The two nodes cite those online sources. LeanSearch was
unavailable (Internal Server Error); recorded as unavailable, not as no match.
LeanFinder and actual Mathlib grep queries were run and logged. Blueprint node
searches for 09YN and connecting maps found no duplicate of either new statement.

## New nodes

`lem-weil-pbc-colimit-sites-degree-zero-descent` states only degree-zero
finite-stage existence, with the degree-zero section identifications, inner-colimit
comparison, finite-covering outer comparison and finite-stage representative proof.
It is carried by `CohomologyColimitSitesDegreeZeroDescent.lean`.

`lem-weil-pbc-colimit-sites-connecting-ladder` constructs a compatible degree-n
coefficient system and comparison cocone, a surjective map to the original
degree-(n+1) target, and stage maps commuting with the comparison legs. Its proof
plan normalizes identity actions, embeds into an injective system, takes cokernels,
proves colimit injective acyclicity by Cech complexes, and constructs connecting maps.
It assumes no induction hypothesis and asserts no finite-stage representative.
It is carried by `CohomologyColimitSitesConnectingLadder.lean`.

There are no change records: existing statements and definitions are unchanged.

## Second reading by E2

1. Compared all delivered files with the repository. The existing declaration's
   signature is byte-for-byte unchanged, verified separately from its proof;
   all three DAG `lean.statement` strings match their declarations. Existing
   node changes are confined to `proof`, `proof_deps`, and `proof_origin`.
   The original two public imports are preserved and the new proof imports are
   private. No change record is needed.

2. Compiled all three modules in import order through `lcompile.py --all`:
   clean, no warnings. Read the entire induction: it generalizes the coefficient
   system and all dependent diagrams; the successor hypothesis is applied to
   degree n, not n+1. Surjectivity supplies z, induction supplies x, and evaluating
   `hcomm t` at x yields the desired equality by hx and hz. Only the two reported
   public split theorems have `by sorry`. No definitions or forbidden declarations
   are introduced. A scratch copy with `#print axioms` for all three theorems
   returned exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`
   (the last is expected from the open split statements). The delivery checks
   also probe every declaration's axioms.

3. Read the primary Stacks pages 09YP, 0739, 09YN and 0EXZ, and the statements of
   `siteCohomology_pullback`, `exists_compatible_injective_system`,
   `colimitSite_sections_isIso`, `colimitSite_cech_complex_isIso`, and
   `isZero_H'_of_siteCech_vanishing`. The zero split is precisely the degree-zero
   finite-stage existence assertion. It requires the inner inverse-image formula
   in addition to the fixed-site section theorem. The ladder is a strictly
   smaller dimension-shifting construction: its conclusion contains no finite-stage
   existence claim. Target acyclicity makes its connecting map surjective;
   stage acyclicity is unnecessary for existence. The supplied map families'
   three clauses match the uniqueness characterization in `siteCohomology_pullback`,
   so no unstated choice of comparison maps is being imposed.

   Checked n=0 (the section-to-H1 boundary), zero coefficients, and the one-object
   constant-site case. Empty coverings require no new nonemptiness hypothesis;
   filteredness already makes J and Under i nonempty. Also checked the nonunital
   coefficient issue: identity actions are split idempotents; the identity laws
   of S and D force their images to give the same inverse-image system and the
   same degree-(n+1) stage groups. The stage boundary for the normalized system
   is followed by the inclusion on cohomology to give the original endpoints.
   This normalization must precede the compatible injective embedding.

   Ran a fresh LeanFinder query for Ext degree zero, Yoneda, sections, and
   dimension shifting, plus launcher Mathlib grep and repository/upstream searches
   for surjective connecting maps and varying-site continuity. Ext exactness and
   the existing fixed-category dimension-shifting theorem are ingredients, not
   either new varying-site statement. No duplicate was found. The upstream
   `Sheaf.H.δSucc_surjective` uses H rather than this signature's H'; its Ext
   argument explains the ladder's surjectivity but does not construct the system.

4. The induction and two split nodes retain the degree-zero/injective-Cech/
   dimension-shifting route of 09YP. All six removed proof imports are now listed,
   including `SiteCechComplex`, and all thirteen old direct proof dependencies
   are explicitly accounted for. Read `dag/units/sk-thm-p1.json`: none of its
   realized statement or step nodes is bypassed or changed. The two sorries
   contain substantial further work; neither can be closed by one of the
   searched declarations in a few minutes.

5. Checked each DAG step against the Lean proof and each split signature. The
   original node lists exactly the two theorems the induction uses. The new
   nodes distinguish their planned proofs from proved code, carry complete
   Lean signatures and source/search/blueprint/creation records, and list the
   union of their steps' dependencies. The ladder's node already explains the
   normalization; its Lean docstring needed the same explanation.

Changes made by this reading: completed the pruning report (sixth import and
all old direct dependency ids), expanded the ladder docstring's normalization
argument, and corrected indentation in the successor proof. No signature,
definition, proof step, or node statement was changed.
