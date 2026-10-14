## What changed

Repaired the false universal pinned-equation helpers in
Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedData. The corrected
perfect_hom_open_restricted_stage_pinned and perfect_hom_open_restricted_limit_pinned
now take equivalence/naturality fields plus their stage/apex identity normalizations.
Their complete proofs use original and restricted testing-object naturality and
naturality of the concrete restriction map. The conjunction helper is corrected
accordingly and proved by pairing these lemmas.

The parent perfect_hom_open_restricted_data keeps its exact signature. It now constructs
compatible restricted equivalences, derives all pinned equations, proves transition and
cocone compatibility at identities and then all testing morphisms, supplies the existing
QCoh fields, and assembles PerfectHomPushPullData explicitly. It no longer applies an
assertion about arbitrary independently chosen representing data.

Four new acyclic modules contain the unchanged concrete map definitions, construction of
normalized equivalences, specialization of existing cartesian transport, and the proved
transition equations. All their proofs compile from existing named dependencies; none has
sorry. The constructions choose supported extensions only inside proofs; the resulting
Hom equivalences are uniquely determined by pinning and naturality. No data is defined
using an arbitrary unproved mere-existence witness.

Change record: coord/changes/perfect_hom_open_restricted_data_compatibility.md.
The three concrete definitions retain their names, signatures, bodies and visibility via
public re-export. The parent signature matches the repository parser exactly. No other
existing module is edited. The unit sk-thm-picard-semicon has empty realized statement and
step lists; no realized unit statement or step is bypassed.

## Proved and sorry left

Textual holes closed: AlgebraicGeometry.perfect_hom_open_restricted_stage_pinned
(new-perfect-hom-open-restricted-stage-pinned) and
AlgebraicGeometry.perfect_hom_open_restricted_limit_pinned
(new-perfect-hom-open-restricted-limit-pinned). These are proofs of corrected true
statements, not proofs of the old false universally quantified types.
Holes added: none. Sorry left in the delivered modules: none. Split-off holes: none.

Also completely proved:
AlgebraicGeometry.perfect_hom_open_restricted_data_pinned,
AlgebraicGeometry.perfect_hom_open_restricted_pinned_equiv,
AlgebraicGeometry.perfect_hom_open_restriction_transport,
AlgebraicGeometry.perfect_hom_open_restricted_pinned_maps, and the new assembly proof of
AlgebraicGeometry.perfect_hom_open_restricted_data. The parent and conjunction already had
proof bodies before this delivery, so they are not counted as newly closed holes.

Existing downstream proof obligations remain in the imported declarations
perfect_hom_open_test_bijective (lem-pc-perfect-hom-open-test-bijective) and
perfect_hom_open_transport_square (lem-pc-perfect-hom-open-transport-square).
Their existing named statements supply exactly the facts used; this is the intended
stage-3 reduction. No new obligation restates the parent or the corrected helper.

All five delivered modules were compiled individually in dependency order with lcompile.py.
The unchanged direct consumer Sheaf.AlgebraicGeometry.PerfectHomOpenStageMaps also compiled
against the sandbox overlay (5.8 seconds), confirming that no adaptation is needed.
The dry run compiled every delivered module with its axiom probe and passed static
preflight; only the independent second-reading section remains for the second worker.
The corrected two naturality helpers use only standard axioms. The parent inherits the
existing dependency holes; this is not claimed as a closed proof under the comparator.

## No longer needed

Removed the proof import Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedDataExists
(node lem-pc-perfect-hom-open-restricted-data-exists). The parent no longer needs that
existence theorem or its assembly route through
Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedCore
(node new-perfect-hom-open-restricted-core) and
Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps
(node new-perfect-hom-open-restricted-maps). These three modules are pruned from this
proof route; other import paths may still reach them.

The old proof dependence on arbitrary-hB pinned equations is replaced by identity-normalized
fields. The formerly cyclic stage/apex proof dependencies on
lem-pc-perfect-hom-open-restricted-data-pinned are removed. Those corrected nodes themselves
remain needed for the new naturality proof. No blueprint unit is pruned.

Complete direct-dependency inventory: the parent also removes
lem-pc-ringed-spaces-derived-pullback-composition,
def-pc-derived-mayer-vietoris-canonical-data, and lem-pc-perfect-hom-transport
from its old proof_deps. These are still used through the unchanged concrete-map
construction and transport dependencies, so they are not globally pruned. The
conjunction removes lem-pc-perfect-hom-push-pull-cocone and
def-pc-derived-mayer-vietoris-canonical-data from its direct proof_deps; both
remain used through its stage/apex lemmas and their concrete-map statements.
The stage and apex each remove their former direct dependence on the conjunction,
as noted above. No other old direct proof dependency is removed.

The existing supported-testing, bijective restriction and transport-square nodes remain
needed and are reused. PerfectHomOpenRestrictedEquivFields remains necessary for its field
structure, not its existence theorem. PerfectHomOpenRestrictedQCoh is retained and used.
The old two public imports remain visible through the re-exported concrete-map module;
this move is not counted as pruning those imports or their nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery's remaining holes are false: independent hB can be sign-twisted,
so Yoneda naturality does not pin independent equivalences to h. The previous attempt
only moved those false obligations into their conjunction. This delivery instead corrects
all three helper statements, supplies their identity compatibility by construction, and
proves the combination without using the false types. Statement-change records cover
all DAG citers. All original parent and target signatures are preserved.

The parent docstring's essential-surjectivity remark is insufficient to lift arbitrary
Hom morphisms into restricted objects from a right-adjoint image. The implemented proof
uses supported extension-by-zero tests, where the existing Hom bijection supplies a unique
lift. The stage and cocone equations then need only identity tests, so no further lifting
argument is needed for them. The two new construction/transport lemmas were ultimately
proved from existing dependencies, rather than left as new sorry obligations.

Searches: Mathlib's representability-at-identity lemmas confirmed the short naturality
route; scheme restriction search returned underived comparison APIs. The actual supported
test, bijectivity and transport statements are present in Sheaf and were reused. LeanSearch
returned HTTP 500 and is recorded as unavailable, not as evidence of absence. Blueprint
search for restriction Hom returned no match.

## New nodes

* def-pc-perfect-hom-open-restriction-map:
  lean/Sheaf/AlgebraicGeometry/PerfectHomOpenRestrictionMap.lean owns the three unchanged
  concrete definitions formerly in the parent. This move prevents cyclic imports.
* new-perfect-hom-open-restricted-pinned-equiv:
  lean/Sheaf/AlgebraicGeometry/PerfectHomOpenRestrictedPinnedEquiv.lean proves existence
  of normalized equivalence/naturality fields by supported Hom lifting. It does not assert
  quasi-coherence or transition compatibility and contains no sorry.
* new-perfect-hom-open-restriction-transport:
  lean/Sheaf/AlgebraicGeometry/PerfectHomOpenRestrictionTransport.lean proves stage and
  apex specializations of the existing cartesian transport square. No new obligation.
* new-perfect-hom-open-restricted-pinned-maps:
  lean/Sheaf/AlgebraicGeometry/PerfectHomOpenRestrictedPinnedMaps.lean proves both map
  fields from pinning at identity and testing-object naturality. No new obligation.

Each new node records source, actual three-kind searches, full Lean signature and the
proof dependencies used. Change record:
coord/changes/perfect_hom_open_restricted_data_compatibility.md.


## Second reading by P1

1. Interface comparison: PASS. Read all five delivered modules and diffed the existing
   item against the repository. The parser confirms the parent signature is unchanged;
   its raw source signature is also byte for byte identical. The three moved definitions
   retain their signatures and bodies and are publicly re-exported. Only the three
   intermediate pinned helper signatures change, as declared in the compatibility change
   record. Source searches find no external users of these helpers. The unchanged direct
   consumer PerfectHomOpenStageMaps compiles against the sandbox overlay. No target
   statement or definition meaning changes.
2. Proof and trust: PASS. All five modules compile separately in import order, without
   errors or warnings. Text inspection finds no sorry or forbidden axiom mechanism, and
   no definition chooses an arbitrary unproved existence witness. The supported extensions
   are selected locally inside an existential theorem, with unique Hom lifts; normalization
   and naturality determine the resulting equivalences. A scratch copy with #print axioms
   confirms standard axioms only for the three concrete definitions and three corrected
   pinned helpers. The parent, pinned-equivalence construction, pinned maps, and transport
   specialization have standard axioms plus inherited sorryAx, consistently with the
   existing bijectivity and transport-square obligations. No original false statement is
   claimed proved: this delivery repairs two disputed holes and proves their corrected
   statements; it adds no holes.
3. New statements: PASS. No split-off sorry is added. The new theorems separate construction
   of normalized equivalences, cartesian transport specialization, and map coherence;
   none merely renames the parent. Read their docstring proofs and named dependencies.
   Checked empty/full opens, zero objects, identity arrows, and singleton stage diagrams:
   all reduce to the same bijection and inverse-cancellation identities, without a new
   nonemptiness or finiteness hypothesis. Independent searches with leanfinder for descent
   of natural Hom bijections, grep for homEquiv naturality, and rg for supported test and
   restriction Hom APIs found generic adjunction results and the existing supported-test
   declarations already used. The old maps_exists theorem constructs unnormalized data
   without retaining a pinned equation, so it cannot replace the new construction.
4. Route and pruning: PASS, with report repair. The parent constructs compatible fields
   from h, propagates pinning by naturality, and assembles all fields explicitly. The
   transition proof reduces to identities, then naturality, avoiding further arbitrary
   Hom lifting. Imports are used and proof-only imports are private. The empty realized
   statement and step lists of sk-thm-picard-semicon are unchanged. Completed the inventory
   of removed direct proof_deps, distinguishing the three obsolete assembly modules from
   dependencies still reached through the concrete-map and transport route.
5. DAG agreement: PASS. Checked every node's Lean signature,
   proof steps, dependency union, and proof_origin against the corresponding proof. New
   nodes have their source, searches, creation, blueprint, unit, and Lean records.
   The base DAG does not list the conjunction as a citer of the stage/apex helpers;
   the delivered conjunction's proof_deps correctly add both helper uses. The tool
   requires statement_change.citers to describe base-DAG users, so those lists remain
   empty for the two helpers. Their use in the delivered conjunction is checked here
   and documented in the compatibility record.

Second reading changed only this report's complete pruning inventory and independent
review. No Lean proof needed repair. The first dry run rejected adding the delivered
conjunction to the helpers' base-DAG citer lists; those attempted additions were removed
and the review now distinguishes base citers from the delivered proof dependencies.
