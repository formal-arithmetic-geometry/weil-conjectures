## What changed

Proved `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_etale_hypercover_homotopy_equalizer`
with its original signature and visibility. Replaced the unimplemented prism Hom object by the
explicit ordered path object `V_[2n+1]`, with blockwise simplicial maps and the cut homotopy.
Its endpoint pullback along `(a,b)` is the actual constructed witness K.

Added eight modules, all proved without `sorry`: the ordinal path construction, nonempty simplex
face intersections, intersections after doubling, gluing families on generated faces, the
endpoint-and-doubled-face boundary family, canonical étale matching schemes, ordinary étale
finite-simplex lifting, and the hypercover property of the ordered endpoint pullback. The proof
uses the existing finite-simplex lifting, singleton matching comparison, and finite Hom-object
statements as the brief requests; it adds no replacement holes.

The matching schemes are actual finite limits. Their universal properties among all schemes over
X are proved by preservation of finite limits. No definition chooses arbitrary data from an
unproved existence theorem. The Hom-object existence theorem is used only within the proof of a
local-lifting proposition; K itself is constructed independently of it.

The relative matching argument first fixes a compatible U_n-simplex, glues the two endpoints and
the doubled proper faces on a finite subcomplex of Delta[2n+1], and extends locally using V.
Evaluated pullback extensionality identifies the resulting K-faces. For absolute covers, pull
back U's matching cover and use the jointly-surjective criterion for the small étale topology.
This works in degree zero as well: there are no proper faces, the finite subcomplex consists of
the two vertices, and the resulting extension problem is V_1 over its two endpoints. Empty base
schemes and empty covering families impose no extra nonemptiness hypotheses. Every degree of
the simplicial subcomplex is nonempty because it contains constant simplices from an endpoint.

The helper modules and the item compile together through `lcompile.py --all`; the required
`deliver3.py --no-push` checks the complete delivery. The original existential binder `hK` is
intentionally unused in the conclusion; a scoped unused-variable linter option preserves the
statement verbatim while avoiding its warning.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_etale_hypercover_homotopy_equalizer`.
No `sorry` remains in the item's module. No `sorry` was added in any new module: zero split-offs.
This is one hole closed from existing library statements, not a decomposition with new holes.

The main new proved interfaces are:

- `CategoryTheory.SimplicialObject.ordinalPathPullbackHomotopy`, together with the explicit
  doubled functor, seven cut identities, evaluated lifting, and projection extensionality.
- `SimplexCategory.exists_face_pullback` and `factor_of_range_subset`.
- `SimplexCategory.OrdinalPath.doubled_face_intersection`, with the endpoint intersection facts.
- `CategoryTheory.SimplicialObject.glue_face_family`.
- `CategoryTheory.SimplicialObject.OrdinalBoundary.exists_family` and `subcomplex_nonempty`.
- `AlgebraicGeometry.EtaleSimplicialMatching.matching_universal`, `properConeIsLimit`,
  `isEtaleHypercover_of_matchingCover`, `matchingCover_of_isEtaleHypercover`, and
  `isSemiRepresentableHypercover_of_isEtaleHypercover`, with canonical data and natural maps.
- `AlgebraicGeometry.EtaleSimplicialMatching.locally_extend_simplex`.
- `AlgebraicGeometry.EtaleSimplicialMatching.locally_lift_ordinal_matching` and
  `isEtaleHypercover_ordinalPathPullback`.

The proof uses the existing `Scheme.hypercover_finite_simplex_lifting`,
`Scheme.sr_matching_object_one_member`, `Scheme.exists_simplicial_hom_object`, and
`Scheme.simplicial_hom_standard_simplex`. At second reading the finite-simplex lifting and
standard-simplex modules have complete proofs; the singleton matching comparison still has its
existing hole. Their proofs are outside this delivery; using their stated conclusions is the
intended stage-3 reduction. The item remains conditional on the existing import obligations.

## No longer needed

Removed the item's direct proof imports
`Sheaf.AlgebraicGeometry.HypercoverFiniteSimplexLifting` and
`Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember`, replacing them with
`Sheaf.AlgebraicGeometry.EtaleOrdinalPathHypercover`. Both removed imports remain needed
transitively through the proved helpers. Their nodes are therefore retained; no existing module
is withdrawn or claimed as globally pruned.

The old direct dependency `lem-weil-pbc-etale-covering-base-change` is also removed from the
item's `proof_deps`: the absolute matching proof uses Mathlib's
`MorphismProperty.of_isPullback` for surjectivity, while finite-simplex lifting still uses
covering base change transitively. The old finite split and ordinary hypercover definition
dependencies are retained directly. Thus every old proof dependency is accounted for, and
no old dependency module is globally pruned.

Second reading removed the redundant public import
`Mathlib.CategoryTheory.Limits.Preserves.Finite` from the new matching module. The étale site
already supplies finite-limit preservation; this module adds no public dependency on it.

The general prism Hom construction is unnecessary: the ordered simplex and explicit cut maps
provide the homotopy directly. No separate existing DAG node or module states that prism
construction, so none is withdrawn for it. Finite split replacement remains a separate parent
step and is not bypassed. The unit `sk-prop-h2` has no recorded realized statement or proof step
in this helper route; all its statement and proof steps remain untouched.

Pruned unused provisional helper lemmas `matchingMap_naturality` and
`surjective_of_cover_lifts` from the new modules. Kept proof-only imports private, including the
simplex intersection implementation, the singleton matching comparison, and the Hom-object
statements. No existing definition or statement was changed, so no change record or forced
adaptation is required.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature defect was found. Second reading corrected the ordinal-face
helper citation: Tag 018V is a coskeleton lemma, so its module and node now cite Tag 0164
for the finite ordered-set definition and explicitly identify the elementary proofs as
agent-written. The original proof plan left the path-object
construction and its relative matching argument entirely informal. The ordered-join variant
makes both explicit and uses the same finite-inclusion lifting principle. The DAG proof route
has been updated to describe the implementation actually proved.

LeanSearch was attempted for all eight new nodes and returned `Internal Server Error`; each
record marks that attempt unavailable without an absence verdict. LeanFinder/Loogle and the
Mathlib-source searches worked. Their relevant results and the searches of the source library
found no duplicate ordered endpoint construction or all-degree hypercover result. The available
union, simplex-face and monomorphism tools were used in the proofs.

The shared source checkout omits the literature bodies. Official Stacks pages for Tags 01GN,
01GH and 01GS were read. WANTED: `literature/stacks-project/simplicial.tex`, Tags 0164, 017J and
0186, and `literature/stacks-project/hypercovering.tex`, Tags 01GN and 01GS, for the local source
bundle. The new proofs are marked agent-written specializations; no unavailable source proof
has been asserted as an exact transcription.

## New nodes

`def-weil-pbc-simplicial-ordinal-path`: constructed doubling, endpoints, cut homotopy and endpoint
pullback, with the evaluated lifting/extensionality API. Module
`Sheaf.CategoryTheory.SimplicialOrdinalPath`.

`lem-weil-pbc-simplex-mono-pullback`: proved range factorization and nonempty pullbacks of
injective ordinal maps. Module `Sheaf.CategoryTheory.SimplexMonoPullback`.

`lem-weil-pbc-ordinal-path-face-intersection`: proved preservation of nonempty face intersections
by doubling and the endpoint intersection formulas. Module
`Sheaf.CategoryTheory.OrdinalPathFaceIntersection`.

`lem-weil-pbc-simplex-face-family-gluing`: proved gluing over the union of generated simplex
faces. Module `Sheaf.AlgebraicTopology.SimplexFaceFamilyGluing`.

`lem-weil-pbc-ordinal-boundary-family`: proved gluing of full endpoints and lower doubled-face
data on the finite subcomplex used by matching lifting. Module
`Sheaf.AlgebraicTopology.OrdinalBoundaryFamily`.

`def-weil-pbc-etale-simplicial-matching`: constructed finite matching limits and proved their
full and proper-face universal properties and hypercover comparisons. Module
`Sheaf.AlgebraicGeometry.EtaleSimplicialMatching`.

`lem-weil-pbc-etale-finite-simplex-lifting`: proved the ordinary étale local-extension interface
from the existing semi-representable statements. Module
`Sheaf.AlgebraicGeometry.EtaleFiniteSimplexLifting`.

`lem-weil-pbc-etale-ordinal-path-hypercover`: proved the relative local matching lifts and absolute
hypercover property of the constructed endpoint pullback. Module
`Sheaf.AlgebraicGeometry.EtaleOrdinalPathHypercover`.

All eight new nodes have complete proofs in words and complete Lean proofs. No new node remains
to be handed on as a proof obligation. There are no change records.

## Second reading by J1

1. **Statements and visible data: pass.** Compared all nine delivered Lean paths with the
   shared repository. Eight are new; the existing item's theorem signature is byte-for-byte
   unchanged, including the unused `hK` binder. Its public imports and visibility are unchanged.
   The only added option is scoped to its unused-variable linter. No target or existing
   definition changes, and no forced adaptations or change records are needed.

2. **Proof and data audit: pass.** Read all 1,578 original delivered Lean lines, then compiled
   all nine modules in dependency order with `lcompile.py --all`, without errors or warnings.
   The delivery contains no `sorry`, forbidden axiom, unsafe implementation or kernel-check
   bypass. A scratch `#print axioms` audit gives only `propext`, `Classical.choice`, `Quot.sound`
   for the constructed endpoint pullback, its homotopy, canonical matching data and universal
   properties, face intersections and glued boundary family. The final theorem and the local
   lifting results additionally have `sorryAx`, inherited from existing imported obligations;
   this is not a fully axiom-closed target. The Hom-object witnesses are eliminated inside
   a proof of local lifting; the constructed K and matching schemes are categorical limits,
   independent of those witnesses. The delivery tool additionally probes every declaration.

3. **New statements and edge cases: pass.** No new statement has an unproved body, so there
   are zero split-off holes or renamed copies of the target's hole. Checked each new node
   against its module and proof. In degree zero the proper-face index is empty, the boundary
   consists of two vertices of Delta[1], and the unique cut is the identity of [1]. In degree
   one the doubled proper faces have vertex sets {0,2} and {1,3}; their intersections with the
   endpoints {0,1} and {2,3} are exactly the vertices used in the gluing proof. Disjoint face
   images are excluded only by a supplied common vertex, never silently. Empty schemes and
   empty covering families require no additional nonemptiness assumption. Independently
   searched LeanFinder for edgewise subdivision and ordered endpoint homotopies, Loogle for
   `CategoryTheory.SimplicialObject.Homotopy`, and Mathlib/source-library text for edgewise
   subdivision, ordinal sums and path/matching objects. The hits supply generic homotopy
   operations or one-step hypercovers, not the all-degree theorem or this construction.

4. **Route, imports and pruning: pass after one repair.** Read the existing finite-simplex
   lifting, singleton matching and standard-simplex statements, and checked their actual
   instantiations. The proper-face family is glued before finite-simplex lifting; the two
   evaluated projections establish the lifted faces; base change and joint surjectivity
   establish absolute matching covers. This keeps finite replacement as the separate parent
   step. Read `dag/units/sk-prop-h2.json`: its `realized` statement and sole step are empty, and
   its Kummer/Brauer route is untouched. All old proof dependencies are accounted for under
   No longer needed; no module is globally pruned. Removed the redundant public
   `Mathlib.CategoryTheory.Limits.Preserves.Finite` import from the new matching module;
   compilation still succeeds. Other public imports support signatures or public data bodies;
   proof-only helper imports remain plain imports.

5. **Nodes and sources: pass after citation repair.** All nine node records have the required
   fields; their `proof_deps` are precisely the union of their steps' `uses`, and all referenced
   nodes exist. The existing node changes only `proof`, `proof_deps` and `proof_origin`.
   The new declarations and verbatim principal signatures agree with their Lean records.
   Independently read Stacks [01GN](https://stacks.math.columbia.edu/tag/01GN) (finite
   inclusions give covering restriction maps), [01GS](https://stacks.math.columbia.edu/tag/01GS)
   (endpoint pullback and relative matching argument),
   [017J](https://stacks.math.columbia.edu/tag/017J) (compatible families),
   [0186](https://stacks.math.columbia.edu/tag/0186) (matching limit), and
   [021D](https://stacks.math.columbia.edu/tag/021D) (etale fibre products).
   Tag 018V does not state the ordinal intersection lemma. Corrected that helper's source
   in its module and new node to [0164](https://stacks.math.columbia.edu/tag/0164), explicitly
   marking the range and intersection proofs as agent-written consequences of the finite
   nonempty ordered-set definition. The ordered join is likewise an explicitly identified
   agent-written variant, not claimed to be the prism in 01GS.

Second reading changed one redundant import, the ordinal-intersection source attribution,
and report accuracy/completeness (inherited obligations and old dependencies). No proof body,
statement, definition or new hole was changed or added.
