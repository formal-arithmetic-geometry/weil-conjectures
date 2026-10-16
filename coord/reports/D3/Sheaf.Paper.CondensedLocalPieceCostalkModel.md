## What changed

Proved `AlgebraicGeometry.ProEtale.condensed_local_piece_costalk_model` without changing
its statement, universes, visibility, or public imports. The proof constructs a functorial
bounded injective resolution, uses the adjunction between extension by zero followed by
closed pushforward and closed costalk followed by restriction, and checks the canonical
cocone-leg identity for the derived Hom comparison. The model retains its strict lower
bound because additive functors preserve zero objects.

Added two proved modules, each with its main public theorem and its DAG node:
`Sheaf.Paper.CondensedClosedCostalkDerivedContinuity` and
`Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity`. The first implements the
recollement/five-lemma argument of Hemo--Richarz--Scholbach, Lemma 5.3(2), using (3.4)
and Lemma 5.3(1). It identifies the actual comparison maps through natural derived
functor isomorphisms. The second applies that result to bounded injective cocones via
the K-injective derived-unit isomorphisms and the existing representative comparison
criterion. Both require only the strict common lower bound actually available here.

Updated the original node's proof, proof dependencies and proof origin to describe the
Lean argument. No existing definition or statement changes, forced adaptations, or
change records are needed. The original and both new modules compile together using
`lcompile.py`; the required delivery dry run is recorded by the delivery tool.

Repair of the landing-tool return: removed the duplicate private
`colimit_isStrictlyGE` proof from the item and exposed the single proved helper
in `CondensedClosedCostalkDerivedContinuity`. The item now imports that module
explicitly and applies its helper. Also removed the duplicate private
`rightDerivedObjQIso_naturality` proof from the item, exposing and reusing the
single proved helper in its existing direct dependency
`CondensedClosedCostalkInjectiveContinuity`. That new module publicly imports
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`
because the shared helper signature uses its comparison isomorphism. Both helpers
have explicit binders, source/proof docstrings, and entries in their owning nodes' `lean.declarations`.
The landing-style duplicate scan also identified the item's private generic
`functorialInjectiveEmbeddings` theorem as a copy of a private helper in
`CondensedOpenClosedRecollement`. That helper is inaccessible to importers.
Removed the duplicate theorem and its existential selection: the item now builds
its specific functor `J₀` and embedding `η` directly from
`CochainComplex.kInjectiveResolutionFunctor`, with monicity and termwise
injectivity supplied by the source library's lemmas. There is no new generic
existence theorem or additional dependency.

No existing public signature or mathematical statement changes, and no hole is
added. This repairs the duplication itself rather than renaming duplicate proofs.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.ProEtale.condensed_local_piece_costalk_model`
(node `lem-weil-pbc-condensed-local-piece-costalk-model`).

Also fully proved, with no remaining holes:

- `AlgebraicGeometry.ProEtale.condensed_closed_costalk_derived_continuity`
  (node `lem-weil-pbc-condensed-closed-costalk-derived-continuity`).
- `AlgebraicGeometry.ProEtale.condensed_closed_costalk_injective_continuity`
  (node `lem-weil-pbc-condensed-closed-costalk-injective-continuity`).

Shared helpers, also fully proved:

- `AlgebraicGeometry.ProEtale.colimit_isStrictlyGE` in the derived-continuity module.
- `AlgebraicGeometry.ProEtale.rightDerivedObjQIso_naturality` in the
  injective-continuity module.

All private helpers are proved. Holes closed in the item: 1 of 1. Holes added: 0.
No `sorry` remains in any of these three delivery modules. Existing imported project
theorems retain their own obligations; this delivery does not claim to discharge them.
The two new nodes record proved intermediate results, not deferred split-offs.

## No longer needed

Removed the original module's proof imports
`Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian` and
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`. The corresponding planned direct
proof dependencies `lem-pur-ringed-site-grothendieck-abelian` and
`prop-pur-kinjective-resolutions-exist` are unnecessary for this proof: the concrete
internal module categories already have the needed instances in the source library.
The functorial embedding is constructed from that library's K-injective resolution
functor and used with the existing functorial bounded injective resolution theorem.

Removed the original module's direct import of
`Sheaf.Paper.CondensedQcqsPushforwardContinuity`; it remains necessary in the new derived
continuity module, including its representative criterion, so this is not a claim that
the qcqs continuity node or module is globally pruned. Recollement and functorial bounded
injective resolutions remain genuine dependencies. No unit statement or realized unit
proof step is bypassed, and no other planned node or module is claimed unnecessary.

Removed redundant trial imports from the new modules after compilation, retaining only
the modules needed for their signatures and proofs. Three unchanged finite-free Hom
modules copied temporarily to populate the local compilation cache were removed from
the sandbox source tree; they are not part of this delivery.

The old direct proof edge
`lem-weil-pbc-condensed-qcqs-pushforward-continuity` is replaced by the new
closed-costalk continuity edge; that qcqs node remains an essential transitive
input. A fresh comparison with the current shared repository finds that all
removed direct imports remain transitively reachable: neither this item's import
closure nor `TargetsCheck` loses any module. There are **no globally pruned
modules**. The earlier report that the K-injective module leaves this item's
closure no longer holds against the current repository.

The repair removes the item's three redundant private helper declarations and its
redundant direct proof import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`,
now publicly provided by the injective-continuity dependency.
Their single implementations in its dependencies are reused. This changes no
module-level pruning claim and adds only the explicit proof import of
`Sheaf.Paper.CondensedClosedCostalkDerivedContinuity` needed for direct access.

## Where the brief, the DAG or earlier work was wrong

The original statement and the recollement route are usable unchanged. The planned
references alone did not already state the required closed-costalk continuity theorem;
the new proved nodes make this categorical argument explicit rather than introducing a
new unproved dependency. The generic ringed-site Grothendieck and resolution nodes were
unnecessary at this concrete instance. The source library's existing concrete instances
and functorial resolution construction suffice.

The proof handles zero complexes and empty open or closed pieces without extra
nonemptiness assumptions. The new derived theorem uses a strict lower bound, sufficient
for the injective complexes actually used, so its good-truncation cocone is genuinely
colimiting. No target signature was changed or weakened.

The first delivery duplicated the strict-colimit-bound helper across two
modules; the landing tool correctly rejected it. The earlier second reading
missed that duplication and the repeated derived-unit naturality helper. Both
are now shared declarations with exactly one proof each. A full-library duplicate
scan additionally caught the generic embedding existence theorem repeated from
a private recollement helper; the item now constructs its actual embedding
functor from the existing resolution API without restating that theorem.

## New nodes

`lem-weil-pbc-condensed-closed-costalk-derived-continuity`, in
`dag/nodes/sec-proper-base-change/`, is attached to the fully proved theorem in
`lean/Sheaf/Paper/CondensedClosedCostalkDerivedContinuity.lean`. It supplies the derived
closed-costalk cohomology comparison for strict uniformly bounded diagrams, using the
open/closed localization triangle, exact filtered colimits, qcqs open pushforward
continuity, the five lemma and fully faithful closed pushforward. Nothing remains to
prove in this new module.

`lem-weil-pbc-condensed-closed-costalk-injective-continuity`, in the same node directory,
is attached to the fully proved theorem in
`lean/Sheaf/Paper/CondensedClosedCostalkInjectiveContinuity.lean`. It converts derived
continuity into a quasi-isomorphism of the actual termwise-costalk colimit map for a
bounded injective cocone. Naturality of the derived unit supplies the required leg
identity. Nothing remains to prove in this new module. Both nodes include their source,
complete proof steps and recorded LeanSearch, LeanFinder, Loogle and Mathlib source
searches. LeanSearch returned an Internal Server Error; this is recorded as unavailable,
not as evidence that no matching theorem exists.

The derived node also records the shared strict-colimit-bound helper; the
injective node records the shared K-injective comparison naturality helper.
These are proved auxiliary declarations of the existing two new nodes; this
repair introduces no further node or deferred split-off.

Repair validation: all three final delivery modules compile without errors or
warnings through `lcompile.py` (the derived module first, then the injective
module and item together). No compilation limit was changed. The final source
scan finds no `sorry` in these modules and no Lean line over 100 characters.
The final duplicate-statement scan uses `tools/leanindex.py`, the landing gate's
parser, against the whole library with all delivery modules overlaid. It passes:
no theorem statement in a delivery module is duplicated in another module.
The required fresh delivery dry run is recorded by the delivery tool.

The second-reading section below records the review of the prior version;
a new reader must check this repair and its fresh validation results.

## Earlier second reading (a previous round; superseded)

1. **Existing interfaces.** I compared the item against the read-only repository.
   Its theorem signature is byte for byte identical, including universes,
   noetherianity, arbitrary P, the strict common lower bound, both isomorphisms,
   and the equation for the original cocone legs. Public imports and visibility
   are unchanged. The two other modules and their public theorems are new; there
   are no adapted existing modules or definition changes. I restored the original
   declaration docstring, retaining the worker's implementation proof sketch as
   a proof-body comment.

2. **Proofs and constructions.** I read all three modules, including the five-term
   exact-sequence argument, the naturality of the right-derived-unit comparison,
   the construction of the bounded resolution cocone, and cancellation against
   its quasi-isomorphism. There are no deferred statements or forbidden trust
   mechanisms in the delivery. The left adjoint is exactly j_! followed by i_*;
   its right adjoint is closed costalk followed by j*. The strict zero terms are
   preserved by these additive functors. The closed costalk is obtained from
   the proved recollement theorem and is determined up to natural isomorphism
   by its adjunction. Resolution choices represent the prescribed complex in
   the derived category; no arbitrary object is obtained from an unproved mere
   existence assertion. I removed stale artifacts for the three temporary
   finite-free dependency modules from the sandbox overlay, so the final checks
   use the published compiled library and precisely the delivery's own modules.

3. **New statements and reuse.** The two new statements are proved intermediate
   results, not outstanding split-offs or renamed copies of the target. Derived
   continuity assumes a common strict lower bound, exactly the case supplied by
   the resolution. Injective continuity assumes both termwise injectivity and
   that bound on all diagram objects and the cocone vertex; these hypotheses
   supply the K-injective comparison at every required object. The map proved
   quasi-isomorphic is the actual universal map to the termwise-costalk cocone.
   I checked zero complexes, zero P, identity and empty closed immersions, empty
   complementary opens, and negative bounds. Filtered indexing is nonempty by
   its existing hypothesis. I repeated a semantic search using localization and
   fully faithful exact embeddings, a Mathlib source search for adjoints and
   colimit comparison maps, and project/upstream searches for costalk continuity
   and the right-derived-unit naturality lemma. They gave general ingredients,
   with no existing public theorem that supplies either new statement.

4. **Route, imports and pruning.** I read Hemo--Richarz--Scholbach, Lemma 5.3(2),
   its last paragraph on page 14, together with (3.3), (3.4), Lemma 3.4 and the
   statement/proof of Lemma 5.3(1), in the supplied scratch PDF/text. I checked
   the actual `condensed_open_closed_recollement` statement: it supplies the
   exceptional adjoint, exact fully faithful i_*, the natural localization
   triangle, and its distinguishedness. Noetherianity makes the complementary
   open quasi-compact; its open immersion is quasi-separated. The middle
   cohomology comparison uses exact filtered colimits; the open comparison uses
   the existing qcqs continuity theorem. The five lemma and reflection through
   i_* give the closed comparison. The injective theorem then uses the existing
   `condensedContinuityComparison_representatives` declaration, recorded among
   the qcqs node's declarations. All proof-only imports are plain imports; the
   new derived module publicly imports the module defining the comparison in
   its signature. The unit `sk-thm-properbasechange` and all its `realized`
   statements and steps are preserved. I completed the removed-direct-edge
   account above and checked that no module is globally pruned.

5. **DAG agreement.** Every recorded Lean statement occurs verbatim in its file.
   Each node's `proof_deps` equals the union of its proof steps' `uses`. The old
   node changes only `proof`, `proof_deps`, and `proof_origin`. Its steps follow
   the actual resolution, closed continuity, and derived-adjunction proof. Both
   new nodes have their source, proof steps, blueprint placement, creation data,
   and logged searches; unavailable LeanSearch is explicitly recorded as such.
   Their hypotheses and conclusions agree with Lean. No new sorry or change
   record is required.

Changes made in this second reading: restored the existing API docstring and
moved the updated implementation sketch into its proof; removed temporary
dependency artifacts from the compilation overlay; clarified direct dependency
removals and the absence of global module pruning; added this independent review.
The mathematical proof and all theorem signatures are unchanged. Compilation,
explicit axiom inspection, and delivery validation are recorded below.

Second-reading validation: all three delivery modules compiled together with
`lcompile.py --all`, without warnings, after excluding the temporary dependency
artifacts. Scratch copies with `#print axioms` for each of the three public
theorems also compiled. Each lists exactly `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`; there are no new holes, and the remaining `sorryAx`
comes from existing imported obligations. The delivery tool additionally checks
every declaration, including private helpers.

The second-reading delivery dry run printed `OK (dry run)`: commit `0ecd96b209`
compiled and passed preflight. It classified the delivery as CODEX because the
two fully proved intermediate modules and their nodes are new. No compiler,
axiom-probe, DAG, or signature check failed.

## Second reading by D3

1. **Existing interfaces — pass.** I read the repository and sandbox versions of
   all delivered modules and compared the item with `diff`. The original
   `condensed_local_piece_costalk_model` signature is byte for byte identical,
   with the same universes, hypotheses, strict lower bound, two isomorphisms,
   and equation for the original cocone legs. Its public imports and visibility
   are unchanged. The other two modules are new. There are no adapted existing
   modules, changed definitions, or changes needing an interface record.

2. **Actual proofs and data — pass.** I read all three proofs, including the
   five-term exact sequences, transfer of comparison maps through natural
   isomorphisms, cancellation of the closed pushforward, derived-unit
   naturality, and the final cocone-leg calculation. The three delivery modules
   contain no `sorry`, forbidden trust mechanism, or hollow definition. The
   repaired item constructs its actual embedding functor from the upstream
   K-injective resolution functor; it does not select an arbitrary embedding
   from an unproved existence claim. I inspected that construction, its monic
   unit and injective-term API, and the fully proved functorial bounded
   resolution theorem. The exceptional adjoint is specified up to natural
   isomorphism by its adjunction. The resolution cocone represents the
   prescribed original diagram and colimit in the derived category.

3. **Intermediate statements and reuse — pass after repair.** Both new main
   theorems are proved, strictly intermediate continuity statements; no holes
   are split off. The derived statement assumes the strict common bound used
   to make the good-truncation cocone colimiting. The injective statement adds
   exactly the termwise injectivity and vertex bound used for its K-injective
   comparisons. Its canonical map is the actual `colimit.desc` map. I checked
   zero complexes and coefficients, identity and empty closed immersions, empty
   complementary opens, arbitrary negative bounds, and the nonempty filtered
   indexing hypothesis. I repeated a semantic search with localization and
   exceptional-adjoint terminology and searched project, upstream and Mathlib
   sources. This found the existing upstream
   `ShortComplex.exact_iff_evaluation`; I removed the redundant private
   `exactFunctorCategory` proof and used that lemma at all three exactness
   steps, with a plain proof import. The general derived-unit naturality fact
   has related private inverse-form proofs elsewhere, but no reusable public
   declaration was found. Its single shared implementation is now reused
   throughout this delivery. I expanded the new injective node's opening
   assumptions so its statement can be read without another node's prose.

4. **Route, imports and pruning — pass.** I read Hemo--Richarz--Scholbach (3.3),
   (3.4), Lemma 3.4 and Lemma 5.3, especially the last paragraph on page 14, in
   `scratchpad/hrs.txt`, and checked the actual recollement and qcqs-continuity
   declarations. Noetherianity makes the complementary open quasi-compact;
   its immersion is quasi-separated. Recollement supplies the distinguished
   natural triangle, exact fully faithful closed pushforward and its adjoint.
   Exact filtered colimits handle the middle comparison, qcqs continuity the
   open comparison, and the five lemma the closed comparison. The existing
   representative criterion then gives injective continuity. All proof-only
   imports are plain imports; the new public imports supply signature terms.
   The original direct proof-dependency removals are all accounted for in
   `## No longer needed`, including qcqs continuity remaining transitively
   necessary. The `sk-thm-properbasechange` realized statements and steps are
   untouched; this is a reduction below that unit's route.

5. **DAG agreement — pass.** I compared each node with its Lean declaration:
   every recorded main statement occurs verbatim, and every `proof_deps` is
   exactly the union of the steps' `uses`. The original node changes only
   `proof`, `proof_deps`, and `proof_origin`. Its new steps follow the actual
   embedding, resolution, continuity and adjunction argument. The two new
   nodes record their proved main results and shared helpers, source places,
   blueprint placement, creation data, and actual logged searches. The
   unavailable LeanSearch result is not treated as a negative mathematical
   search. The sole original hole is closed; zero holes are added.

Changes in this reading: replaced redundant functor-category exactness with
`ShortComplex.exact_iff_evaluation` and its proof import; made the new injective
node's assumptions self-contained; removed surplus blank lines; added this
independent review. No existing mathematical statement or public import changed.

Fresh source-overlay validation in this reading found no duplicate theorem
statements across delivery modules and the whole library. It also confirmed
that no module leaves either the item or `TargetsCheck` import closure against
the current repository; the pruning paragraph above has been corrected.

Fresh explicit axiom validation: scratch copies of all three final modules with
`#print axioms` compiled without errors or warnings. The three main theorems
list only `propext`, `Classical.choice`, `Quot.sound`, and imported `sorryAx`.
Both shared helpers list only the three permitted axioms. No delivery declaration
contains a new hole. The required delivery dry run additionally probes all
module declarations, including private helpers.
