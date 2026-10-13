## What changed

Replaced the sole sorry in
`RingTensorCohomology.affineTensorCohomology_localization_square` by a composition
of the existing balanced derived-localization theorem with a new single-ring
resolution-realization theorem. Its signature and visibility are unchanged.
The proof constructs the coefficient tensor associator, proves its pure-tensor
formula, proves K-flat preservation using the existing base-change theorem,
and writes both naturality arguments and the comparison-square cancellation in Lean.

Added `Sheaf.Algebra.Homology.PrescribedTensorCohomologyModelRealization` with
`RingTensorCohomology.prescribedTensorCohomology_model_realization`.
This statement treats one base ring and an arbitrary natural K-flat replacement;
it supplies the identification of prescribed lifts with balanced cohomology models
and ordinary tensor cohomology. It asserts no localization isomorphism and does
not repackage the item's statement. The item applies it twice and combines its
output with the existing localization theorem. New imports are proof-only.

The node's proof and proof dependencies now describe the written Lean proof.
The unit's realized lists are empty and its route is preserved.

Repair: added the five recorded proof-plan imports to
`PrescribedTensorCohomologyModelRealization.lean`:
`KFlatScalarExtensionCounit`, `MixedTensorKFlatQuasiIso`,
`BaseDerivedTensorCohomologyModelMap`, `BaseTensorOrdinaryIso`, and
`FlatScalarExtensionHomologyAdjunct`. They are proof-only imports and match the
module's recorded proof dependencies.

## Proved and sorry left

Closed the item's one hole:
`RingTensorCohomology.affineTensorCohomology_localization_square`
(node `lem-pc-affine-tensor-cohomology-localization-square`).
There is no sorry left in the item and no changed signature.

Added one named hole:
`RingTensorCohomology.prescribedTensorCohomology_model_realization`
(node `lem-pc-prescribed-tensor-cohomology-model-realization`), in its own module.
This is a decomposition, with one hole closed and one added, not a net reduction
in holes. Its complete argument is in the docstring and node. Existing imported
holes in derived localization, coefficient flatness, and model construction are
unchanged and are not claimed as proved here.

Edge cases checked for the new statement: the zero functors/replacement give
zero cohomology and the same canonical maps; an empty indexing category makes
all component requirements vacuous; identity replacement is the usual balanced
tensor cohomology identification; nonflat B over R is allowed since only the
A-replacement is tensored ordinarily and the R-tensor remains derived; no
boundedness is needed. A nonidentity quasi-isomorphism pi is used in the common
K-flat span, rather than assuming it is a chain isomorphism.

## No longer needed

Removed direct proof imports `Mathlib.RingTheory.Localization.BaseChange` and
`Mathlib.Algebra.Module.LocalizedModule.Exact`.
Removed the direct proof-dependency edges to
`lem-weil-pbc-localization-tensor-product` and
`lem-weil-pbc-localization-module-exact`: the main proof uses scalar-extension
associativity and the exactness instances furnished by flat extension instead.
These results can still occur transitively in the existing dependencies; this
delivery does not claim that they leave the entire targets' import closure.

Retained `DerivedTensorLocalizationCohomology` and `AffineTensorLocalizationFlat`.
Added the needed `PrescribedTensorCohomologyModelRealization`,
`KFlatModuleBaseChange`, and `WeilConjectures.Algebra.Homology.HomotopyCategory.Braided`
proof imports. No other module is claimed to become globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned transport from arbitrary prescribed lifts to balanced models was
not stated by any of the original four dependencies. It additionally requires
comparison of the localized A-resolution with the local functorial resolution.
The new realization theorem isolates exactly this single-ring work, including
naturality and comparison compatibility; the actual localization comparison
remains the existing theorem and is used explicitly.

The item's blueprint ancestor tool cannot traverse its immediate ancestor,
`lem-pc-affine-tensor-cohomology-localization-isos`, because that ancestor's own
blueprint metadata has no nearest imported ancestor. The new node records the
known imported ancestor `lem-pc-rf-perfect-base-change`, reached through
`lem-pc-affine-derived-base-change-comparison-map` and
`lem-pc-rf-single-complex-affine-base-change`, instead of altering metadata outside
this delivery's scope. The blueprint search found no existing realization statement.

LeanSearch was unavailable (HTTP Internal Server Error); LeanFinder, Loogle,
logged Mathlib grep, local DAG searches, and library searches were performed.
The remote clone omits the Stacks sources, so the official Tag 0DJ8 and 06Y6 pages
were read online, together with Tags 064L, 065Z, 00HD, 00CS and 06Y1.
The proof is marked as an agent-written explicit argument.

The inherited balanced-model documentation labels Tag 08IB as a general comparison
construction; the current official page instead states the geometric base-change
isomorphism under Tor independence. The new lemma cites the actual ring comparison
equation, Tag 065Z, and the K-flat construction, Tags 06Y6 and 064L; it does not
assume Tor independence. General exact flat extension is Tag 00HD, while Tag 00CS
is the localization special case used by the original item.

## New nodes

`lem-pc-prescribed-tensor-cohomology-model-realization`: the single-ring
K-flat replacement realization and its counit-compatible map identities.
The existing `lem-pc-mixed-tensor-kflat-quasi-iso` and
`lem-pc-base-tensor-ordinary-iso` are used in its proof plan as generic tools for
K-flat tensor invariance and ordinary tensor associativity, respectively; they
do not replace any step of the unit route.
Its statement is independent of prime localization, and its use leaves the
entire global-to-local comparison and the composition/cancellation argument
in the item. No definition or existing declaration signature changed. The static checker
requires an elaboration-command record at
`coord/changes/affineTensorCohomology-localization-square-elaboration.md` for
`open` and the local instance attribute; it lists the unchanged downstream users.
There is no forced adaptation.


## Earlier second reading (a previous round; superseded)

1. Interface: PASS. Read the full diff of both delivered modules against the
repository. The existing theorem signature is byte-for-byte identical, including
all hypotheses, universe, visibility and conclusion. The new realization theorem
is the only new public declaration. The three helpers are private; no existing
definition changed. The elaboration-command change record covers the local opens
and instance attribute and requires no downstream adaptation.

2. Proof and trust: PASS. Both modules compile through lcompile.py in import
order with no errors or warnings. The target has no sorry. The only delivered
sorry is the named prescribedTensorCohomology_model_realization theorem listed
above, with its own module, proof docstring and matching node. No axiom, unsafe,
opaque, implemented_by or extern declaration occurs. The coefficient associator
is actual constructed data, not a choice from an unproved existence assertion.
The chosen imported balanced models have universal counits and fixed generator
equations; their downstream identifications are up to the resulting compatible
isomorphisms. The axiom probe results are recorded below.

3. Split statement: PASS. Read the model fields, RingTensorCohomology definitions,
K-flat counit and scalar-extension lemmas, model-map lemma, and flat homology
adjunct. The realization is a single-ring resolution identification, strictly
part of the global-to-local argument. It makes no assertion comparing two base
rings or prime localizations. Its gamma, model-map and comparison equations are
all used by the target. Rechecked zero/acyclic replacements, identity replacement,
empty indexing category, nonflat B over R, and genuinely quasi-isomorphic (rather
than chain-isomorphic) pi. The common A-K-flat span handles the target; the
R-resolution handles the source; flatness is needed only for final coefficient
cohomology extension. The proof works for arbitrary E because pi commutes with
scalar endomorphisms as an A-linear chain map; it does not require such
endomorphisms to lift to morphisms of E.

Independent searches used different words: LeanFinder queried "homology of
derived tensor evaluated on a quasi-isomorphic K-flat replacement natural
comparison" (homology factorization infrastructure, no realization theorem);
Loogle queried CategoryTheory.Functor.leftDerivedUnique (the universal uniqueness
isomorphism); logged Mathlib grep queried homologyFunctorFactorsh and
mapHomologyIso_hom_naturality (13 infrastructure hits). The initially unqualified
Loogle name was unknown and was retried fully qualified. Local searches read
BaseDerivedTensorModelQuasiIsoComparison and its ordinary counterpart: they
transport between supplied models, and do not identify prescribed source/target
lifts on an arbitrary replacement. Upstream searches found no duplicate
realization statement. Independently read the official Stacks pages
[064L](https://stacks.math.columbia.edu/tag/064L),
[065Z](https://stacks.math.columbia.edu/tag/065Z) and
[00HD](https://stacks.math.columbia.edu/tag/00HD): these support the K-flat tensor
invariance, canonical comparison and exact flat-extension steps. Closing this
realization hole would require the full span and action transport formalization,
not a few-minute application of a found lemma.

4. Route and pruning: PASS. Read the target from its conclusion down through
alpha, beta, the two realization applications, derived localization and the
coefficient associator. All imported proof tools are used. Public imports supply
the unchanged signature; added imports are proof-only. No shorter complete route
was found. No longer needed lists every removed old proof dependency: localization
tensor product and localization module exactness. This is direct-import pruning;
no claim is made that these modules leave the whole target closure. The unit
sk-thm-picard-semicon has empty realized statement/step lists and is unchanged;
the unit and chapter routes are preserved. One hole closed and one added remains
a decomposition with net zero, not a net proof advance.

5. DAG: PASS. Both lean.statement records exactly match their Lean signatures.
Only proof, proof_deps and proof_origin differ in the existing node. Its steps
follow the actual two realization calls, K-flat preservation, coefficient
flatness, derived localization, associativity, naturality and final cancellation.
The new node contains its self-contained hypotheses, source, full proof steps,
union of dependencies, origin, search records, split status, creation metadata,
blueprint ancestry, chapter, unit and Lean record. No dependency cycle or
relabelled copy of the item is introduced.

Second reading changed: repaired the prescribed realization citation from
`lem-sc-kflat-scalar-extension-derived-iso` to `lem-pc-mixed-tensor-kflat-quasi-iso`
in both K-flat extension steps, and added the required B[0]/C[0] specialization
explanations to the node and theorem docstring. The mathematical statements and
imports required no repair.

Axiom probe: #print axioms for both public theorems reports exactly propext,
Classical.choice, Quot.sound and sorryAx. The latter is expected from the named
realization hole and still-open imported statements. No additional axiom occurs.
The probe scratch copy was removed before delivery.

## Earlier second reading (a previous round; superseded)

1. Interface: PASS. Compared the entire item diff with the repository version.
Extracted the existing theorem signature from `theorem` through the final
conclusion and checked byte-for-byte equality. Both delivered node Lean records
also match their declaration signatures exactly. The only added public
statement is prescribedTensorCohomology_model_realization. No existing
definition, hypothesis, conclusion or visibility changed. The change record
covers the local instance, opens and elaboration option; no downstream
adaptation is delivered.

2. Proof and trust: PASS. Compiled both modules in import order with
lcompile.py --all: no errors or warnings (16.8 and 15.2 seconds). Read the
three private helpers and the entire composition proof. The coefficient
isomorphism is constructed from extendScalarsComp and scalar-map equality;
no data are chosen from the new unproved theorem inside a definition. The
imported balanced models are characterized by universal counits, generator
formulas and comparison equations, giving compatible identifications up to
the isomorphisms actually used. There is exactly one delivered sorry, the
named realization theorem with its docstring and node; no prohibited
trust declaration occurs. A scratch copy of the actual delivered item,
compiled against its sandbox overlay, prints exactly propext, Classical.choice,
Quot.sound and sorryAx for both public theorems (22.6 seconds). An initial
import-only probe outside the overlay failed to find the new module and was
replaced by this actual-file probe; its failure was not treated as an axiom
check. The scratch probe was removed before delivery.

3. Split statement: PASS. Read RingTensorCohomology, every field of
BaseDerivedTensorCohomologyModel, MixedTensorKFlatQuasiIso,
KFlatScalarExtensionCounit, BaseDerivedTensorCohomologyModelMap and
FlatScalarExtensionHomologyAdjunct. The first proof step uses an R-K-flat
resolution of restricted Q and resolution_R(pi); the second uses the
A-K-flat span resolution_A(Q) to Q and resolution_A(U). Clause (i) of the
mixed-tensor theorem applies with B[0] and C[0], respectively; no flatness
of B over R or R-K-flatness of restricted Q is assumed. The universal
counit theorem applies only on the R-K-flat resolution. Tensor-generator
linearity follows from A-linearity of pi and the model action equations;
scalar endomorphisms need not come from morphisms of E. The model-map
step uses universal uniqueness, and comparison_eq and localized_eq fix
the final comparison adjunct. Flatness C to D is used for that final
cohomology extension. Checked identity replacement, an acyclic K-flat
replacement of zero, zero rings, empty E and nonflat B over R. These
introduce no exception to the proof. The new theorem is only the
single-ring realization: it asserts neither prime localization nor an
isomorphism between two base rings, and all its output clauses are used.
It is strictly part of the argument, not a renamed copy of the item.

Independently read official Stacks Tags
[064L](https://stacks.math.columbia.edu/tag/064L),
[065Z](https://stacks.math.columbia.edu/tag/065Z),
[00HD](https://stacks.math.columbia.edu/tag/00HD) and
[0DJ8](https://stacks.math.columbia.edu/tag/0DJ8). The first three support
tensor invariance, the comparison and flat tensor exactness; the affine
localization identity in 0DJ8 is the item's source. New searches used
LeanFinder's query “canonical derived tensor cohomology isomorphism computed
using any K flat resolution compatible with augmentation” (eight Tor and
representation-cohomology infrastructure hits), Loogle's fully qualified
CategoryTheory.Functor.leftDerivedUnique (one uniqueness-isomorphism hit),
and logged grep for scalarExtension_quasiIso_of_kFlat, leftDerivedUnique
and mapHomologyIso_hom_naturality (five Mathlib infrastructure hits).
Read the library's BaseDerivedTensorModelQuasiIsoComparison: it transports
already supplied balanced models, not prescribed source/target lifts.
Upstream homotopy/derived-category searches found no duplicate realization.
The existing scalar-extension quasi-isomorphism lemma shortens an eventual
proof step, but none of these results closes the full realization in a
few-minute application.

4. Route and pruning: PASS. Read the proof from alpha and beta down to
the two realization applications, the existing derived-localization
comparison, coefficient flatness and the coefficient associator. The
three final goals are explicitly proved by naturality and cancellation.
All added imports are proof-only and used; the public imports serve the
unchanged signature. Compared the original proof_deps list: the only
removed edges are localization-tensor-product and localization-module-exact,
and both are listed under No longer needed with their removed direct
imports. No global-unreachability claim is made. Read the unit record
sk-thm-picard-semicon: realized.statement is empty and its sole realized
step list is empty. No unit or chapter route is changed. This closes one
upper hole and adds one lower hole, a decomposition with net zero holes,
not a claim of a net proof advance.

5. DAG: PASS. Checked both verbatim Lean statement records and the exact
union of uses against proof_deps. The existing node changes only Lean/proof
metadata and retains its mathematical statement. Its steps track the two
realizations, K-flat extension, flatness, derived localization, tensor
associativity and cancellations actually written. The new node has its
self-contained statement, source, full proof, dependency union, origin,
three search modes (including the recorded unavailable LeanSearch service),
split status, creation metadata, blueprint ancestry, chapter/unit and Lean
record. Its dependencies supply exactly the facts described above. The
metadata names the mixed-tensor theorem for the B[0]/C[0] applications.
No new cycle or duplicate statement was found.

Second reading changed: appended this independent review and renewed the
compile, signature, search and axiom checks. No Lean or node repair was
needed; the earlier citation repair is retained. The single realization
hole remains explicitly reported as a decomposition.

Repair follow-up: independently checked that the five proof-plan imports added
to `PrescribedTensorCohomologyModelRealization.lean` are present exactly as
recorded and compile cleanly.


## Second reading by G2

1. Interface: PASS. Compared the complete item diff with the read-only repository
and checked its existing theorem signature byte for byte by extraction. Hypotheses,
conclusion, visibility and public imports are unchanged. There is one new public
statement, in its own module. The elaboration-command change record covers local
opens, the local instance and the per-declaration option; no adaptation is present.

2. Proof and trust: PASS. Both delivered modules compile in import order through
lcompile.py, without errors or warnings (13.2 and 15.2 seconds). Read all private
helpers and the complete main proof. There is no sorry in the item and exactly one
in the named realization theorem. No prohibited declaration or hollow definition
is introduced. The coefficient associator is constructed directly. The imported
balanced models are determined up to the compatible isomorphisms used here by
universal counits, cohomology/action isomorphisms and generator/comparison equations;
they are not arbitrary unspecified witnesses. A separate axiom probe is recorded
below after compilation.

3. Split statement: PASS. Read RingTensorCohomology, the balanced-model fields,
the universal K-flat counit, mixed-tensor invariance, the model-map theorem and
the flat homology adjunct. The new theorem identifies models over one ring and
asserts no localization comparison; it is strictly part of the argument. Each
output clause is used in the main proof. The source uses an R-K-flat resolution
of restricted Q; it does not assume restricted Q is R-K-flat. The target uses
an A-K-flat span, so B need not be R-flat. For arbitrary E, A-linearity of pi
supplies commutation with scalar endomorphisms even when E has no such arrows.
Checked zero and identity replacements, acyclic replacements of zero, empty E,
zero coefficient rings, unbounded complexes and nonflat B. These require no
additional hypothesis. The natural-language proof and node describe the whole
remaining construction, including comparison compatibility.

Independent searches: LeanFinder queried "K-flat resolution cohomology scalar
extension augmentation natural counit compatibility" (eight resolution/Ext
infrastructure hits); Loogle queried CategoryTheory.Functor.leftDerivedUnique
(one uniqueness isomorphism); logged Mathlib grep queried
isLeftDerivedFunctor_iff_isIso_app_of_kFlat, homologyFunctorFactorsh and
mapHomologyIso_hom_naturality (13 infrastructure hits). Read the nearby proved
AffineTensorCohomologyScalarParts and AffineDerivedBaseChangeComparison and the
model quasi-isomorphism transport theorem: none identifies all the prescribed
lifts with arbitrary balanced models and the required natural comparison maps.
They do not close this remaining theorem in a few-minute application. Official
Stacks Tags 064L and 00HD were read again for tensor invariance and exact flat
extension; the web fetch of 065Z failed in this reading (its prior reading is
recorded above).

4. Route and pruning: PASS. Read the main proof from alpha/beta and the final
square down to the two realization applications and the existing derived
localization theorem. The coefficient associator and all cancellations are
proved. Added imports are proof-only; all five proof-plan imports in the new
module are present. Compared the old proof_deps: the two removed edges are
localization-tensor-product and localization-module-exact, both reported under
No longer needed. Only direct imports/edges are pruned; no global-unreachability
claim is made. The unit sk-thm-picard-semicon has empty realized statement/step
lists, which are unchanged. This remains one hole closed and one added, a
net-zero decomposition.

5. DAG: PASS. Checked both lean.statement strings against their actual signatures
and both proof_deps lists against the union of their steps' uses. The existing
node changes only proof, proof_deps and proof_origin. Its steps match the written
proof. The new node has its self-contained hypotheses, source, full argument,
dependency union, origin, searches, split status, creation, blueprint ancestry,
chapter/unit and Lean record. Its proof-plan modules agree with the added imports.

Second reading changed: appended this independent review and renewed compilation,
byte-for-byte signature, dependency, edge-case, duplicate-search and axiom checks.
No Lean or node repair was needed; the five proof-plan imports from the repair
are retained. The remaining realization hole is explicitly a decomposition.

Axiom probe: both public declarations report exactly propext, Classical.choice,
Quot.sound and sorryAx. The probe compiled against the sandbox overlay in
23.8 seconds and was removed before delivery.
