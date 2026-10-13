## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.perfect_of_directSum` by a compiling
proof with its original signature and visibility. The proof follows 08CS through
pseudo-coherence and local Tor dimension. It constructs both derived retracts from
the biproduct isomorphism, restricts them by functoriality, and proves each local
Tor-vanishing assertion with the new, proved retract lemma.

Added `DerivedTensorVanishingRetract`: its public theorem proves vanishing is
preserved by a retract, using the existing private `tensor_vanishes_iff` theorem
in `TorAmplitudeOpenLocal` through an ordinary `import all`. Removed the three
duplicate helpers `exists_kFlat_model`, `tensor_model_iso`, and
`tensor_vanishes_iff`; none is redeclared in the repaired module. The import is
proof-only and changes no existing interface or visibility.

Added `PerfectOfPseudoCoherentLocallyFiniteTor`: its public theorem is proved by
explicit affine models, rather than leaving local-to-global perfectness as a hole.
It imports all of
`PerfectOfPseudoCoherentFiniteTorDimension` to reuse the existing private
`affine_finiteFree_model` and `affine_projective_strictlyPerfect` theorems.
The duplicate declarations `affine_free_iso`, `affine_finiteFree_model`, and
`affine_projective_strictlyPerfect` have been removed from the new module. The argument intersects the free-model
neighbourhood with a Tor neighbourhood before refining to an affine open.

Added `AffineLocalSheafificationTorAmplitude`: the remaining hole isolates transfer
of Tor bounds from an open neighbourhood to its affine module model. This is a
proper substep of the argument: it mentions neither pseudo-coherence, perfectness,
nor direct summands. The existing affine transfer theorem assumes a global bound
on the original scheme and does not apply to these local bounds.

Second reading removed the copied localization transport helper from the item.
An ordinary `import all Sheaf.AlgebraicGeometry.SchemeIsoDerivedLocalizations`
reuses its existing private `hasDerivedCategory_of_equivalence` theorem, which
constructs localization data from the exact complex equivalence. The item applies
this proved construction to `Modules.overEquiv`; no arbitrary unproved witness
is chosen.
All imports required only by proofs are ordinary imports. No existing declaration
signature, definition, public import, or target statement changed. All four modules
compile together through lcompile.py in import order.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Scheme.perfect_of_directSum` (`lem-pc-perfect-summand`).
There were 1 original holes; 0 remain in the item's module.

New complete public proofs:
`AlgebraicGeometry.schemeDerivedTensorCohomologyVanishes_of_retract`
(`lem-pc-derived-tensor-vanishing-retract`) and
`AlgebraicGeometry.Scheme.isPerfect_of_isPseudoCoherent_of_hasLocallyFiniteTorDimension`
(`lem-pc-pseudo-coherent-locally-finite-tor-perfect`). The localization helper and affine helpers are
reused from existing modules, not redeclared.

Exactly one new hole:
`AlgebraicGeometry.Scheme.finiteTorAmplitude_of_affine_sheafification_of_open_tor`
(`lem-pc-affine-local-sheafification-tor-amplitude`), the entire proof of the public
named theorem in its own module. Its docstring and node contain its source and
complete mathematical argument. Neither the module model nor any definition
contains a hole.

This is a decomposition (1 original hole closed, 1 strictly narrower hole added),
not a claim of a sorry-free target or positive net hole reduction. Existing
imported theorem holes, notably pseudo-coherence of summands, remain with their
existing modules and nodes for later workers.

## No longer needed

Second reading removed the item's direct proof import
`Mathlib.CategoryTheory.Localization.Equivalence` and its copied private
`hasDerivedCategory_of_equivalence` declaration. The import remains a transitive
dependency of the reused `SchemeIsoDerivedLocalizations` module; no global module
pruning is claimed. The owner node `lem-pc-scheme-iso-derived-localizations` is now
a direct proof dependency of the item, specifically for its proved generic helper.

Repair: removed direct imports `Sheaf.Algebra.Homology.KFlatResolution` and
`Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison` from the retract module.
Their nodes `lem-pc-kflat-resolution` and
`lem-pc-kflat-derived-tensor-comparison` are no longer direct proof dependencies
of the retract node; they remain transitive dependencies of the reused comparison.
`TorAmplitudeOpenLocal` is now needed and is not pruned. All three duplicate
private helper declarations are removed.

The item no longer imports `PerfectOfPseudoCoherentFiniteTorDimension` directly,
but the new local criterion now imports it with `import all`. Its node
`lem-pc-pseudo-coherent-finite-tor-perfect` is a proof dependency of the local
criterion as the owner of the two reused private helpers. Neither the module nor
its transitive dependencies, including `AffineSheafificationTorAmplitude`, are
pruned from the import closure. The global perfectness theorem itself is not
applied: the existing affine-model and projective-sheafification lemmas are used.

Removed the local criterion's direct imports
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` and
`Mathlib.RingTheory.Finiteness.Projective`: only the removed private proofs needed
them. They remain transitive dependencies of the reused helper module.
The nodes `lem-pc-affine-perfect-module-model` and
`lem-weil-pbc-spec-module-tilde-sections` are no longer direct dependencies of the
local criterion; the helper-owning node replaces them. No global pruning of
those modules is claimed.

The old direct proof dependency `def-pc-perfect-complex` is now used in the new
local criterion rather than unfolded by the item itself; its definition and module
remain needed, and it is not a pruned module. This accounts for the other old
`proof_deps` entry absent from the new item node.

The other original proof imports remain needed. The ring criterion, affine
associated-sheaf construction, and localized derived sheafification are still
used in the new local criterion; those nodes are not pruned. These statements
concern this proof's dependency route, not an assertion that other target branches
cannot reach the old modules. No unit or chapter route is bypassed.

## Where the brief, the DAG or earlier work was wrong

Repair of return 88e3f33e7: the local criterion had copied three private
lemmas from `PerfectOfPseudoCoherentFiniteTorDimension` word for word. Removed
all three and imported the existing module with `import all`, preserving every
existing signature and visibility. The local criterion applies its existing
`affine_finiteFree_model` and `affine_projective_strictlyPerfect` directly;
`affine_free_iso` is used internally by those existing proofs. Updated the
criterion node's steps and dependencies to record this reuse. The import-cycle
check permits the import. All four delivered modules compile with no warnings.
The report's previous claim that the global criterion module and its affine
transfer dependency were pruned has been corrected. The previous second readings
below predate this repair and require a fresh independent reading.

Repair of the landing-tools return at bdcbfe831: the first delivery duplicated
three private comparison statements already present word for word in
`TorAmplitudeOpenLocal`. Lean supports access to these existing private theorems
with `import all`, so copying them was unnecessary. The repaired retract proof
uses the existing `tensor_vanishes_iff` directly, and its DAG records the module
that supplies it. No existing module is adapted. The second-reading section below
is the prior delivery review; this repair awaits a fresh independent reading.

The DAG's mathematical argument is sound, but its step 3 was marked elementary
without an available Lean theorem connecting the existential K-flat predicate to
functorial homology vanishing. That step is now a complete Lean proof using
`KFlatDerivedTensorComparison` and the retract equations.

Step 4's existing Lean theorem has global finite Tor dimension as a hypothesis;
the forward perfectness theorem supplies local finite Tor dimension. Applying the
global theorem directly on X would be invalid. The new local criterion makes the
affine construction within a Tor neighbourhood explicit and isolates only the
local affine Tor transfer.

The forward theorem also requires derived categories on the open subschemes, while
the item supplies them on localized open sites. The proof now transports the given
localizations through the exact over equivalences without changing the signature
or adding hypotheses.

The repository's literature sources are absent on this machine. I read the
official Stacks pages for 08CS, 08CQ, and 08CK, then downloaded the corresponding
cohomology.tex and perfect.tex sources into the sandbox scratchpad. The cited
labels and proof steps were checked there. LeanSearch returned Internal Server
Error; this is recorded as unavailable, with real LeanFinder, Loogle and source
searches recorded separately. Empty schemes, empty affine opens, zero rings and
zero summands require no additional hypotheses.

## New nodes

`lem-pc-derived-tensor-vanishing-retract`, in
`DerivedTensorVanishingRetract`, is proved. It makes the 08CK vanishing step
functorial at a single degree for any retract.

`lem-pc-pseudo-coherent-locally-finite-tor-perfect`, in
`PerfectOfPseudoCoherentLocallyFiniteTor`, is proved from the existing ring
criterion and reused affine construction lemmas, plus the single local transfer hole.
It realizes 08CQ (2) to (1) with local, rather than global, Tor bounds.

`lem-pc-affine-local-sheafification-tor-amplitude`, in
`AffineLocalSheafificationTorAmplitude`, remains sorry. It transfers bounds from
an open W containing an affine open U to the module model of K on U, independently
of pseudo-coherence or perfectness. It generalizes the locality substep of the
existing global affine transfer statement, rather than restating the item.

All new nodes inherit the item's unit, chapter, and nearest blueprint ancestor.
The unit's realized lists are empty, and no fixed unit or chapter step was changed.
No change record or forced adaptation is required.

## Earlier second reading (a previous round; superseded)

1. Compared the complete item with the repository version using `diff -u`, then
   compared the signature from `theorem perfect_of_directSum` through `:= by`
   byte for byte: identical. X, both localization assumptions, K/L/M, the
   biproduct isomorphism, the perfectness hypothesis and both conclusions are
   unchanged. The only existing module edited is the item; the other three
   modules are new. Its existing public import is unchanged, and new proof
   imports are ordinary imports. The existing node changes only `proof`,
   `proof_deps` and `proof_origin`. Verdict: no accidental interface change.

2. Independently compiled all four files through `lcompile.py --all`, with no
   errors or warnings (5.1, 7.1, 16.1 and 4.5 seconds). Read every proof and the
   concrete lifted-complex construction. The only delivered `sorry` is the
   named affine local transfer theorem; no forbidden axiom, unsafe declaration,
   opaque declaration, implementation override or hollow definition is present.
   Scratch copies with `#print axioms` checked all named public theorems and
   private helpers. The retract lemma, its three helpers, the three affine-model
   helpers and the localization helper use only `propext`, `Classical.choice`
   and `Quot.sound`. The local criterion and item additionally use `sorryAx`
   through the stated open results. The localization helper constructs its
   category and localization functor; it chooses no arbitrary unproved data.
   Affine localized derived sheafification is used with its factorization
   isomorphism, which determines the functor up to the isomorphism used here.
   Verdict: sound reduction, not a sorry-free proof of the target closure.

3. Read `cohomology.tex` labels `lemma-summands-perfect` (08CS),
   `lemma-summands-tor-amplitude` (08CK) and `lemma-perfect` (08CQ), and
   `perfect.tex` label `lemma-tor-dimension-affine` (08E9). The only new hole
   transfers finite Tor dimension from W to a representing ring complex on
   an affine U contained in W. Its representing isomorphism and inclusion
   supply exactly the comparisons its docstring uses. Restriction is exact;
   direct image of each test sheaf restricts back to that sheaf; associated
   sheafification detects zero cohomology. Thus its argument proves the
   stated result without boundedness or pseudo-coherence assumptions. Tested
   the empty scheme, empty U, zero ring, zero representative and U = W cases:
   none require a missing hypothesis. The retract statement also allows the
   identity retract and zero summand. This is strictly a substep of 08CS,
   mentioning neither perfectness nor pseudo-coherence. Independent searches
   used LeanFinder's query about local affine Tor dimension, Loogle's
   `"torAmplitudeIn"`, Mathlib grep with Tor/retract keywords, and `rg` in
   both library roots and upstream AlgebraicGeometry. The upstream generic
   Tor-amplitude retract instance does not identify our existential K-flat
   predicate; the new proved comparison is necessary. The existing global
   affine transfer theorem assumes finite Tor dimension on all of S and
   cannot take the local hypothesis on W directly. Verdict: true, narrower
   split with a source, complete docstring argument and matching node;
   no existing declaration directly closes it in a few minutes.

4. Read the proof downward. The biproduct equations construct genuine retracts;
   derived pullback maps them, and the proved vanishing lemma keeps each local
   interval. The criterion intersects the pseudo-coherent and Tor opens
   before choosing an affine refinement, so neither global Tor bounds nor an
   affine intersection is assumed. Its free-model lift constructs differentials
   by full faithfulness, verifies their relations and preserves the upper bound.
   The ring criterion is applied only after both its hypotheses are established;
   finite projectives sheafify to explicit retracts of finite free sheaves.
   The public imports of the transfer module supply its signature, including
   the ModuleCat derived tensor instances from FlatResolution; the remaining
   new imports are proof imports. Checked the original dependency list against
   `No longer needed`, including `def-pc-perfect-complex`, whose use moved into
   the local criterion and whose module stays needed. Read the unit record:
   `realized.statement` is empty and its sole `realized.steps` entry is empty;
   no fixed unit route was bypassed. Verdict: correct downward reduction and
   accurately scoped pruning, with no positive net hole reduction claimed.

5. Opened all four delivered node JSON files and compared each recorded Lean
   statement with its module after whitespace normalization: all agree.
   Each `proof_deps` equals the union of its steps' `uses`. The item records
   pseudo-coherence, both retracts, local Tor bounds and the local criterion;
   the retract node records K-flat resolution and tensor comparison; the local
   criterion records the concrete affine sheafification construction, ring
   criterion and localized derived comparison. The affine model node is used
   for its defined functor, not by applying its strictly-perfect-model theorem
   to a merely pseudo-coherent complex. The remaining hole's node describes
   the open restriction and affine Tor criterion steps. New nodes have their
   source, searches, creation, blueprint, chapter, unit and Lean records.
   Verdict: records agree with the code and the remaining obligation.

Second reading changed only this report: accounted explicitly for the old
`def-pc-perfect-complex` dependency and added this independent review. No Lean
proof or statement required repair. One original hole is closed and one narrower
hole is added: a decomposition, with zero net hole reduction.


## Earlier second reading (a previous round; superseded)

Fresh independent reading of the repaired delivery, 2026-10-13.

1. Compared every delivered module against the repository. Only PerfectSummand
   exists there; its complete theorem signature, from `theorem perfect_of_directSum`
   through the colon before its proof, is byte-for-byte identical. Its sole public
   import and visibility are unchanged. The other three modules are new. Compared
   the existing node field by field: only proof, proof_deps and proof_origin differ.
   No definition or target statement changes, and no change record is necessary.
   Verdict: no accidental interface change.

2. Independently compiled all four modules in import order with lcompile.py --all
   (4.7, 3.2, 17.8, 4.7 seconds), without errors or warnings. Read every proof,
   including the explicit localization and finite-free complex constructions.
   Searched all delivered Lean for forbidden declarations and holes: exactly one
   sorry, the named public affine local transfer theorem. Scratch copies checked
   #print axioms for all four public theorems and all four private theorem helpers.
   The retract theorem and the localization/free/projective helpers use only
   propext, Classical.choice and Quot.sound. The criterion, item and explicitly
   open transfer theorem additionally use sorryAx. There are no hollow definitions
   or arbitrary constructions from unproved mere existence: the lifted differentials
   are explicit, the localization is explicitly built, and the derived
   sheafification functor is used with its localization factorization, which
   determines it up to the natural isomorphism used downstream.
   Verdict: valid decomposition; not a sorry-free import closure.

3. Independently checked Stacks 08CS, 08CK, 08CQ and 08E9 on their official tag pages.
   The remaining affine transfer hole is true: open restriction preserves the Tor
   interval (test direct images of sheaves on the smaller open); exact affine
   associated sheafification identifies tensors and detects zero homology. The
   representing isomorphism is essential and present. Checked empty schemes,
   empty affine opens, zero rings, zero models, identity retracts and U = W;
   none need additional assumptions. Its docstring gives the whole argument and
   its node matches. It does not restate perfectness of summands.
   Fresh msearch searches used LeanFinder on restriction detecting Tor amplitude,
   Loogle on torAmplitudeIn/retract, and grep on retract/affine Tor comparisons;
   also searched both library roots with different keywords. No exact reusable
   transfer statement was found. The existing global affine transfer theorem
   needs a bound on S; using it on W would still require the missing restriction
   and affine-model transport comparisons. The generic Tor-amplitude retract
   instance does not supply our existential vanishing comparison. No split-off
   hole can be closed by an immediate existing declaration.
   Verdict: true, necessary and strictly narrower remaining obligation.

4. Read the reduction from the target down. Genuine biproduct retracts retain the
   local Tor interval by functorial tensor and homology. The criterion refines the
   intersection of the free-model neighbourhood and the Tor neighbourhood before
   choosing an affine open; it never assumes a global bound on S. Its finite-free
   lift and finite-projective sheafification are proved constructions. Every public
   import supplies a signature or required signature instance; other imports are
   proof-only. The retract module now reuses the private tensor_vanishes_iff via
   import all, with no copied comparison helpers. Checked both old proof_deps
   removed from the item: the global criterion is replaced, while the perfect
   definition is still used in the new criterion. The report distinguishes removed
   direct dependencies from transitive dependencies and globally pruned modules.
   The unit sk-thm-picard-duality has empty realized statement and step lists;
   no unit or chapter step is bypassed.
   Verdict: appropriate downward reduction and complete scoped pruning report.

5. Parsed all four node files and compared their recorded Lean statements with
   the corresponding declaration headers after whitespace normalization: all
   match. Each proof_deps is exactly the union of its proof steps' uses. Read each
   route against the implementation: the repaired retract node now correctly
   names TorAmplitudeOpenLocal, the criterion records the ring criterion and
   affine constructions, and the open transfer node records the restriction and
   affine comparison obligations. New nodes contain source, proof, searches,
   creation, blueprint, chapter, unit and Lean records.
   Verdict: DAG and Lean agree.

Second reading changed only this report and added independent search evidence;
no Lean proof or statement needed repair. The original perfect_of_directSum hole
is closed; finiteTorAmplitude_of_affine_sheafification_of_open_tor is the sole
added hole. This remains a decomposition with zero net hole reduction.


## Second reading by Q1

Fresh independent reading of the repaired affine-helper reuse, 2026-10-13.

1. Compared all four delivered modules with the read-only repository using diff
   and a byte-for-byte declaration-header check. PerfectSummand is the sole
   existing module; perfect_of_directSum has precisely its original signature,
   visibility and public import. The other three modules are new. Compared the
   existing node field by field: only proof, proof_deps and proof_origin change.
   No target, definition or existing public interface changes. Verdict: pass.

2. Compiled all four modules through lcompile.py in import order without errors
   or warnings (5.5, 3.1, 14.9 and 3.5 seconds), then compiled the repaired item
   (5.3 seconds). Fresh scratch copies checked #print axioms for every delivered
   public theorem and the reused localization helper. Retract vanishing and
   localization transport use only propext, Classical.choice and Quot.sound;
   the criterion, item and explicitly open transfer theorem additionally use
   sorryAx. Exactly one delivered sorry occurs, in the named public affine
   transfer theorem. No forbidden declaration, hollow definition or arbitrary
   witness from unproved mere existence occurs. The affine derived functor's
   localization factorization determines it up to the isomorphism used here.
   Verdict: valid decomposition, not a sorry-free import closure.

3. Read scratchpad/cohomology.tex at lemma-summands-perfect (08CS),
   lemma-summands-tor-amplitude (08CK) and lemma-perfect (08CQ), and
   scratchpad/perfect.tex at lemma-tor-dimension-affine (08E9). The single
   remaining hole follows by testing the bound on W with direct images from U,
   restricting back, transporting the representing isomorphism, and applying
   the affine criterion. Its hypotheses supply the inclusion U <= W and the
   representing isomorphism; no quasi-coherence or boundedness hypothesis on P
   is needed. Checked empty schemes, empty U, zero rings, zero complexes, U = W,
   identity retracts and zero summands: no missing nonemptiness assumption.
   Its docstring contains this argument and its matching node cites restriction
   and affine comparisons. It neither states perfectness nor mentions summands,
   so is strictly narrower than the item. Fresh msearch used LeanFinder on an
   affine complex inheriting an interval from a larger open, Loogle on
   "torAmplitudeIn", and grep on finiteTorAmplitude/open, TorDimension/restrict
   and torAmplitude/retract; none returned an exact reusable transfer theorem.
   rg also checked both library roots and upstream AlgebraicGeometry. The global
   affine transfer theorem needs a bound on S, while applying it on W still
   requires affine-model and iterated-restriction transport. No immediate proof
   closes the hole. Verdict: true and necessary split, with source and node.

4. Read the proof downward: biproduct maps give actual retracts; derived
   pullback and tensor/homology preserve them; the local criterion intersects
   the two neighbourhoods before affine refinement. It reuses the existing
   affine_finiteFree_model and affine_projective_strictlyPerfect helpers through
   import all; their statements supply exactly the free lift and strictly
   perfect associated complex used. It applies the ring criterion only after
   both hypotheses are established and composes the localization factorization
   isomorphisms in the correct directions. Found one further duplicate: the
   item's localization helper already exists generically in the small module
   SchemeIsoDerivedLocalizations. Removed the copy and reused that proved
   helper by import all; removed the now unnecessary direct Mathlib localization
   import. All proof-only imports are ordinary imports. No longer needed accounts
   for every removed old proof dependency, distinguishing direct dependency
   changes from transitive closure pruning. The unit sk-thm-picard-duality has
   realized.statement = [] and realized.steps = [[]]; no fixed route changes.
   Verdict: correct reduction, now with the remaining copied helper removed.

5. Parsed every delivered JSON node and checked normalized declaration headers
   against its Lean record; all match. Each proof_deps is the union of step uses.
   Read the dependency declarations, including TorAmplitudeOpenLocal's private
   tensor_vanishes_iff and the global criterion's two affine helpers. Their
   owner nodes are explicitly recorded as helper reuse, without pretending to
   apply their differently scoped public conclusions. Updated the item node's
   first step and proof_origin to record reuse of the generic proved localization
   helper from lem-pc-scheme-iso-derived-localizations, and added that dependency.
   New nodes contain sources, searches, creation, blueprint, chapter, unit and
   Lean records. Verdict: DAG agrees with the repaired Lean.

Second reading changed PerfectSummand's proof imports, removed its copied private
localization helper, updated the item node's proof/dependencies/origin, and corrected
this report. No statement changed. Closed perfect_of_directSum; added only
finiteTorAmplitude_of_affine_sheafification_of_open_tor. One original hole closed
and one strictly narrower hole added is a decomposition with zero net reduction.
No module is claimed pruned globally.
