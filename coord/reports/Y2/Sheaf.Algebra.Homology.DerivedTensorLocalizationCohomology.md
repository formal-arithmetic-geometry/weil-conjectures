## What changed

Replaced the sorry in `RingTensorCohomology.derivedTensor_localization_cohomology` by
composition of first-factor localization and base/second-factor localization through
an intermediate `BaseDerivedTensorCohomologyModel R Aq B` for the localized complex.
The original signature and visibility are unchanged. The proof constructs the
intermediate coefficient algebra map by the tensor universal property and verifies
its scalar towers. It proves the comparison square by composing the two smaller
squares and cancelling an equality-induced scalar-extension isomorphism. It proves
naturality by composing the two equations through a characterized intermediate
cohomology morphism. Three new modules and nodes record these smaller interfaces.

The intermediate model is chosen only locally in this theorem. Its universal
counit and coefficient-action equations determine the cohomology and comparison
up to the equality-preserving model isomorphisms used downstream. No new data
construction chooses an undetermined witness of a mere existence theorem.

## Proved and sorry left

Closed the original hole in
`RingTensorCohomology.derivedTensor_localization_cohomology`
(node `lem-pc-derived-tensor-localization-cohomology`). This is a decomposition,
not a sorry-free proof of the full mathematical localization argument.

Also proved `RingTensorCohomology.exists_baseDerivedTensorCohomologyModelMap`
(node `lem-pc-base-derived-tensor-cohomology-model-map`) directly from the model
fields and Mathlib's uniqueness of total left derived functors. The construction
conjugates the induced B-linear map by the two cohomology identifications, proves
commutation with A by naturality, and uses tensor induction to prove full
A-tensor-B linearity.

New holes:

- `RingTensorCohomology.derivedTensor_first_localization_models`
  (`lem-pc-derived-tensor-first-localization-models`).
- `RingTensorCohomology.derivedTensor_base_second_localization_models`
  (`lem-pc-derived-tensor-base-second-localization-models`).

No sorry remains in the original module or the model-map module. Each remaining
sorry is the entire proof of a public named theorem in its own new module,
with the source and proof in words in its docstring.

## No longer needed

Removed direct proof imports from the original module:

- `Sheaf.Algebra.Homology.BalancedDerivedTensorModel`
  (`lem-pc-balanced-derived-tensor-model`).
- `Sheaf.Algebra.Homology.DerivedTensorActionNaturality`
  (`lem-pc-derived-tensor-action-naturality`).
- `Sheaf.Algebra.Homology.DerivedTensorFlatSecondLocalization`
  (`lem-pc-derived-tensor-flat-second-localization`).
- `Sheaf.Algebra.Homology.KFlatPullback`
  (`lem-pc-kflat-pullback-preservation`).

The first three are still needed in the proof plans of the smaller localization
items; they are not claimed globally pruned. The ring-level K-flat extension
lemma `lem-pc-kflat-extension-of-scalars` replaces the one-point-space detour
through KFlatPullback. The ringed-space module and its stalkwise prerequisites
are no longer needed for this item's localization argument.

The old direct proof dependencies `lem-weil-pbc-localization-module-exact` and
`lem-weil-pbc-localization-tensor-product` move into the smaller localization
nodes and remain necessary there. No unit statement or realized proof step is
bypassed: the unit record has empty realized statement/step arrays, and the
parent's two localization and compatibility operations are retained.

## Where the brief, the DAG or earlier work was wrong

The supplied balanced/action lemmas quantify a bifunctor on derived categories
and its coefficient action; the existing flat-second-factor lemma uses fixed
resolution functors and B-linear source objects. None directly gives the
arbitrary `BaseDerivedTensorCohomologyModel` localization comparisons quantified
by this theorem. The two new localization interfaces isolate that missing
transport while separating first-factor localization from changing the base
and second factor. Each leaves one factor/operation unchanged and is strictly
part of the original argument; neither restates the original conclusion.

The first smaller theorem works for general multiplicative-subset localization
and arbitrary Q; the second assumes Q is already over the localized base via A.
Edge cases checked mathematically: identity localizations give model-identification
isomorphisms; zero complexes and zero cohomology give the zero-object isomorphism;
localizations containing zero yield zero rings/modules. For R=k[t] and
A=B=R/(t), first-factor localization does not replace the R-derived tensor by
ordinary tensor: resolving B over R preserves its nonzero Tor. No flatness of
A over R is used. The compatibility hypotheses tying the primes are unused in
the final composition because the given algebra/scalar towers already specify
compatible maps, and the smaller statements hold for general localizations.

The local Stacks TeX source is absent on this machine. Read the original sources
at https://stacks.math.columbia.edu/tag/0DJ8 and
https://stacks.math.columbia.edu/tag/06Y6. Search used LeanFinder, Loogle, grep
and local rg; LeanSearch returned Internal Server Error and is recorded as
unavailable, not as a negative mathematical result. Blueprint searches for
localization and tensor cohomology models found no exact existing blueprint
statement of the new interfaces.

## New nodes

`lem-pc-derived-tensor-first-localization-models` in
`Sheaf.Algebra.Homology.DerivedTensorFirstLocalizationModels`: localize only
A and its complex while leaving the base R and second algebra B fixed.

`lem-pc-derived-tensor-base-second-localization-models` in
`Sheaf.Algebra.Homology.DerivedTensorBaseSecondLocalizationModels`: change
R to its localization and localize B, keeping the already localized A-complex
fixed. These are the two remaining theorem holes.

`lem-pc-base-derived-tensor-cohomology-model-map` in
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModelMap`: a proved general
model-map lemma, with no localization hypotheses. It constructs the intermediate
map needed to compose the naturality equations. No interface change record is
needed: all existing public signatures and public imports remain unchanged.

## Second reading by Y2

1. PASS: compared every delivered module with the read-only repository. Only
   DerivedTensorLocalizationCohomology existed there. Its theorem signature is
   byte-for-byte unchanged, as are its public imports, variables, scalar towers,
   universe parameters and visibility. The declaration-table comparison reports
   no statement changes. The other three modules are new; no existing definition
   or target is changed and no forced adaptation or change record is needed.
2. PASS: compiled all four modules in import order through lcompile.py. Compiled
   scratch copies with #print axioms for all four public theorems. The model-map
   theorem uses only propext, Classical.choice and Quot.sound. The two localization
   theorems and the original theorem additionally use sorryAx, as reported.
   Exactly two whole, named public theorem proofs remain sorry; no data definition
   contains sorry and no forbidden axiom/unsafe/opaque/extern mechanism occurs.
   The equality-induced scalar-extension isomorphism is explicitly constructed.
   The locally chosen intermediate model is determined up to the isomorphisms
   relevant downstream: universal counits identify derived functors uniquely;
   cohomologyIso and cohomologyIso_smul determine tensor-linear cohomology, and
   comparison_eq/localized_eq determine the comparison maps. Thus this is a
   choice of a universal-property model, not an arbitrary undetermined witness.
3. PASS: independently checked both localization statements against their full
   signatures and the Stacks arguments at https://stacks.math.columbia.edu/tag/0DJ8,
   https://stacks.math.columbia.edu/tag/06Y6 and
   https://stacks.math.columbia.edu/tag/064K. First-factor localization fixes R,B;
   base/second-factor localization fixes the already Rp-linear complex. Both are
   strictly parts of the combined argument and include the necessary comparison
   and naturality clauses. Checked identity localizations, zero complexes, zero
   localizations, and R=k[t], A=B=R/(t), where Tor_1 must survive. An arbitrary
   nonflat D causes no gap: exact localization identifies cohomology before
   subsequent scalar extension to D; no commutation of D-tensor with homology
   is asserted. Each hole has a source, complete proof docstring and matching
   node. Repeated searches with different terms using msearch.py: LeanFinder
   for flat ring epimorphisms and commuting algebra actions found flatness and
   exactness tools, not either localization statement; Loogle for
   CategoryTheory.Functor.leftDerivedUnique confirmed the uniqueness tool used
   in the proved map lemma; grep and local rg found no duplicate localization
   interface. Read the existing BalancedDerivedTensorModel,
   DerivedTensorActionNaturality, DerivedTensorFlatSecondLocalization and
   FlatBaseDerivedTensorComparison statements; none directly closes these
   arbitrary-model localization holes in a few minutes.
4. PASS: the original proof constructs the coefficient map, composes the two
   smaller isomorphisms, proves comparison by homology functoriality and
   cancellation, and composes naturality through the proved model-map theorem.
   This is a real reduction. Imports are needed for the signatures or proofs;
   new proof-only imports are plain imports. No shorter ready-made theorem was
   found. The six old direct proof dependencies are all accounted for in
   No longer needed: four imports removed and two ring-localization dependencies
   moved into the new plans. No global pruning of shared modules is claimed.
   Read dag/units/sk-thm-picard-semicon.json: realized.statement and its single
   realized step are empty; the parent affine localization argument remains
   realized by this composition, without bypassing a unit statement or step.
5. PASS: checked all four nodes against the Lean and verified that proof_deps
   equals the union of proof-step uses. The existing node changes only proof,
   proof_deps and proof_origin. All new nodes have source, statement dependencies,
   searches, split status, creation provenance, blueprint lineage, chapter/unit,
   Lean module/file/declaration and statement. Updated the three new nodes'
   Lean statements to preserve the exact multiline declaration signatures.

Second-reading changes: replaced the original theorem's stale proof docstring,
which still named the removed ringed-space KFlatPullback detour, with the actual
composition, comparison-cancellation and intermediate-map argument. Preserved
all proof terms and signatures. Made the three new node Lean signatures verbatim.
Added this independent review and explicit axiom results.

Hole accounting: one existing hole closed
(RingTensorCohomology.derivedTensor_localization_cohomology), two holes added
(RingTensorCohomology.derivedTensor_first_localization_models and
RingTensorCohomology.derivedTensor_base_second_localization_models), net -1
before any whole-closure pruning. The auxiliary
RingTensorCohomology.exists_baseDerivedTensorCohomologyModelMap is fully proved
without sorryAx. The original theorem still depends on the two new holes; this
is a decomposition, not a completed proof of derived tensor localization.
