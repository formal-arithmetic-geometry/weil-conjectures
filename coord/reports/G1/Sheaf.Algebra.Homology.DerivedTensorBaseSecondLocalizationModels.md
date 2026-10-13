## What changed

Reduced `RingTensorCohomology.derivedTensor_base_second_localization_models` to
second-factor localization with base fixed and localized-base change with second
factor fixed. The theorem's signature and existing public imports are unchanged.
Constructed the intermediate coefficient algebra map by the tensor universal
property. Composed the two D-linear isomorphisms, their comparison squares and
naturality equations. Added proof-only imports of the two new modules and
`BaseDerivedTensorCohomologyModelMap`.

The intermediate cohomology model is chosen using its existing existence theorem:
its derived functor, cohomology and comparison are determined up to the
counit-compatible/cohomology identifications used downstream. No arbitrary
uncharacterized mathematical object or holed definition is introduced.

## Proved and sorry left

Closed the original hole in
`RingTensorCohomology.derivedTensor_base_second_localization_models`
(node `lem-pc-derived-tensor-base-second-localization-models`).
Added two holes, each exactly a part of the localization argument:

- `RingTensorCohomology.derivedTensor_second_localization_models`
  (node `lem-pc-derived-tensor-second-localization-models`).
- `RingTensorCohomology.derivedTensor_base_localization_models`
  (node `lem-pc-derived-tensor-base-localization-models`).

This is a decomposition, not a sorry-free proof: one hole closed, two added.
The original module contains no remaining sorry.

## No longer needed

No existing imports removed. No module is claimed globally pruned. The original
node's balanced-model, tensor-localization, exactness, K-flat base-change,
flat-second-localization, localization-flatness and action-naturality dependencies
are needed only by the two smaller lemmas, and are retained in their proof plans.
The original node uses only the two new nodes, model existence and model maps.
Its old direct proof dependencies no longer used directly are:
`lem-pc-balanced-derived-tensor-model`,
`lem-weil-pbc-localization-tensor-product`,
`lem-weil-pbc-localization-module-exact`,
`lem-pc-kflat-extension-of-scalars`,
`lem-pc-derived-tensor-flat-second-localization`,
`lem-weil-pbc-localization-flat`, and
`lem-pc-derived-tensor-action-naturality`.
These are retained below the two split nodes; this delivery does not globally prune them.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped without implementing any reduction. The old plan
mixes base change and second-factor localization in one construction. Applying
second-factor localization first makes Bp already an Rp-algebra; subsequent
base localization then leaves the second factor fixed and is a distinct simpler
obligation. The unit route is retained (its realized lists are empty).
`DerivedTensorFlatSecondLocalization` proves an analogous result for the
resolution/source interface, but does not directly supply arbitrary-model
transport or the localizedComparison interface used here.

Edge cases: S={1} makes base change model transport; T={1} makes second-factor
change model transport. If either localization is the zero ring, D is also the
zero ring through the relevant compatible coefficient maps, and both extended
objects are zero. No boundedness or flatness of A over R was added. Arbitrary D
is valid: flatness is used only for localization, then tensor associativity
extends its isomorphism to D.

The local literature sources are absent from this checkout; the cited primary
source text was read at https://stacks.math.columbia.edu/tag/0DJ8 and
https://stacks.math.columbia.edu/tag/06Y6. The new proof plans expand the
model transport omitted in the displayed identity, and are marked agent-written.

## New nodes

`lem-pc-derived-tensor-second-localization-models` in
`Sheaf.Algebra.Homology.DerivedTensorSecondLocalizationModels` isolates exact
second-factor localization and its arbitrary-model transport. It does not change
the base, and its plan retains the already proved flat-second-factor lemma.

`lem-pc-derived-tensor-base-localization-models` in
`Sheaf.Algebra.Homology.DerivedTensorBaseLocalizationModels` isolates change of
localized base when both tensor factors are already Rp-modules. It performs no
second-factor localization. Its plan retains the original balanced-model,
K-flat base-change, tensor-localization and action-naturality nodes.

## Second reading by G1

1. Compared the complete original module with the repository using diff. The existing
   variables, included scalar towers, theorem signature, docstring, visibility and
   public imports are byte-for-byte unchanged. The only additions are three private
   equality-transport helpers, three proof-only imports and the theorem body. No
   statement or definition change record is needed.
2. Read the composed proof: the tensor universal property constructs the intermediate
   coefficient map with the required A and Bp restrictions. Equality of scalar maps
   constructs tau0; tau0 inverse followed by tau supplies the second square. Homology
   composition and associativity compose both squares. The existing model-map theorem
   supplies delta0 and g0, so the two naturality clauses apply to the same intermediate
   models. Local compilation and axiom checks are recorded below. There are exactly
   two direct sorries, both named theorems in the new modules, and no forbidden trust
   mechanism or hollow definition. The local choice U uses the universal derived
   functor, prescribed action and comparison equations of the existing model, which
   determine the data up to the identifications actually used here.
3. Read Stacks Tags 0DJ8 (lemma-single-complex-base-change-condition, displayed
   localization identity) and 06Y6 (lemma-derived-base-change). Neither new lemma
   restates the full simultaneous localization: the first keeps R fixed; the second
   assumes both factors already have Rp-actions and keeps B fixed. Localization
   exactness and K-flat extension justify their two different reductions. No flatness
   of A or boundedness of Q is assumed. At T={1} or S={1} the relevant statement is
   canonical model transport; Q=0 gives zero cohomology; a zero localization forces
   D=0 via its compatible algebra map. Arbitrary D is allowed because further scalar
   extension is applied to an isomorphism, not claimed to commute with homology.
   Additional LeanFinder search for derived flat scalar-extension cohomology gave
   unrelated Ext/group-cohomology hits. Loogle reported the unqualified
   Functor.leftDerivedUnique identifier unknown. Local and upstream rg searches found
   DerivedTensorFlatSecondLocalization, whose resolution/source interface lacks the
   arbitrary-model comparison asserted here. No shorter direct matching declaration
   was found, and neither remaining hole can be closed by a few-line application.
4. Checked all imports against the signatures and bodies: existing public imports
   supply model, complex and localization notation; all three added imports are used
   only in the proof and are plain imports. Listed every replaced old direct
   dependency explicitly under No longer needed. The sk-thm-picard-semicon unit has
   empty realized statement/step lists; no realized unit node is bypassed.
5. Compared all node statements and recorded Lean signatures with the modules. The
   original proof_deps union is exactly the two split results, model existence and
   the existing model-map result used in the proof. New nodes have matching named
   declarations, source, complete proof plans, searches, creation and blueprint
   records. Repaired their prose statements to mathematical notation and explicit
   citations of both definition nodes, without changing either Lean statement.

Changes in this reading: completed the exact replaced-dependency list, repaired
new-node notation/definition citations, and added this independent review. The
Lean proof and its two split statements needed no repair. One original hole is
closed by a decomposition into two holes, so this is not net hole reduction.

Validation: `lcompile.py --all` compiled all three delivered modules with exit
code 0 and no warnings. A scratch copy of the original module with explicit
`#print axioms` for all three public theorems compiled with exit code 0;
each uses only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
The latter remains through the two documented open split theorems and existing
open model dependencies. All delivered Lean lines are at most 100 characters;
the existing node changes only proof, proof_deps and proof_origin.
