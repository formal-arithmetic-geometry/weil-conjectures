## What changed

Preserved Q3's proof of `RingTensorCohomology.exists_affineDerivedBaseChangeComparison`.
Reduced `RingTensorCohomology.exists_affineDerivedBaseChangeLocalization` to additive
base-scalar compatibility and localization isomorphisms for prescribed coefficient lifts.
The original signatures, public imports and definitions are unchanged.

Added `AffineTensorCohomologyLifts`, which proves the tensor-algebra functor lifts and
comparison linearity. Its private proved helpers construct linear maps by tensor induction,
transport objectwise actions into functors, and verify functor laws and naturality.
It reuses the proved `ModuleCat.tensorAction_of_additiveFunctor`.
The main theorem chooses these lifts globally and locally, then applies the localization
isomorphism statement. All four sandbox modules compile without warnings.

## Proved and sorry left

Closed the remaining item hole:
`RingTensorCohomology.exists_affineDerivedBaseChangeLocalization`.
This is a decomposition, not a sorry-free proof: one item hole closed, two lower holes added
(net -1 among the delivered declarations). This is not a claim about the ledger net in the
whole targets import closure: that census also includes extant holes reached through the
recorded proof-dependency imports. The first theorem was already proved by Q3 in the refreshed baseline and is not
counted as R3 progress. The initially supplied snapshot had both item theorems unproved.

Proved the new `RingTensorCohomology.exists_affineTensorCohomologyLifts`
(node `lem-pc-affine-tensor-cohomology-lifts`), including its map and naturality glue.

Every remaining sorry in the delivery is the whole proof of one of:

- `RingTensorCohomology.affineTensorCohomology_additive_scalar`, node
  `lem-pc-affine-tensor-cohomology-additive-scalar`.
- `RingTensorCohomology.affineTensorCohomology_localization`, node
  `lem-pc-affine-tensor-cohomology-localization-isos`.

No sorry remains in the item's module. No definition contains a sorry. The lower statements
assert separate portions of the argument: functor additivity/base scalars, and localization
compatibility of already supplied global and local lifts. Neither is the original existential
statement under a new name. Edge cases checked in their proof docstrings: zero complexes,
zero rings/empty prime spectrum, identity maps and localization, and unbounded complexes.

## No longer needed

No imports were removed from the item relative to the current Q3 baseline.
Removed unused prime-localization imports from the new scalar and lift modules, and
the unused tensor-product import from the scalar module before delivery. The original brief's
`DerivedChangeOfRings`, `DerivedTensorLocalizationCohomology`, `KFlat`, and `KFlatResolution`
proof imports had already been removed by Q3. Do not count that as R3 pruning.

The item now directly depends on `lem-pc-affine-tensor-cohomology-lifts` and
`lem-pc-affine-tensor-cohomology-localization-isos` for its second theorem; it no longer
uses the old localization nodes directly. They remain needed in the lower localization
node's proof plan: `lem-pc-derived-tensor-localization-cohomology`,
`lem-weil-pbc-localization-tensor-product`, `lem-weil-pbc-localization-module-exact`.
No underlying localization theory or unit route is declared unnecessary.

## Where the brief, the DAG or earlier work was wrong

The source snapshot advanced during this session: Q3's first-theorem proof landed and
became the current baseline. It is preserved verbatim; this delivery addresses localization.
The existing localization theorem uses `BaseDerivedTensorCohomologyModel` and is pointwise
with naturality equations for model morphisms. Its signature does not directly provide the
natural isomorphisms between the specific functor lifts required here. The lower localization
node records the required model and functor transport explicitly.

The functorial flat resolution is not assumed additive. Additivity and scalar compatibility
must be transported from the derived functors to the cohomology functors; these are isolated
as the smaller scalar statement instead of asserting linearity of the resolution itself.

## New nodes

`lem-pc-affine-tensor-cohomology-additive-scalar`: additivity and original-base scalar equations
for source and target; module `Sheaf.Algebra.Homology.AffineTensorCohomologyAdditiveScalar`.

`lem-pc-affine-tensor-cohomology-lifts`: proved tensor-algebra functor lifting and comparison
linearity; module `Sheaf.Algebra.Homology.AffineTensorCohomologyLifts`.

`lem-pc-affine-tensor-cohomology-localization-isos`: natural localization isomorphisms,
comparison square and target identification for supplied lifts; module
`Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationIsos`.

All inherit `sec-picard-framework`, `sk-thm-picard-semicon` from the item. The unit's realized
statement and steps are untouched. No interface change record or forced adaptation is needed.

LeanSearch was attempted for the new nodes and returned Internal Server Error;
LeanFinder, Loogle and source grep were also run, and their actual results are recorded.


## Second reading by R3

1. **Existing interfaces — pass.** Read the full item and compared it with the repository
   using `diff -u`. The only changes are two plain proof imports and the proof body of
   `RingTensorCohomology.exists_affineDerivedBaseChangeLocalization`. Both existing theorem
   signatures are byte for byte unchanged, as are the private helpers, definitions, public
   imports and Q3's first theorem proof. There are no adapted existing modules, target
   changes or interface change records.

2. **Proof and axioms — pass as a decomposition.** Independently compiled all four delivered
   modules through `lcompile.py --all`, without warnings or errors. Read tensor induction
   in `liftMap`, the conjugated maps and functor laws in `exists_functorLift`, and the
   comparison naturality proof. The only two textual sorries are whole named theorems,
   precisely the two reported lower statements. No forbidden declaration, bypass option,
   or sorry in a definition occurs. Scratch copies with `#print axioms` check every
   declaration, including the private helpers. The new private helpers use only standard
   axioms; the lifted comparison and localization assembly additionally use `sorryAx`
   from the reported lower statements. Existential elimination occurs inside theorem
   proofs; no definition chooses arbitrary data from an unproved existence theorem.

3. **Split statements — pass.** Read their complete signatures, proof docstrings and nodes.
   Additivity/scalar compatibility and localization of prescribed lifts are separate,
   strictly smaller parts of the original argument. The actual functor lifting, tensor
   linearity, comparison naturality and existential assembly are proved, so this is not
   the original existential theorem renamed. Checked zero complexes, zero coefficient
   rings (hence empty prime spectrum), identity localizations, and nonflat coefficients:
   for R=integers and A=B=F_2, source has a nonzero degree -1 Tor group while target does
   not; none of the statements asserts the comparison is invertible. Prescribed lifts
   may be changed by natural isomorphisms: their generator equations force the tensor
   action, so conjugating transports the asserted localization square. No boundedness
   is used. Read the existing `tensorAction_of_additiveFunctor`,
   `exists_baseDerivedExtension_linear`, `baseDerivedExtension_scalar`, and
   `derivedTensor_localization_cohomology`: the last uses cohomology model records and
   objectwise naturality equations, rather than these specific functor lifts. Repeated
   LeanFinder searches with “cohomology functor computed by K flat resolution” and
   “localizing cohomology ... both factors”, Loogle with `Functor.Additive, Iso`, and
   local source searches for additive transport, scalar maps and resolution functors.
   Found generic additive/linear transport and ordinary localization lemmas, no exact
   replacement. Results are in `searches.jsonl`. The referenced local Stacks tex files
   are not present on this machine; read the official pages instead:
   https://stacks.math.columbia.edu/tag/0DJ8 and
   https://stacks.math.columbia.edu/tag/06Y6.

4. **Route and pruning — pass.** The top-level reduction starts with the proved generic
   coefficient-action construction and then applies localization to the chosen lifts.
   There is no evident short exact-library replacement for either remaining transport
   theorem; closing them needs the derived-model identification and naturality glue,
   not an immediate `simp` or an existing theorem application. Public imports are used
   by signatures; new proof-only imports are plain imports. All three old localization
   proof dependencies removed from the item's direct dependency list are enumerated
   under No longer needed and retained in the lower localization plan. No pruning credit
   is claimed. Read `dag/units/sk-thm-picard-semicon.json`; its realized fields and its
   statement and step remain untouched, and the affine localization route is retained.

5. **DAG agreement — pass after repair.** Compared the existing item's JSON with the
   repository: only `proof`, `proof_deps`, and `proof_origin` differ. Checked every new
   node's source, chapter, unit, blueprint provenance, created record, search records,
   module and declaration; mechanically compared all three new Lean signatures with
   the node signatures modulo whitespace and checked dependency unions. The proved
   lifting node records the additive scalar and objectwise tensor-action dependencies,
   while the two holed nodes retain their mathematical proof plans. Made the new
   localization node's prose statement self-contained by spelling out the contracted
   primes, localization models, compatible maps and prescribed-lift equations rather
   than referring readers to the Lean signature.

**Second-reading changes.** Added plain proof-dependency imports to the two split modules:
`BaseDerivedExtensionLinear`, `BaseTensorOrdinaryIso`,
`DerivedTensorLocalizationCohomology`, `Mathlib.RingTheory.Localization.BaseChange`, and
`Mathlib.Algebra.Module.LocalizedModule.Exact`. Expanded the localization docstring and
its node proof to explain why f is a localization (hence exact) and why the localized
resolution and the local functorial resolution give naturally identical cohomology.
Clarified the report's net count as a declaration-level decomposition count. No Lean
signature or proof body was changed in this second reading, and no additional hole was
closed or added.
