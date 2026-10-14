## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationRootNotSquare`
by a complete Lean proof from two separate remaining geometric/arithmetic statements.
The original declaration, every binder, universe, conclusion, visibility and docstring stay intact.
Added three proof imports for the new modules and a Mathlib local-ring import.

The proof establishes regularity of the structural root image independently of ramification:
the inverted function g is regular on normalization, and the proved relation t^|G|=g
then makes t regular. A DVR comparison identifies the actual stalk with a localized
root model; a separate DVR Abhyankar calculation supplies its maximal-ideal equality.
The proof transports that equality through the root-compatible ring equivalence and
cancels a hypothetical equation tau*z=tau with z in the maximal ideal. Properness of
the actual maximal ideal supplies the contradiction.

New `NormalizationStalkRegularBasicOpen` is completely proved from Mathlib:
`ker_toNormalization` gives injectivity on sections, stalkwise invertibility on the source
gives a unit section, and prime localization preserves the resulting nonzerodivisor.
Its proof works without reducedness, Noetherianity, torsors or a root construction.
`RootNormalizationDvrComparison` isolates localization and chart/pullback compatibility;
it asserts no normalized maximal-ideal or nonmembership property.
`DvrRootNormalizationMaximalIdeal` isolates the DVR ramification calculation for a
G-torsor over the fraction field; it contains no arbitrary H or ambient chart.
Model witnesses are eliminated inside the theorem proof; no definition chooses data
from an unproved existence theorem.

All four delivered modules compile together through lcompile.py, without warnings.
After second-reader cleanup the item compiled in 37.9 seconds in the dependency-order check,
within the unchanged 60-second limit. Dependent model witnesses are unpacked in stages, registering the domain,
DVR and qcqs instances before their dependent types are used. Two private, fully proved
helpers perform proper-ideal cancellation and ring-equivalence ideal transport.
No existing dependent module or library definition is changed.

## Proved and sorry left

Item hole closed (1 of 1):
`AlgebraicGeometry.Scheme.root_normalization_root_not_square`
(node `lem-sbc-root-normalization-root-not-square`). No sorry remains in the item's module.

Additional completely proved declaration:
`AlgebraicGeometry.Scheme.normalization_stalk_regular_basicOpen`
(node `lem-sbc-normalization-stalk-regular-basic-open`). Both private item helpers are proved.

New holes, each exactly the whole proof of its named public theorem:

- `AlgebraicGeometry.Scheme.root_normalization_dvr_comparison`
  (`lem-sbc-root-normalization-dvr-comparison`), in its own new module.
- `AlgebraicGeometry.Scheme.dvr_root_normalization_maximalIdeal`
  (`lem-sbc-dvr-root-normalization-maximal-ideal`), in its own new module.

This is a decomposition, not a sorry-free proof of the original mathematical assertion.
It closes one upper hole and adds two strictly separate lower holes (net -1 if both
new modules are counted in the targets' import closure). Each new hole has a source,
complete natural-language proof and matching DAG node. No target is claimed axiom-clean
until those two statements are proved. There are no other new or surviving delivery holes.

## No longer needed

No existing library import, node or module is pruned. The item's original public imports
are retained. The old planned dependencies `lem-sbc-normalization-stalk-base-change`
and `lem-exc-etale-field-galois-classification` remain needed within the comparison and
DVR-calculation plans, respectively; they have not been silently dropped or bypassed.
The item's direct proof_deps now name the three new declarations actually used.
The old two dependencies are no longer direct dependencies of the item: each is retained
as a proof import and planned dependency of its respective new lower statement.
Removed redundant imports from new modules only: `Mathlib.AlgebraicGeometry.OpenImmersion`
from `NormalizationStalkRegularBasicOpen`, and `Mathlib.RingTheory.RegularLocalRing.Defs`
from `RootNormalizationDvrComparison`. Neither removal prunes an existing library module.

No longer needed locally: the rejected generator theorem, false arbitrary-ideal helper,
and rejected node copies under scratchpad/rejected. They were never library dependencies
and are not counted as pruning.

The node's unit is unchanged, and its realized statement/step lists are empty. The proof
continues through the original localization, tame root-base-change and index-one route.

## Where the brief, the DAG or earlier work was wrong

The earlier arbitrary-ideal helper was false for m=top and tau=1. The new cancellation
helper explicitly requires properness and is fully proved; the actual maximal ideal is
proper by its IsMaximal instance. The earlier generator helper bundled the entire
geometric assertion into one stronger assumption. This delivery separates the substantive
DVR localization comparison from the arithmetic calculation and proves regularity directly.
Neither new holed statement asserts the original square-nonmembership conclusion.

The original two proof dependencies alone do not state Abhyankar's index-one calculation
or the explicit root-compatible chart/localization comparison. They provide parts of
those arguments. The two new interfaces state those missing groups of proof steps with
complete hypotheses. In particular, the DVR lemma retains a genuine G-torsor over its
fraction field: an arbitrary unrelated group would not control ramification degrees.
Existing generic-unramifiedness/maximal-ideal declarations that import this item cannot
be used, because that would create a cycle.

The original regular-base-stalk hypothesis stays in the item signature. The new comparison
needs only the Noetherian principal-prime localization with regular g and domain H/(g),
which already gives the required DVR; it does not require that extra stalk hypothesis.
For n=1 the root ring is the base ring and the same argument applies. Disconnected torsors
are handled factor by factor in the arithmetic proof. Empty normalization has no x.
The new regularity theorem also covers nonreduced bases and zero/unit functions: the
zero basic open has empty source and normalization, while the unit case is immediate.

The Mathlib searches were run through msearch.py and are recorded from searches.jsonl.
LeanSearch returned HTTP 500 and is marked unavailable, not treated as a negative match.
Loogle/LeanFinder and source searches found useful general APIs but no exact DVR root
Abhyankar statement. Stacks Tags 09EV, 09EB, 0BRM, 09E7 and 0307 were read online.
No server details, keys, or tokens are recorded in delivery files.

## New nodes

`lem-sbc-normalization-stalk-regular-basic-open`, module
`Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkRegularBasicOpen`, is a proved general
regularity statement for a function inverted on a qcqs source over an affine base.

`lem-sbc-root-normalization-dvr-comparison`, module
`Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationDvrComparison`, is the remaining
localization comparison. Its prescribed construction is B=H_(g), pi the image of g,
and T the original torsor pulled back to Spec Frac(B). It supplies a root-compatible
ring equivalence and transfers finiteness, but no ramification conclusion.

`lem-sbc-dvr-root-normalization-maximal-ideal`, module
`Sheaf.AlgebraicGeometry.Morphisms.DvrRootNormalizationMaximalIdeal`, is the remaining
index-one statement over a DVR. The proof uses the root DVR calculation 09EV, the
Galois degree formula 09EB, and Abhyankar 0BRM followed by 09E7 and normalization locality.
It is independent of the ambient chart and the geometric localization comparison.

All nodes inherit sec-smooth-base-change and sk-prop-input-spreading from the item.
The existing item's proof, proof_deps and proof_origin follow the actual Lean reduction.
No change records are needed: no existing statement or definition changes.

## Second reading by R4

1. **Interfaces: PASS.** Compared the existing module with the repository by diff and
   an exact text check. Its theorem signature and original docstring are byte-for-byte
   identical; all original public imports remain. Its only additions are proof imports,
   two proved private helpers, and the proof body. No existing definition or statement
   is changed; no change record is required. The other three modules and their nodes
   are new, with no matching declaration in the repository.

2. **Proof and trust: PASS as a decomposition.** Compiled all four modules in dependency
   order through lcompile.py after cleanup: no errors or warnings. There are exactly two
   sorry tokens, the whole proofs of the two reported public lower theorems. No definition
   contains a hole; no forbidden declaration or trust mechanism is present. The model
   witnesses are eliminated inside a proof, never used to define arbitrary chosen data.
   A scratch copy checks axioms of the item, both lower statements, the regularity lemma,
   and both private helpers; the exact results are recorded below. One upper hole is
   closed and two lower holes are added, so this is a decomposition with net -1, not an
   axiom-clean proof or positive hole-count progress.

3. **Split statements: PASS.** Read both statements and their complete docstring proofs
   against Stacks 09EV, 09EB, 0BRM, 09E7 and 0307. Comparison constructs H_(g) and
   preserves the actual root germ; the arithmetic statement concerns only a DVR model
   and index one. Neither restates square-nonmembership. Checked positive group order,
   n=1, disconnected torsors, and empty normalization. A regular principal prime in a
   Noetherian ring localizes to a DVR, without assuming H itself is a domain. The torsor
   action makes each field factor Galois with degree dividing |G|; invertibility removes
   inseparable residue degree and wild ramification. A proper maximal ideal is essential
   to the proved cancellation helper and is supplied explicitly. Repeated LeanFinder,
   Loogle and grep searches with different queries for tame-root ramification, localization
   stalk equivalences and regularity. Results include Irreducible.maximalIdeal_eq,
   IsLocalization.localizationLocalizationAtPrimeIsoLocalization and
   Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, but none closes either geometric hole.
   The similar library generic-stalk results import this item transitively and cannot be
   used without a cycle. Neither lower hole can be closed in a short local repair.

4. **Route and pruning: PASS after cleanup.** The item proves regularity by the
   normalization injection and t^n=g, transports the DVR maximal-ideal equality, then
   cancels in a proper ideal. It retains the localization, tame-root and index-one route.
   Read sk-prop-input-spreading and its realized record; these support lemmas change no
   unit statement or step. No old library module is pruned. The two original proof_deps
   have moved to the respective lower plans, both now imported there. Removed only two
   redundant imports from the newly created modules, listed above.

5. **Node agreement: PASS after cleanup.** Checked each node's proof_deps equals the
   union of its proof-step uses, each Lean attachment names the delivered declaration,
   and all new-node required source, search, origin, creation, blueprint, chapter and
   unit fields are present. Replaced the new nodes' whitespace-collapsed lean.statement
   fields by the verbatim multiline signatures. The existing node changes only its
   proof, proof_deps and proof_origin; its statement and other contract fields stay.

Second-reader changes: removed the two redundant imports; added ordinary proof imports
NormalizationStalkBaseChange and EtaleFieldGaloisClassification to the two remaining
holed modules so their imports match their plans; made all three new Lean signatures
verbatim in node metadata; clarified direct-dependency pruning and decomposition counts
in this report. The mathematical statements and working proofs were not rewritten.

Axiom check (scratch copy through lcompile.py, 42.6 s):

- normalization_stalk_regular_basicOpen and both private helpers: only propext,
  Classical.choice and Quot.sound.
- root_normalization_root_not_square, root_normalization_dvr_comparison and
  dvr_root_normalization_maximalIdeal: those same three plus sorryAx.

No other axiom appears. The item remains conditional on exactly the two reported
lower holes; this delivery makes no axiom-clean claim for it.
