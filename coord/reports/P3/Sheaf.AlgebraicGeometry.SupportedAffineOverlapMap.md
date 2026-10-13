## What changed

Completed `AlgebraicGeometry.Scheme.exists_supported_affine_overlap_map` without changing
its statement. Constructed the affine source by supported extension, applied the existing
affine perfect map-lifting theorem through a compact-open restriction comparison, and
proved the final compatibility equation by naturality and inverse identities.

Added four modules, each with its DAG node:

- `LocalPerfectSupportedStabilization`: explicit transport of strictly perfect local models,
  homology/stalk support comparison, and stabilization using the split biproduct triangle
  and the existing perfect two-out-of-three theorem.
- `CompactOverlapRestrictionModel`: proved the compact-open restriction comparison by the
  open-range scheme isomorphism and exact derived equivalence, preserving Hom universe w.
- `SupportedOverlapRestrictionData`: the remaining named gap, concerning only restriction
  of a supported perfect object to a compact-open model of the overlap.
- `SupportedOverlapPerfectExtension`: proved from that restriction data and the existing
  supported affine extension theorem; its resulting source and comparison are used by the item.

Repair of the returned delivery: removed the three duplicate private declarations
`perfect_shift`, `restrict_model`, and `restrict_strictlyPerfect` from
`LocalPerfectSupportedStabilization`. The unchanged call sites now use the existing
private theorems through proof-only `import all` of `PerfectTwoOutOfThree` and
`PerfectCommonAffineModels`; their visibility in the library is unchanged. Added the
common-models dependency to the local stabilization node.

The private categorical helper `map_lift_transport` proves the conjugation/naturality
calculation independently of the scheme-specific derived functors. Updated the item's
proof plan and dependencies to match the Lean. No existing statement, definition,
visibility, or target signature changed; no forced adaptations or change records are needed.

## Proved and sorry left

Closed the item's single direct hole:
`AlgebraicGeometry.Scheme.exists_supported_affine_overlap_map`
(node `lem-sc-supported-affine-overlap-map`).

Also proved the new declarations:

- `AlgebraicGeometry.Scheme.local_perfect_supported_stabilization`
  (`lem-sc-local-perfect-supported-stabilization`).
- `AlgebraicGeometry.Scheme.exists_compact_overlap_restriction_model`
  (`lem-sc-compact-overlap-restriction-model`).
- `AlgebraicGeometry.Scheme.exists_supported_overlap_perfect_extension`
  (`lem-sc-supported-overlap-perfect-extension`).

One new direct hole remains, with its entire proof `:= by sorry`:
`AlgebraicGeometry.Scheme.exists_supported_overlap_restriction_data`
(`lem-sc-supported-overlap-restriction-data`). It constructs only a supported perfect
restriction and its comparison data; it asserts neither an affine extension nor a lifted
map. The affine extension and map lifting are actual applications of the existing theorems.
This is a decomposition: one upper hole closed and one lower hole added, not an axiom-free
proof. No new use of the still-holed perfect thick-closure theorem is needed: shift
perfectness uses the already-proved private `perfect_shift` from `PerfectTwoOutOfThree`,
and stabilization uses the already-proved
`isPerfect_two_out_of_three`.

The remaining restriction statement was checked against empty W, empty V, empty overlap,
T empty, T all of X, and zero F. It needs only quasi-separatedness for the two compact-open
intersections, and no uniform bound or global quasi-compactness of X. The chosen derived
localizations retain the same Hom universe w. Existential choices occur inside theorem
proofs; no definition chooses arbitrary data from an unproved existence theorem.

## No longer needed

Removed the three duplicate local helper proofs `perfect_shift`, `restrict_model`,
and `restrict_strictlyPerfect`; their existing declarations are reused instead.
`PerfectCommonAffineModels` remains needed for the two restriction helpers.

Removed the direct proof import `Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction`
from the item's module. The compact-open comparison constructs the needed localization
using the exact equivalence and local-smallness, without deriving an adjunction. The node
`lem-pc-open-derived-localization-adjunction` is not needed for that construction.

Moved the direct import `Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension` from the
item to `SupportedOverlapPerfectExtension`, where its theorem is applied. That module and
node `lem-sc-affine-perfect-support-extension` remain needed; this is not global pruning.
The explored route through `PerfectThickClosure`, `PerfectSummand`, `PseudoCoherentSummand`
and `RingPseudoCoherentSummand` is unnecessary: shifted models and the split triangle suffice.
Those imports were not in the baseline, so this avoids extra dependencies rather than
claiming that baseline modules have become unreachable. The original perfect-complex definition remains needed by the statement and the local
stabilization helper; the other original proof dependencies remain used. No blueprint unit statement or step
is bypassed, and no other global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated three existing private lemmas. Their statements are
identical, including the explicit binders. Lean module-system `import all` makes the
existing private proofs available in proof bodies, so no duplicate or visibility change
is necessary. The repair removes all three duplicates rather than renaming them.

The previous sandbox attempt contained no proof or report, only the original direct hole.
The source plan is mathematically sound but omitted Lean interfaces for relative overlap
restriction, its compact-open model, and supported local-model transport. Those interfaces
are now explicit, and all except supported overlap restriction data are proved.

Read Stacks Tags 09IM, 08EK, 08EH and 08CM. Searches through the library and Mathlib found
restriction comparisons and exact-equivalence ingredients but no complete relative
supported overlap theorem. LeanSearch returned Internal Server Error; Loogle, LeanFinder
and local grep ran successfully, with their actual queries logged. Validation uses single-file
compilation of all delivered modules, axiom probes and the delivery preflight. Blueprint searches for
supported perfect objects, restriction, and perfect complexes found no exact replacement.
The unit record `sk-thm-picard-duality` has no realized step at this node, and its route stays
unchanged. No mathematical source error or disputed statement was found.

## New nodes

`lem-sc-local-perfect-supported-stabilization`: proved local restriction and stabilization,
including support, for any subset T and without compactness assumptions.

`lem-sc-compact-overlap-restriction-model`: proved a compact-open model and natural comparison
for overlap restriction, with no assertion about perfect complexes or lifting morphisms.

`lem-sc-supported-overlap-restriction-data`: the one remaining hole; gives only a supported
perfect object on the compact-open overlap model, with coherent restriction comparisons
and the required chosen open-site localizations.

`lem-sc-supported-overlap-perfect-extension`: proved from the preceding restriction data
and supported affine extension. It asserts only the affine supported source and its
stabilized overlap isomorphism, leaving the map lift to the item's complete Lean proof.


## Earlier second reading (a previous round; superseded)

1. Compared every delivered module with the repository. Only SupportedAffineOverlapMap
   already exists. Its theorem signature is byte-for-byte identical after restoring one
   extra space before the proof delimiter; its original docstring and public imports are
   unchanged. The other four modules are new. No existing definition or target changed,
   and there are no forced adaptations or required change records. Verdict: pass.

2. Compiled all five modules with lcompile.py in import order, without errors or warnings.
   A scratch import probe printed the axioms of all five public theorems. The compact
   overlap comparison uses only propext, Classical.choice and Quot.sound. The other four
   also use sorryAx through open dependencies, including the one reported new hole.
   Scanned every delivered Lean file: the only direct sorry is the entire named theorem
   exists_supported_overlap_restriction_data; there are no forbidden declarations or
   hollow definitions. Existential witnesses are eliminated inside theorem proofs only.
   Verdict: valid decomposition, not a completed axiom-free proof of the original item.

3. Read every new signature and its proof or full proof docstring. The remaining hole is
   a restriction statement, asserting neither an extension to V nor a lifted morphism.
   On empty W or V it uses the empty overlap; for T empty it restricts zero stalks; for
   T all of X the support condition is vacuous; zero F restricts to zero. Compactness of
   the pulled-back complement follows from quasi-separated intersection of the compact
   open complement of T with affine V. The localized-site structures on U are obtained
   from the supplied family on V by open-image equivalences, retaining Hom universe w.
   No arbitrary witness is used to define data. Independently searched LeanFinder for
   open-immersion pullback of perfect complexes with stalk support, Loogle for
   Modules.restrictStalkNatIso, and Mathlib grep for stalk, exact-homology and localization
   transport APIs; searched both library roots for perfect open restriction. The private
   perfect_exactOpenRestriction helper in PerfectRestrictionClassesSmall is related but
   supplies neither support nor the required overlap/localization comparisons. No complete
   replacement for the split-off restriction-data statement was found. Verdict: true,
   necessary and strictly smaller than the item; not a restatement.

4. Read the full top-down reduction, including map_lift_transport. It really applies the
   existing supported affine extension and affine map-lifting theorems; naturality then
   proves the compatibility equation. The private shift proof avoids importing the
   holed thick-closure theorem. Proof-only imports are plain imports. Checked the old
   proof_deps against the new route: affine support extension moved to the extension
   helper, perfect-complex definitions remain needed, and the other original dependencies
   remain used. OpenDerivedLocalizationAdjunction is removed directly, without a claim
   of global unreachability. The unit's realized statement and step lists are empty and
   unchanged. No shorter complete route was found. Verdict: pass; no global pruning.

5. Checked all five node signatures against Lean (normalizing whitespace for stored
   one-line signatures), the new-node metadata and search fields, the dependency unions,
   and the proof steps against the actual theorem applications. Only proof, proof_deps
   and proof_origin change on the existing node. Found a wrong citation on the new compact
   overlap node: Stacks Tag 08BV states a Mayer-Vietoris triangle, not its claimed exact
   restriction comparison. Corrected its module and node to cite the overlap setup in
   Tag 09IM, and marked its explicit Mathlib categorical implementation as agent-written.
   Checked Tags 09IM and 08EK directly: they contain the supported affine extension and
   map-lifting route used here. Verdict: pass after this citation repair.

Second-reading changes: restored exact signature whitespace; corrected the compact-overlap
source and proof attribution; clarified the surviving original dependency in the pruning
report. No proof or statement needed mathematical repair. The direct-hole balance remains
one original hole closed and one smaller hole added, hence net zero (a decomposition).


## Second reading by P3

1. Compared the existing SupportedAffineOverlapMap module with the repository using
   diff, and separately compared the theorem signature through the proof delimiter
   byte for byte: identical. Its docstring and public imports are unchanged. The four
   helper modules are new; no existing definition, visibility or target was altered.
   Only proof, proof_deps and proof_origin differ on the existing node. No change
   record or forced adaptation is required. Verdict: pass.

2. Compiled all five delivered modules in import order using lcompile.py --all;
   every module compiled without errors or warnings, within the single-file limit.
   A scratch copy of the main module, using the sandbox overlay, printed axioms for
   all five public theorems. The compact-overlap theorem uses only propext,
   Classical.choice and Quot.sound; the other four additionally use sorryAx through
   the reported restriction-data hole or upstream open statements. Scanned every
   delivered file: precisely one direct sorry, the complete named theorem
   exists_supported_overlap_restriction_data; no forbidden declarations and no
   holed definitions. All existential witnesses are eliminated within theorem proofs.
   Verdict: sound reduction with an open dependency, not an axiom-free completed item.

3. Read each new signature, proof and proof docstring against its node. Read Stacks
   [09IM](https://stacks.math.columbia.edu/tag/09IM),
   [08EK](https://stacks.math.columbia.edu/tag/08EK), and
   [08CM](https://stacks.math.columbia.edu/tag/08CM).
   The residual theorem restricts a supported perfect object; it supplies neither
   an extension over V nor a lifted map. Its compactness claims use quasi-separated
   intersections of compact opens: W with affine V, and the open complement of T
   with affine V. No global quasi-compactness or uniform bound on X is used.
   Transporting the supplied localized-site categories via open-image equivalences
   retains Hom universe w. Empty W, empty V and empty overlap give the same empty-open
   restrictions; T empty gives zero homology stalks everywhere, T equal to X makes
   support vacuous, and zero F uses zero restrictions. These cases do not require a
   nonempty point. Independently searched LeanFinder for derived open pullback of
   perfect objects with vanishing stalks, Loogle for Modules.restrictUnitIso, and
   Mathlib grep for restrictStalkNatIso, mapDerivedCategoryHomologyFunctorIso and
   hasLocalizationOfLocallySmall. Also searched both library roots for perfect
   restriction and read PerfectRestrictionClassesSmall, OpenPerfectModelTransport,
   and SchemeIsoDerivedLocalizations. Their results are ingredients, not the complete
   supported restriction and stabilized comparison statement. Finishing the remaining
   hole requires these comparisons and local model transport; no few-minute complete
   proof was found. Verdict: true, needed and strictly smaller than the original item.

4. Read the top-down argument and map_lift_transport in full. The extension helper
   really applies exists_perfect_supported_extension; the main proof really applies
   exists_perfect_map_lift_of_isAffine. The naturality calculation transports its
   equation and cancels q and kV with their inverses. Support uses the lifting
   theorem's clause for the closed inverse image of T. Read the existing private
   restrict_model, restrict_strictlyPerfect and perfect_shift proofs: the two import
   all directives reuse them without changing visibility or duplicating statements.
   Every added import is proof-only unless its declarations occur in a signature.
   Against the old proof_deps, def-pc-perfect-complex remains a statement dependency
   and is used in local stabilization; lem-sc-affine-perfect-support-extension is
   used by the extension helper rather than directly; the QCoh restriction and map
   lift dependencies are applied directly. OpenDerivedLocalizationAdjunction is the
   removed direct import, with no claim of global pruning. Read the unit record:
   its realized statement and step lists are empty and unchanged. The local overlap
   stage follows the affine extension and lifting paragraph of 09IM. Verdict: pass;
   no shorter complete route or globally pruned module established.

5. Checked all five stored Lean signatures against their files after whitespace
   normalization, and checked each proof_deps equals the union of the proof steps'
   uses. Checked new-node source, creation, search, blueprint, chapter, unit and Lean
   records. The local stabilization node now records PerfectCommonAffineModels and
   PerfectTwoOutOfThree, matching the reused private proofs. The compact-overlap node
   accurately attributes its explicit Mathlib implementation to the agent and its
   setup to 09IM. The remaining node has its complete natural-language restriction
   argument in the theorem docstring. Verdict: pass.

Second-reading changes in this round: appended this independent review and recorded
fresh searches and compilation/axiom verification. No Lean proof, statement, node or
import needed further repair. One original hole closed and one lower hole added:
net zero direct holes, a decomposition. No global pruning is claimed.
