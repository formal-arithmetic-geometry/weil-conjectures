## What changed
Split the Tag 09XN argument into existence (`EtaleSectionsFpqcExistence`) and separatedness (`EtaleSectionsFpqcSeparated`). The original unique-existence theorem now combines those statements in Lean, without changing its signature. Both new modules and the target compile together. The second reading removed the unused section-description/open-descent imports from separatedness, replaced its public composition-unit import by the minimal public `EtaleSheaves` import, and added its proof-only identity-restriction import. The existence statement keeps the full overlap compatibility hypothesis; separatedness needs only equality of global-section pullbacks.

## Proved and sorry left
Closed the hole in `AlgebraicGeometry.existsUnique_etaleSection_of_fpqc_cover` (node `lem-weil-pbc-etale-sections-fpqc-descent`) by decomposition, not an unconditional proof.
Added two holes: `AlgebraicGeometry.exists_etaleSection_of_fpqc_cover` (node `lem-weil-pbc-etale-sections-fpqc-existence`) and `AlgebraicGeometry.etaleSections_eq_of_fpqc_pullbacks` (node `lem-weil-pbc-etale-sections-fpqc-separated`). No other holes are left in the delivered files. Net holes: one closed, two added.

## No longer needed
Removed direct proof imports `Sheaf.AlgebraicGeometry.EtaleInverseImageSectionDescription`, `Sheaf.AlgebraicGeometry.EtaleOpenFpqcDescent`, and `Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpen` from the target. Their nodes remain needed by the intermediate proofs; no underlying nodes or modules are globally pruned. All six old direct proof dependencies are now mediated through the intermediates: `lem-weil-pbc-etale-sections-equal-open`, `lem-weil-pbc-sets-etale-inverse-image-composition-units`, `lem-weil-pbc-etale-open-fpqc-descent`, `lem-weil-pbc-etale-inverse-image-section-description`, `def-weil-pbc-fpqc-covering`, and `def-weil-pbc-etale-sheaf-of-sets`. Composition units remain a statement dependency and public import of the target. The second reading also removed `EtaleInverseImageSectionDescription` and `EtaleOpenFpqcDescent` from separatedness; their nodes were never dependencies of that intermediate. Existence uses the original planned agreement-open, open-descent, local-representative and sheaf-gluing route; separatedness uses agreement-open and joint surjectivity.

## Where the brief, the DAG or earlier work was wrong
No mathematical error in the original statement or route was found. Search found no existing fpqc section-descent theorem. Attempted direct uniqueness proof encountered explicit identity-pullback transport bookkeeping; it is included in the complete natural-language proof of the separatedness intermediate. The original target statement and public visibility remain unchanged.

## New nodes
`lem-weil-pbc-etale-sections-fpqc-existence` states only existence for compatible sections. Its proof follows steps 1–3 and the existence part of step 4 of Tag 09XN.

`lem-weil-pbc-etale-sections-fpqc-separated` states equality of two global sections whose fpqc pullbacks agree. It has no local-section existence or overlap-compatibility hypothesis. Its proof is the final uniqueness paragraph of Tag 09XN, with identity restriction justified by Tag 03S2. Both statements are true also for the empty base; an empty family covering a nonempty base is excluded by joint surjectivity. No arbitrary object is chosen from either unproved existence theorem in a definition.

## Second reading by J2

1. Interface preservation: read the repository/sandbox diff of the original module.
   The only differences are private proof imports and the proof body. Independently
   compared the full existing theorem signature byte for byte: identical. Public
   imports, universe levels, fpqc cover hypothesis, sheaf category, compatibility
   transports, and unique-existence conclusion are unchanged. No definition changes
   or change records are necessary. The two added declarations have their own modules.
2. Kernel/proof check: compiled all three modules together with lcompile.py, cleanly.
   A scratch copy printed axioms of all three declarations: only propext,
   Classical.choice, Quot.sound, and sorryAx. The only delivered sorries are the two
   named intermediates listed above, each exactly `by sorry`. No definitions or
   forbidden declarations were added. The target obtains an existing section and
   proves uniqueness by comparing its pullbacks with those of a candidate; it chooses
   no data in a definition. This is a decomposition (net minus one), not a complete proof.
3. New statements: read Stacks Tag 09XN online at
   https://stacks.math.columbia.edu/tag/09XN (the literature checkout is absent locally),
   the agreement-open declaration, local-representative declaration, open-descent
   declaration, and identity-restriction declaration. Existence retains every covering
   and overlap hypothesis and drops only uniqueness; separatedness compares arbitrary
   global sections without any supplied local family. Each is a strict part of the
   argument, neither restates unique existence. Checked the empty base (the empty-site
   sheaf axiom gives one global section), empty family (joint surjectivity forces the
   base empty), singleton identity cover, and singleton general fpqc cover. No reduced,
   connected, or nonempty assumption is hidden. Independent LeanFinder search used
   “injectivity of global sections under jointly surjective scheme pullback etale
   sheaves”; results concern structure sheaves or scheme-point injectivity, not this
   statement. Loogle `Sheaf, Function.Injective` did not resolve Sheaf; direct grep
   `fpqc.*(section|sheaf)|etale.*(separated|descent)` and repository/upstream searches
   found no replacement. Mathlib's continuous-map constant-sheaf theorem is a special
   sheaf, not arbitrary F. A second existence search used “compatible sections of
   inverse image sheaves on small etale sites glue over faithfully flat covers”;
   Zariski scheme gluing and TopCat open-cover gluing results do not apply to this
   small-etale inverse-image family. Expanded new node statements to specify all objects,
   hypotheses and pullback maps. Both docstrings give the complete source argument.
4. Route/pruning: inspected dag/units/sk-thm-iff.json realized statement and step,
   both carried by lemma-weil-pbc-property-iff-acyclicity. This helper decomposition
   changes neither realization nor the underived-comparison route. Existence retains
   agreement opens, fpqc open descent, etale local representatives and sheaf gluing.
   Separatedness retains agreement opens and joint surjectivity, with Tag 03S2 for
   identity restriction. All old direct proof dependencies are accounted for above;
   none is globally pruned. Removed unrelated imports from separatedness and retained
   proof-only imports privately. A bounded attempt to close separatedness reached
   dependent transport involving HasPullbacksAlong for a composite versus a morphism;
   restored the named theorem to `by sorry`, leaving no partial proof.
5. DAG/Lean agreement: target proof uses precisely the existence and separatedness
   declarations recorded by its proof steps/dependencies. Checked each intermediate's
   Lean record against its signature and its source proof against the imported
   declarations. New nodes have chapter/unit, creation data, source, three original
   search kinds, proof-origin and blueprint ancestry via the original item. Added
   missing ancestry `via` and lean_audit records; expanded their formerly terse
   natural-language statements. The separatedness planned identity-restriction
   dependency is now actually imported. No source statement is changed.

Changes on second reading: corrected separatedness imports, added module blueprint
references and more precise source places, expanded new node statements and completed
new-node ancestry/audit metadata, and made pruning and net-hole reporting explicit.
