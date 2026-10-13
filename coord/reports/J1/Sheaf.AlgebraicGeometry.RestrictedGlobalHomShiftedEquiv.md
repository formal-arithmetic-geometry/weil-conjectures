## What changed

Replaced the sole sorry in `AlgebraicGeometry.restrictedGlobalHom_shiftedHom_equiv`
by a compiling composition of three additive equivalences. Scalar restriction and its
cohomology naturality are proved privately from the proved
`Functor.mapDerivedCategoryHomologyFunctorIso`. The two integer shifts and underlying
global-section-group comparison are isolated in one new module. The final identification
with derived morphisms uses the existing `CategoryTheory.rhom_global_sections` on the opens
site of X. Naturality is proved by congruence and equality transitivity.
The original public signature, universes, and public import are unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.restrictedGlobalHom_shiftedHom_equiv`, node
`lem-sc-restricted-global-hom-shifted-equiv` (1 of 1 original holes).
There are no sorries left in the item's module. Both private scalar-restriction helpers
are fully proved.

Added: `AlgebraicGeometry.schemeGlobalHom_shiftedHypercohomology_equiv`, node
`lem-sc-global-hom-shifted-hypercohomology` (one sorry in its own new module).
This is a decomposition, not a net reduction in holes: one closed and one added.
The proof also uses the pre-existing declaration `CategoryTheory.rhom_global_sections`,
node `lem-pur-rhom-global-sections`, whose current source now has a complete proof. The new comparison stops at site hypercohomology:
it asserts neither an identification with derived morphisms nor scalar restriction,
so it is a strict part of the original argument.

## No longer needed

No imports removed. No existing nodes or modules pruned. The existing global Hom adjunction
module is required publicly for `schemeGlobalScalarRestriction`.
The original dependency `lem-pur-rhom-global-sections` is used, not bypassed.
No K-injective-to-derived-morphism theory needs to be duplicated in the new comparison:
that step remains the existing rhom_global_sections theorem.

## Where the brief, the DAG or earlier work was wrong

The first DAG step cannot be instantiated from rhom_global_sections alone: that declaration
only treats H^0 with sheaf-valued RHom, while the item uses H^(n-m) of module-valued RΓ.
The new node states this missing comparison. Scalar restriction does reduce to the existing
exact-functor homology natural isomorphism. The sources were read at
https://stacks.math.columbia.edu/tag/08JA and https://stacks.math.columbia.edu/tag/0B6A;
the referenced .tex files are absent from this checkout.

Edge checks: m=n gives degree zero after simultaneous shifts; m=n=0 compares global-section
definitions; negative degrees use the same signed reindexing; zero P or Q gives zero groups;
the empty scheme has only zero modules. No boundedness, quasi-coherence, flatness, or
perfection is introduced. The unit's realized arrays contain no node to bypass, and the
existing rhom dependency remains. The new bridge reindexes degree k with factor (-1)^(m*k).

Mathlib searches used LeanFinder, Loogle and grep; LeanSearch returned Internal Server Error.
HomComplex.CohomologyClass.homAddEquiv concerns abstract complex Hom groups and does not
supply the comparison between the two global-sections constructions.

## New nodes

`lem-sc-global-hom-shifted-hypercohomology` is in
`dag/nodes/sec-picard-framework/lem-sc-global-hom-shifted-hypercohomology.json`, with its
statement in `lean/Sheaf/AlgebraicGeometry/GlobalHomShiftedHypercohomology.lean`.
The docstring describes K-flat/K-injective representatives, signed shift reindexing,
evaluation at 1, and naturality before the independent derived-morphism identification.
The parent node records the three-equivalence composition and its naturality proof.
No statement or definition changed; no change record or forced adaptation is necessary.

Retry repair (2026-10-13): the authoritative baseline now contains the original item
and node. Restored the parent node metadata from that baseline, retaining only the
new proof route. Restored the original `open` command and qualified
`_root_.Opens.grothendieckTopology` in the proof, removing the interface
change detected by preflight. The second reading below records the earlier baseline
and remains preserved as historical review evidence.

## Earlier second reading (a previous round; superseded)

1. Interface check: BLOCKED against the actual repository baseline. Neither
   `lean/Sheaf/AlgebraicGeometry/RestrictedGlobalHomShiftedEquiv.lean` nor
   `dag/nodes/sec-picard-framework/lem-sc-restricted-global-hom-shifted-equiv.json`
   exists in the group clone, including after deliver3.py fetched origin/sheaf-dag.
   The original module is preserved in the review log for V1 delivery cd2b46279
   (`/home/ubuntu/weil-launcher/xreviews/V1__Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective__cd2b46279/log.txt`,
   lines 913 onward). Extracting that original and comparing the entire theorem
   signature before `:= by` gives byte-for-byte equality. Its public import and
   docstring are unchanged; the open command adds TopologicalSpace for Opens.
   No existing definition is edited and no data is selected from an open theorem.
2. Proof check: PASS. Both modules compile locally in import order (9.2 s and
   6.6 s). Scratch copies with explicit #print axioms checks show only propext,
   Classical.choice and Quot.sound for both scalar-restriction helpers. The
   parent theorem and new comparison additionally use sorryAx, as reported.
   There is precisely one explicit sorry, in the named new comparison theorem.
   No forbidden declaration or hollow definition occurs.
3. Split statement check: PASS mathematically, still open formally. The bridge
   separates a cohomology/shift/global-section comparison from the existing
   derived-morphism identification. At m=n=0 it is the comparison of the two
   global-section functors; evaluation at 1 and its multiplication inverse are
   additive and natural. For general shifts the component reindexing p to p+m
   and factor (-1)^(m*k) rectify the adjacent-degree differential signs, including
   negative degrees. Zero arguments and the empty scheme give zero groups.
   New independent LeanFinder/Loogle/grep searches found unitHomEquiv and its
   composition lemmas, but no exact derived comparison. Also read the existing
   HomComplexSectionsCanonicalComparison, HomComplexSectionsDerivedNaturality,
   DerivedStructureSheafHomHypercohomology, and
   DerivedStructureSheafGlobalSectionsHom modules: they supply representative
   or structure-sheaf special cases rather than this natural shifted comparison
   across the independent localization universes. The new theorem has a source,
   full proof docstring, node, and strictly simpler conclusion than the parent.
4. Route/pruning check: PASS for the sandbox reduction. Scalar restriction uses
   the proved exact-functor homology iso, followed by the new bridge and the
   existing rhom_global_sections. Naturality follows by composing the three
   naturality equations. The sole archived parent proof dependency
   lem-pur-rhom-global-sections remains used. Both public imports of the bridge
   supply its signature; its private imports record its unfinished node's
   representative proof dependencies. The parent's original public import
   supplies schemeGlobalScalarRestriction and is necessary. No old dependency
   or module was bypassed. The unit sk-thm-picard-duality has empty realized
   statement/step arrays, so no recorded unit route is changed.
5. Node check: the sandbox proof/proof_deps/proof_origin correctly describe the
   actual composition. The new bridge's node has the required creation, source,
   search, proof, and verbatim Lean-statement records. However the parent's
   partial node update presumes an existing node that is absent from the fetched
   baseline. Thus the delivery cannot pass metadata/interface preflight as a
   stage-3 proof update.

Changes by the second reader: appended this review and independent search
records; kept the mathematical proof unchanged. Saved the archived original in
scratchpad/RestrictedGlobalHomShiftedEquiv.original.lean for comparison. Temporary
axiom probes were removed.

Delivery blocker: deliver3.py --no-push failed with 11 preflight reasons, notably
that the parent is a new module requiring an interface change record and that
its presumed existing node lacks the metadata required of a new node. The
failure also listed this then-missing second-reading section, now supplied.
The item must first be restored/landed in the authoritative stage-3 baseline
(or redispatched with an explicit new-module brief and complete original node).
Recreating an absent baseline as a purported proof-only update would misstate
what was proved and is not an authorized repair of this proof.

Final dry run after the second-reading section was added: compilation and axiom
probes passed again; preflight still failed with the remaining 10 baseline/new-node
reasons above. Nothing was pushed.

Retry verification (2026-10-13): reran the authorized deliver3.py dry run after
reading the preserved delivery and review. Local compilation and axiom probes passed.
The freshly fetched baseline still lacks the assigned original module and node;
preflight rejected the same 10 new-module/new-node reasons. No proof, signature,
node, or tool was changed, and nothing was pushed. Restoring the original item
and node in the authoritative baseline remains necessary for a stage-3 proof update.


## Second reading by J1

1. PASS: compared both delivered modules with the current repository. The existing
   module and node are now present. The complete existing theorem signature is
   byte-for-byte identical; its docstring, universes, open command, visibility,
   and public import are unchanged. Only private helpers, a private proof import,
   and the proof are added. No existing definition or target is changed.
2. PASS: compiled both modules locally in dependency order (8.2 s and 6.3 s).
   Scratch copies with #print axioms show only propext, Classical.choice, and
   Quot.sound for restrictionCohomologyEquiv and its naturality theorem; the
   parent and the new bridge additionally use sorryAx, as explicitly reported.
   Exactly one explicit sorry remains, in the named bridge theorem. No axiom,
   unsafe, opaque, implemented_by, extern, hollow definition, or selection of
   arbitrary data from an unproved existence theorem occurs. The existential
   equivalences are eliminated within a theorem proof, not used to define data.
3. PASS as a decomposition: independently checked the bridge against the concrete
   definitions of schemeGlobalDerivedHom and ringedSiteZerothHypercohomology and
   the Stacks sources https://stacks.math.columbia.edu/tag/08JA and
   https://stacks.math.columbia.edu/tag/0B6A. In degree k the shifted Hom differential
   has coefficients (-1)^n and -(-1)^(k+m); multiplication by (-1)^(m*k) changes
   these to the differential of Hom(L,I)[n-m]. This works also for negative
   integers. Checked m=n, m=n=0, either zero argument, and the empty scheme.
   Evaluation at 1 and multiplication by a section are inverse and natural.
   The bridge omits scalar restriction and the derived-morphism identification,
   so it is strictly part of the original argument, not a renamed restatement.
   Its source, complete proof docstring, and matching node are present.
   Fresh LeanFinder, Loogle, and grep searches used different queries about
   derived global sections, unitHomEquiv, and coyoneda. Found abstract Hom-complex
   cohomology and unitHomEquiv lemmas, but no exact bridge. Read the proved
   HomComplexSectionsCanonicalComparison, DerivedStructureSheafHomHypercohomology,
   and DerivedStructureSheafGlobalSectionsHom: the latter two fix the standard
   module localization and compare structure-sheaf Hom; none supplies this
   shifted comparison for independent localization universes in a few minutes.
4. PASS: followed the proof from the parent down through exact scalar restriction,
   the bridge, and the existing rhom_global_sections. Checked all three naturality
   equalities and their composition. The existing dependency
   lem-pur-rhom-global-sections remains used. No old proof dependency is unused,
   hence the No longer needed list is complete. Both public bridge imports occur
   in its signature; private representative imports record its still-open proof
   plan. No recorded unit route is bypassed: sk-thm-picard-duality has empty
   realized statement and step arrays. One hole closed and one added is a
   decomposition, not a net proof or net reduction.
5. PASS: the parent diff changes only proof, proof_deps, and proof_origin.
   These describe the actual three-equivalence composition and naturality.
   The new node has source, creation, blueprint, chapter/unit, search records,
   and Lean metadata. Verified its Lean statement verbatim and proof_deps as
   the union of step uses. No change record or forced adaptation is needed.

Changes by this second reader: appended this current-baseline review and recorded
fresh independent searches in searches.jsonl. No mathematical proof, statement,
import, or node required repair. Temporary axiom probes were removed.
