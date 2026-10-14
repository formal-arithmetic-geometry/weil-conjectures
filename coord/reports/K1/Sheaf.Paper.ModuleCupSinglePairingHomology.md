## What changed

Proved the reconstructed assigned theorem
`AlgebraicGeometry.Scheme.Modules.moduleCup_single_pairing_homology` using the
normalized tensor-cycle interface, class-comparison formulas, the supplied cup
diagram and localized homology naturality. The two proved helpers carry the
categorical transport and tensor-cycle image subarguments. No target changes.

The previous landing failed because the class-comparison source was absent.
This repair initially included that source. During the second reader's dry run,
another delivery restored it. Compared its source: the comparison wrapper is
unfolded to the definitionally identical natural-transformation component.
The delivery tool verified that no adaptation is needed. Removed our duplicate
source and node and use the restored existing module. Added the public
`ModuleCupNaiveDerivedCompatibility` import because the main signature names
its comparison wrapper, which the restored class module no longer exports.

## Proved and sorry left

Assigned theorem proved: `AlgebraicGeometry.Scheme.Modules.moduleCup_single_pairing_homology`.
Supporting delivered theorems proved:
`AlgebraicGeometry.Scheme.Modules.moduleCup_tensor_cycle_image` and
`AlgebraicGeometry.Scheme.Modules.moduleCup_comparison_diagram`.
No sorry remains in the three delivered modules; no holes added or split off.
The assigned module is absent from the current repository baseline, so this is
reconstruction, not a claimed existing closure-hole reduction. The pinned ledger
measures actual progress. The existing `exists_cupDerivedClassComparison` is
used and is not delivered or changed.

## No longer needed

Removed `Sheaf.Paper.ModuleCupDerivedHomologyTensor` from the generic comparison
helper: it requires only Mathlib monoidal-category infrastructure. Removed the
unused `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` import from the cycle
helper. Removed the abandoned sandbox tensor-interface source and node
`new-module-cup-derived-homology-tensor-interface`; the main theorem uses the
normalized tensor interface already in the library.

The old planned `def-sc-module-cup-derived-class-comparison-data`,
`lem-sp-kinjective-computes` and `lem-sc-module-cup-resolution-invariance` are
not used by this route. Removed the unused cycle-witness node from the earlier
attempt. None of the three delivered module/node paths exists in the current
repository; there is no existing proof_deps entry or target-reachable module
removed by this delivery. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The main and class-comparison modules were initially absent. The previous
landing's missing-import-source return was correct. During this second reading,
the class-comparison source and node became present through another delivery,
so the final set preserves that restoration and supplies only the three absent
modules. The earlier zero-normalization tensor interface could not support the
assigned conclusion; the current library's normalized interface does. The
surviving proofs contain no duplicate helpers or reducibility attributes.

## New nodes

`lem-sc-module-cup-single-pairing-homology`: the assigned evaluation formula.
`new-module-cup-tensor-cycle-image`: the proved image calculation for extended
cycles, including zero degrees and zero cycles.
`new-module-cup-comparison-diagram`: the proved categorical transport substep.
The existing `lem-sc-module-cup-derived-class-comparison` is not delivered.
Change record: `coord/changes/ModuleCupSinglePairingHomology-reconstruction.md`.

## Second reading by K1

1. Compared all four delivered Lean paths with the repository using diff; all
   four were initially absent, including the class-comparison source. During
   the dry run, the repository gained a restored class-comparison module. Read the
   missing-import-source return at coord/returns/K1.md and the reconstruction
   change record. Compared that restored source and node: its formula unfolds
   moduleCup_globalComparison to the identical comparisonNatTrans component.
   The delivery tool confirmed that it compiles unchanged against this set.
   Removed our duplicate class-comparison source and node and use the restoration.
   No existing declaration, definition or target is edited. Read the main
   signature against its node: V supplies normalized tensor cycles, J supplies
   resolution classes, hnatural transports augmentations, hdiagram supplies
   the section tensor map and comparison square, and ht and hc supply precisely
   the realized output. No extra normalization of D.derivedMap is assumed.
2. Compiled the four modules in import order with lcompile.py: clean, in
   1.2, 34.6, 16.6 and 49.1 seconds. Scanned sources for forbidden constructs
   and sorry; none occur. A scratch module printed axioms of all four public
   theorems, cupDerivedSections and CupDerivedClassComparison: only propext,
   Classical.choice and Quot.sound, with no sorryAx. Removed the scratch source.
   injectiveData and injectiveClassIso construct their data from a genuine
   injective resolution and canonical isomorphisms. No definition chooses an
   arbitrary witness from an unproved existence theorem. Verdict: valid proofs.
3. No statements are split off with sorry. Read the categorical helper: inverse
   augmentations cancel by isomorphism and tensor naturality. Read the cycle
   helper: cyclesMap_i, the tensor-summand formula and Realizes identify the
   section, then the extension isomorphism and mono cycle inclusion cancel.
   Degree zero, zero cycles, zero sheaves and identity augmentations introduce
   no missing hypothesis. The class comparison transports through the actual
   injective-resolution comparison over F; its cycle witness is the inverse
   extension cycles isomorphism. Fresh Loogle search for cyclesMap_i, LeanFinder
   search for injective-resolution right-derived comparison naturality and
   grep search for extension-cycle/homology compatibility found infrastructure
   already used. rg on both library roots found no duplicate public theorem;
   ExtEdgeResolution.sectionHomologyIso compares forgetting scalars, a different
   statement. Verdict: each helper is a strict proved subargument.
4. Read Stacks Tags 0FKU (Lemma 20.31.3 and the global cup description) and 01DZ
   and the actual imported interfaces. The proof opens the target by extending
   representatives and applying the two proved substeps, then uses V.natural
   and localized homology naturality. No shorter complete theorem was found.
   Public imports provide signature names; the two main proof helpers and the
   class-comparison extension-map proof import are private imports. The unit
   sk-prop-av-cube has empty realized entries; none is changed or bypassed.
   All abandoned imports and old planned dependencies are named above; since
   these delivered paths are absent, no existing proof_deps entry or reachable
   library module is pruned. Verdict: route and imports agree with the proof.
5. Read all four node files against the declarations and proofs. The main node
   cites the tensor-cycle helper for the cycle calculation and the diagram
   helper for transport; the restored existing class node follows injective resolution,
   extension and homology naturality and is preserved untouched. Nodes include sources, searches, origin,
   creation, blueprint, chapter/unit and Lean records. Expanded the cycle-image
   node statement to introduce its scheme, sheaves, complexes, maps, cycles and
   equations explicitly, and removed its unused naive/derived stmt_deps entry.
   Added the missing module-docstring blueprint identifier to the generic
   diagram module. The class-comparison documentation change is not delivered. Verdict: metadata agrees.

Second-reading changes: made the cycle-image node statement self-contained,
removed its unused statement dependency, added the generic module-docstring blueprint
identifier, and recorded this fresh review. Removed the now-restored dependency
source and node, and added the public naive/derived import required by the main
signature after the restored comparison ceased exporting it. No proof or Lean signature changed.
The assigned theorem and two supporting public theorems are delivered proved; zero
new or remaining holes. These are reconstructed absent sources, so no current
repository closure-hole reduction is claimed; the pinned ledger measures it.

Final validation: the main module compiled against the restored dependency in
45.7 seconds. deliver3.py --no-push printed OK: the final three-module set
compiles and passes preflight, with its declaration axiom probes. Review class
is CODEX because this reconstruction adds modules and nodes.
