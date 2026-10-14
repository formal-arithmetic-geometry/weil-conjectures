## What changed

Proved `AlgebraicGeometry.exists_compact_flat_bar_union_augmentation`, the sole
hole in the assigned module, without changing its signature. Its two added
imports are proof-only imports. The delivery includes 26 new supporting modules
and 51 new DAG nodes; all constructions and proofs in them are complete.

The inherited sandbox already constructed the source and enlarged bar towers,
finite telescope cone blocks, least-block preorder, split transitions, strict
augmentation squares, and the canonical cokernel-to-union isomorphism. This
session completed its two residual obligations and the full theory needed for
them. No witness or object data is chosen from an unproved existence theorem.

The source augmentation is a quasi-isomorphism by expressing the full bar as the
colimit of its principal-lower-ideal bars. Each lower ideal has a greatest element,
so its bar contracts explicitly. Exact filtered colimits preserve these
quasi-isomorphisms, using the proved source-library result in
`WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim`.
This proof does not require a bounded-diagonal spectral-sequence argument.

For the enlarged bar, an explicit simplicial prism contracts reindexing along the
unit of the least-block adjunction. Horizontal homotopies are totalized with
opposite vertical signs in adjacent columns. The target-chain diagram is the
objectwise cone of two partial-sum diagrams. Their bars contract onto the infinite
sums by prepending the first stage containing each coefficient. An explicit
signed chain isomorphism identifies the total of these cones with the cone of
the totalized arrow. The isomorphism theorem for morphisms of distinguished
triangles then proves that the target-chain augmentation is a homotopy
equivalence. Strict augmentation identities and the canonical colimit
isomorphism give the original cokernel augmentation for every zero-relation proof.

Updated the original node's proof, proof_deps and proof_origin, and documented
the supporting nodes and declarations. No pre-existing declaration other than
the assigned theorem's proof and proof documentation changed. There are no
forced adaptations or change records.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_compact_flat_bar_union_augmentation` (one of one).
Added zero holes. No `sorry` remains in any delivered module. This is a proof,
not a decomposition into remaining obligations; the delivery's direct net is
one original hole closed and zero added.

Also completed the two residual declarations inherited in the sandbox:

- `AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams.sourceBarAugmentation_quasiIso`
  (`lem-sc-compact-flat-source-bar-quasi-iso`).
- `AlgebraicGeometry.CompactFlatBarIndex.targetComparison`
  (`lem-sc-compact-flat-bar-target-comparison`).

The main newly proved interfaces are:

- `CategoryTheory.PreorderBar.horizontalHomotopy` and `totalUnitHomotopy`.
- `CategoryTheory.PreorderBar.terminalTotalEquiv` and
  `terminalAugmentation_quasiIso`.
- `CategoryTheory.PreorderBar.lowerBarsIsColimit_nonempty` and
  `augmentation_quasiIso`.
- `CategoryTheory.PreorderBar.PartialSum.extraDegeneracy` and
  `augmentation_isIsoHomotopy`.
- `CategoryTheory.PreorderBar.coneTotalXIso`, `coneTotalXHom_comm`,
  `totalConeIso`, `totalConeIso_augmentation`, and `coneAugmentation_isIso`.
- `AlgebraicGeometry.CompactFlatBarIndex.targetRetraction_inclusion_homotopy`
  and `targetAugmentation_isIso`.

Every original construction/property node in the inherited sandbox is proved as
well, including all bounds, flatness assertions, splitting assertions, the two
colimit universal properties, and the final homotopy-category cancellation.
A complete sandbox build compiled all 27 delivered modules. A separate `#print
axioms` audit of the assigned theorem and all 51 supporting DAG declarations
reported only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.
The slowest file took 15.8 seconds in that build. The final warning-free checks
and delivery dry run are recorded by the tools. The second reader repeated the
52-declaration axiom audit after narrowing the imports.

## No longer needed

No existing module or node is pruned. The assigned module's direct proof-only
import `Sheaf.AlgebraicGeometry.FlatTelescopeStageMap` was removed and replaced
by the two actual proof dependencies; its definitions remain available through
`CompactFlatFiniteSubcomplexDiagrams` and are still required. Every new
supporting module lies in the assigned module's import closure.

The old proof dependency `lem-sc-compact-flat-finite-subcomplex-diagrams` is
no longer used as an existence theorem: the diagram D is supplied as an input.
It remains a statement dependency, and its module remains publicly imported.
`def-sc-flat-telescope-stage-map`, the other original proof dependency, is used.

The second reader removed redundant direct imports of
`Mathlib.CategoryTheory.Limits.Shapes.Products` from `PreorderBarTotal`, and of
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` from
`PreorderBarTotalSplit`, `CompactFlatSourceBarTower`, and
`CompactFlatTelescopeBlocks`. These APIs are already provided by required imports.
No associated proof node or module becomes unreachable.

The proof of `sourceBarAugmentation_quasiIso` no longer needs
`lem-sc-compact-flat-source-bar-bounded`: the source bound remains necessary for
the bounded-stage conjunct of the assigned theorem. No finite-strip or
bounded-diagonal total-comparison module is imported.

The projective-resolution comparison described in the inherited target proof is
replaced by the two partial-sum extra degeneracies and the explicit signed cone
isomorphism. No projective-resolution or Cartan--Eilenberg-resolution module is
needed or imported. The supplied finite-subcomplex diagram remains an input;
its existence constructor is not re-proved or used.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed target was needed. The earlier attempt correctly
constructed the towers, but left source exactness and target homotopy comparison
unproved. Its report therefore described a decomposition; the present delivery
closes both obligations and all the theory introduced to prove them.

The source proof can avoid its planned bounded-diagonal comparison entirely:
principal lower ideals have terminal objects, and exact colimits preserve the
quasi-isomorphisms of their contracted bars. For the target proof, the cone blocks
are already the objectwise cones of partial sums. Their coefficientwise extra
degeneracies make a separate projective-resolution comparison unnecessary.

The sign on the source cone summand is essential: in horizontal degree p it is
(-1)^p. With this sign the cone comparison respects both the horizontal face
sum and the vertical differential, including degree zero. The natural-number
target chain is lifted by ULift to the source-index universe; explicit universe
arguments keep both partial-sum diagrams and target bars in that same universe.
The lift changes no mathematical object or hypothesis.

All new constructions were tested on their boundary cases in the actual proofs:
empty source indexing types, horizontal degree zero, the first target stage,
zero coefficients, and truncated subtraction in the first available stage.
No global bound on the target tower is used. No compiler time limit was raised.

## New nodes

`def-sc-compact-flat-bar-index`: The concrete enlarged indexing diagram. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.diagram` in
`Sheaf.AlgebraicGeometry.CompactFlatBarIndex`; complete construction/proof, no remaining hole.

`def-sc-compact-flat-bar-target-retraction`: Concrete target-chain bar retraction. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.targetRetraction` in
`Sheaf.AlgebraicGeometry.CompactFlatBarTargetRetraction`; complete construction/proof, no remaining hole.

`def-sc-compact-flat-bar-union-iso`: Canonical cokernel-to-full-bar isomorphism. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.unionIso` in
`Sheaf.AlgebraicGeometry.CompactFlatBarUnion`; complete construction/proof, no remaining hole.

`def-sc-compact-flat-enlarged-bar-tower`: Explicit enlarged bar tower. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.enlargedBar` in
`Sheaf.AlgebraicGeometry.CompactFlatEnlargedBarTower`; complete construction/proof, no remaining hole.

`def-sc-compact-flat-source-bar-tower`: The explicit source bar tower. Realized by
`AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams.sourceBar` in
`Sheaf.AlgebraicGeometry.CompactFlatSourceBarTower`; complete construction/proof, no remaining hole.

`def-sc-compact-flat-telescope-blocks`: Explicit finite telescope cone blocks. Realized by
`AlgebraicGeometry.FlatTelescopeBlocks.block` in
`Sheaf.AlgebraicGeometry.CompactFlatTelescopeBlocks`; complete construction/proof, no remaining hole.

`def-sc-partial-sum-bar-extra-degeneracy`: An explicit extra degeneracy for bars of partial sums. Realized by
`CategoryTheory.PreorderBar.PartialSum.extraDegeneracy` in
`Sheaf.AlgebraicGeometry.PartialSumBarExtraDegeneracy`; complete construction/proof, no remaining hole.

`def-sc-preorder-bar-cone-diagram`: The objectwise cone diagram and augmented cocone. Realized by
`CategoryTheory.PreorderBar.coneDiagram` in
`Sheaf.AlgebraicGeometry.PreorderBarConeDiagram`; complete construction/proof, no remaining hole.

`def-sc-preorder-bar-total`: Explicit preorder bar total. Realized by
`CategoryTheory.PreorderBar.total` in
`Sheaf.AlgebraicGeometry.PreorderBarTotal`; complete construction/proof, no remaining hole.

`def-sc-preorder-bar-total-cone`: The explicit degreewise total-cone comparison. Realized by
`CategoryTheory.PreorderBar.coneTotalXIso` in
`Sheaf.AlgebraicGeometry.PreorderBarTotalCone`; complete construction/proof, no remaining hole.

`def-sc-preorder-bar-total-cone-iso`: The explicit total-cone cochain isomorphism. Realized by
`CategoryTheory.PreorderBar.totalConeIso` in
`Sheaf.AlgebraicGeometry.PreorderBarTotalConeIso`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-bar-cokernel-homotopy`: Canonical cokernel augmentation in the homotopy category. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.cokernelAugmentation_isIso` in
`Sheaf.AlgebraicGeometry.CompactFlatBarUnionHomotopy`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-bar-index-adjunction`: Least-block adjunction. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.retractOrder_le_iff` in
`Sheaf.AlgebraicGeometry.CompactFlatBarIndex`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-bar-target-augmentation`: The target-chain bar augmentation is a homotopy isomorphism. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.targetAugmentation_isIso` in
`Sheaf.AlgebraicGeometry.CompactFlatBarTargetAugmentation`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-bar-target-cancellation`: Cancellation of target-chain bar comparisons. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.fullBarAugmentation_isIso_of_target` in
`Sheaf.AlgebraicGeometry.CompactFlatBarTargetRetraction`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-bar-target-comparison`: Unit contraction and target-chain telescope comparison. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.targetComparison` in
`Sheaf.AlgebraicGeometry.CompactFlatBarHomotopyComparison`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-bar-target-section`: Strict target-chain bar section. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.targetInclusion_retraction` in
`Sheaf.AlgebraicGeometry.CompactFlatBarTargetRetraction`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-bar-union-colimit`: The full enlarged bar is the stage-bar colimit. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.unionIsColimit_nonempty` in
`Sheaf.AlgebraicGeometry.CompactFlatBarUnion`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-bar-union-homotopy`: Full-bar augmentation in the homotopy category. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.fullBarAugmentation_isIso` in
`Sheaf.AlgebraicGeometry.CompactFlatBarUnionHomotopy`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-bar-union-iso-augmentation`: The canonical isomorphism preserves augmentation. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.unionIso_augmentation` in
`Sheaf.AlgebraicGeometry.CompactFlatBarUnion`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-bar-unit-homotopy`: The least-block unit contracts the enlarged bar. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.targetRetraction_inclusion_homotopy` in
`Sheaf.AlgebraicGeometry.CompactFlatBarUnitHomotopy`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-diagram-term-flat`: Flat terms of diagram pieces. Realized by
`AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams.diagram_flat` in
`Sheaf.AlgebraicGeometry.CompactFlatSourceBarTower`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-enlarged-bar-bounded`: Bounded enlarged bar stages. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.enlargedBar_bounded` in
`Sheaf.AlgebraicGeometry.CompactFlatEnlargedBarTower`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-enlarged-bar-flat`: Flat enlarged bar terms. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.enlargedBar_flat` in
`Sheaf.AlgebraicGeometry.CompactFlatEnlargedBarTower`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-enlarged-bar-map-split`: Split enlarged bar transitions. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.enlargedBarMap_split` in
`Sheaf.AlgebraicGeometry.CompactFlatEnlargedBarTower`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-enlarged-bar-naturality`: Strict enlarged augmentation squares. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.enlargedBarAugmentation_naturality` in
`Sheaf.AlgebraicGeometry.CompactFlatEnlargedBarTower`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-factor-telescope-block`: Factor finite compact pieces through cone blocks. Realized by
`AlgebraicGeometry.FlatTelescopeBlocks.factor_diagram_object` in
`Sheaf.AlgebraicGeometry.CompactFlatTelescopeBlocks`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-source-bar-bounded`: Bounded source bar stages. Realized by
`AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams.sourceBar_bounded` in
`Sheaf.AlgebraicGeometry.CompactFlatSourceBarTower`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-source-bar-flat`: Flat terms of source bars. Realized by
`AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams.sourceBar_flat` in
`Sheaf.AlgebraicGeometry.CompactFlatSourceBarTower`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-source-bar-naturality`: Strict source bar augmentation squares. Realized by
`AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams.sourceBarAugmentation_naturality` in
`Sheaf.AlgebraicGeometry.CompactFlatSourceBarTower`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-source-bar-quasi-iso`: Filtered source bar augmentation. Realized by
`AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams.sourceBarAugmentation_quasiIso` in
`Sheaf.AlgebraicGeometry.CompactFlatSourceBarQuasiIso`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-source-enlarged-augmentation`: Compatibility of source and enlarged augmentations. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.sourceToBar_augmentation` in
`Sheaf.AlgebraicGeometry.CompactFlatEnlargedBarTower`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-source-enlarged-naturality`: Strict source-to-enlarged tower map. Realized by
`AlgebraicGeometry.CompactFlatBarIndex.sourceToBar_naturality` in
`Sheaf.AlgebraicGeometry.CompactFlatEnlargedBarTower`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-source-global-augmentation`: Global augmentation of source pieces. Realized by
`AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams.augmentationTo_eq` in
`Sheaf.AlgebraicGeometry.CompactFlatSourceBarTower`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-telescope-block-bounded`: Bounded finite cone blocks. Realized by
`AlgebraicGeometry.FlatTelescopeBlocks.block_bounded` in
`Sheaf.AlgebraicGeometry.CompactFlatTelescopeBlocks`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-telescope-block-flat`: Flat finite cone-block terms. Realized by
`AlgebraicGeometry.FlatTelescopeBlocks.block_flat` in
`Sheaf.AlgebraicGeometry.CompactFlatTelescopeBlocks`; complete construction/proof, no remaining hole.

`lem-sc-compact-flat-telescope-cone-map-split`: Split maps between cone terms. Realized by
`AlgebraicGeometry.FlatTelescopeBlocks.cone_map_split` in
`Sheaf.AlgebraicGeometry.CompactFlatTelescopeBlocks`; complete construction/proof, no remaining hole.

`lem-sc-flat-telescope-cokernel-colimit`: The sequential telescope cokernel is the colimit. Realized by
`AlgebraicGeometry.flatTelescopeCokernelIsColimit` in
`Sheaf.AlgebraicGeometry.FlatTelescopeCokernelColimit`; complete construction/proof, no remaining hole.

`lem-sc-partial-sum-bar-augmentation`: Partial-sum bar augmentation is a homotopy isomorphism. Realized by
`CategoryTheory.PreorderBar.PartialSum.augmentation_isIsoHomotopy` in
`Sheaf.AlgebraicGeometry.PartialSumBarExtraDegeneracy`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-cone-augmentation`: Homotopy-invertible bar augmentations give an invertible cone augmentation. Realized by
`CategoryTheory.PreorderBar.coneAugmentation_isIso` in
`Sheaf.AlgebraicGeometry.PreorderBarConeAugmentation`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-filtered-augmentation`: Exact colimits preserve the preorder bar augmentation. Realized by
`CategoryTheory.PreorderBar.augmentation_quasiIso` in
`Sheaf.AlgebraicGeometry.PreorderBarFilteredAugmentation`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-horizontal-homotopy`: Horizontal homotopies on mixed bar totals. Realized by
`CategoryTheory.PreorderBar.horizontalHomotopy` in
`Sheaf.AlgebraicGeometry.PreorderBarTotalHomotopy`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-lower-ideals-colimit`: A bar total is the colimit of its principal lower ideals. Realized by
`CategoryTheory.PreorderBar.lowerBarsIsColimit_nonempty` in
`Sheaf.AlgebraicGeometry.PreorderBarLowerIdeals`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-terminal-augmentation`: A terminal preorder bar contracts to its value. Realized by
`CategoryTheory.PreorderBar.terminalTotalEquiv` in
`Sheaf.AlgebraicGeometry.PreorderBarTerminalAugmentation`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-total-bounded`: Uniform bounds on preorder bar totals. Realized by
`CategoryTheory.PreorderBar.bounded_total` in
`Sheaf.AlgebraicGeometry.PreorderBarTotal`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-total-cone-augmentation`: Total-cone comparison preserves canonical augmentation. Realized by
`CategoryTheory.PreorderBar.totalConeIso_augmentation` in
`Sheaf.AlgebraicGeometry.PreorderBarTotalConeIso`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-total-cone-differential`: The total-cone comparison commutes with differentials. Realized by
`CategoryTheory.PreorderBar.coneTotalXHom_comm` in
`Sheaf.AlgebraicGeometry.PreorderBarTotalConeDifferential`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-total-differential`: The differential on a labelled total-bar generator. Realized by
`CategoryTheory.PreorderBar.ιTerm_d_succ` in
`Sheaf.AlgebraicGeometry.PreorderBarTotalDifferential`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-total-single-collapse`: Collapse of a single-column total. Realized by
`CategoryTheory.PreorderBar.collapse_isIso` in
`Sheaf.AlgebraicGeometry.PreorderBarTotal`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-total-split`: Split reindexing of bar totals. Realized by
`CategoryTheory.PreorderBar.totalMap_split` in
`Sheaf.AlgebraicGeometry.PreorderBarTotalSplit`; complete construction/proof, no remaining hole.

`lem-sc-preorder-bar-unit-homotopy`: A preorder unit contracts its bar reindexing. Realized by
`CategoryTheory.PreorderBar.totalUnitHomotopy` in
`Sheaf.AlgebraicGeometry.PreorderBarUnitHomotopy`; complete construction/proof, no remaining hole.


## Second reading by P2

1. **Visible statements and definitions: pass.** Compared all 27 modules with
   the repository using diff. Exactly one module already exists there. Its
   theorem signature, from `theorem` to `:=`, is byte for byte unchanged.
   Its public import is unchanged; only proof imports, proof documentation,
   and the proof differ. The other 26 modules are new. No existing target,
   definition, or declaration used by another group changes, and there are
   no forced adaptations or change records. The existing node changes only
   `proof`, `proof_deps`, and `proof_origin`.

2. **Proof and object data: pass.** Compiled the complete set locally, then
   recompiled the affected modules in import order after the import repairs.
   No Lean error or warning remains. Scanned every delivered Lean module:
   zero `sorry`, axioms, unsafe/opaque/extern/implemented_by declarations,
   or kernel-check bypasses. Independently printed the axioms of the target
   and all 51 supporting node declarations in a scratch module: only
   `propext`, `Classical.choice`, and `Quot.sound`. The scratch audit is
   `scratchpad/second-reading-axioms.log` and is not delivered. Read the
   actual coproduct, bar, cone, least-block, and colimit constructions.
   Factorization witnesses are supplied by a proved construction; the
   embedding is monic, so factor maps are unique. The colimit structures
   come from proved universal properties. No data comes from an unproved
   arbitrary-existence theorem.

3. **Supporting statements: pass; no open split-offs.** Read the generic
   total and homotopy APIs, both colimit proofs, finite-block factorization,
   unit prism, partial-sum extra degeneracy, signed cone comparison, and
   the final cancellation. Each is strictly part of the argument, rather
   than a restatement of the existential target. Their Lean proofs cover
   horizontal degree zero, the first target block, arbitrary nonnegative
   offset r with truncated subtraction, zero coefficients, empty supports,
   and an empty generic indexing preorder where applicable. The source
   stage itself is nonempty by D.filtered. Repeated searches with different
   words through msearch.py (LeanFinder, Loogle, and grep), and searched
   lean/ and the upstream source. No matching generic preorder-bar theorem
   was found. The proofs already use Mathlib extra-degeneracy contraction
   and distinguished-triangle comparison, plus the proved upstream exact
   colimit/quasi-isomorphism API. LeanSearch returned Internal Server Error;
   recorded that unavailability, without treating it as a negative search.

4. **Route and pruning: pass after report/import repair.** Followed the
   target downward through the explicit source and enlarged towers and
   both augmentation proofs. The principal-lower-ideal proof avoids an
   unnecessary bounded-diagonal comparison; the two partial-sum
   contractions and signed cone isomorphism close the target comparison.
   All 26 new modules are reached by the target's imports, including the
   ones whose imports are now private. The original two proof dependencies
   are accounted for above. No existing module is pruned. Read
   dag/units/sk-thm-picard-duality.json and its realized fields: this item
   is below that unit's statement and steps, and the delivery changes no
   unit record or route.

5. **DAG and Lean agreement: pass after metadata repair.** Checked all 52
   node records against their declarations, verified each proof_deps is
   the union of the steps' uses, and checked every dependency resolves.
   All 51 new nodes have the required source, creation, blueprint, chapter,
   unit, search, proof, and Lean fields. Corrected 14 new-node lean.statement
   records to start at `def`, as the project's signature parser requires;
   this changes metadata only. Added the missing actually-run LeanSearch
   records to 16 nodes. The prose proof routes agree with the constructed
   maps, the source colimit argument, and target cone argument.

Changes made by the second reader: corrected the 14 node signatures and
16 search records; completed `## No longer needed`; removed four redundant
imports; made the proof-only imports of PreorderBarTotalSplit private in
PreorderBarLowerIdeals and PreorderBarTotalCone; replaced the public upstream
GrothendieckAxioms.Colim import by a public Mathlib definition import and a
private upstream proof import; narrowed PreorderBarUnitHomotopy's public
imports to the total, chain-homotopy type, and simplicial-homotopy type, with
its two proof APIs private. PreorderBarTerminalAugmentation imports those APIs
publicly because its exposed homotopy-equivalence construction uses them.
PreorderBarTotalConeDifferential now imports its generator-map API directly
and privately. No proof body, theorem signature, or mathematical definition
needed correction. One original hole closed, zero holes added.
