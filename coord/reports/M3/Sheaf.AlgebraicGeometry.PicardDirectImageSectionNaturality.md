## What changed

Constructed `AlgebraicGeometry.Scheme.picardDirectImageSectionMap` in the new module
`Sheaf.AlgebraicGeometry.PicardDirectImageSectionMap`. Its data are explicit: the
projection-preserving lift between fibre products, the coefficient comparison obtained
from the pinned tensor adjunctions, the canonical derived base-change map, the canonical
single pullback comparisons, and degree-zero homology followed by evaluation at 1.
The additive-map laws are proved. No definition contains `sorry` and no arbitrary witness
of a mere existence theorem supplies the map.

Replaced the original theorem's hole with a proof forming `AddEquiv.ofBijective` from this
map at each base change, then applying its restriction equation. Two strictly separate
properties of the fixed map are stated in new modules, with source citations and complete
proof plans: pointwise bijectivity and compatibility with restriction. The latter holds
for arbitrary modules and morphisms; it has no geometric hypotheses and asserts no
bijectivity. The original theorem's signature and docstring are unchanged. The parent
DAG proof now records this assembly, and the three new nodes record the actual construction
and the two properties. The unit's route is untouched.

## Proved and sorry left

Closed the original named hole
`AlgebraicGeometry.Scheme.picard_direct_image_section_naturality`
(node `lem-sc-picard-direct-image-section-naturality`). This is a decomposition, not a
complete axiom-free proof: one upper hole closed, two lower holes added, net -1.

The two holes added are:
- `AlgebraicGeometry.Scheme.picardDirectImageSectionMap_bijective`, node
  `lem-sc-picard-direct-image-section-map-bijective`.
- `AlgebraicGeometry.Scheme.picardDirectImageSectionMap_restriction`, node
  `lem-sc-picard-direct-image-section-map-restriction`.

Each hole is the entire proof of a named public theorem in its own module. The constructed
map has no hole. Local `lcompile.py --all` compiled all four delivered modules successfully.
The delivery dry run performs the required declaration/axiom probes.

## No longer needed

Removed the parent's direct proof imports of
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`,
`Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf`,
`Sheaf.AlgebraicGeometry.DerivedAdjoint`, and
`Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare`.
The perfect-base-change and adjunction modules remain imports of the bijectivity item;
the canonical degree-zero module is used by the constructed map. These are relocated
requirements, not globally pruned work.

The route does not use
`AlgebraicGeometry.nonempty_derivedPullback_structureSheaf_iso`, node
`lem-sc-derived-pullback-structure-sheaf-local`, module
`Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf`: the explicit canonical single
pullback comparison supplies the structure-sheaf isomorphism instead. No claim is made
that this module is unreachable through other target paths. All eleven original `proof_deps` are removed from the parent's direct proof dependency
list: `def-pc-base-change`, `def-pc-derived-direct-image`, `def-sc-invertible-module`,
`def-sc-picard-derived-model-sections`, `lem-pc-canonical-degree-zero-mate-square`,
`lem-pc-module-pullback-adjunction`, `lem-pc-module-pullback-identity-composition`,
`lem-pc-rf-perfect-base-change`, `lem-pc-ringed-spaces-derived-adjoint`,
`lem-pc-ringed-spaces-derived-pullback-composition`, and
`lem-sc-derived-pullback-structure-sheaf-local`. The first ten remain statement or
construction dependencies, or requirements of the two lower proofs; their removal from
this direct list does not claim global pruning. The last is bypassed by the explicit
canonical single-pullback comparison. The parent's new direct dependencies are exactly
the bijectivity and restriction nodes.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's compatibility claim for every family of pointwise additive
equivalences is false: independently negating one member preserves pointwise equivalence
but breaks restriction naturality. A reflexive equation is also not a pinning condition;
that exploratory draft was withdrawn and is absent from this delivery. Both current
properties refer to the explicitly constructed map, with no arbitrary family parameter.

Checked the empty-scheme and zero-module cases: all operations are canonical module and
derived-category morphisms, with no chosen point or nonzero section. The bijectivity
argument identifies zero section groups in the empty cases. The restriction statement
asserts an equality of maps for arbitrary modules, so it does not claim general base-change
invertibility. The parent statement is not disputed.

The given ingredient statements do not directly state the full identification of this
fixed degree-zero Hom comparison with section evaluation, nor the successive-mate
coherence formula. Those are the two precisely separated remaining obligations. Searches
found the ingredient adjunctions and evaluation lemmas, not a complete replacement.

## New nodes

`def-sc-picard-direct-image-section-map` records the actual additive-map construction in
`Sheaf.AlgebraicGeometry.PicardDirectImageSectionMap`. Its Lean declaration is a complete
construction, not a choice from an unproved existence result.

`lem-sc-picard-direct-image-section-map-bijective` records only pointwise bijectivity of
that map under the original flat, proper, finite-presentation and invertible hypotheses.
Its natural-language proof uses canonical arbitrary base change, derived adjunction,
full faithfulness of the single functor, and degree-zero section evaluation.

`lem-sc-picard-direct-image-section-map-restriction` records only its restriction equation,
without those geometric hypotheses. Its proof plan uses canonical mate transitivity,
derived composition coherence, the degree-zero mate square and ordinary unit evaluation.
There is no new change record: no existing signature, definition or public import changed.


## Second reading by M3

1. **Interface preservation — pass.** Diffed the parent against the repository file.
   Only its four private proof imports and its theorem body changed. The entire existing
   theorem signature and docstring are byte-for-byte unchanged. The other three delivered
   modules are new; no existing definition or target statement is edited, and no forced
   adaptation or change record is needed.
2. **Proof and data — pass as a decomposition.** Compiled all four modules sequentially
   with `lcompile.py --all`. Scanned the delivered sources: exactly the two reported named
   theorem holes remain; there is no forbidden declaration or hole in the definition.
   A scratch copy with `#print axioms` reports only `propext`, `Classical.choice` and
   `Quot.sound` for `picardDirectImageSectionMap`; the parent and the two property theorems
   additionally use `sorryAx`, as expected. Read the construction: a is the explicit
   pullback lift; c is the inverse mate of pushforward composition; d transports between
   the two fixed left adjoints; B is the canonical base-change mate followed by the single
   comparison and d. The only inversion needing a geometric property is the structure
   sheaf comparison, supplied by `isIso_canonicalSinglePullbackMap` for the unit.
   H0, its single comparison z, the direct-image comparison r, evaluation at 1 and
   restriction then give the actual additive map. The adjunction witness is pinned by
   `exists_tensorPullbackAdjunction`'s unit formula, not arbitrary existence data.
3. **Split properties — pass.** Read [0B91](https://stacks.math.columbia.edu/tag/0B91)
   clause (2), [08HY](https://stacks.math.columbia.edu/tag/08HY)'s counit-transpose
   construction, and [0D5S](https://stacks.math.columbia.edu/tag/0D5S)'s K-flat composition
   argument. Bijectivity uses exactly proper finite presentation and relative flatness
   of the invertible coefficient after base change; the added Flat f hypothesis supplies
   that relative flatness and is already in the parent. Restriction is a mate-coherence
   identity and needs no invertibility of B or of the coefficient single comparison.
   Thus its lack of geometric hypotheses is valid. Checked zero coefficients and empty
   schemes (zero groups), and identity restriction (composition/unit identities), with
   no point or nonzero section chosen. The two properties concern the fixed constructed
   map and are strictly separate parts of the argument, not a renamed existential
   naturality theorem. Their source/proof docstrings and matching nodes are present.
   Independent leanfinder search for Hom from the structure sheaf to a derived direct
   image found only ordinary scheme-section ingredients; Loogle search for
   `SheafOfModules.unitHomEquiv_naturality` found no identifier; grep found
   `pushforwardSections_unitHomEquiv`. Read the library's `unitHomAddEquiv`,
   `canonicalDegreeZeroMateSquare`, `canonicalSinglePullbackSquare`,
   `perfect_derivedDirectImage_baseChange`, and `schemeGlobalSections_baseChange_mate`.
   These do not state either fixed-map property; the last also requires extra module
   derived localizations. Upstream section/evaluation searches found the ordinary
   `unitHomAddEquiv` ingredient, not a complete replacement. Neither hole closes by a
   short application of these declarations.
4. **Route and pruning — pass after report repair.** The parent forms
   `AddEquiv.ofBijective` and applies restriction, whose underlying map is definitionally
   the same map. The old argument's base-change, adjunction, composition and evaluation
   route is kept inside the construction and its two properties. The unit
   `sk-prop-av-cube` has empty `realized.statement` and `realized.steps[0]` in the supplied
   repository; this delivery does not alter the unit record or bypass its cube step.
   Expanded “No longer needed” to enumerate every old direct proof dependency, separating
   relocation from the unused structure-sheaf existence lemma. In the new construction,
   removed the redundant direct tensor-adjunction, locally-free, injective-resolution
   and enough-injectives imports; they are already public transitive imports of the
   retained modules. Public imports for construction data remain. All four files
   compile after this change.
5. **DAG alignment — pass.** The parent's proof and `proof_deps` name exactly the two
   properties applied in its body. The construction node records the explicit lift,
   coefficient mate, B, structure-unit comparison, H0 and evaluation. The bijectivity
   node records the fixed-map bijectivity obligation and the restriction node the full
   displayed arbitrary-coefficient identity. Each new node is in the parent's chapter
   and unit and has its source, creation record, blueprint origin, searches and Lean
   record. The natural-language proof dependencies agree with the cited ingredient
   declarations; no statement field of an existing node was changed.

Second-reading changes: four redundant imports removed from the new map module;
completed the old-dependency inventory in this report. No theorem statement or
construction data was changed. One upper hole is closed and two lower holes are added:
this remains a decomposition, with net holes closed minus added equal to -1.
