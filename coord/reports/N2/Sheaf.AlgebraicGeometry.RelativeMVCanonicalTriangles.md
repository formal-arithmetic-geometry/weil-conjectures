## What changed

Replaced the sorry in `AlgebraicGeometry.relativeMV_canonicalTriangles` by a complete
Lean construction from two strictly smaller intermediate statements. The existing
signature, public imports, visibility and docstring stay unchanged.

Added `Sheaf.AlgebraicGeometry.RelativeMVMaps`: genuine constructions of the pinned
derived adjunction, pullback composition comparison, its right-adjoint mate, the
relative unit and restriction maps, and the two sequence maps on the original and
pullback covers. The local and global arrow definitions abbreviate exactly the
arrows in the original statement. All data definitions have real bodies. No
boundary is chosen in any public definition.

Added `Sheaf.AlgebraicGeometry.RelativeMVRestrictionSquares` for the first two
commuting squares of these fixed maps. Added
`Sheaf.AlgebraicGeometry.RelativeMVBoundaryCompletion` for distinguished completion
of those same fixed sequences and their connecting square. The latter does not
assume or assert either restriction square or a triangle morphism. The former has
no cover, compactness, affine-base or quasi-coherence hypothesis and asserts no
boundary or distinguishedness. Thus neither new hole restates the original result.

The original proof selects the two existential boundary witnesses locally in a
THEOREM, obtains their distinguishedness and boundary equation, applies the
restriction-squares theorem, and constructs `Triangle.homMk` from all three actual
commuting equations. Its component equalities are reflexive. Selecting witnesses
locally in this existential proof creates no definition of arbitrary data.

Updated the existing node's proof, proof dependencies and proof origin. Added one
definition node and two statement nodes. No interface changes or forced adaptations.

All four delivered modules compile through lcompile. The latest main proof took
24.5 seconds; the map constructions took 37.7 seconds. Launcher queue waits are
included in its displayed elapsed times for other files. Early `obtain` elaboration
unfolded the large existential arrow types and timed out; direct projections of the
existence proofs avoid that unnecessary elimination motive. No compilation limit
was raised and no argument was split to evade it.

Edge-case checks: the zero object-map gives zero global and local components by
additivity of pullback and direct image, deduced from the pinned adjunctions. These
checks were compiled without sorry in `scratchpad/EdgeCases.lean` (not delivered).
The empty-open, identical-open, zero-complex and zero-map cases require no extra
hypotheses: units and counit-induced restrictions remain defined, and the boundary
construction is the same functorial short-exact-sequence construction with zero
terms for empty opens. The negative V restriction is present on both sides.

Sources read online because the local Stacks source texts are not present on this
machine: https://stacks.math.columbia.edu/tag/08BV (K-injective SES construction),
https://stacks.math.columbia.edu/tag/08HZ (relative construction and functoriality),
https://stacks.math.columbia.edu/tag/08HY (canonical counit mate), and
https://stacks.math.columbia.edu/tag/0DJ9 (the induction diagram).

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.relativeMV_canonicalTriangles`.
There is no sorry left in the item's module. This is a decomposition, not a
sorry-free proof: it adds two holes, so the holes-closed-minus-holes-added count
for this delivery is 1 minus 2 = -1, before shared-closure accounting.

The delivery adds exactly these named public theorem holes:

- `AlgebraicGeometry.relativeMV_restriction_squares`, node
  `lem-pc-relative-mv-restriction-squares`: only the two restriction squares for
  the explicitly constructed fixed maps.
- `AlgebraicGeometry.relativeMV_boundary_completion`, node
  `lem-pc-relative-mv-boundary-completion`: two distinguished completions and only
  their connecting square, for the explicitly constructed fixed maps.

Each has its source, blueprint tag and complete natural-language argument in its
docstring and matching node. No sorry occurs in RelativeMVMaps, any definition,
any private declaration, or the main proof. No target statement changes.

## No longer needed

Removed the direct proof import of
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` from the original module;
its planned use now belongs to the boundary-completion module, which imports it.
Consequently this is relocation, not pruning that module from the target closure.
No public import was removed or added in the original module.

The original theorem now directly needs only the two new theorem nodes and the
canonical-map definition node. Its previous proof dependencies remain needed
below the new boundary statement or in the map definitions. The bare-existence
`derivedDirectImageComposition` is not used to define the new canonical mate;
existing functoriality still imports its module. No existing node or module is
claimed globally pruned. In particular DerivedBaseChangeMayerVietoris and
AffineDerivedPullbackTensorTilde are not newly imported by this delivery.

The old direct proof dependencies, all replaced at the item's top level, are:
`def-pc-derived-base-change-map`, `def-pc-derived-open-restriction-maps`,
`def-pc-derived-pullback`, `lem-pc-derived-direct-image-composition`,
`lem-pc-derived-direct-image-preserves-qcoh`, `lem-pc-derived-mayer-vietoris-functorial`,
`lem-pc-derived-mayer-vietoris-triangle`, `lem-pc-right-derived-functor-triangulated`,
`lem-pc-ringed-spaces-derived-adjoint`, `lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-weil-pbc-affine-morphism-permanence`, `lem-weil-pbc-morphism-affine-schemes-affine`,
and `lem-weil-pbc-qcqs-over-affine`. They remain lower-level dependencies or imports;
`lem-pc-derived-direct-image-composition` is retained transitively by the existing
functoriality module, while the new maps use right-adjoint uniqueness instead.
No module is pruned from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The pre-identification theorem in DerivedBaseChangeMayerVietoris chooses the
open-restriction comparison from a bare `Nonempty` statement. Its interface does
not identify that choice with the pinned derived-composition comparisons in this
item. Therefore it does not alone justify transporting its components to the
exact displayed arrows. No equality between arbitrary comparisons was assumed.
The new sequence maps use the pinned adjunctions and right-adjoint mates instead.
This is an interface gap for the contemplated short route, not a claim that the
source theorem or any existing Lean statement is false.

The existing blueprint unit `sk-thm-picard-semicon` has empty `realized.statement`
and `realized.steps`; no realized unit step is bypassed. The relative
Mayer--Vietoris route, all cover hypotheses and the connecting square are retained.
The proof of the remaining boundary statement still needs the canonical
restriction/derived-pullback identification and shift-compatible adjunction;
neither is silently inferred from existence of arbitrary isomorphisms.

## New nodes

`def-pc-relative-mv-maps` records the canonical relative unit and restriction
construction, including its right-adjoint composition mates, pullback-cover
inclusions and the sequence/arrow abbreviations. Its module is RelativeMVMaps.
All constructions are real; this node adds no proof hole.

`lem-pc-relative-mv-restriction-squares` records the two canonical restriction
squares, independent of distinguished completions. Its module is
RelativeMVRestrictionSquares.

`lem-pc-relative-mv-boundary-completion` records distinguished completion of the
fixed restriction maps and only the compatible connecting square. Its module is
RelativeMVBoundaryCompletion. Generic derived Mayer--Vietoris construction and
functoriality are retained as tools, as in the existing node; this does not replace
the unit's route. There are no change records.

## Earlier second reading (a previous round; superseded)

The two new statements are strictly smaller than the target: one has only the
first two squares and the other only distinguished completion plus the boundary
square. Their hypotheses and conclusions match their Lean signatures. The map
module contains only real definitions from pinned adjunctions and composition
comparisons. The target proof constructs `Triangle.homMk` with exactly the three
required components.

## Second reading by N2

1. Interface: PASS. Compared the delivered item with the repository version; its
   existing theorem signature is byte-for-byte identical. Only its proof and two
   plain proof imports change. The other three modules are new, with no existing
   declarations replaced. No target, definition or statement interface changes.
2. Kernel and constructions: PASS as a decomposition. All four delivered files
   compiled in sandbox import order, and the delivery tool's all-declaration axiom
   probe passed. A scratch copy with explicit `#print axioms` shows only `propext`,
   `Classical.choice`, `Quot.sound` for relativeMVAdj, relativeMVComp and
   relativeMVRestriction; the main theorem and the two new theorem holes also use
   `sorryAx`. Exactly the two reported public theorem bodies contain sorry.
   The adjunction Hom equivalence is pinned by exists_schemeDerivedAdjunction;
   comparison maps are pinned by the left-derived universal property. The
   right-adjoint comparison is constructed by rightAdjointUniq. No arbitrary
   boundary witness is stored in a definition. Triangle.homMk uses all three
   actual commuting equations with the required component maps.
3. Split statements: PASS. Read both docstring arguments and their nodes against
   [08BV](https://stacks.math.columbia.edu/tag/08BV),
   [08HZ](https://stacks.math.columbia.edu/tag/08HZ),
   [08HY](https://stacks.math.columbia.edu/tag/08HY), and the induction diagram of
   [0DJ9](https://stacks.math.columbia.edu/tag/0DJ9).
   The restriction-squares statement contains no boundary or distinguishedness;
   boundary completion fixes the sequence arrows and asserts no first or second
   square. Each is a proper part of the argument, not a renamed existential target.
   Recompiled the zero-object-map tests: local and global components are zero.
   Checked empty opens, U = V, zero complexes, and the negative V sign in the
   mathematical construction; no nonemptiness or invertibility is assumed.
   Fresh leanfinder search for naturality of adjunction mates with restriction
   units and counits found general mate/unit lemmas, not either full statement;
   loogle search for rightAdjointUniq found its general uniqueness identities.
   Local rg also found singleComplexOpenComparison_unit_naturality, which covers
   only one individual unit square in a conjugateIsoEquiv presentation. It does
   not supply the overlap restriction square or boundary completion. The older
   DerivedBaseChangeMayerVietoris uses an arbitrary open comparison, so it does
   not identify the pinned displayed components. Neither remaining hole has a
   complete existing match or a closure available in a few minutes.
4. Route and pruning: PASS. The theorem reduces to the fixed restriction squares
   and boundary completion and explicitly constructs the triangle morphism.
   Proof-only imports are plain imports. The functorial Mayer--Vietoris import
   moves to the boundary module, so it is relocation, with no closure pruning.
   Enumerated every former direct proof dependency above. The unit's realized
   statement and steps are empty, and the relative Mayer--Vietoris route is kept.
5. DAG: PASS after repair. For each node, proof_deps is exactly the union of uses
   in its proof steps. The original node describes precisely the construction
   now in Lean. New nodes have sources, search records, creation and blueprint
   fields, and match their modules. Replaced the compressed one-line Lean
   signatures of both new theorem nodes with the exact multiline source text;
   also normalized the definition node's signature to the exact source text.

Second reading corrected node signature metadata and this report, including
an explicit accounting of all removed top-level dependencies. It also made the
derived-category instance and universe arguments explicit in RelativeMVMaps and
reused relativeMVComp for the two local-arrow comparisons. These are the same
constructed data by definitional equality; they avoid repeated inference of the
large pinned-existence types. The full set compiles against these changes without
changing the main theorem signature or its proof. No time limit was raised.
One original hole closed, two holes added: decomposition,
net -1 before shared-closure accounting; zero modules pruned.
