## What changed

Prepared a reduction of `AlgebraicGeometry.finiteSurjectiveSetDescent_compatible_lift`
in `Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentEqualizer`, without changing its
signature. The remaining geometric argument is isolated in the new module
`Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentLocalLifts` as local existence:
the image sieve of the unit at a compatible section covers X. This gives local
preimages, not a global preimage or a repackaged form of the original conclusion.

The original module proves objectwise injectivity by lifting geometric points,
applying the inverse-image stalk germ formula, and using section extensionality.
Its other private helper proves a general gluing result for an objectwise injective
morphism of set sheaves and a section whose image sieve covers. This helper has
compiled independently in scratchpad/Glue.lean. Local preimages agree on overlaps
by injectivity and naturality; the sheaf axiom glues them, and separatedness of the
target identifies the image with the given section. The main theorem applies this
argument to the unit. New proof-only imports supply the germ formula, section
extensionality, geometric-point lifting, local-lifting theorem and image-sieve APIs.

Validation is now clean: `lcompile.py --all` compiles all six sandbox modules, including the Injective and geometric-germ dependencies. No missing dependency was copied or redefined.

## Proved and sorry left

The item's single sorry has been replaced by the reduction proof described above;
the full module now typechecks against the published library.
The generic private helper `lift_of_covering_image` typechecks in an independent
scratch file against Mathlib. `unit_injective_on_object` is the existing proved
injectivity argument specialized to arbitrary U; it now compiles.

The delivery adds exactly one sorry:
`AlgebraicGeometry.finiteSurjectiveSetDescent_compatible_locally_lifts`, node
`lem-weil-pbc-sets-finite-descent-local-lifts`, in the new LocalLifts module. Its
proof is exactly `by sorry`; its docstring gives the complete geometric-stalk and
local-refinement argument. Other sorries in existing imported modules are untouched.

## No longer needed

The original public import supplies the statement definitions and remains public.
Removed proof-only imports `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
and `Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk`: their geometric calculations
are now recorded in LocalLifts; the former is also available through Injective.

The following old proof dependencies are eliminated from the route altogether:
- `lem-weil-pbc-sets-etale-iso-on-geometric-stalks`;
- `lem-weil-pbc-sets-etale-stalk-finite-limits`;
- `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`.

These are Mathlib leaves, not separate Sheaf modules. There is no sectionwise
equalizer object or stalkwise isomorphism detection in the new argument. The
ordinary set-sheaf axiom performs global gluing directly.

The finite pushforward stalk theorem, finite base-change/composition facts,
fibre-product universal property, geometric stalks, colimit facts, algebraic
closures, and small étale-site definitions move from direct dependencies of the
item to dependencies of LocalLifts; they are retained, not pruned. The new local
lemma additionally uses the existing pointed-neighbourhood cofilteredness and
filtered-colimit elementwise-equality nodes. No blueprint unit realization or
chapter route was changed.

## Where the brief, the DAG or earlier work was wrong

The earlier build-availability diagnosis was stale: the local mirror now contains the needed oleans and the complete sandbox import graph compiles.

The repository has no local literature/stacks-project/etale-cohomology.tex. Read
Stacks tags 09Z3 and 09Z2 online instead. The local statement is the local-existence
part of that stalkwise descent argument. Edge cases checked mathematically: empty
X uses the empty covering sieve; a nonempty geometric fibre supplies a coordinate
even if G_x is empty (a compatible germ then cannot exist); identity f reduces to
local membership in the identity unit's image. No statement correction is needed.

## New nodes

`lem-weil-pbc-sets-finite-descent-local-lifts` states precisely that the image sieve
of the unit at a compatible section covers X. It carries the finite-stalk product,
nonempty geometric fibre, diagonal/coordinate calculation, and the local
filtered-colimit refinement step. Its source is Stacks 09Z3/09Z2 with 03QP and
03Q1. Searches were actually run using msearch: LeanSearch failed with Internal
Server Error and is recorded unavailable; LeanFinder and grep found generic image
and local-surjectivity APIs but no finite-descent local-lifting theorem. The
blueprint search found no duplicate. The item node's proof and proof_deps now
record local lifting followed by injectivity and direct sheaf gluing. There are
no interface changes and no change records.


## Second reading by K2

1. **Statements and signatures.** I compared the item's Lean declaration with the repository version: the theorem signature is unchanged, including hypotheses, universe, compatibility equation, and existential conclusion. The new local-lifting theorem has the smaller image-sieve conclusion recorded by its node and does not restate global descent.
2. **Proof and axioms.** I read the equalizer and LocalLifts modules. The equalizer proof closes the original sorry using objectwise injectivity, local image-sieve lifting, and sheaf amalgamation. `lcompile.py --all` compiled all six sandbox modules without errors or warnings. The only remaining sorry is the named local-lifts theorem; no definition contains sorry.
3. **New statement and searches.** The local-lifting statement handles empty schemes (empty sieve), identity morphisms, and nonempty geometric fibres. Its node records LeanSearch unavailability plus LeanFinder and grep searches, with no existing declaration found. I additionally ran msearch grep for `locallySurjective|imageSieve.*cover|surjective.*stalk` and searched both library roots; no finite-descent local-lifting duplicate appeared. It is strictly local existence, exactly as strong as needed.
4. **Pruning and imports.** The proof uses the existing injectivity, germ, geometric-point, locally-surjective, and LocalLifts declarations. The old stalk finite-limit and sectionwise-equalizer route is not used and is listed as pruned. Proof-only imports are plain imports, and the unit's local-lift-then-glue route remains intact.
5. **DAG agreement.** The item node's proof and `proof_deps` match the Lean route, and the new node's Lean record matches its theorem. No target statement, definition, or change record was altered.

I changed this report to replace the stale build diagnosis, list the removed proof imports, and add this second reading; no Lean or DAG changes were needed.

I read [Stacks 09Z3](https://stacks.math.columbia.edu/tag/09Z3) and [09Z2](https://stacks.math.columbia.edu/tag/09Z2). The source uses finite surjectivity to make the geometric lift set nonempty, and identifies the two stalk comparison maps with the two coordinate projections. These are precisely the hypotheses and calculation used by the new local-lifting node; filtered-colimit equality then provides its covering image sieve.

The complete deliver3 dry run passed (commit af0b8339e); its declaration axiom probes and server checks passed. The review class is CODEX because of the new node, new module, and named local-lifting sorry.

Explicit scratch-copy `#print axioms` for both the item and LocalLifts reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` (the named open dependencies); the scratch copy was removed.
