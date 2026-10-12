## What changed

Replaced the sorry in `finite_stalk_second_cohomology_retraction` with an explicit
finite-filtration induction. The proof obtains trace injection data, proves each terminal
cohomology group subsingleton, and supplies their dependent product as the codomain.
The original theorem signature, public imports, and existing docstrings are unchanged.
Added a private, proved helper `subsingleton_H_of_iso`, which transfers subsingletonness
using `Sheaf.H.map` and the inverse-isomorphism identities.

Two new modules isolate strictly different parts of the argument:
`Sheaf.AlgebraicGeometry.Curve.GenericFiniteTraceFiltrationData` constructs the injection
and prime constant filtrations without assuming constant-sheaf vanishing;
`Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep` propagates vanishing through
one short exact sequence without assuming finite stalks or constructing any trace.
The item module now has only these two proof imports. Its node records the new route.
The second reader restored the constituent proof-dependency imports in the two new
modules, so their planned supporting obligations remain in the import-based queue.

All three modules compiled cleanly with `lcompile.py --all`.

## Proved and sorry left

`finite_stalk_second_cohomology_retraction` is proved. The intermediate theorems `exists_generic_finite_trace_filtration_data` (node `lem-sc-generic-finite-trace-filtration-data`) and `subsingleton_generic_prime_filtration_step` (node `lem-sc-generic-prime-filtration-step`) remain as named sorries.

## No longer needed

Removed these proof imports from the item:

- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity`
- `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`
- `Sheaf.RepresentationTheory.SylowModuleFiltration`
- `Sheaf.FieldTheory.OpenSubgroupFixedField`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTrace`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree`
- `WeilConjectures.SixFunctors.Finite.GlobalSections`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison`
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `Sheaf.AlgebraicGeometry.NormalGenericConstant`

The thirteen existing proof dependency nodes remain needed below the new obligations.
They are reassigned to the appropriate new node, not claimed as globally pruned.
`RootsOfUnity` is unnecessary in this reduction. `EtalePoint` is a statement dependency
of the trace-filtration data module and is publicly imported there. No existing module
or node is asserted to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The old node compresses all three paragraphs into one step. Existing declarations cover
the constituent tools but not the intervening sheaf filtration and trace constructions.
The reduction exposes two independently provable obligations rather than restating the
original conclusion. The general affine vanishing theorem cannot be used here:
`import_direction.py may` confirms it already reaches this module.

The Sylow lemma supplies finite trivial vector-space quotients, not necessarily rank-one
quotients. The trace-data obligation explicitly refines each by a basis. Generic direct
image is only left exact: the prime-step obligation handles its cokernel defect using
generic acyclicity and two long exact sequences, rather than assuming exactness.

Edge cases checked: the zero module can use an empty family of models; length-zero
filtrations start and end at zero; the prime-step lemma allows arbitrarily large first
and middle terms, since its cokernel defect is a quotient of the uniformly ell-killed
third direct image. Primes equal to the characteristic are allowed throughout.

WANTED: the local copy of
`literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd-affine/lem-sc-affine-generic-second.md`,
proof paragraphs 1--3, is absent on this machine. The source reference is inherited from
the existing nodes; the expanded argument was written by the worker from their proof
texts and is marked `proof_origin.by = agent`.

## New nodes

`lem-sc-generic-finite-trace-filtration-data` records finite primary decomposition,
Sylow rank-one refinement, trace retraction, and finite-normalization cohomology transfer.
Its module is `lean/Sheaf/AlgebraicGeometry/Curve/GenericFiniteTraceFiltrationData.lean`.

`lem-sc-generic-prime-filtration-step` records one short exact filtration step, normal
generic constant comparison, and generic cokernel acyclicity. Its module is
`lean/Sheaf/AlgebraicGeometry/Curve/GenericPrimeFiltrationStep.lean`.

Each has the full argument in its docstring, a source, three search records, and an
unchanged-unit blueprint ancestry. No definition or existing statement changed, so no
change record or downstream adaptation is required.


## Second reading by M1

1. Compared GenericFiniteSecondReduction.lean with the repository version using diff.
   Both existing public theorem signatures and their docstrings are byte for byte
   unchanged; no definition or target was changed. The private isomorphism helper is
   proved and appears in no public signature. No change record is required.
2. Compiled all three modules locally in import order. The only remaining sorries are
   exists_generic_finite_trace_filtration_data and
   subsingleton_generic_prime_filtration_step, in their own public named theorems.
   Scratch copies with #print axioms confirmed only propext, Classical.choice,
   Quot.sound and sorryAx. No axiom, unsafe, opaque, implemented_by, extern or hollow
   definition occurs. The main proof really inducts over every finite chain: the zero
   case uses mapped IsZero, and the successor transfers H² along both isomorphisms
   and applies the prime-step theorem. The final injection has the dependent product
   of terminal groups as codomain; its Subsingleton instance follows pointwise.
3. Read both new statements and docstrings against their JSON nodes and the existing
   constituent declarations. The trace statement drops hconstant entirely and ends
   with filtered terminal groups, so it is genuinely the construction part rather
   than the item's conclusion renamed. Finite primary decomposition, the Sylow
   prime-to-ell subgroup, rank-one refinement of each trivial finite vector-space
   quotient, fixed field, degree trace splitting, and exact finite pushforward give
   exactly its clauses. Zero summands are omitted; the zero sheaf uses the empty
   product, and repeated zero quotients are removed before rank-one refinement.
   The prime-step theorem assumes one short exact generic sequence and constant H²
   vanishing, with no finite-stalk or normalization-model assumption. Left exactness
   yields the two image short exact sequences. Its cokernel is ell-killed and has
   zero generic restriction; continuity gives locally generically vanishing sections,
   so generic acyclicity applies. Smooth finite-type integral D is normal Noetherian,
   allowing normal generic constant comparison. The two long exact sequences then
   give H²(I)=0 and H² of the middle direct image zero. Checked length-zero and
   length-one chains, arbitrary first and middle terms, and ell equal to char k.
   Independent searches used LeanFinder for generic image/short-exact vanishing,
   Loogle for Sheaf.H.map (unknown identifier; no usable result), msearch grep for
   prime filtration/trace injection/generic subsingleton, and rg on the curve,
   Sylow, and cohomology modules. The existing cohomology exact-sequence lemmas supply
   constituent tools but neither new obligation; no duplicate was found.
4. Read from the unchanged target downward, the upstream Affine.lean generic-extension
   docstring and proof, GenericComparison.lean generic acyclicity, and
   NormalGenericConstant.lean. The general affine generic theorem reaches this item,
   so applying it back here would be circular. No shortcut closing either split in
   a few minutes was found. The blueprint source file itself is absent locally, as
   the worker reports; I do not claim to have read it. The inherited source argument
   is corroborated by those upstream declarations and the original DAG proof.
   The unit sk-prop-cd-affine.json has empty realized arrays, which remain unchanged;
   the constant-vanishing assumption and finite trace/filtration route are kept.
   No old proof-dependency node is globally pruned: all thirteen are retained under
   the appropriate split, with RootsOfUnity alone an unused direct proof import.
5. Checked the existing node's proof and proof_deps against the Lean induction and
   both new nodes' signatures, sources, proof origins, ancestry, searches, and lean
   records. New-node proof_deps are exactly the unions of their cited steps. Found
   that the new modules originally lacked their planned dependency imports, so the
   report's claim that supporting obligations stayed reachable was not implemented.
   Restored all those modules as plain imports (the existing public Defs import
   already supplies direct-image left exactness). Clarified continuity before
   applying generic acyclicity in the prime-step docstring and JSON proof. Corrected
   the prime-step module's copied title. No theorem signature was changed.

Second-reading changes: restored constituent proof-dependency imports in both new
modules, clarified the generic-acyclicity hypothesis in the prime-step documentation
and node, corrected that module's title, and added this review. Both split obligations
remain open; the original module's one sorry is replaced by a genuine induction.
