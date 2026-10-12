## What changed

Replaced `AlgebraicGeometry.Scheme.Modules.counitBaseChange_degreeZero_comparison`'s
whole-proof sorry with explicit comparison isomorphisms and cancellation in a general
commutative square. Its signature, visibility and existing docstring are unchanged.

Added three modules: `CanonicalSinglePullbackComparison`,
`CanonicalSingleDirectImageComparison`, and `CanonicalDegreeZeroMateSquare`, under
`Sheaf.AlgebraicGeometry.Picard`. The first two construct real canonical morphisms and
prove their invertibility from existing library results. The third constructs the H^0
isomorphism from the existing unbounded/classical right-derived comparison and states
one remaining compatibility square. All data constructions use fixed derived counits,
right-derived units or uniqueness of adjoints; no arbitrary existence witness is used.

The reduction keeps the original unit route. It uses the original proof's flat pullback,
nonnegative injective-resolution, and mate-compatibility steps. The new square holds
without invertibility, higher vanishing, invertibility of M, or even cartesianness.
It is strictly a compatibility step; the final proof separately supplies invertibility
and constructs the requested isomorphisms.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.counitBaseChange_degreeZero_comparison`
(node `lem-pc-counit-base-change-degree-zero-comparison`). This is a decomposition,
not a claim of a sorry-free target: one hole closed and one strictly smaller hole added.

Also proved:
`AlgebraicGeometry.Scheme.Modules.isIso_canonicalSinglePullbackMap`
(node `lem-pc-canonical-single-pullback-comparison`) from the existing canonical
flat-module comparison theorem; and
`AlgebraicGeometry.Scheme.Modules.isIso_canonicalSingleDirectImageMap`
(node `lem-pc-canonical-single-direct-image-comparison`) using
`Functor.quasiIso_map_of_rightAcyclic`, K-injectivity of the nonnegative injective
resolution, and naturality of the unbounded right-derived unit.

The only delivered sorry is
`AlgebraicGeometry.Scheme.Modules.canonicalDegreeZeroMateSquare`
(node `lem-pc-canonical-degree-zero-mate-square`). It is exactly the whole proof of
that public theorem, with its complete argument and source in the docstring.
There are no remaining sorries in the original module, no hollow definitions, and
no new axioms. Existing imported statements with sorry remain the next items.

## No longer needed

Removed direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`
- `Sheaf.AlgebraicGeometry.DegreeZeroCohomology`
- `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`

`Sheaf.AlgebraicGeometry.DegreeZeroCohomology` and node
`lem-pc-degree-zero-properties` are genuinely bypassed: Mathlib's
`DerivedCategory.singleFunctorCompHomologyFunctorIso` and the existing source
`Functor.homologyRightDerivedFunctorObjSingleFunctorIso` provide the necessary
identifications directly. No theorem of DegreeZeroCohomology is used anywhere in
this delivery.

The other four removed direct imports remain needed transitively for their actual
constructions or the flat-module comparison; their nodes are not claimed pruned.
The original node's direct proof dependencies now name the three new comparison nodes.
Both existing public imports remain unchanged.

For completeness, all six old direct proof dependencies are accounted for:
`lem-pc-degree-zero-properties` is bypassed;
`lem-pc-flat-complex-derived-pullback` remains through the flat-module comparison;
`def-pc-derived-direct-image` remains through the direct-image constructions;
`def-pc-derived-base-change-map` remains in the square's explicit morphism;
`lem-pc-ringed-spaces-derived-pullback-composition` remains in the pinned pullback
map and composition compatibility; and `lem-pc-module-pullback-adjunction` remains
in the tensor-to-ordinary comparison and the mate. The latter five are not claimed
pruned from the transitive route.

The second reader narrowed the new modules' public imports. The pullback module
now publicly imports DerivedPullbackComposition and the invertible-sheaf interface;
FlatModuleCanonicalDerivedPullback supplies the proof's cohomology support privately.
The direct-image module publicly imports SchemeDerivedDirectImage and Mathlib's
ordinary right-derived interface, and imports EnoughInjectives privately for its
resolution proof. The square explicitly imports SchemeDerivedBaseChangeMap and
EnoughInjectives publicly because its statement and H^0 construction use them.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies did not state either the right-derived unit's invertibility
on a module with vanishing higher images or the compatibility square for the pinned
canonical constructions. Existing acyclic-resolution theory proves the former;
the latter is isolated as the one remaining step instead of duplicating the full
existential conclusion. No mathematical error in the original statement was found.

The local `literature/stacks-project/cohomology.tex` file is absent. Read the cited
source online at Stacks Tags 08HY, 079V and 06YD. In particular Section 079V,
Lemma 20.28.6 gives the derived/ordinary counit diagram used in the new square.
The original ZeroScheme docstring was also read. The zero module, empty schemes,
identity morphisms and noncartesian commutative squares introduce no additional
hypotheses in the new comparisons; no nonzero module or point is chosen.

## New nodes

`lem-pc-canonical-single-pullback-comparison`: fixes the exact counit used in
canonical derived composition and proves its ordinary single-module comparison
invertible on invertible modules. This node's theorem is proved from the existing
flat-module canonical comparison, not left with sorry.

`lem-pc-canonical-single-direct-image-comparison`: constructs the canonical unit
`(f_*M)[0] → Rf_*(M[0])` and proves it invertible when positive ordinary derived
images vanish, without any flatness or invertibility hypothesis. The proof uses
existing acyclic resolution theory.

`lem-pc-canonical-degree-zero-mate-square`: the one remaining theorem, a naturality
square for arbitrary modules and commutative scheme squares. It provides no
invertibility conclusion. Its docstring gives the derived adjunction, composition,
and injective-resolution compatibility argument.

New-interface change record:
`coord/changes/Q2-canonical-degree-zero-comparisons.md`.

## Second reading by Q2

1. **Existing interfaces: PASS.** Compared every delivered module with the repository.
   The three comparison modules are new. The item's diff changes only its proof and
   private proof imports; its existing theorem signature, visibility, docstring and
   two public imports are byte-for-byte unchanged. No target or existing definition
   was edited. The new interfaces have the supplied change record.
2. **Kernel and holes: PASS.** Compiled all four modules in import order with lcompile.py,
   without errors or warnings (17.8, 23.7, 5.3 and 10.2 seconds respectively).
   Scratch copies with `#print axioms` checked all eight delivered declarations:
   only `propext`, `Classical.choice`, `Quot.sound` and imported/local `sorryAx` occur.
   Scanned the sources for forbidden declarations and attributes. The sole local
   sorry is the whole proof of public theorem `canonicalDegreeZeroMateSquare`.
   The maps are explicit counit/unit composites, the tensor-to-ordinary isomorphism
   comes from uniqueness of adjoints, and H^0 uses existing resolution comparisons.
   No arbitrary witness of mere existence or hollow definition was introduced.
3. **Split statement and search: PASS.** Read the square against the pinned data in
   SchemeDerivedBaseChangeMap and DerivedPullbackComposition, the source's PlusSingle
   and PlusCompatibility constructions, and Stacks Tags 08HY and 079V, especially
   Lemma 20.28.6. The pullback counit, derived adjunction and composition comparison
   use the same choices. The H^0 identification respects the right-derived unit by
   rightDerivedUnique and the injective-resolution augmentation. The square is true
   for arbitrary modules and commutative squares; it asserts no invertibility.
   Zero modules make both maps zero; empty schemes have the zero module category;
   identity morphisms reduce to the counit/unit identities. Neither cartesianness
   nor flatness is needed for compatibility. Its source, full docstring argument
   and node are present. Independent leanfinder search for total/classical derived
   augmentation compatibility, Loogle search for derivedε_fac_app, and grep for
   acyclic-unit and single/base-change comparisons found generic derived-unit and
   adjunction tools, not this square. Local searches also found CompConjugate and
   the existing finite-sheaf adjunction argument, neither of which states this
   non-exact tensor-pullback comparison. The remaining square is strictly the
   compatibility part: invertibility and both requested isomorphisms are constructed
   separately in proved declarations. Closing it requires further formalizing these
   lift and augmentation compatibilities, not a short application found in review.
4. **Route and pruning: PASS after import repair.** Checked the reduction from the
   top down: it uses the existing flat-module comparison, the source's acyclic
   resolution theorem, the source's H^0 comparison, then categorical cancellation.
   All old proof dependencies are accounted for under No longer needed. Only the
   degree-zero-properties node is bypassed; the other five remain transitively.
   The unit record sk-thm-picard-f-representable has empty realized statement/step
   lists, and this reduction keeps the original flat-pullback, injective-resolution
   and mate-compatibility route. No unit or chapter record changed.
5. **DAG agreement: PASS after record repair.** Checked all four nodes' proof steps,
   proof_deps and proof_origin against the Lean; each dependency list is precisely
   the union of its steps' uses. The three new nodes have the required source,
   searches, creation record, blueprint ancestry, chapter/unit and Lean record.
   Replaced their flattened lean.statement strings with the theorem signatures
   verbatim from their modules. Existing non-stage-3 node fields were not changed.

Second reading changed only the new modules' imports (narrowed public dependencies,
kept proof support private, and made the square's actual dependencies explicit),
the three new nodes' verbatim signature records, and this report's complete dependency
accounting. The mathematical statements and proofs were retained. The original
hole closed and the new compatibility hole added give a decomposition with net zero
local holes, not a sorry-free target proof.
