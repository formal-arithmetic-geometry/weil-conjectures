## What changed

Proved `AlgebraicGeometry.Etale.truncation_exchange_exact_couple_abutment` in
`lean/Sheaf/AlgebraicGeometry/TruncationExchangeAbutment.lean`, preserving the original
signature verbatim. No other existing declarations or public imports changed.

The proof establishes term vanishing and applies `halfPlaneConvergence`. It uses the
already proved `DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app` for
both composites, and constructs the canonical abutment isomorphisms from the diagonal
colimit universal properties. It identifies the transported filtrations with the
canonical truncation images, including the exact inverse-image comparison. Exchange
naturality gives the abutment square and the maps on filtration steps and cokernels.
`derivedCoupleFunctoriality` on the same limiting subobjects gives the infinite-page
map. Explicit isomorphisms on steps give isomorphisms on graded pieces; cancellation
of the epimorphism to the infinite page proves the final compatibility square.

Added only proved private helpers for equality transport, canonical diagonal maps,
vanishing, and transport of image filtrations and graded pieces. Their universe and
category parameters are local to each declaration, preserving the original file-level
elaboration context; the static interface comparison reports no interface changes. All objects defined
in these helpers are explicit constructions, using universal properties and canonical
image factorizations. No object is selected from an unproved mere existence theorem.
The existing couple-morphism theorem is used for its three commutative-square
properties; its existential couple objects are discarded.

Added proof imports `Sheaf.CategoryTheory.DerivedCoupleFunctoriality` and
`WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage`. Retained the existing
proof import of `Sheaf.CategoryTheory.HalfPlaneConvergence`. Updated only `proof`,
`proof_deps`, and `proof_origin` in the existing node
`lemma-weil-pbc-exact-couple-abutment` to describe the implemented route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.truncation_exchange_exact_couple_abutment`
(node `lemma-weil-pbc-exact-couple-abutment`). All private helpers are proved.

Validation: `lcompile.py` compiled the complete module in 29.2 seconds with no errors
or warnings. The original theorem signature was also compared verbatim with the
repository version and is identical.

Holes closed: 1. Holes added: 0. Split-off statements: 0. Sorries remaining in the
item module: none. No other Lean module is changed. This is a proof from existing
library declarations, including `truncation_exchange_couple_morphism`, whose own
unproved obligations remain in its existing module; it does not claim to close
those pre-existing dependencies.

## No longer needed

Removed these nine unused direct proof imports:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`
- `Sheaf.CategoryTheory.Filtration` (duplicate of the retained public import)
- `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.SixFunctors.BaseChange.Derived`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.CategoryTheory.Abelian.Filtration`

The last five are already available through retained public imports. The standalone
exactness proposition is unnecessary because inverse image already has the required
exact-functor instances. The generic proved truncation criterion replaces the
separate right-derived-functor truncation-map theorem. The explicit image formulas
replace any appeal to the hypercohomology-filtration module.

Removed these nodes from this item's proof dependencies:

- `def-weil-pbc-hypercohomology-filtrations`
- `lem-weil-pbc-derived-functor-truncation-iso`
- `prop-weil-pbc-inverse-image-exact`
- `def-sp-etale-dictionary`
- `lem-sp-couple-morphism`

The last node's theorem is not invoked: `derivedCoupleFunctoriality` works with the
limiting subobjects already chosen by convergence. The original public import of
`ExactCoupleMorphism` is retained to preserve the module's exported interface, so
this does not assert that its module leaves the global target closure. The
truncation-couple definitions and all unit-level statements and steps remain used.
No module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable definition was found. The original plan was longer
than necessary at two points: the source library already proves the canonical
truncation criterion for either triangulated composite preserving lower bounds,
and the generic couple-morphism abutment theorem chooses its own colimits and
limiting subobjects. Using the underlying proved functoriality theorem on the
half-plane theorem's chosen subobjects avoids identifying independent choices.
The supplied heterogeneous identifications require explicit equality transport,
especially at total degree `p + (n - p)` and in the degree-zero g map; all such
transport is proved in Lean. No statement, definition, target, or unit route changed.


## Second reading by D2

1. **Existing interface: pass.** Compared the delivered file against the repository
   with `diff` and compared the full theorem signature byte for byte, from the
   declaration name through its conclusion: identical. The interface checker reports
   no changed statements. The only existing public declaration is unchanged; the new
   helpers are private with declaration-local category and universe parameters. No
   definitions, target statements, other modules, or public imports were changed.

2. **Proof and data: pass.** Independently compiled the complete delivered module
   through `lcompile.py`: exit 0, no warnings, 30.1 seconds. Compiled a scratch copy
   ending in `#print axioms AlgebraicGeometry.Etale.truncation_exchange_exact_couple_abutment`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last is
   inherited from existing dependencies, including the still-open exchange-couple
   theorem, and is not a new hole. The delivered source has no `sorry`, custom axiom,
   `unsafe`, `opaque`, `implemented_by`, or `extern`. Read each private helper:
   `canonicalMap` is the actual truncation map with degree transport;
   `canonical_iso` obtains its map from the colimit universal property, which uniquely
   determines it. The two image isomorphisms use the explicit canonical factorization
   and cokernel map. No definition selects arbitrary data from unproved existence.
   The exchange-couple theorem contributes only its three square identities; its
   existential exact couples are discarded.

3. **Split statements: pass, none.** There are no split-off statements or new nodes,
   and all private helpers are proved. Checked the boundary cases in the argument:
   `q < a` kills the upper truncation and layer, `p < 0` uses the layer's lower bound,
   `n < a` is allowed, and every diagonal transport uses the integer identity
   `p + (n - p) = n`. The filtration formulas hold for every integer `p`, with no
   positivity restriction. A fresh LeanFinder search and searches through `lean/Sheaf`
   and the upstream derived-category and filtration files found no direct replacement
   for the whole result or for the canonical comparison glue. The already proved
   PlusDevissage criterion is used directly, rather than restated.

4. **Route and pruning: pass.** Read the proof from vanishing through the final
   epimorphism cancellation. The normalized colimits from `halfPlaneConvergence`
   are reused throughout; `canonicalMap_naturality` supplies the abutment square,
   image-map functoriality supplies the step maps, and cokernel equations supply the
   graded maps. `derivedCoupleFunctoriality` acts on these same limiting subobjects,
   avoiding a second choice of abutments. Checked the original proof dependencies:
   all five removed nodes are explicitly listed under No longer needed. The nine
   removed direct proof imports are also listed there. The retained public
   `ExactCoupleMorphism` import supplies the convergence definitions used in the
   theorem's signature through its public imports; retaining the existing export
   preserves callers' interface. The proof-only additions are plain imports.
   Read `dag/units/sk-thm-properbasechange.json`: none of its realized statement or
   step nodes is removed or bypassed. Truncation couples, exchange, and half-plane
   convergence remain the argument's route.

5. **DAG agreement: pass.** The node differs from the repository only in `proof`,
   `proof_deps`, and `proof_origin`. Its five steps describe the implemented
   vanishing, canonical colimit isomorphisms, transported image filtrations,
   exchange/step/quotient maps, and limiting-page compatibility. Verified that
   `proof_deps` is exactly the union of the step citations. Checked the actual
   signatures of `truncation_exchange_couple_morphism`, `halfPlaneConvergence`,
   `derivedCoupleFunctoriality`, and the PlusDevissage criterion against the uses
   made of them. No new-node obligations or change records are needed.

Second-reading changes: added this independent review and the explicit axiom audit.
No Lean proof or node repair was needed. Holes closed remain 1, holes added 0,
split-off statements 0; no additional proof credit is claimed for this reading.
