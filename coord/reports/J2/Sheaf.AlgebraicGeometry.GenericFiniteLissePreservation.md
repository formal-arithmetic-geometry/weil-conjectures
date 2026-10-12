## What changed

Kept the statement of `AlgebraicGeometry.Scheme.exists_dense_open_finite_lisse_preservation` unchanged and proved it by choosing a geometric splitting cover, proving lissity on that cover, and descending to each smaller open. The original blueprint unit's route is retained; its `realized` statement and steps are empty, and no chapter or unit record was changed.

Added four single-statement modules:

- `GenericFiniteSchemeSplitting`: the dense open and scheme-level splitting cover, independent of the sheaf.
- `DisjointUniversalHomeomorphismsLisseImage`: the componentwise local-constancy argument and finite-product assembly. Its conclusion is only local constancy; finiteness of stalks is proved independently.
- `FiniteSplitCoverLisseImage`: proved the inverse-image restriction, finite base-change, composition, and forgetful-functor glue from the existing declarations.
- `LisseEtaleSurjectiveDescent`: proved descent of local constancy and finite geometric stalks.

The main proof extracts the cover and component data, installs etaleness and surjectivity, applies the proved splitting-cover lemma, and applies the proved descent lemma. The split-cover proof constructs the lift of the pullback projection to `g⁻¹(V)`, applies `pullback_finite_locally_constant`, obtains local constancy from the disjoint-component statement, proves finite stalks via `Etale.stalkIsoPi`, `sheafFiberCompIso`, `PreservesProduct.iso`, and `Types.productIso`, and composes four explicit isomorphisms. Its private isomorphism-invariance helper is proved. The descent proof constructs a composite trivializing cover, compares restrictions using the localized-site equivalence and uniqueness of left adjoints, and lifts geometric points to transport finite stalks. Its private helpers are proved.

## Proved and sorry left

Proved the sole original `sorry`:
`AlgebraicGeometry.Scheme.exists_dense_open_finite_lisse_preservation`.

Also proved:
`AlgebraicGeometry.Scheme.isLisse_pullback_finite_directImage_of_split_cover`,
`AlgebraicGeometry.Scheme.isLisseEtaleSheafOfSets_of_etale_surjective_pullback`,
and all private helpers in their modules.

Exactly two delivered declarations retain `sorry`, each as its entire theorem proof:

- `AlgebraicGeometry.Scheme.exists_dense_open_finite_scheme_splitting` in `GenericFiniteSchemeSplitting`, node `lem-weil-pbc-generic-finite-scheme-splitting`.
- `AlgebraicGeometry.Scheme.isLocallyConstant_finite_disjoint_universalHomeomorphism_directImage` in `DisjointUniversalHomeomorphismsLisseImage`, node `lem-weil-pbc-disjoint-universal-homeomorphisms-lisse-image`.

Both have source citations and complete natural-language proofs. They are strictly different parts of the original argument: the first has no sheaf, and the second has no dense-open choice, integral/Noetherian base, or generic statement. Their combination requires the actual finite-base-change glue and etale descent proved in the other modules.

Checked the relevant edge cases: the geometric decomposition permits zero components for an empty source; an empty smaller open permits an empty cover; the zero-component sheaf argument gives the zero abelian sheaf with constant singleton underlying set sheaf. An inseparable component is retained as a universal homeomorphism, not incorrectly treated as an isomorphism or etale morphism. Descent uses surjectivity and etaleness to lift each geometric point.

## No longer needed

No original mathematical dependency is pruned: all six original dependencies are still needed, directly or through the two remaining obligations. The item module imports the scheme splitting, splitting-cover glue, and descent modules instead of importing those six directly. The scheme splitting retains the generic algebra splitting and the finite-integral tool. The disjoint-component statement retains universal-homeomorphism invariance and pullback finite local constancy. The splitting-cover proof also uses the already proved finite-stalk formula to prove finiteness of stalks independently of the remaining local-constancy obligation. The proved splitting-cover glue retains the finite exchange, inverse-image composition, and algebraic-structure compatibility.

Removed the draft proof import `Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction` from `LisseEtaleSurjectiveDescent`: the restriction isomorphism is constructed directly from the site adjunction and uniqueness of left adjoints, so this proof does not need the composition-with-units theorem imported by that module. This does not claim global pruning of that module, which other targets may reach. No existing repository import was removed.

## Second reading by J2

1. I diffed the delivered item module against the repository version. The target declaration and all existing declaration signatures are unchanged; only the target proof and its proof-only imports changed. The four auxiliary modules contain new declarations and are represented by matching new nodes.

2. I compiled all five delivered modules with `lcompile.py --all`. They compile without errors. A search of all delivered modules found no forbidden `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or definition containing `sorry`; exactly the two named split theorems retain `sorry`. Their proofs are whole theorem proofs, with source and natural-language arguments in their docstrings. The target proof is a genuine composition of the splitting and descent results. Explicit `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound`, and the permitted `sorryAx` for the target and splitting bridge; the descent theorem has no `sorryAx`. The delivery probe also checks all declarations.

3. I checked the two split statements against their nodes and edge cases. Scheme splitting is sheaf-independent and allows the empty finite family; the disjoint-component theorem asserts only local constancy and separately handles the empty family. Neither restates the target. Independent LeanFinder queries for radicial components after shrinking and for etale pushforward across disjoint universal homeomorphisms found no equivalent result. Loogle could not resolve the project-specific universal-homeomorphism identifier. Grep and repository searches found no existing equivalent declaration; `SplitNbhd.exists_hom` only splits neighborhoods at one geometric fiber and does not establish universal-homeomorphism components on a dense open.

4. I read the proof dependencies and imports. The item now imports the three auxiliary interfaces it uses. The auxiliary proofs retain the algebra splitting, universal-homeomorphism invariance, pullback local-constancy, finite exchange, and stalk dependencies required by their written proofs. The removed draft restriction import is recorded above. The unit record and route are retained as required.

5. I compared every node's Lean declaration, proof steps, `proof_deps`, and `proof_origin` with the code. The existing target node records the three interfaces used by the final proof; each new node records its exact declaration and dependencies. No statement or definition change record is needed.

I changed only this report section during second reading. The dry run and delivery checks are the final verification steps.

## Where the brief, the DAG or earlier work was wrong

The original plan has the right mathematical route, but its existing declarations do not provide the scheme-level passage from algebraic splitting to lifted disjoint open components, nor a set-sheaf theorem assembling universal-homeomorphism component images into a locally constant direct image. These are the two remaining obligations. The final descent and finite-exchange steps can be completed from existing interfaces and are now proved rather than left as large unnamed glue.

The local clone contains only literature lists and import tools, not the referenced blueprint source text. Reading that path failed and an attempted upstream retrieval returned 404. The proofs in words therefore expand the source argument as already reproduced in the item's node and its existing docstring, and the existing generic algebra splitting, invariance, and pullback docstrings. No unsupported new proof route is introduced. LeanSearch returned an internal-server-error response; LeanFinder, Loogle, and repository/Mathlib searches were used and recorded.

## New nodes

`lem-weil-pbc-generic-finite-scheme-splitting`: the geometric part of original steps 1--2, with every smaller-open restriction included and no sheaf in its statement. This remains an obligation.

`lem-weil-pbc-disjoint-universal-homeomorphisms-lisse-image`: the local-constancy portion of original steps 3--4 for an already decomposed source. Finite stalks have been removed from this intermediate conclusion and proved in the splitting-cover module from the existing finite-stalk formula. This local-constancy statement remains an obligation.

`lem-weil-pbc-finite-split-cover-lisse-image`: the proved bridge from the restricted source hypothesis to the lisse product on the splitting cover, using finite base change and the inverse-image/forgetful comparisons.

`lem-weil-pbc-lisse-etale-surjective-descent`: the proved descent part of original step 5, including finite geometric stalks.

The existing item's node has its proof, proof dependencies and proof origin updated to the Lean composition. No existing statement or definition changed; no change record is needed.
