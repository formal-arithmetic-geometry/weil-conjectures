## What changed

Reduced `AlgebraicGeometry.Etale.exists_rawModule_abelianHom_comparison` to invertibility
and naturality of one explicit additive map. Its existing signature and docstring are unchanged.
The item has two new proof-only imports, RawModuleAbelianHomMapIsIso and
RawModuleAbelianHomMapNaturality.

RawModuleScalarPullbackComparison constructs scalar forgetting, its exactness instances,
the canonical inverse-image comparison from Kan extension and sheafification, and the
map of free represented sheaves sending the abelian generator to the module generator.
RawModuleAbelianHomMap constructs the raw comparison by applying exact derived forgetting,
precomposing the source comparison and postcomposing the shift/single/coefficient comparison.
All these data are actual constructions. No witness is selected from a mere existence theorem.
The only inverse used is the inverse of a constructed natural isomorphism.

The parent proof takes `asIso` of this map using componentwise invertibility, then uses
naturality of the same map. The two remaining proof obligations are independent parts:
invertibility does not assert a natural family, and naturality does not assert invertibility.
This is a decomposition, not a complete elimination of the underlying mathematics.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.exists_rawModule_abelianHom_comparison`
(node lem-sbc-raw-module-abelian-hom-comparison), by decomposition.
No sorry remains in the item's module or either construction module.

Added exactly two holes:

- `AlgebraicGeometry.Etale.isIso_rawModuleAbelianHomMap`
  (lem-sbc-raw-module-abelian-hom-map-is-iso).
- `AlgebraicGeometry.Etale.rawModuleAbelianHomMap_naturality`
  (lem-sbc-raw-module-abelian-hom-map-naturality).

Thus one upper hole is replaced by two strictly separate lower obligations; the local
net is -1. Each lower theorem has an explicit source and complete proof in words.
Edge cases were checked in the construction and proof descriptions: q=0 is the sections
adjunction; empty test schemes have zero section complexes; the zero ring introduces no
flatness assumption. Underlying abelian injectivity is not assumed.

## No longer needed

No pre-existing import is removed: all three public imports supply the unchanged statement.
The parent node no longer directly uses
`lem-weil-pbc-injective-module-abelian-acyclic` or
`lem-weil-pbc-inverse-image-composition`; both remain required by the lower nodes.
No original mathematical dependency is declared globally unnecessary. The original
injective-module abelian acyclicity dependency is retained under the invertibility node;
inverse-image composition is retained under the naturality node.
The construction uses the canonical comparisons underlying
`exists_upperStar_forget₂_natIso`, rather than importing and choosing an unconstrained
isomorphism from that existence statement. No restricted-cohomology or continuity comparison
is added as a proof dependency. No modules are pruned from the existing target closure.

## Where the brief, the DAG or earlier work was wrong

The original single proof step combines construction, componentwise invertibility and
compatibility with all pullbacks. The stated acyclicity and inverse-image composition lemmas
do not directly close this Lean statement. The former is in the SheafOfModules encoding,
with a smaller-universe coefficient ring; this item uses constant ModuleCat-valued sheaves
with coefficients in Type (u+1). The remaining invertibility theorem will need to bridge
that encoding/universe difference or prove the same acyclicity for this encoding.
This delivery does not change either existing statement.

Naturality cannot be asserted for arbitrary componentwise isomorphisms; it must refer to a
fixed comparison. The delivered theorem refers to the explicit map, independently of its
invertibility proof. The canonical inverse-image isomorphism is constructed from the same
Kan-extension and sheafification formulas already used by the library.

The unit `sk-lem-failure-field` is unchanged; its realized entries are empty. This split is
below that unit, within the already planned scalar-forgetting comparison.

## New nodes

`def-sbc-raw-module-scalar-pullback-comparison` records the explicit exact scalar-forgetting
functor, canonical inverse-image isomorphism and free generator map in
Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison.

`def-sbc-raw-module-abelian-hom-map` records the concrete derived scalar map in
Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap.

`lem-sbc-raw-module-abelian-hom-map-is-iso` isolates the injective-resolution/acyclicity
argument for componentwise invertibility, in its own module.

`lem-sbc-raw-module-abelian-hom-map-naturality` isolates compatibility of that fixed map
with the five-factor pullbacks, in its own module. No change records or forced adaptations
are needed; existing declarations and public visibility are unchanged.

## Second reading by M4

1. Compared the delivered comparison module with the repository version: the existing
   theorem signature and docstring are byte-for-byte unchanged; only proof-only imports and
   the proof body changed. Verdict: pass.
2. Compiled all five sandbox modules with `lcompile.py --all`; compilation succeeds, and the
   only remaining `sorry`s are the two named split-off theorems. No forbidden declarations or
   hollow definitions occur. Verdict: pass.
3. Checked both split-off statements against their docstrings and DAG nodes. They are true,
   independent obligations (componentwise isomorphism and pullback naturality), with no
   weakened hypotheses or conclusions and no duplicate library declarations. Verdict: pass.
4. Checked the proof route and imports: the comparison uses the fixed explicit map, obtains
   its componentwise `IsIso`, and applies the independently stated naturality theorem;
   the two added imports are proof-only and no old import is unnecessary. Verdict: pass.
5. Checked DAG `proof`, `proof_deps`, `proof_origin`, unit references, and the realized route;
   they agree with the Lean code and preserve the planned scalar-forgetting comparison.
   Verdict: pass.

Scratch-copy `#print axioms` checks show only `propext`, `Classical.choice`,
`Quot.sound`, and upstream/split `sorryAx` for the raw map and comparison; the
canonical pullback isomorphism, free generator map, and finite-colimit instance
have no `sorryAx`. Additional grep and Lean Finder searches found cohomology and
Ext-resolution APIs, but no theorem closing either fixed-map obligation.

Corrected the scalar-construction node to record its actual finite-colimit proof
dependency, and made the parent dependency replacement explicit under
No longer needed. Added this second-reading record. No Lean statements or
definitions were changed during review.
