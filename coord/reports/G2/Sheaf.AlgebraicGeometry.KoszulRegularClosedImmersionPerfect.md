## What changed

The statement of `AlgebraicGeometry.koszulRegular_closedImmersion_perfect` is unchanged.
Its proof now compiles without an internal hole. It converts the existing normalized
`ExteriorAlgebra.exists_koszul_quotient_augmentation` from integer cochain complexes to
natural-number chain complexes using Mathlib's fully faithful extension functor and
`quasiIso_extendMap_iff`. Mathlib's exterior-power instances prove every term finite free;
the empty exterior-power basis above the sequence length proves the vanishing bound,
without a nontrivial-ring hypothesis. The proof constructs a `ProjectiveResolution` with
that very Koszul complex and uses it directly in the definition of perfect immersion.

Two new modules state the remaining geometric bridges for arbitrary input resolutions:
`Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification` and
`Sheaf.AlgebraicGeometry.AffineFiniteFreeResolutionPerfectModel`. The former accepts an
algebraic quotient augmentation and returns its sheafified quasi-isomorphism. The latter
accepts a bounded finite free complex and a sheafified quasi-isomorphism, and returns a
strictly perfect representative on one specified open. Neither assumes Koszul regularity
or asserts the global conclusion of the item. The main proof combines these bridges with
the proved term calculations, the existing augmentation, and the given open covering.
All new proof imports in the main module are non-public. No definition or existing
statement was changed. The item's DAG proof now follows the Lean proof.

Mathlib searches were run through msearch in all three required kinds. LeanSearch returned
HTTP 500 and is recorded as unavailable. LeanFinder found projective resolutions and
bounded derived representatives, but no affine quotient comparison or strictly perfect
localized-site model. Loogle returned no hit for the exterior-power query; source search
found and used `Module.Basis.exteriorPower`, `exteriorPower.instFree`, and
`exteriorPower.instFinite`. Searches in both library roots found the existing augmentation
and no theorem with either new bridge's signature. The relevant source pages read were
Stacks Tags 068C, 08C4 and 08CM. The local literature checkout is absent on this machine,
so these pages were read online.

Edge cases: the term proof handles `r=0`, the zero ring, and empty exterior-power index
types without excluding them. The global proof is pointwise and handles an empty target
scheme vacuously. The first new bridge also allows unbounded complexes and arbitrary
ideals, including the unit ideal; exact localization and the quotient presentation still
apply. The second allows rank-zero terms, a zero sheaf, and `r=0`; extension has support
in `[-r,0]`, so the resulting interval remains valid in each case.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.koszulRegular_closedImmersion_perfect`
(node `lem-sc-koszul-regular-closed-immersion-perfect`).
No `sorry` remains in the item's module. This is a decomposition, not an unconditional
proof of the target: one upper hole is closed with two new lower holes.

Added holes, each a complete named theorem with proof exactly `by sorry`:

- `AlgebraicGeometry.exists_affine_quotient_sheafified_resolution`
  (node `lem-sc-affine-quotient-resolution-sheafification`).
- `AlgebraicGeometry.exists_affine_finite_free_perfect_model`
  (node `lem-sc-affine-finite-free-resolution-perfect-model`).

The imported existing theorem `ExteriorAlgebra.exists_koszul_quotient_augmentation`
(node `lem-sc-koszul-regular-sequence-dual-complex`) still has its existing `sorry`.
It is reused unchanged; no new algebraic augmentation hole was introduced. The direct
term freeness, finiteness, vanishing, extension conversion, projective-resolution
construction, covering argument, and conjunction assembly are proved in the item.
The existing augmentation node is a tool from the same blueprint unit, and only its
augmentation declaration is used, not its conormal-duality conclusions. That module has
several unrelated declarations; this delivery does not claim to prove those declarations.

All three delivered modules compile cleanly with lcompile.py --all.

## No longer needed

Removed the direct proof import `Sheaf.Paper.KoszulComplex`: its definitions are already
publicly imported through `Sheaf.RingTheory.KoszulRegularSequence`, and the direct import
was redundant. The node `def-weil-pbc-koszul-complex` remains required by the statement
and the term calculations; its module is not pruned from the target closure.

Removed from the item’s old `proof_deps`: `def-weil-closed-immersion` and
`def-weil-pbc-koszul-regular-sequence`. Both remain in `stmt_deps`; their content is
now used through the given quotient presentation and the existing augmentation.
Neither definition module is pruned from the target closure.

No mathematical dependency module is claimed pruned. The original closed-immersion,
Koszul-regularity, Koszul-complex and perfectness definition nodes all remain in the
statement closure. The proof no longer asks a worker to reconstruct the augmentation,
finite free terms, the bound, or the perfect-immersion assembly inside this item: it reuses
an existing augmentation and proves the remaining algebraic steps directly. No unused
new proof import remains in the main module.

## Where the brief, the DAG or earlier work was wrong

The original DAG marked its full sheafification and localized-site representative steps
as elementary while citing only definitions. Those are substantial Lean bridges between
module complexes, scheme-restricted sheaves, and localized-site sheaves. They are now
explicit new statements with full proof sketches and nodes, rather than hidden inside
an upper `sorry`. The mathematical statement itself was not found false.

The existing augmentation uses integer-indexed cochain complexes, whereas this item
requires natural-number-indexed chain complexes. Mathlib's fully faithful extension
functor resolves this mismatch without a changed statement or an additional hole.

The unit `sk-thm-picard-duality` has no realized nodes in its recorded statement/step
lists; the delivery preserves the diagonal finite-duality route of the item's blueprint
ancestor and does not bypass a unit. The absence of local literature files required
reading the cited Stacks pages online. The older delivery-errors file has no section I.

## New nodes

`lem-sc-affine-quotient-resolution-sheafification`, in
`dag/nodes/sec-picard-framework/lem-sc-affine-quotient-resolution-sheafification.json`,
states sheafification of an arbitrary quotient augmentation on one affine closed-immersion
chart. Its proof separates the quotient pushforward identification from preservation of
homology through exact localization and stalk detection. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineQuotientResolutionSheafification.lean`.

`lem-sc-affine-finite-free-resolution-perfect-model`, in
`dag/nodes/sec-picard-framework/lem-sc-affine-finite-free-resolution-perfect-model.json`,
states passage from an arbitrary bounded finite free chart resolution of a sheaf to a
strictly perfect complex on the localized open site and a derived restriction isomorphism.
Its proof details extension to negative degrees, finite bases, the open-site equivalence,
and localization of the given quasi-isomorphism. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineFiniteFreeResolutionPerfectModel.lean`.

No change record is required: no existing signature, definition, or public import changed.

## Second reading by G2

1. **Statements and signatures.** I diffed the delivered main module against the repository
version. The theorem signature of `AlgebraicGeometry.koszulRegular_closedImmersion_perfect`
is byte-for-byte unchanged. The two added theorem signatures are exactly the corresponding
DAG node statements: the first is an arbitrary nonnegative quotient resolution with no bound
or finiteness assumption, and the second is a bounded finite-free affine resolution producing
a local strictly perfect model. Their hypotheses include the derived-category instances,
closed-immersion quotient presentation, quasi-isomorphism, and all edge cases (`r = 0`,
rank-zero terms, and the zero ring).

2. **Proof and axioms.** I compiled all three delivered modules with
`lcompile.py --all`; there are no errors or warnings. The main proof closes its original
`sorry`: it proves exterior-power freeness and finiteness, the vanishing bound, converts the
existing normalized augmentation through `embeddingDownNat`, builds a projective resolution,
and assembles the affine and pointwise clauses. The two geometric bridge theorems remain
intentional named `sorry` declarations listed above, each with a source, proof docstring,
and DAG node. An axiom probe reports only the permitted standard axioms plus `sorryAx`, the
latter arising solely through those two imported split statements and the existing
augmentation theorem.

3. **New statements.** I searched the library and Mathlib by declaration names and by the
concepts “affine quotient resolution”, “tilde quasi-isomorphism”, and “bounded finite-free
strictly perfect model”; no existing declaration has either bridge signature. The first new
statement is strictly smaller than the item because it only transports one given augmentation
and does not assert perfectness. The second is strictly smaller because it only constructs one
local model from one given bounded resolution and does not assert global perfectness. Their
proof sketches cite the quotient identification, stalk localization and exactness, finite
basis comparison, and derived localization statements recorded in their nodes. I checked
small cases in the node arguments: the zero ring and zero terms are allowed, and an empty
exterior-power index for `r < n` gives the zero object.

4. **Imports and DAG route.** The proof-only imports added to the main module are
`ExteriorPower.Basis`, `Embedding.ExtendHomology`, the existing normalized Koszul augmentation,
and the two bridge modules. The old direct `Sheaf.Paper.KoszulComplex` import is removed as
redundant. The DAG proof and `proof_deps` now follow the actual route: existing augmentation,
Mathlib exterior-power basis/instances, the quotient bridge, the perfect-immersion definition,
and the local perfect-model bridge. The unit route is retained; no unit statement or target
statement was changed. No definition is hollow and no public statement was altered.

5. **Source and edge-case review.** I read Stacks Tags 068C, 08C4, and 08CM. Tag 068C
states that a Koszul-regular immersion is perfect via a finite free Koszul resolution;
08C4 defines strictly perfect complexes as bounded complexes of finite free summands; and
08CM gives the local derived definition of perfectness. The Lean proof matches these clauses
and does not add Noetherian or nonzero hypotheses. The `r = 0` and empty-target cases are
handled by the same construction. I changed only this report: added this second-reading
record and explicitly listed the two removed old proof dependencies under
`## No longer needed`. No Lean declarations, node statements, or definitions changed.
