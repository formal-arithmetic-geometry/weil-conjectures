## What changed

Reduced `AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap` to compatibility
of the fixed comparisons with a single adjunction counit and with the pullback square.
The private categorical lemma proves the mate-transport calculation from these identities
using naturality and `mateEquiv_counit`.

Validation: all four delivered modules compiled in import order; the four direct theorem
consumers compiled unchanged against the sandbox outputs. A declaration-by-declaration
comparison confirms all seven original signatures are identical, all five definition
bodies are identical, and the existing smooth-base-change proof is identical.

The five existing comparison-isomorphism definitions were moved verbatim to
`Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons`, publicly imported
by the item. This permits the two compatibility statements to import their definitions
without an import cycle. Names, signatures, visibility and constructions are unchanged.

## Proved and sorry left

One original hole is closed: `AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`.
Two holes are added, so this delivery is a decomposition, not a net proof:

- `AlgebraicGeometry.ProEtale.comparison_counit`: compatibility of a single edge's fixed
  right-derived direct-image comparison with its fixed left-derived pullback comparison.
  What remains is identifying the right-derived transformation with the mate of the
  pullback comparison, including the bounded-below/unbounded compatibility maps.
- `AlgebraicGeometry.ProEtale.comparison_square`: compatibility of the four pullback
  comparisons with the canonical square maps. What remains is descending the equality
  of the underived restriction-square maps through exact derived functors and their
  composition isomorphisms.

Edge cases checked: neither obligation asserts that an arbitrary exchange map is an
isomorphism; pullback needs no quasi-compactness because it is exact here. Identity
morphisms and the zero coefficient ring give the canonical identity/trivial equations.

Both are strictly parts of the argument: the first involves one morphism and no square;
the second involves pullbacks only and no direct images or exchange map. There are no
holes in definitions or in the private categorical calculation.

## No longer needed

The new proof replaces the following original direct proof obligations with existing
source-library definitions or proved Mathlib calculus; their separate Sheaf modules are
not imported by this proof:

- `def-weil-pbc-adjunction-mate`
- `def-weil-pbc-ambient-ringed-exchange`
- `def-weil-pbc-cartesian-square`
- `def-weil-pbc-derived-exchange`
- `def-weil-pbc-proetale-operations`
- `def-weil-pbc-site-comparison-morphism`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-module-abelian-derived-exchange-compatibility`
- `lem-weil-pbc-proetale-derived-pullback-composition`
- `prop-weil-pbc-proetale-constant-exact`
- `prop-weil-pbc-proetale-constant-ring-map`

The two comparison-coherence nodes remain relevant through the new obligations:
`lem-weil-pbc-comparison-direct-image-canonical-mate` and
`lem-weil-pbc-comparison-pullback`. No UNIT statement or its required proof route is bypassed:
the counit normalization, square coherence, and explicit transpose comparison are retained.

The item needs no proof import of `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
`Sheaf.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility`,
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, or
`WeilConjectures.SixFunctors.BaseChange.Derived`. These were exploratory imports and
are absent from the final item. No existing module is withdrawn.

## Second reading by G1

1. **Signatures.** I compared the item module with the repository version. Every existing
   declaration signature is unchanged byte for byte; the five moved comparison definitions
   are unchanged in body and interface. The two new modules contain only the explicitly
   split obligations recorded by their nodes.
2. **Proof status.** The item and all four delivered modules compile in import order. The
   transport theorem is proved without `sorry`; the only remaining `sorry`s are the named
   `comparison_counit` and `comparison_square` split-offs. No definitions contain `sorry`,
   and no forbidden axiom or unsafe declaration was introduced.
3. **New statements.** The counit and square statements are true, strictly smaller parts of
   the transport argument, and are needed by its proof. Neither duplicates the item theorem;
   the first is a one-edge counit identity and the second is pullback-only coherence.
4. **Pruning and route.** The proof uses the generic mate calculus and the fixed comparison
   constructions. The exploratory imports and their unused dependency nodes are removed as
   listed above; the unit’s counit, square, and transpose route remains intact.
5. **DAG agreement.** The item and split-node `proof`, `proof_deps`, and `proof_origin`
   records match the Lean proof and docstrings. The relocated definitions are recorded by
   `def-weil-pbc-fixed-derived-comparisons`, with the placement change documented separately.

I changed only the report by adding this review record; no mathematical or interface repair
was needed during second reading.

## Where the brief, the DAG or earlier work was wrong

Some updated DAG dependency records point to comparison modules not present in this
checkout. Their older available alternatives do not directly express the fixed derived
comparisons in this module. The two new obligations state precisely the one-edge counit
normalization and the square coherence that the transport proof needs.

## New nodes

- `stage3-proetale-comparison-counit`
- `stage3-proetale-comparison-square`
- `def-weil-pbc-fixed-derived-comparisons` records the relocated data, with no new hole.

Change record: `coord/changes/G1-proetale-comparison-definition-placement.md`.
