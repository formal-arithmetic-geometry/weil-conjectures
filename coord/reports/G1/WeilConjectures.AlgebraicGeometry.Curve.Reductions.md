## What changed

Closed two of the nine original proof holes, without changing any existing declaration's
signature, definition, public import, or the unit route.

- `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`: obtain the mapped derived
  cohomology colimit from `etaleCohomology_isColimit_of_isFiltered`, transport it along a
  natural Ext/derived comparison, and use Mathlib's concrete filtered-colimit API to prove
  both stage representation and eventual vanishing. The latter compares the representatives
  `y` and `0` and uses the two additive maps' zero identities.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_topologicalKrullDim_le_zero`: in
  degree zero identify the given cohomology map with the conjugate of the canonical
  global-sections pullback. In positive degrees derive vanishing from the existing
  zero-dimensional cohomology theorem and the Ext/derived comparison. Obtain the dimension
  bound on the actual cartesian square through `Spec.map_surjective`, the induced algebra
  structure, `zeroDimensional_baseChange_points`, and `h.isoPullback`. Explicitly prove
  injectivity and surjectivity between the resulting zero groups.

The proved private helper `subsingleton_sheafH_of_dim_zero` chooses the existing
`Scheme.algClosurePoint` family; it has no postponed proof. Added only proof imports to the
item: the two new modules below, `EtaleCohomologyFilteredColimit`,
`ZeroDimensionalBaseChangePoints`, `EtaleCohomologyPullbackDegreeZero`,
`Sheaf.Paper.ZeroDimensionalCohomology`, and the Mathlib filtered-group-colimit and concrete
colimit modules. Updated the two corresponding node proof routes.

All three delivered Lean modules compile together with lcompile.py, without warnings.
The source comparison reports no changed signatures, interface changes, or new public
item declarations. New statements were checked against degree zero, positive degrees,
empty schemes, nonreduced zero-dimensional schemes, arbitrary abelian coefficients,
and arbitrary cartesian squares. Neither new statement assumes torsion or reducedness.

## Proved and sorry left

Complete Lean proofs, relative to the named dependencies:

- `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`
  (`lemma-weil-pbc-curve-filtered-cohomology`).
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_topologicalKrullDim_le_zero`
  (`lem-weil-pbc-zero-dimensional-field-extension`).

The seven original holes below are untouched:

- `AlgebraicGeometry.IsCurve.Assertions.of_shortExact`
  (`lemma-weil-pbc-eight-curve-devissage`).
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_forall_isReduced`
  (`lem-weil-pbc-curve-constructible-reduction`).
- `AlgebraicGeometry.IsCurve.Assertions.of_forall_isReduced`
  (`lemma-weil-pbc-curve-constructible-primary-reduction`).
- `AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_lowerShriek`
  (`lemma-weil-pbc-curve-dense-open-reduction`).
- `AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_forall_lowerShriek`
  (`lem-weil-pbc-curve-dense-open-localization`).
- `AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar`
  (`lemma-weil-pbc-normalization-exact-sequence`).
- `AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite`
  (`lemma-weil-pbc-curve-normalization-constant`).

The delivery adds exactly two named public theorems with `:= by sorry`:

- `AlgebraicGeometry.Scheme.nonempty_sheafH_extDerivedIso`
  (`lem-weil-pbc-sheafH-ext-derived-comparison`). This compares cohomology functors on any
  scheme; it has no colimit, dimension, or field-extension conclusion.
- `AlgebraicGeometry.Etale.bijective_globalSectionsUpperStarMap_of_dim_zero`
  (`lem-weil-pbc-zero-dimensional-pullback-global-sections`). This concerns the underived
  canonical sections map. It supplies only the degree-zero part of the dimension-zero
  argument; positive-degree vanishing and the dimension of the base change are proved
  separately in the item from existing named theorems.

The complete natural-language proofs and source locations are in the new docstrings and
nodes. The closed declarations still transitively depend on the existing sorried continuity,
zero-dimensional-cohomology, base-change-points, and degree-zero comparison statements, as
intended in stage 3. No axiom-free closure of the targets is claimed.

## No longer needed

No existing import was removed, and no entire module is claimed globally pruned: the seven
untouched original declarations still need their planned theory.

For the filtered-continuity declaration, the former proof dependencies not used by the new
Lean argument are `def-weil-directed-colimit-abelian-groups`,
`def-weil-pbc-category-colimit`, `def-weil-pbc-cohomology-pullback`,
`def-weil-pbc-inverse-image`, `lem-pod-separated-finite-type-base-change`,
`lem-weil-pbc-cohomology-pullback-functorial`,
`lem-weil-pbc-inverse-image-preserves-colimits`, and `lem-weil-pbc-qcqs-over-affine`.
The qcqs hypotheses are already in its signature; Mathlib supplies the elementwise colimit
argument; this declaration does not itself assert field-extension compatibility. In
particular `Sheaf.AlgebraicGeometry.EtaleInverseImageColimits` and
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` were not imported for this proof.
The base-change permanence lemma is still used in the dimension-zero argument.

The degree-zero sections/stalk and inverse-image-germ arguments are not pruned: they now
belong to the new global-sections node. Its future proof still needs
`lem-weil-pbc-zero-dimensional-sections-stalks` and
`lem-weil-pbc-inverse-image-stalk-germ`. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing continuity dependency is stated using derived global sections, whereas the
item uses Ext-defined `Sheaf.H`. Applying it directly leaves an interface mismatch; the
new natural comparison records the missing glue and also transports positive-degree
vanishing. An arbitrary family of objectwise isomorphisms would not suffice for continuity:
the comparison must be natural so that the cocone legs remain the specified `H.map` maps.

The existing dimension-zero DAG's proof is usable. Its points theorem is stated for the
canonical algebra-map pullback, but the item allows any Spec morphism and any cartesian
square. The Lean proof explicitly supplies the induced algebra structure and transports
through the pullback isomorphism; it does not add hypotheses to the item.

`Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension` is an existing stronger geometric
result for sheaves of sets on a canonical pullback. Its coefficient category and sections
map do not directly match `globalSectionsUpperStarMap` on abelian sheaves. The new node
keeps the original dimension-zero stalk argument in that existing abelian interface;
forgetting coefficients and comparing the adjunction units is an alternative future route.

LeanSearch returned HTTP Internal Server Error for both new-node queries. The unavailable
searches are recorded honestly, alongside successful LeanFinder, Loogle, and source grep
searches. No mathematical absence verdict is inferred from the unavailable service.

## New nodes

`lem-weil-pbc-sheafH-ext-derived-comparison`, in
`lean/Sheaf/AlgebraicGeometry/EtaleSheafHExtDerivedComparison.lean`, records the natural
comparison from Ext out of the constant integer sheaf to homology of derived global
sections. Its proof uses the same injective resolution on both sides, the constant-sheaf
adjunction, and naturality of resolution lifts. It is a reusable comparison and is strictly
part of both arguments, rather than either original theorem under another name.

`lem-weil-pbc-zero-dimensional-pullback-global-sections`, in
`lean/Sheaf/AlgebraicGeometry/ZeroDimensionalPullbackGlobalSections.lean`, records the
canonical sections comparison from the degree-zero argument of the existing
zero-dimensional-field-extension node. Its proof uses the finite point bijection, product
of germ maps, and inverse-image stalk/germ compatibility. It handles the empty scheme via
empty products. No change record is needed: no existing signature, definition, or public
import changed.

## Second reading by G1

1. **Signatures and visibility.** Compared the delivered reductions module with the repository version. All existing declaration signatures and definitions are byte-for-byte unchanged; the added imports in the reductions module are proof-only imports. The two new modules expose only their newly split theorem statements.
2. **Proof checking.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds without warnings. The reductions proofs contain no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The two split theorems are named public declarations with documented proofs and remain the only intentional `sorry`s.
3. **Split statements.** Reviewed both split statements and their nodes. The Ext/derived comparison is a general natural comparison and is strictly smaller than either target. The dimension-zero global-sections theorem is exactly the degree-zero component and does not restate the field-extension cohomology target. Edge cases (degree zero, positive degree, empty and nonreduced schemes, arbitrary abelian coefficients) are covered by the statements and proof structure. No existing Mathlib or library declaration duplicates either result.
4. **Pruning and imports.** The proof routes use the listed comparison, filtered-colimit, zero-dimensional cohomology, base-change, and degree-zero declarations. The report's former dependencies and unused imports are recorded under “No longer needed”; no unit statement or realized unit step is bypassed.
5. **DAG agreement.** Checked the four changed node records against the Lean declarations and proof dependencies. The two new nodes include source, proof steps, searches, creation metadata, and Lean records; the existing target nodes record the updated proof routes and dependencies. The unit `sk-thm-p1` remains realized.

No further changes were needed in this second reading.
