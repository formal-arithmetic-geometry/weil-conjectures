## What changed

Proved `AlgebraicGeometry.derived_hom_mayer_vietoris` in
`lean/Sheaf/Paper/DerivedHomMayerVietoris.lean`, with its signature, public imports,
existing definitions and instances unchanged. Added a proof-only import of
`Sheaf.Algebra.Homology.OpenHomTriangleRealization`.

The new module states the geometric part of the argument: a distinguished triangle
and additive identifications of its Hom terms with the local Hom groups, including
the negative-shift overlap term and the two restriction-map identities.
It does not assert Hom exactness. The item proves the connecting map is additive
and proves both implications of both exactness claims by
`Pretriangulated.Triangle.yoneda_exact₂/₃` and the two square-zero triangle identities.
Two proved private helpers identify the generic nested restriction with the existing
one by reflexivity and transport Hom exactness through the additive equivalences.
The latter avoids repeatedly elaborating large sheaf-derived functor expressions.

The generic nested restriction definition in the new module is the same conjugation
construction as `derivedOpenHomRestriction`, with the ring sheaf as a parameter.
Its comparison with the existing definition is proved by `rfl`; the existing
public definition is unchanged. An explicit parameter R and equality hR in the new
statement keep its structure sheaf identical to the original ringed-space setting
without expensive repeated unfolding. All restriction exactness and additivity
hypotheses are supplied by the item's already proved instances.

Updated the item's DAG proof, proof dependencies and proof origin to match this
reduction; added the structural node below it. No change record is needed: no
existing public statement, definition, instance, public import or command changes.

## Proved and sorry left

Proved: `AlgebraicGeometry.derived_hom_mayer_vietoris`
(node `lem-sc-derived-hom-mayer-vietoris`), the only original sorry in the item.
This is a decomposition: one original hole closed, one lower hole added, and zero
net holes removed by this delivery. The item is not yet proved without `sorryAx`.
The private helpers `derivedOpenHomRestriction_eq` and
`hom_exact_of_open_triangle` are fully proved; the generic
`SheafOfModules.openHomRestriction` is a real definition with no sorry.

Remaining sorry added by this delivery:
`SheafOfModules.open_hom_triangle_realization`
in `Sheaf.Algebra.Homology.OpenHomTriangleRealization`, node
`lem-sc-open-hom-triangle-realization`. Its whole proof is `by sorry`; its docstring
and node give the source and geometric argument. The remaining work is construction
of the triangle and coherent additive adjunction/shift identifications, not either
Hom-exactness claim. The completed proof in the item constructs the actual
connecting homomorphism and obtains and transports both factorizations separately.

## No longer needed

No modules pruned; no imports were removed. The old direct dependencies no longer
used directly by the item are `lem-sc-derived-mayer-vietoris-triangle` and
`lem-sc-derived-open-shriek-derived-adjunction`; both remain indirect geometric
dependencies through `lem-sc-open-hom-triangle-realization`. The existing public imports support the unchanged
restriction infrastructure. The original direct proof dependencies
`lem-sc-derived-mayer-vietoris-triangle` and
`lem-sc-derived-open-shriek-derived-adjunction` now occur below the new structural
node; they are still needed there and are not pruned. The generic Mathlib Hom-out-of-
triangle exactness node remains a direct dependency. No blueprint unit statement
or step was bypassed (`sk-thm-picard-duality.realized` has empty entries).

## Where the brief, the DAG or earlier work was wrong

The proposed dependency modules cannot be imported into the item:
`Sheaf.Algebra.Homology.DerivedMayerVietorisTriangle` reaches the item through
`DerivedOpenShriekAdjunction` and `OpenRestrictionAdjunctionExact`, which publicly
imports it for `moduleRings` and the restriction instances.
`tools/import_direction.py may` reports that this import closes a cycle.
A simultaneous extraction of the shared infrastructure would affect many modules;
this delivery instead isolates a structural interface independent of the item's
module. It keeps the original geometric route in the DAG.

The original triangle statement describes its first arrow through composites with
counits. Identifying Hom restriction maps also needs its canonical extension maps
and adjunction compatibility, so the new node explicitly cites the underlying
short-exact sequence node and spells out the unit/comparison calculation.

Searches: LeanFinder returned the underived Mathlib MayerVietorisSquare short
complex results; Loogle found the generic yoneda_exact₂ theorem; grep found its
companions and the already known project statements, but no geometric Hom-map
identification interface. LeanSearch returned Internal Server Error and is recorded
as unavailable. The local Stacks TeX files are absent on this machine; the official
Stacks pages for Tags 08BU and 08BW were read directly. The source argument is
retained, including the extension-by-zero triangle and the derived adjunction.

Edge cases checked in the new statement's proof: an empty member of the cover has
zero extension term; both opens equal to the whole space give the split stalk
sequence M → M ⊕ M → M; zero E or F gives zero Hom groups. No surjectivity onto
the overlap Hom is asserted, and no vanishing of negative Ext is assumed.

## New nodes

`lem-sc-open-hom-triangle-realization`:
`dag/nodes/sec-picard-framework/lem-sc-open-hom-triangle-realization.json`, realized
by `SheafOfModules.open_hom_triangle_realization` in
`lean/Sheaf/Algebra/Homology/OpenHomTriangleRealization.lean`.
It packages the geometric triangle and coherent additive Hom identifications of
Stacks Tags 08BU, 08BT and 08BW. This is a structural part of the argument;
Mathlib Hom exactness and construction of the connecting homomorphism are proved
in the original module. Its dependencies are the original triangle, its underlying
canonical short exact sequence, the derived open adjunction, and exact-functor
factorization for shift comparison. There are no change records.


## Second reading by V2

1. **Existing interface: pass.** Compared the complete module with the repository
   version by `diff` and by extracting each declaration's original source span.
   All 16 existing signatures are byte-for-byte identical. Every previously closed
   declaration body, including `moduleRings`, the restriction definition and the
   exactness/additivity instances, is unchanged. The only new item import is private
   to its proof. No change record or downstream adaptation is needed.
2. **Proof and axioms: pass, with the declared lower hole.** Both files compile locally
   in dependency order without errors or warnings. Scratch `#print axioms` checks
   show only `propext`, `Classical.choice`, and `Quot.sound` for both private helpers
   and both restriction definitions. The item and the geometric realization also
   use `sorryAx`, from the one declared new theorem. No forbidden declarations,
   hollow definitions, hidden holes or partial proofs containing sorry were found.
   The additive boundary map and both directions of each exactness statement are
   proved in `hom_exact_of_open_triangle`; the equality of restrictions is `rfl`.
3. **Split statement: pass as a decomposition.** Independently checked the triangle
   against [Stacks 08BU](https://stacks.math.columbia.edu/tag/08BU), the derived
   adjunction against [08BT](https://stacks.math.columbia.edu/tag/08BT), and the
   application to Hom against [08BW](https://stacks.math.columbia.edu/tag/08BW).
   Its data omit both exactness claims and the connecting homomorphism, which are
   constructed in the item, so it is a geometric part rather than a renamed item.
   The docstring gives the degreewise stalk argument and the adjunction mate
   calculation for the actual nested comparison maps. Checked empty opens,
   coincident whole-space opens, disjoint covers, and zero E or F: the stalk sequence
   is respectively the identity or the split difference/sum sequence, and the shift
   is Hom(A[1],F) = Hom(A,F[-1]). No overlap surjectivity or negative-Ext vanishing is
   imposed. The theorem is true with the stated parameters; hR merely identifies
   the explicit ring sheaf. Construction of these geometric data is substantial
   work and cannot be closed by a short additional proof in this reading.
   Independent LeanFinder search for extension-by-zero adjunctions and derived
   open-cover Hom identifications, Loogle for `Adjunction.homEquiv`, and grep with
   `lowerShriek`, `extensionByZero`, and additive Hom-equivalence terms found generic
   infrastructure, not this geometric theorem. In particular Mathlib's
   `Adjunction.homAddEquiv` supplies the additive adjunction equivalences once the
   geometric functors and adjunction are constructed; it does not replace the hole.
4. **Route and pruning: pass.** The generic Mathlib exactness lemmas are used directly.
   Independently ran `import_direction.py may` for both original geometric modules:
   each import would close a cycle through the item's restriction infrastructure.
   The new interface avoids this cycle and retains those geometric dependencies
   below it. Every original direct dependency is accounted for under No longer
   needed; no library module has been pruned. All public imports in the new module
   support its signatures or definition: exact derived functors, open restrictions,
   the module-sheaf abelian instance, and RingedSpace. In particular FilteredColimits
   supplies the sheafification instances needed by the public derived-category
   signatures, as documented in Mathlib's Sheaf/Abelian module. The unit
   `sk-thm-picard-duality.realized` has empty statement and step entries, and no
   realized unit step is bypassed.
5. **DAG agreement: pass.** The parent proof records the realization, the additive
   boundary, and the two Yoneda factorizations actually used. Its proof_deps are
   exactly the realization and generic Hom-out-of-triangle exactness. The new node
   records the geometric construction and coherent map identifications, with the
   matching Lean signature, source, creation fields, chapter, unit and searches.
   Both proof origins describe this reduction; the unit records are unchanged.

Changed in this reading: repaired two grammatical errors in the new theorem's
proof docstring; explicitly recorded the one-for-one decomposition and the old
geometric dependencies now used indirectly. No Lean proof or signature changed.
