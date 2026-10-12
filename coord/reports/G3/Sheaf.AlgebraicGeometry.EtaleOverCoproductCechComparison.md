## What changed

Proved `AlgebraicGeometry.Scheme.nonempty_etale_over_coproduct_cech_iso` with its
original signature and visibility. The proof constructs a cosimplicial restriction
transformation directly on Mathlib categorical products. Product projection
identities prove naturality for all simplex maps; Mathlib's alternating-coface
functor therefore supplies differential compatibility. Disjoint-cover sections
and the unique singleton-tuple product make its components invertible.

Added the fully proved module `Sheaf.AlgebraicGeometry.EtaleOverCoproductPowerCofan`
with `AlgebraicGeometry.Scheme.etale_over_coproduct_power_isColimit`. It transports
the existing `etale_fibre_product_coproduct` through `Etale.overEquiv U` and product
comparison isomorphisms. The coproduct cofan universal property is explicitly
transported, then forgotten to schemes. Added a private, fully proved
`cofan_sections_isIso` helper to the item's module, deriving open immersions,
monicity, coverage and disjointness directly from a scheme cofan's colimit property.

Both modules compile without warnings through `lcompile.py --all`. No existing
statement, definition or public import was changed. No forced adaptations.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.nonempty_etale_over_coproduct_cech_iso`
(node `new-etale-over-coproduct-cech-comparison`).

The new theorem `AlgebraicGeometry.Scheme.etale_over_coproduct_power_isColimit`
(node `new-etale-over-coproduct-power-cofan`) is fully proved. The private sections
helper is fully proved. No `sorry` remains in either delivered module; no hole was
added or split off. This is one hole closed, zero added, rather than a decomposition.
The proof still uses the existing named statement
`AlgebraicGeometry.etale_fibre_product_coproduct`, which currently contains `sorry`;
that existing geometric dependency is the next work, not a new hole in this delivery.

Edge cases: `I` empty is handled by the same colimit and empty-cover section proofs;
`n=0` is a one-factor product; singleton `I` requires no distinct-index case.
No cover of `U`, affineness or nonemptiness assumption is introduced. Finite large
index types have the required `Small` instances; no universe binder was changed.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.EtaleCoproductCechRestriction`, node
  `lem-sc-etale-coproduct-cech-restriction-bijective`: replaced by the proved generic
  disjoint-cover sections theorem plus the private cofan sections proof.
- `Sheaf.AlgebraicGeometry.EtaleSiteCechComplexComparison`, node
  `lem-weil-pbc-etale-site-cech-complex-comparison`: no chosen `SiteCechComplex`
  is used, so transport from chosen products to Mathlib complexes is unnecessary.

Removed `Sheaf.AlgebraicGeometry.EtaleFibreProductCoproduct` as a direct import of
the item, but it is retained by the new supporting module and its node is still
required. It is not pruned. Retained all original public Mathlib imports.
The chosen-product comparison route and its `SiteCechMathlibComparison` /
`SiteCechComplex` modules are unnecessary on this proof branch; this does not
assert that other target branches no longer use those modules.

The unit `sk-prop-h2` has empty realized statement/step lists, so none of its
mandated realization nodes is bypassed. Only the below-unit coproduct comparison
route changed.

## Where the brief, the DAG or earlier work was wrong

The existing restriction-bijectivity interface takes an index type in `Type u`
and maps to the terminal etale object. It does not directly apply to the item's
`Type (u+1)` family over an arbitrary `U`. The direct categorical-product proof
avoids restating or changing that interface, avoids sheaf transport, and proves
naturality without using the omitted-factor clause of the distribution theorem.

Mathlib formal coproduct categories at different index universes cannot share a
single formal-coproduct morphism between this large family and `Fin 1`.
A natural transformation between their evaluated cosimplicial objects does type
check and preserves exactly the original complexes and coefficient universe.

The Stacks source was read at https://stacks.math.columbia.edu/tag/03OZ, specifically
the disjoint-section equation and the following displayed fibre-product formula.
The finite-product comparison and forgetful-functor transport use existing proved
Lean declarations. Searches: LeanFinder on the complex comparison found only
supporting sheaf lemmas; Loogle on `cechComplexFunctor` found the definition only,
and on `piComparison` found the comparison/projection/preservation lemmas used.
LeanSearch on slice coproduct distribution was unavailable (Internal Server Error).
Repository and Mathlib `rg` found the existing distribution, localization and
proved disjoint-cover theorems; no duplicate of the new categorical cofan statement.

## New nodes

`new-etale-over-coproduct-power-cofan` records the fully proved geometric cofan
transport lemma in `lean/Sheaf/AlgebraicGeometry/EtaleOverCoproductPowerCofan.lean`.
It uses `lem-sc-etale-fibre-product-coproduct` and the already proved localized-site
equivalence `lem-weil-pbc-etale-site-localization-open`. It has no sheaf or complex
conclusion and adds no sorry. The item's node proof and proof dependencies now
match the direct categorical-product Lean proof. No change record is necessary.

## Second reading by G3

1. PASS: compared the existing module and its node with the repository using diff.
   The existing theorem signature, universe, hypotheses, conclusion and visibility
   are byte-for-byte unchanged. All existing public imports are retained. The
   additional public theorem has its own new module and node; no definition or
   existing statement changes, and no change record or forced adaptation is needed.
2. PASS: both delivered modules compile without errors or warnings using
   lcompile.py --all. Scratch copies with #print axioms show only propext,
   Classical.choice and Quot.sound for the private cofan sections helper, and those
   three plus sorryAx for the comparison and product-cofan theorems. The latter
   depend on the existing etale_fibre_product_coproduct hole. Neither delivered
   module contains sorry or forbidden declarations. The isomorphism witness of
   the existing distribution theorem is uniquely determined by its coprojection
   and product-projection equations; no arbitrary data are chosen from existence.
3. PASS: no statements are split off with sorry. Independently checked the new
   geometric theorem for empty I, singleton I and n=0: products have n+1 factors,
   so the empty-family case never introduces a zero-factor power. The supporting
   cofan theorem is strictly geometric, with no sheaf or complex conclusion.
   Additional Loogle search for Cofan and IsColimit finds generic transport results;
   LeanFinder search on disjoint scheme sections finds topological-sheaf and scheme
   structure-sheaf lemmas, not this etale complex comparison. Repository/Mathlib rg
   finds the already used disjoint-cover theorem and no duplicate product-cofan
   result. Checked the related EtaleCoproductRepresentation module, whose private
   sections helper concerns base changes of scheme coprojections, not this cofan.
4. PASS: read the proof top downward. Its direct cosimplicial map treats every
   simplex map, and the alternating-coface functor supplies differential
   compatibility. The existing proved disjoint-cover theorem is used directly;
   product uniqueness and comparison isomorphisms supply the remaining transport.
   No shorter matching library declaration was found. The proof-only imports are
   plain imports; public imports supply the types and instances of the signatures.
   The two unused old dependencies are completely listed under No longer needed;
   fibre-product distribution remains needed through the new module. The unit
   sk-prop-h2 has empty realized statement/step lists, so its route is preserved.
5. PASS: compared the DAG proof steps, proof_deps and proof_origin to both Lean
   proofs. Dependencies name the product cofan, proved disjoint sections theorem,
   existing distribution theorem and localized-site equivalence actually used.
   The new node's statement matches its Lean signature and it has the required
   source, proof, searches, creation, blueprint, chapter, unit and Lean fields.
   Only allowed proof-route fields of the existing node changed.

Second-reading repairs: replaced the comparison theorem's stale natural-language
proof (which described the abandoned sheaf-transport route) by a description of its
actual direct cosimplicial proof; added explicit autoImplicit=false to the new
supporting module. No proof term or statement needed repair. Source checked against
[Stacks Tag 03OZ](https://stacks.math.columbia.edu/tag/03OZ), its disjoint-section
identity and displayed product decomposition. One original hole closed, zero
holes added; the existing distribution hole is not claimed as closed.
