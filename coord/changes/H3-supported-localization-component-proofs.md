# AlgebraicGeometry.Etale.supportedProductLocalizationFirst_map

## Reason

The two component-extension statements lacked proofs. The new proofs verify their
support-inclusion and open-restriction squares and assemble TriangleMorphism from
those squares and a separate connecting-map theorem. The latter is a genuine
remaining proof obligation; its module and DAG node include the coefficient-cone
argument and both tensor shift signs.

## Old

Both supportedProductLocalizationFirst_map and supportedProductLocalizationSecond_map
had their existing signatures and proof bodies `by sorry`.

## New

The signatures and all public definition bodies remain verbatim. Both theorem
proofs now construct the three specified components explicitly. Their comm₁ and
comm₂ fields have complete proofs; comm₃ uses supportedExteriorProduct_boundary.
The two map theorems and their distinguishedness wrappers are moved after the
existing helper block so their proofs can use those helpers. Two private proof
imports expose the new support-map and boundary lemmas.

The new support-map theorem is proved via ordinary quotient normalization, derived
tensor comparison naturality, the derived conjugate counit identity, and a generic
adjunction calculation. Its scheme tensor remains explicit to avoid expanding the
native derived monoidal construction. No existing definition is repaired or changed.

## Users

The downstream script reports zero module importers of the item. Each of the two
map declarations is used only by its distinguishedness wrapper in the item.
DAG parents with unfinished proofs continue to need the item and are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | H3 | Same signatures and data; completed component assembly from a smaller connecting-map obligation. |

No other module is adapted. The new public declarations live in new Sheaf modules.

## Status

landed 20261021T120411-L-3883305 2026-10-21 (merge of deliver/H3/Sheaf.AlgebraicGeometry.SupportedProductLocalization)

The two map-node metadata statements also had a circular dependency on their
parent theorem: their entire stmt_deps was
`["lem-pur-supported-product-localization"]`, while the parent proof uses them.
Their old statement was, verbatim:

> For the corresponding supported localization triangles, the three specified supported exterior-product components extend to a morphism of triangles. This is the component-extension conjunct of [lem-pur-supported-product-localization].

Their new statements spell out exactly the original hypotheses and the three
specified maps, citing their definition nodes instead of assuming the parent
assertion. stmt_deps now lists those same definition/context dependencies as the
parent's statement. This repairs the two local graph cycles and changes no Lean
signature or mathematical hypothesis. Other pre-existing cycles farther below
the item are outside this delivery.
