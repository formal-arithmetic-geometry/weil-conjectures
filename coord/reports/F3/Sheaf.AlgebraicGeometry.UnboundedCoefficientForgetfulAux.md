## What changed

Proved `AlgebraicGeometry.isIso_restricted_derivedBaseChangeMap_iff` in
`Sheaf.AlgebraicGeometry.UnboundedCoefficientForgetfulAux`, with its signature unchanged.
The proof uses the existing `Etale.unbounded_abelian_exchange_comparison` for both rings.
Proved private helpers normalize the `L(g*)` exchange to the exact `D(g*)` exchange,
cancel the comparison isomorphisms, and identify restriction followed by forgetting
with direct forgetting. No new assumption, public declaration, or module is introduced.

Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` for the proved
composition and inverse laws of `mapDerivedCategoryNatIso`. Updated the existing node's
proof and proof origin to describe the Lean argument; its proof dependency is unchanged.

The module compiles without warnings through `lcompile.py` (40.2 seconds before final
comments). The required delivery dry run also checks the axiom probe and packaging.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.isIso_restricted_derivedBaseChangeMap_iff`
(node `lem-kun-proper-base-change-forgetful-aux`).

No `sorry` remains in the delivered module, and no holes are added. All private helpers
are proved. This is a proof from the existing stated dependency, not a decomposition:
`Etale.unbounded_abelian_exchange_comparison` remains an existing dependency whose proof
is outside this item. The delivery does not claim that its transitive axioms are closed.

## No longer needed

None. Every original import is retained and used. The sole original proof dependency,
`lem-kun-unbounded-abelian-exchange-comparison`, remains necessary. No nodes or modules
are pruned, and no new split-off modules are introduced.

## Where the brief, the DAG or earlier work was wrong

The node's intended argument works. Its existing comparison theorem is stated for
`exactDerivedBaseChangeMap`, whereas this item concerns `derivedBaseChangeMap` using
left derived inverse image. The missing normalization is now proved privately in this
module. It is sufficient to transport adjunction mates through the inverse-image
isomorphisms: no unproved equality of the two derived adjunction constructions is used.

The source library's bounded-below restriction theorem does not apply to this unbounded
statement, and its unbounded restriction/direct-image isomorphism assumes flatness.
Neither is used. The local Stacks source file is absent on this machine; Tag 0D6J(3)
was read directly at https://stacks.math.columbia.edu/tag/0D6J, confirming the source of
the existing comparison dependency. No literature or statement change is needed.

## Second reading by F3

1. Interface: PASS. Compared the delivered module and node with the shared repository.
   The existing theorem's signature and docstring are byte-for-byte unchanged. The only
   added declarations are private implementation helpers; the added import is proof-only.
   No definition, public statement, target, or other module is changed, and no change
   record is needed.
2. Proof: PASS. Independently compiled the delivered module through `lcompile.py` without
   errors or warnings (44.5 seconds). A scratch copy with `#print axioms` for every added
   helper and the public theorem also compiled (39.7 seconds). The mate helpers, L-to-D
   normalization, and restriction-forgetting isomorphism use only `propext`,
   `Classical.choice`, and `Quot.sound`. The exact-to-abelian helper and final theorem
   additionally use `sorryAx` through the existing open exchange-comparison dependency.
   No direct `sorry`, forbidden declaration, or hollow definition occurs in the delivery.
   The restriction-forgetting isomorphism is constructed from localization comparison
   isomorphisms and `Iso.refl`, not chosen from an unproved existence assertion.
3. Split statements: PASS (none). No new holes or public statements are introduced.
   Checked the generic mate-transport argument and its orientation against Mathlib's
   two conjugate/mate composition laws. No injectivity, nonzero-ring, flatness,
   properness, or boundedness assumption is hidden: identity ring maps, zero rings,
   noninjective ring maps, empty schemes, and zero complexes require no separate case
   in these functorial isomorphism and conservativity arguments.
4. Route and pruning: PASS. Repeated searches with Loogle (`CategoryTheory.mateEquiv`),
   LeanFinder (invertibility of adjunction mates under isomorphic left adjoints), and
   source searches for coefficient restriction and exact/unbounded exchange. The hits
   supply the Mathlib laws already used; the upstream restriction exchange theorem is
   bounded below, and its unbounded direct-image restriction comparison requires
   flatness. No shorter applicable theorem was found. Both original public imports
   supply the theorem's signature; the existing comparison import and added generic
   coherence import supply the proof. The old `proof_deps` is retained in full, so
   `## No longer needed` is complete. The unit's `realized` record is unchanged; this
   argument retains the original coefficient-forgetting step and dependency.
5. DAG: PASS. The only changed node fields are `proof` and `proof_origin`; the four
   proof steps describe exactly the normalization, restriction conservativity,
   cancellation, and naturality used in Lean. Their dependency union is the unchanged
   `lem-kun-unbounded-abelian-exchange-comparison`. No new nodes require validation.

Second-reading changes: appended this independent review and its verification results
to the report. No Lean or DAG repair was necessary. One original hole is closed,
zero holes are added, and nothing is pruned.
