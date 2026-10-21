## What changed

Prove `CategoryTheory.RingedHomColimitTransport.source_transport` using the actual
termwise complex colimit, source localization, and the existing uniquely normalized
signed Hom shift. Construct the comparison as `Q(colimit.post)` followed by the
inverse fixed-resolution comparison, and descend it through `Q.op`. The shift map
is the localized colimit of the signed chain isomorphisms, with the exact final
representative identity required by the statement. All added helpers are private
and proved. The existing public statements and definitions are unchanged.

The node proof records the independent-universe quasi-isomorphism theorem, the
existing resolution theorem supplying Grothendieck abelianness, the Hom projection
API, and the normalized shift interface used by the proof. No source-library file
is changed. The local proof elaboration commands are documented in
`coord/changes/rhom-colimit-source-transport-private-proof.md`; the public API
and both existing definition bodies remain verbatim. The complete module compiled on the server with no holes (56.2 s).
Private generic projection and currying helpers avoid unfolding the large sheaf
models during the signed-shift calculation.

## Proved and sorry left

Close the one original hole in
`CategoryTheory.RingedHomColimitTransport.source_transport`
(node `lem-sfb-rhom-colimit-source-transport`). No holes are added or split off.
There are no remaining `sorry` declarations in the delivered module.

## No longer needed

Remove the private proof imports
`WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`,
`WeilConjectures.Algebra.Homology.HomComplex`,
`WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`, and
`WeilConjectures.Algebra.Homology.HomComplexShiftLeft`.
The Hom definition and component API are already reexported by the public
statement dependencies. Localization infrastructure is likewise already public
through `DerivedInternalHomOfUniverses`; no direct extra import is needed.


The proof does not directly use `lem-pur-rhom-well-defined`: its universe-general
companion `lem-pur-rhom-well-defined-universes` supplies exactly the needed source
quasi-isomorphism statement. The independent-universe K-injective resolution theorem
`prop-pur-kinjective-resolutions-exist` supplies Grothendieck abelianness, replacing
the direct use of `lem-pur-ringed-site-grothendieck-abelian`.

The direct dependency `lem-pur-hom-complex-shift-left` is replaced by the already
normalized independent-universe shift interface
`lem-weil-pbc-ringed-internal-hom-exact-restriction`, together with
`lem-sc-hom-complex-projections` for its joint chain-level naturality.
Remove the obsolete top-level tool approvals for
`lem-pur-ringed-site-grothendieck-abelian`, `lem-pur-rhom-well-defined`, and
`lem-pur-hom-complex-shift-left`; retain the exact-colimit homology approval.
No library module is withdrawn; these dependency changes concern this proof only.

## Where the brief, the DAG or earlier work was wrong

The original quasi-isomorphism dependency has fewer universe parameters than this
item; its existing independent-universe companion is needed. The final shift clause
requires a chain-level identity before localization. Testing on derived images of
colimit injections alone would not establish that identity. The proof first uses
chain-level colimit extensionality and then the localization universal property.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
