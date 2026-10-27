## What changed

Proved `AlgebraicGeometry.Scheme.exists_finite_etale_model_of_codimension_one_neighbourhoods`
in `Sheaf.AlgebraicGeometry.Morphisms.CodimensionOneNeighbourhoodEtaleExtension`, with
its statement and public imports unchanged. Construct W as the complement of the
finite image of the closed bad locus. Check membership by the whole fibre; establish
etaleness by a proved private source-local neighbourhood helper. Use Mathlib's affine
stalk dimension/height equality to prove the boundary dimension bound, and transport
regularity through `Spec.stalkIso`. Apply the existing regular codimension-two
extension theorem. Convert its comparison to pullbacks and restrict it to D(f) by
pullback functoriality and pasting isomorphisms.

Updated the existing node's proof to match this implementation. No new declarations
with postponed proofs, no definition or signature changes, and no consumer adaptations.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_finite_etale_model_of_codimension_one_neighbourhoods`
(node `lem-sfb-codimension-one-neighbourhood-etale-extension`).

One of one original sorries proved; zero sorries left in the item; zero added or split
off. The private helper `etale_of_source_neighbourhoods` is fully proved. The proof
uses the already declared codimension-two extension theorem as intended; this report
does not claim to close any holes in its transitive dependencies.

## No longer needed

Removed the unused proof imports `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`,
`Mathlib.AlgebraicGeometry.FunctionField`, and
`Mathlib.RingTheory.Localization.AtPrime.Basic`. Finite fibres and function fields
are unnecessary: only the closed-image property, affine stalk localization, and
height/dimension identities are used. The explicit length-two prime-chain argument
is replaced by the proved Mathlib height identities. The comparison of the base
changes of O and N is replaced by source locality directly on q⁻¹(W).

No DAG dependency or whole module is withdrawn: the stalk-localization node still
supplies the affine stalk identification, and the existing extension theorem and
permanence/locality inputs remain used. Public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original planned argument is valid; Mathlib already
packages its localization dimension calculation, so no new chain lemmas are needed.
The unit route is preserved, including the codimension-two extension theorem.
Checked the empty-source case and the case where f is a unit: W is then the whole
base, and all constructions and boundary conditions still apply. Empty fibres are
handled by the fibre membership criterion without a surjectivity hypothesis.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
