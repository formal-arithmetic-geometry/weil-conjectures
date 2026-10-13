## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.exists_radicial_preparation_construction` with a complete Lean
assembly proof, preserving its signature and public imports. Added two new modules:
`Sheaf.AlgebraicGeometry.ReducedFlatAffinePreparation` and
`Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre`.

The proof first deduces that the generic point lies in V from the nonempty
geometrically irreducible fibre. The first intermediate gives a reduced affine
flat family over an integral affine reduction of an open base. The existing
`exists_radicial_preparation_fibre_comparison` transfers the generic-fibre
hypothesis. The second intermediate gives the radicial base extension and geometric
reducedness of the canonical reduced pullback. The main proof explicitly takes
that reduction, base-changes the first universal homeomorphism, and composes two
pullback pasting isomorphisms. Their projection identities prove the required
factorization over S. Affineness and local finite type are inferred
from the actual reduction and pullback constructions; reducedness is obtained
explicitly from the reduction theorem.

The second intermediate also imports the existing finite purely inseparable
separably generated extension and separably generated tensor reducedness modules,
which its proof plan uses. All added imports in the item are proof-only. No existing definition or signature
changes, and no forced adaptations are needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_radicial_preparation_construction`
(node `lem-sbc-radicial-preparation-construction`). No `sorry` remains in the item.

Added and left open:
- `AlgebraicGeometry.exists_reduced_flat_affine_preparation`
  (node `lem-sbc-reduced-flat-affine-preparation`).
- `AlgebraicGeometry.exists_radicial_reduced_flat_generic_fibre`
  (node `lem-sbc-radicial-reduced-flat-generic-fibre`).

This is a decomposition: one upper hole closed and two strictly smaller holes
added, rather than a net decrease in holes. The first theorem does not assume or
conclude geometric irreducibility/reducedness of a generic fibre and contains no
field-extension step. The second begins with a reduced flat finitely presented
family over an integral affine base, contains no reduction/shrinking of the
original base, and fixes the resulting source to the canonical reduction.

## No longer needed

Removed the item's direct proof import
`Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation`; that module remains a
dependency of `ReducedFlatAffinePreparation` and therefore is not globally pruned.
The removed direct proof dependency is `lem-sbc-generic-flat-finite-presentation`;
it remains in the new first intermediate's proof dependencies. No DAG nodes or
modules are claimed to leave the targets' closure.

The second reader replaced the new radicial module's public import of
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` with
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: only the latter supplies the
nilradical subscheme appearing in its signature. The former's reduction instance
is obtained in the main proof from the explicitly imported reduction theorem.

## Where the brief, the DAG or earlier work was wrong

The original construction node names no declarations for its reduction,
principal-open lifting, or finite purely inseparable extension steps. Its only
recorded proof dependency, generic flat finite presentation, does not provide
those constructions. The new statements expose these two independent stages and
the real Lean proof composes them. The unit's route remains unchanged.

Read Stacks Tags 0559 (second proof) and 030R. Edge checks: the first intermediate
allows an empty source and uses the supplied generic point to exclude an empty
base. The second excludes an empty generic fibre by geometric irreducibility,
allows empty special fibres, and uses the identity field extension in
characteristic zero. Scaled generators have the required power identity
(db)^q = a*d^(q-1); reduction preserves injectivity of ring embeddings because
nilpotence is reflected by an injective map. No definition selects an arbitrary
existence witness; the source of the final model is a canonical reduction.

Mathlib searches used LeanFinder, Loogle, and source grep; none supplied the full
construction. LeanSearch returned Internal Server Error, recorded as unavailable.
The full imported blueprint searches for 'reduced flat affine', 'separably
generated', and '0559' returned no matching blueprint node. The new nodes inherit
the established slicing ancestor from the existing preparation node's parent.

## New nodes

`lem-sbc-reduced-flat-affine-preparation`, in
`dag/nodes/sec-smooth-base-change/`, records Tag 0559's reduction and first
generic-flat shrinking, including the universal homeomorphism to the original
pullback. Its Lean is `ReducedFlatAffinePreparation.lean`.

`lem-sbc-radicial-reduced-flat-generic-fibre`, in the same directory, records
Tag 0559's finite purely inseparable base extension and the geometric reducedness
of the canonical reduced generic pullback. Its Lean is
`RadicialReducedFlatGenericFibre.lean`. No change record is needed.

## Second reading by H1

1. Interface: PASS. Compared the delivered item with the repository using `diff`
   and the declaration parser. The existing signature is byte-for-byte identical;
   no existing declaration, definition, visibility, or public import changes.
   The new modules contain only the two reported theorem statements. No change
   record or forced adaptation is needed.
2. Proof: reviewed the nonempty-fibre argument, the two intermediate applications,
   the canonical nilradical reduction, and both pullback pasting isomorphisms.
   The projection identities give the required factorization, and the
   generic-point equalities compose. There are exactly two named theorem holes,
   neither in a definition; no prohibited declaration or kernel bypass occurs.
   All three modules compile locally without errors or warnings after the repair.
   A scratch copy of the full assembly proof with `#print axioms` for all three
   declarations compiled successfully: each uses only `propext`,
   `Classical.choice`, `Quot.sound`, and the expected `sorryAx` from the two
   named open intermediate theorems.
3. New statements: PASS as a decomposition, not a net proof gain. Checked against
   [Stacks 0559](https://stacks.math.columbia.edu/tag/0559), second proof, and
   [Stacks 030R](https://stacks.math.columbia.edu/tag/030R). Reduction and the first
   flat shrinking need no generic geometric-irreducibility hypothesis. Empty
   source is allowed in the first statement; a generic point excludes an empty
   base. In the second, the generic fibre is nonempty and a reduced domain;
   characteristic zero permits the identity extension. The power equations
   for scaled generators and the reduced tensor injection justify the radicial
   model even over a non-Noetherian base. Empty special fibres are harmless. As concrete small cases, the first statement
   sends the identity family over `Spec(k[ε]/(ε²))` to `Spec(k)` with its
   reduction maps. The second handles `Spec(k[t]/(t^p-a))` for a non-pth-power
   `a` by adjoining its pth root to k; the canonical reduced pullback is
   `Spec(k(a^(1/p)))`, so its generic fibre is geometrically reduced.
   Neither statement restates the item: one handles reduction/shrinking, the
   other the field extension of an already reduced flat family. The two holes
   require substantial affine and field constructions, so neither has a quick
   closure. Independent LeanFinder, Loogle and grep searches found component
   lemmas, notably `Algebra.IsGeometricallyReduced.of_injective`, but no duplicate
   of either construction. Searched `lean/Sheaf` as well;
   `exists_spread_purely_inseparable_factors` requires Noetherianity and an already
   constructed finite domain algebra, so it does not replace this construction.
4. Route and pruning: PASS. The proof uses the first preparation, the existing
   fibre comparison, the radicial generic-fibre step, and the reduction theorem.
   Proof-only imports remain private. Replaced the new radicial module's public
   upstream subscheme import with Mathlib's subscheme module: its signature needs
   the subscheme construction, not the upstream reduction instances. The compiler exposed that private imports do
   not re-export the upstream reducedness instance, so the main proof now installs
   `IsReduced Y` explicitly from the reduction theorem it already uses. The removed
   original proof dependency is explicitly listed above and remains reachable
   through the first intermediate. No globally pruned module is claimed.
   `dag/units/sk-prop-normal-form.json` is unchanged (its existing realized arrays
   are empty); this item realizes none of those arrays and changes no unit step.
   The reduction, first shrinking, and purely inseparable extension retain the
   preparation route used by the parent nodes.
5. DAG: PASS. Read all three delivered records against the declarations and proof.
   Existing statement and Lean signature stay unchanged. The main node's four
   proof dependencies are exactly its four private Sheaf imports. Both new nodes
   have source, complete word proofs, declaration signatures, creation metadata,
   chapter/unit, and blueprint ancestry. Added missing Loogle records to each;
   corrected the first node's copied proof-origin note to describe reduction and
   principal-open lifting rather than the other node's field argument.

Second reading changed: one unnecessary public upstream import, missing Loogle
search records, the copied proof-origin note, and explicit pruning/review details
in this report; also supplied the explicit reducedness instance from the
existing reduction theorem. No theorem signature was changed.
