## What changed

Preserved the existing orientation assembly and every existing declaration signature.
Proved `affineDiagonalIntegration_exponent` from normalized finite Tate exponent
comparisons and the new proved assembly `affineDiagonalTranspose_powerCompatible`.
Its proof obtains the base root comparison, applies two separate step statements,
and combines their equations by associativity and pullback functoriality. The item
then obtains the compact-support equation by source naturality of the exceptional
adjunction Hom equivalence. All new proof imports are private imports.

The two remaining new steps separate coefficient pullback coherence (no trace or
exceptional inverse image) from raw ordered tower trace compatibility (no external
coordinate presentation, dualizing base change, integration or existence clause).
Both retain explicit kernel and pure-generator normalizations of the root maps.
No definition, source-library declaration, target, or unit route changes.

## Proved and sorry left

Of the item's three original holes, closed
`WeilConjectures.PurityFiniteSetting.affineDiagonalIntegration_exponent` by decomposition.
The existing `affineDiagonalIntegrationOrientation` proof remains intact.
The new `affineDiagonalTranspose_powerCompatible` and its private categorical
transport helper are proved from the two step statements.

Two original holes remain, both under
`lem-pur-affine-diagonal-integration-orientation`:

- `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegration_translation`;
- `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegration_zero`.

Two holes added:

- `WeilConjectures.PurityFiniteSetting.affineDiagonalPower_coefficient`, node
  `lem-pur-affine-diagonal-power-coefficient`;
- `WeilConjectures.PurityFiniteSetting.affineDiagonalRawTranspose_power`, node
  `lem-pur-affine-diagonal-raw-transpose-power`.

This is a decomposition, not a net hole reduction: one upper hole closed and two
strictly narrower step holes added. No sorry occurs in a definition or private helper.

## No longer needed

No existing imports, nodes or modules are withdrawn. The source search considered
`DiagonalAffineRankZeroActual`, but its site-compared smooth-purity maps depend on
projection-purity agreement and do not directly identify this raw ordinary identity
transpose. It is not imported, and no claim is made that its parent route is pruned. The original trace and DNC
proof dependencies are still used by the unchanged orientation proof; translation
and rank zero retain their planned dependencies. The exponent proof does not need
an additional global vector-bundle integration package: it works on the ordinary
etale ordered tower and then applies the explicit coordinate formula.

## Where the brief, the DAG or earlier work was wrong

The main orientation theorem was already proved by P2; the item still had three
ancillary holes. The existing `affineTranspose_exponent_transition` in
`Sheaf.Paper.AffineIntegrationExponentTransition` requires a separated base and
states the equation after a pro-etale comparison. The present exponent statement
allows a finite-type base without separatedness. Its new raw step uses the ordinary
etale ordered adjunction, and its coefficient step handles the coordinate pullback.
`IntegrationExponentTransposeTransport` gives a larger package conditional on
comparison of the independently constructed pro-etale vector trace with ordinary
integration. Its ordered trace equation is stated in a different coefficient-level
presentation and under that hypothesis. It does not directly provide the unconditional
ordinary raw trace equation in this packet. The new raw step isolates the projective
Kummer, open-counit and ordered-adjunction portion, with no vector/site premise.

The structured finite Tate pullback data already supplies root comparison existence;
that part did not need a new existence lemma.

The rank-zero diagnostic also showed that its comparison maps are not definitionally
identities: the identity lower-shriek normalization and dualizing base-change mate
must be proved coherent. The original hole and its docstring are preserved.

## New nodes

`lem-pur-affine-diagonal-power-coefficient` states only the naturality square for
coefficient pullback and descent, including both root-power normalizations. Its
proof in words is tensor induction from normalized line pullback and composition
naturality, with rank zero and the empty base included.

`lem-pur-affine-diagonal-raw-transpose-power` states only the raw tower counit
transpose equation. Its proof in words follows Kummer naturality, projective trace,
open counit restriction, ordered iteration and adjunction source naturality.

`lem-pur-affine-diagonal-transpose-power` is the proved assembly of those two steps.
Its proof explicitly chooses the normalized comparison on the base and pastes the
two equations, appending the unchanged dualizing base-change mate.

The normalized finite Tate pullback theorem is used as a generic coefficient tool.
The raw trace node also cites the ordinary Kummer sequence, derived-boundary naturality
and ordinary projective-line adjunction for the exact ingredients of its proof in words.
No maintainer tool approvals are altered; these are the same coefficient and ordered
trace constructions already underlying the orientation's exponent clause.

All three are refinements of the existing orientation node under the same blueprint
unit. No change records are needed because no existing statement or definition changed.

Verification: all four delivered Lean modules compile together on the project
server, with no warnings, by lcompile.py --all (exit code 0). Every existing theorem signature
was compared to the repository source and is unchanged. The zero and orientation
sections are byte-identical to the original. No new-node dependency returns to
any of the three new nodes.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
