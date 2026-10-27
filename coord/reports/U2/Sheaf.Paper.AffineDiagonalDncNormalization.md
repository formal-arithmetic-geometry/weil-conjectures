## What changed

The unchanged theorem `WeilConjectures.PurityFiniteSetting.affineDiagonalDncNormalization`
is assembled from two independent compatibility statements, by actual Lean isomorphism
cancellation. All existing signatures, definitions, public imports, target statements,
and unit steps are preserved. There are no edits outside the assigned sandbox.

The new module `Sheaf.Paper.AffineDiagonalSectionCoordinates` constructs the geometric
section-coordinate isomorphisms before specifying any integration orientation. They are
inverses of canonical exceptional base-change mates, with the canonical identity-pullback
isomorphism. The source map uses the already proved difference coordinates; the normal
map uses the already proved homogeneous normal coordinates. The normal zero-section
identity is proved from the normalized Rees comparison and conormal augmentation.
There is no choice from an existence theorem and no new data containing a hole.

The first new step, `affineDiagonalDncCoordinateIdentity`, concerns the normalized DNC
arrow in those geometric coordinates, with no annihilator exponent or integration
transpose. The second, `affineDiagonalRestrictedTransposes`, identifies the two restricted
integration transposes in ordinary etale geometric coordinates, without any DNC arrow.
These are strictly separate parts of the old argument. The original theorem cancels
the common geometric normal coordinates and restricted normal transpose to obtain
its required inverse identity. Its new imports are private proof imports.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.affineDiagonalDncNormalization` by decomposition.
There was one hole in the original module, and its delivered proof has none.

The delivery adds exactly two holes:

- `WeilConjectures.PurityFiniteSetting.affineDiagonalDncCoordinateIdentity`, node
  `lem-pur-affine-diagonal-dnc-coordinate-identity`.
- `WeilConjectures.PurityFiniteSetting.affineDiagonalRestrictedTransposes`, node
  `lem-pur-affine-diagonal-restricted-transposes`.

Also proved `affineDiagonalNormalCoordinates_zero`,
`affineDiagonalTranslatedCoordinates_zero`, and the private normal-function-augmentation identity. The coordinate constructions have zero holes.
This is a decomposition, not a claim of a net reduction in the ledger's hole count.
Both remaining theorems have their complete argument in their docstrings and DAG nodes.
The three new modules compiled successfully with `lcompile.py --all`; after repairing
the original proof, its final single-file compile passed cleanly in 21.4 seconds.

## No longer needed

No existing import was removed and no module was withdrawn or globally pruned.

The original node's seven direct proof dependencies are replaced by the two precise
compatibility steps. `def-sbc-affine-space`, `def-pur-normal-bundle`,
`lem-pur-dnc-section-geometry`, and `lem-pur-affine-diagonal-graded-coordinates` are needed
through the already implemented coordinate constructions and the geometric DNC step.
`lem-pur-affine-translation-trace` and `lem-pur-trace-transpose-base-change` are needed by
the independent restricted-transpose step. `thm-pur-dnc-invariance` is needed by the
geometric DNC step and still appears in the original statement. None is claimed unused
in the targets' closure. The final cancellation proof imports only its two new step
modules in addition to its unchanged public construction import.

## Where the brief, the DAG or earlier work was wrong

The proof plan's polynomial coordinates were already implemented by the construction
module, but the listed declarations did not state either of the required global
compatibility equations. In particular, `existsUnique_dncInvariance` states normalization
through `sectionRestrictionIso` applied to a family trivialization; it does not directly
state compatibility with the actual ordered affine trace transpose. The two new steps
separate these independent calculations instead of renaming the original obligation.
The source's rank-zero and empty-base cases are preserved in all statements.

## New nodes

`def-pur-affine-diagonal-section-coordinates` owns the explicit standard zero section,
standard section invariant, geometric pair comparison and its source/normal
specializations. The normal-zero equation is proved by degree-one augmentation.

`lem-pur-affine-diagonal-dnc-coordinate-identity` isolates the standard-pair DNC
calculation and exceptional-mate fibre coherence without any integration orientation.
Its source is the standard-pair paragraph of projection-purity agreement, DNC section
geometry (4), and the normalized DNC invariance theorem.

`lem-pur-affine-diagonal-restricted-transposes` isolates ordinary etale trace-translation
invariance and transpose naturality in the explicit geometric coordinate comparisons.
Its source is the translation paragraph of Agreement on the model. It does not mention
DNC normalization. LeanSearch, LeanFinder, Loogle, source grep and blueprint searches
found no existing statement of either compatibility equation. No existing definition
or statement was changed, so no change record or forced adaptation is required.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
