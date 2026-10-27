## What changed

Proved `AlgebraicGeometry.exists_finite_closedImmersion_locus` with exactly the
signature recorded in its existing DAG node. The shared checkout had no item Lean
file, no quarantine copy and no rework row; the existing node and H9 delivery report
retain its exact interface and its one original hole. Reconstructed the module at
that interface, without withdrawing or detaching anything.

The proof uses the already proved source theorem
`AlgebraicGeometry.exists_isClosedImmersion_restrict_of_fiber`, rather than rebuilding
its finite-cokernel argument with sheaf modules. The private, proved helper
`closedImmersion_fiber_descend` descends a closed-immersion fibre along the extension
of residue fields supplied by a cartesian square. It uses the proved source fpqc
descent theorem, installed locally, and Mathlib's faithful-flatness of field
extensions. Flatness is required only for this field extension.

The open W is explicitly the locus of closed-immersion fibres. The neighbourhood
theorem shows openness; its second application to the restriction to W and target
locality prove the restriction is a closed immersion. Two applications of the
private helper prove the required inclusion for every point of W0. The public
imports provide only the finite morphism, fibre and pullback interface. The two
private imports are FiniteClosedImmersionNearFibre and the source Mathlib extension
Morphisms.FlatDescent. Updated the existing node's proof, proof_deps and proof_origin.

The statement and all definitions are unchanged. No source-library file or consumer
is edited. The item realizes no unit statement or step; the proper-base-change unit
route is preserved. The existing near-fibre node is already Lean-closed, so its use
from the other unit requires no new unproved tool assumption.

## Proved and sorry left

Closed the one assigned hole:
`AlgebraicGeometry.exists_finite_closedImmersion_locus`
(`lem-weil-pbc-finite-closed-immersion-locus`). Proved 1 of 1; zero split off;
zero holes left in the delivered module; zero holes added elsewhere.
The private helper is also proved. This is a proof, not a decomposition.

## No longer needed

No existing module is withdrawn. The old explicit sheaf-module proof plan no longer
requires these direct dependencies:

- `lem-pc-f3-finite-pushforward-finite-type`, module
  `WeilConjectures.AlgebraicGeometry.FinitePushforwardFiniteType`;
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`, module
  `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`;
- `lem-weil-pbc-finite-type-module-support-closed`, module
  `WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed`;
- `lem-weil-pbc-support-pullback-finite-type`, module
  `WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback`.

The existing closed near-fibre theorem already supplies the finite-cokernel/Nakayama
step. Its dependencies remain intact, and this report makes no claim that any of
the above modules is globally unused. The intermediate development import of
`WeilConjectures.AlgebraicGeometry.FieldExtensionDescent` was removed in favour of
the smaller source flat-descent module; the three-line field-extension argument
uses Mathlib directly. No original import text was available in the shared copy.

## Where the brief, the DAG or earlier work was wrong

The assigned item source was absent despite its queue entry and retained Lean
attachment; no rework record or return authorized withdrawal. Its interface has
therefore been preserved and restored with a proof. H9's report records the single
hole and the parent use. The local parent's proof is still its older unfinished
version, so zero current importers would not justify withdrawal.

The recorded finite-cokernel support argument is mathematically valid but longer
than necessary given the already proved near-fibre theorem. The replacement uses
that declaration without introducing any new obligation. It never assumes that
the arbitrary base change is flat, finitely presented or Noetherian. Empty W0,
empty source or target, and zero fibres are handled by the same proof; the
near-fibre theorem explicitly includes zero fibres. Nonreduced schemes and
nonflat base changes impose no extra condition. No data is chosen from an
unproved existence statement.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
