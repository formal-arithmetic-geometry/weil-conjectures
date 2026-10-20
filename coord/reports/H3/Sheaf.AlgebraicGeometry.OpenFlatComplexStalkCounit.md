## What changed

Restored Sheaf.AlgebraicGeometry.OpenFlatComplexStalkCounit from its rework quarantine
and repaired the two proof imports that loaded the upstream twin of the retained
Sheaf base-derived tensor model. The original archive reproduced the recorded
duplicate-declaration error before the repair.

Preserved both public imports, every existing declaration, and the exact public
statement of AlgebraicGeometry.openFlatComplex_stalk_counit. Replaced the ordinary
comparison import with a proved private AlgebraicGeometry.extensionComplexIso:
Mathlib adjoint uniqueness identifies scalar extension under compatible ring
isomorphisms, then the natural isomorphism is applied termwise. Replaced the scalar
counit import with its lower K-flat quasi-isomorphism helper and the generic
left-derived-functor criterion. This also removes an unnecessary conversion from
categorical K-flatness to acyclic tensor flatness and back. The existing construction
of r and cancellation definition of l remain.

Updated only proof, proof_deps and proof_origin in the existing node
lem-pc-open-flat-complex-stalk-counit. The node attachment and statement are preserved.
Change record: coord/changes/open-flat-complex-stalk-counit-import-repair-h3.md.
No source-library file, definition or consumer is changed.

Validation: the repaired module compiles without diagnostics in about 15 seconds.
The exact archived StandardSingleFlatCounitLocalizationHomology consumer also compiles
unchanged against the repaired module (16.6 seconds). Searches included the current
rework and claims, DAG parents, live and quarantined consumers, existing change records,
repository/mathlib rg, and msearch LeanFinder, Loogle and grep. These found no full
ready-made replacement; Mathlib's scalar-restriction composition and conjugateIsoEquiv
provide the smaller ordinary comparison used here. Unit sk-thm-picard-coherence has
empty realized lists at this level; no unit statement or route changes.

## Proved and sorry left

This is a zero-hole rework repair, not a new proof closure. The archived item had
zero holes; zero holes are closed, zero added and zero split off. No sorry remains
in the delivery. AlgebraicGeometry.openFlatComplex_stalk_counit is fully proved,
as are private AlgebraicGeometry.extensionComplexIso and the preserved private
AlgebraicGeometry.tensorStalkIsoAt, all attached to the existing node
lem-pc-open-flat-complex-stalk-counit. Explicit #print axioms checks list only
propext, Classical.choice and Quot.sound for all three declarations.

## No longer needed

Removed these proof-only imports and their corresponding direct proof dependencies:

- WeilConjectures.Algebra.Homology.BaseDerivedTensorOrdinaryRingComparison /
  lem-pc-base-derived-tensor-ordinary-ring-comparison. Only its private ordinary
  coefficient-transport helper was used; Mathlib adjoint uniqueness now proves
  exactly the needed ordinary comparison locally.
- WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit /
  lem-pc-kflat-scalar-extension-counit. Its conclusion follows directly from
  categorical K-flatness and the generic criterion, using the already proved
  scalar-extension helper from lem-sc-kflat-scalar-extension-derived-iso.

No public import or module is withdrawn. Both upstream declarations are preserved
verbatim in the library, and this report makes no global unreachability claim.
All other existing proof dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

The archived item had already been proved; its assignment is the current rework
failure, with zero original holes. The upstream sync migrated the two proof imports
to upstream modules while a public dependency still needs the retained Sheaf model.
Mixing those environments causes the reproduced duplicate constant error.

The repair avoids the two conflicting imports without changing the public model,
SingleComplexBaseChange coordinates, counit, theorem signature or consumer call.
The new helper is ordinary functorial transport and uses no arbitrary object chosen
from an unproved existence theorem. Its argument covers zero rings and complexes:
ring equivalences remain equivalences, and adjoint uniqueness requires no nonzero
hypothesis. The existing cancellation proof needs only existential isomorphisms,
which are exactly what the node and Lean statement request.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
