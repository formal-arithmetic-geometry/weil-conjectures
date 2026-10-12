## What changed

Proved AlgebraicGeometry.Scheme.Modules.affine_finiteType_generatingSections with its
signature and public imports unchanged. Added the proof-only import
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel. The proof obtains finite
sections from quasicoherent_finite_type_affine, then proves that a spanning family makes
the top component of its free-sheaf map surjective. epi_of_surjective_app, applied to the
singleton cover by top, gives the sheaf epimorphism. Module.Finite.exists_fin supplies the
finite family; each global section is constructed by restriction, with functoriality
proving compatibility. No definition chooses arbitrary data from an unproved existence theorem.

Three proved private helpers transfer finite type along continuous, cocontinuous
left-adjoint pushforwards with an isomorphic ring map. They follow the private proofs of
QuasicoherentFiniteTypeAffine and are needed because finite type of G.over top is not an
existing inferred instance. Removed an unused copied helper before final validation.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.Modules.affine_finiteType_generatingSections
(lem-weil-pbc-affine-finite-type-generating-sections). No sorry remains in the item;
no holes were added or split off. The existing epi_of_surjective_app declaration is proved.
The compiler validates every private helper as well as the unchanged public theorem.
The argument works for k = 0, the zero module, and the empty affine scheme; it uses no
nonempty-generator assumption. Arbitrary index families are allowed in the internal epi argument.

## No longer needed

No existing import was removed: the original three public imports support the signature,
and the original proof import QuasicoherentFiniteTypeAffine supplies the finiteness criterion.
The item's direct proof no longer needs these planned dependencies:

- lem-weil-pbc-spec-module-tilde-sections (Mathlib.AlgebraicGeometry.Modules.Tilde).
- lem-weil-pbc-affine-tilde-gamma-adjunction (Mathlib.AlgebraicGeometry.Modules.Tilde).
- lem-weil-pbc-spec-domain-stalks-function-field (Mathlib.AlgebraicGeometry.StructureSheaf
  and Mathlib.AlgebraicGeometry.FunctionField).
- lem-weil-pbc-spec-tilde-stalk-localization (Mathlib.AlgebraicGeometry.Modules.Tilde).
- lem-weil-pbc-locally-surjective-iff-stalks (Mathlib.Topology.Sheaves.LocallySurjective).

These were DAG dependencies, not existing explicit imports of the item. They are removed
from its proof_deps. Some remain needed transitively by the source library or other modules;
this delivery makes no claim that their modules leave the entire target closure.
The unit's statement and realized steps are unchanged; the item is below those unit steps.

## Where the brief, the DAG or earlier work was wrong

The planned stalk argument was valid but unnecessary: the proved source-library
AlgebraicGeometry.Scheme.Modules.epi_of_surjective_app already supplies the needed
local-surjectivity step using basic-open denominators. Lean's finite-type class currently
does not automatically transfer to G.over top; the private transfer proofs close that glue.
No statement, definition, visibility, or public import changed. No forced adaptations.

## New nodes

lem-weil-pbc-quasicoherent-epi-affine-cover records the already proved source declaration
AlgebraicGeometry.Scheme.Modules.epi_of_surjective_app, with existing: true and no new Lean
module or sorry. Its proof uses the existing affine basic-open localization node.
Searched the DAG for the declaration and blueprint for the affine-cover epimorphism;
no matching node was found. LeanSearch was unavailable and recorded as such; LeanFinder
returned general locally-surjective sheaf lemmas; local rg found the exact source theorem.
There are no change records because all existing interfaces are unchanged.

## Second reading by B2

1. Compared the delivered module against the repository version. The existing public
   declaration's signature, visibility, docstring and three public imports are unchanged.
   No definitions or statements are changed, and no forced adaptations are present.
2. Read all three private transport proofs and the public proof. The module compiled
   cleanly locally in 50.5 seconds. There are no sorry declarations or forbidden trust
   mechanisms in the delivered source. An independent scratch copy compiled in 39.3 seconds; #print axioms for
   affine_finiteType_generatingSections lists exactly propext, Classical.choice and
   Quot.sound. This transitively validates the private helpers used in its proof.
   Compilation and axiom validation are also checked by the delivery dry run below. Initial retries encountered the 60-second wall limit
   on a heavily loaded shared machine; no limit was bypassed.
3. No statements were split off and no holes were added. The new node records the
   already proved epi_of_surjective_app, rather than adding a Lean theorem. Verified its
   actual signature and proof against QuasicoherentKernel. The affine basic-open lifting
   proof needs only quasi-coherence of the target. Empty covers of the empty scheme and
   empty generating families are handled. Independent msearch grep and loogle searches
   for finite-type restriction and generating sections found no public replacement for
   the private transport helpers; existing local restriction helpers are private.
4. The proof uses the affine finite-type criterion and the existing affine-cover epi
   theorem, then constructs sections by restriction. The five discarded planned
   dependencies are all listed under No longer needed. Both proof-only imports are used;
   the public imports support the signature. Read sk-thm-p1's realized fields: this item
   is below its realized steps, and no unit statement or route is bypassed.
5. Checked both delivered node records against the actual Lean declarations. The updated
   proof_deps is exactly the union of the steps' uses; proof_origin records the alternate
   affine-cover route. The existing node's statement and statement dependencies remain
   unchanged. The new node identifies the existing proved source declaration, includes
   search records, creation provenance, chapter/unit and blueprint provenance.

Second reading retained the Lean proof and both nodes unchanged. Added this review report.
Tested a shorter specialized restriction helper and explicit inference options after
wall-clock timeouts; they did not improve validation and were reverted. A trial lean.file
field for the existing source declaration was refused by preflight (existing declarations
must omit that field), and was removed before delivery.
