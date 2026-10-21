## What changed

Replaced the item’s hole by an assembly from an ordinary flat-term tensor short
exact sequence, Mathlib’s derived triangle of a short exact sequence, and the
canonical K-flat counits. The new ordinary-sequence module has a complete, compiler-checked proof
with no sorry terms: construct the presheaf coefficient sequence, sheafify,
apply the exact sheaf tensor functor in each flat degree, and recover quotient-linear
maps through full and faithful scalar restriction. Its private tensor/extension
comparison works with independent site and coefficient universes and checks both
normalizations on local pure tensors.

The ordinary cochain witnesses are packaged in SuccessiveQuotientFlatTensorData
before specializing the coefficient rings. A completely expanded statement alone
exceeded the 60-second limit. The packaged statement with typed models checks in
8.5 seconds. The three existing definitions successiveQuotientTensorModel,
successiveQuotientTensorSection and successiveQuotientRestrictedModel move verbatim
to the ordinary module and are publicly re-exported by the item. Their names,
signatures, bodies and docstrings stay unchanged. The original triangle structure,
its other definition, and the target theorem’s signature stay unchanged.

Validation: `lcompile.py --all` compiled both delivery modules against the published
library: SuccessiveQuotientFlatTensorSequence in 51.5 seconds and
SuccessiveQuotientLinearTriangle in 13.8 seconds. The ordinary proof uses explicit
sheafification-unit naturality and hom-extensionality lemmas, plus direct local
sieve proofs for the coefficient unit. These avoid repeatedly comparing entire
adjunction and forgetful-functor structures. A generic, proved transport lemma
assembles the normalized cochain data in the same module.

The existing main theorem signature, triangle structure and localization definition
were compared verbatim with the current source. The moved Models section is also
verbatim, and every original public import remains. Both Lean files satisfy the
100-character line limit.

## Proved and sorry left

Closed one of one original holes:
SheafOfModules.successive_quotient_linear_triangle.

Added zero holes. SheafOfModules.successive_quotient_flat_tensor_sequence and all
private helpers are proved. Both delivered Lean modules contain zero sorry terms;
there are no definition holes and no unresolved statements split off. Existing
holes in imported library dependencies are unchanged.

## No longer needed

Removed direct proof imports KFlatResolutionIndependentCoefficients and
CochainTensorUniverses from the item; the supplied P, hf and hflat already provide
the needed resolution. Their modules may still occur transitively through the
adopted derived-change-of-rings interface, so this is not a global pruning claim.
The ordinary module now owns its tensor, module-SES and presheaf epi/mono proof
imports. No existing module is withdrawn and every original public import remains.

The item’s old proof-only dependencies are replaced as follows:

- lem-pc-kflat-resolution: resolution existence is unnecessary for the given P and hf.
  Removed its obsolete top-level tool_uses entry; the derived-change approval remains.
- lem-pe-successive-quotient-flat-complex-sequence: replaced by the actually constructed
  normalized ordinary sequence. Its live legacy node has no Lean attachment or proof.
- lem-pe-restricted-kflat-tensor-identification: the prescribed models compute P by
  their universal counits, and the ordinary sequence is already over the middle
  quotient ring. No separate derived restriction identification is used. Its live
  legacy node also has no Lean attachment or proof.
- def-weil-abstract-derived-category: no separate conjugation of a derived triangle
  is needed; Mathlib constructs the triangle directly on the requested cochain
  objects. Derived-category definitions remain in the statement’s import closure.

No globally pruned module is claimed.

## Where the brief, the DAG or earlier work was wrong

The resolution-existence step is redundant for this statement, which quantifies
an already supplied flat-term K-flat resolution. Two old proof dependencies named
in the DAG have no live Lean attachment or proof. The new ordinary node realizes
those coefficient steps explicitly, preserving the blueprint unit’s route.
The specialized ExtensionTensorComparison interface does not cover all of this
item’s independent universes; the ordinary module supplies the needed general
comparison privately through the sheafification universal property.

The retained canonical_computation helper had lost its explicit target-ring,
ring-map and derived-category binders after moving outside the Models section;
these are restored. All quotient-ring constructions are actual sheafifications.
No statement is disputed or weakened, no axiom is added, and no source-library
module is edited. The item’s generic model definitions are only relocated, as
recorded below. No other group’s module is adapted.

Earlier attempts failed before elaboration with missing modules. This session’s
initial required delivery check correctly refused the retained original hole.
Busy-server replies were retried, and all compiler errors were repaired. Diagnostic
files remain outside lean/ and are not part of the delivery.

## New nodes

lem-pe-successive-quotient-flat-tensor-sequence, implemented by
Sheaf.Algebra.Homology.SuccessiveQuotientFlatTensorSequence and
SheafOfModules.successive_quotient_flat_tensor_sequence. It is the genuine ordinary
coefficient and flat-tensor part of the argument; the item separately constructs
the derived triangle and counit equations. The new node’s record is marked split
as the stage-3 schema requires, although its Lean proof is complete and has zero holes.
Both DAG copies describe the implemented route and the normalized cochain data.
The search record includes LeanSearch, Loogle, LeanFinder and source grep; the
first delivery check identified the omitted LeanSearch kind, which is now recorded.

Change record: coord/changes/successive-quotient-models-location.md. The downstream
check finds no current Lean importers of the item and no users of the moved names
except the item itself. Its unfinished DAG parents and public import interface
are preserved.

Edge cases: n=2 gives the usual B/t to B/t² to B/t sequence; if t is a unit all
quotient coefficient modules vanish; the zero ring also gives zero sequences.
The construction is degreewise for unbounded P, and flatness is always sheaf
flatness, never an assumption about modules of sections.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
