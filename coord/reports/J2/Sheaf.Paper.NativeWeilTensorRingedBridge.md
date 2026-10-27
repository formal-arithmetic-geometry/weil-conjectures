## What changed

Constructed the native bridge from a specified NativeFrobeniusRingedModel and its
specified twisted action-site presentation. The native equivalence is the inverse
of the lifted fixed-pair equivalence; its existence is proved separately so that
the inverse and unit/counit are abstract during the construction. The ordinary
equivalence is A.E.inverse.
Restriction is P.modules.functor followed by forgetPairs. Both Hom comparisons
are transported through these same inverse equivalences, so their square can be
proved by naturality and the unit/counit identities.

The coefficient-unit comparison uses ihomAdicConstantIso and uniqueness of the
left adjoint to internal Hom. Exact orbit induction supplies preservation of
K-injectives. The supplied ringed-topos pullback, identified with restriction by
uniqueness of left adjoints, supplies flat-term K-flat preservation.

Added Sheaf.CategoryTheory.TwistedActionUnderivedRestriction for the ordinary
coherence of the specified action-site tensor and Hom maps. It contains no
native category, site-existence assertion, or resolution comparison. All source
library declarations are unchanged. The existing bridge record and instances move
verbatim to NativeWeilTensorRingedBridgeData, publicly re-exported by the original
module. NativeNormalizedActionHom exposes the normalization of the already proved
forward comparison. These splits follow profiler results:
the original combined files spent over 90 seconds type checking their declarations.
Local opacity alone did not sufficiently reduce that cost. The ordinary forward
Hom assembly and recognition of the tensor unit are also proved in separate modules:
profiling attributed substantial kernel checking to both components. The full
normalized inverse-Hom square is likewise isolated as a proved theorem; it
contains no underived coherence, coefficient-unit or complex-preservation
assertion.

Final validation: lcompile compiled every delivered module and the unchanged
direct importer Sheaf.Paper.NativeWeilTensorRingedStructure. Profiler settings
were removed before that run. The temporary consumer copy was removed afterward.
The original theorem signature, complete record and instance-attribute block
were checked textually unchanged.

## Proved and sorry left

The proved helper declarations are
AlgebraicGeometry.ProEtaleWeilSheaf.normalized_action_hom,
AlgebraicGeometry.ProEtaleWeilSheaf.normalized_ordinary_hom,
AlgebraicGeometry.ProEtaleWeilSheaf.native_inverse_hom_square, and
CategoryTheory.TwistedActionRingedSite.unit_iso_of_identity_hom.

The original hole is
AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_bridge
(lem-sf-native-weil-tensor-ringed-bridge). Its construction is reduced to the
ordinary action-site coherence theorem. This is a decomposition, not a net hole
closure: one original hole closed, one strictly smaller hole added. The original
module has zero sorries (previously one); the ordinary restriction module has one;
all other delivered modules have zero holes.

The added hole is
CategoryTheory.TwistedActionRingedSite.underived_restriction
(lem-sf-twisted-action-underived-restriction), in
Sheaf.CategoryTheory.TwistedActionUnderivedRestriction. The theorem fixes its Hom
component maps to P.hom; the remaining data are a coherent tensor comparison
and its evaluation compatibility. The proof plan constructs these using
the natural isomorphism assembled from P.tensor and P.unit. Unused tensor/unit
equality assertions were removed from the intermediate conclusion.

## No longer needed

The two original public imports move with the unchanged record to its data module;
the original module publicly imports that data module and exposes the same public
declarations. No module is withdrawn or globally pruned. The forward Hom helper imports move
from the bridge into NativeWeilInverseHomSquare; both helpers remain used in
the target import closure.
The existential theorem native_weil_ringed_presentation is not used: we construct
its normalized equivalence directly so that the Hom square uses the same choices.
Its module remains a proof import for its proved fixed-pair equivalence and inverse
Hom transport helpers, so its DAG dependency remains.

Likewise frobenius_action_resolutions is not chosen as a second, unrelated
realization. Restriction's preservation properties follow from the same P used
for the native equivalence. Its module remains imported for the proved K-flat and
flatness transport helpers. The corresponding node remains a dependency.

## Where the brief, the DAG or earlier work was wrong

The blueprint ancestor lookup returns None for this synthetic item. New nodes
retain that null lookup result and the full split ancestry, with the actual
internal-Hom/evaluation source paragraph recorded. Whole-blueprint searches found
no statement matching the ordinary restriction coherence, unit recognition or
normalized Hom square.

No statement was changed. The plan's unit step can be shortened: preservation of
internal Hom plus the native constant-Hom identity determines the unit by the
tensor-Hom adjunction. No separate Frobenius coefficient-object identification is
required. The previous proof plan did not isolate the ordinary associativity and
unit calculations required by Underived; the new node records exactly those
calculations and evaluation, independently of the native realization.

## New nodes

lem-sf-native-inverse-hom-square: proved construction of both inverse Hom
comparisons and their normalized restriction square for any specified forward
equivalence. This self-contained part is separated after reducing expensive
monoidal unfolding; it adds no hole.

lem-sf-native-normalized-ordinary-hom: proved NatIso assembly of A.hom, with
its component equation.

lem-sf-sheaf-hom-identity-unit: proved recognition of the genuine sheaf tensor
unit from a specified natural identity-Hom comparison.

lem-sf-native-normalized-action-hom: proved normalized version of the existing
forward action-site comparison. The original definition node
def-sf-native-weil-tensor-ringed-bridge now points to the data module; its statement
and the complete declaration block are unchanged (checked by textual comparison).

lem-sf-twisted-action-underived-restriction: ordinary tensor/Hom restriction on a
specified action-site presentation, with coherence and evaluation for its fixed
comparison maps. This is only the ordinary underived field of the original bridge;
the native equivalences, normalized Hom square, coefficient unit and preservation
of complexes are constructed in the original module. The relocation preserves the
complete existing definition and its public visibility;
no definition or statement changes semantically, and no consumer needs adaptation.
The relocation record is coord/changes/J2-native-weil-bridge-module-split.md.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
