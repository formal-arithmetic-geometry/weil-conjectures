## What changed

Replaced the assigned module's presentation-transport hole by a complete categorical
argument, with its public statement byte-for-byte unchanged. All four original public
imports remain necessary for that statement. Added only private proof imports and proved
private helpers in the assigned module.

The argument constructs the actual functor from internal modules on X to fixed-k sheaves
on the coefficient slice. Its first three factors are equivalences and its last two
factors are left adjoints, so it preserves finite colimits. Point pullback also preserves
finite colimits. The image of the regular module is identified with the constant regular
k-module, and the finite biproduct comparison then identifies both free terms, including
rank zero. Conjugating the image of d defines the matrix a. PreservesCokernel.iso and
cokernel.mapIso give its cokernel, with the conjugation square proved by cancellation.
The monoidal point-pullback composition comparison identifies the internal restriction
of the point cokernel on X with the given point cokernel on the underlying scheme of U.

Added CoefficientSliceRestrictionIso with one named remaining geometric comparison:
reconstruction on the coefficient slice respects an isomorphism between internal inverse
images of two arbitrary modules. This separates the section/inverse-image/localization
square from the now-proved regular-module, finite-free, matrix and cokernel argument.
The new statement contains no discrete coefficient A, ring equivalence e, rank, point
module, matrix or cokernel. It is a strict part of the original argument, not the
presentation statement under another name. Its docstring and node give its source and
the complete adjunction/localization argument for the next worker.

No shared definitions, statements, instances, attributes, source-library files, targets,
or other existing modules were changed. Instance priorities and irreducibility settings
in the assigned file are local. There are no hollow definitions or new axioms.

## Proved and sorry left

Closed the original body hole of
AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_point_presentation_transport
(node lem-sfb-discrete-point-presentation-transport). Its module has zero holes.

Added one hole, exactly the public theorem
AlgebraicGeometry.ProEtale.IntegralModelsStacks.coefficient_slice_iso_of_internal_restriction_iso
in Sheaf.AlgebraicGeometry.CoefficientSliceRestrictionIso
(node lem-sfb-coefficient-slice-restriction-iso).

This is a decomposition: one upper hole closed, one strictly smaller geometric hole
added, net zero holes. It is not reported as an unconditional proof of the original
obligation. All private helpers are completely proved. In particular the free-term and
cokernel calculations have no new assumed lemmas. The supplied ring-sheaf isomorphism c
already identifies regular modules, so e is retained but unnecessary for this route.

The same finite-biproduct proof covers m=0 and n=0. The new geometric statement was
checked on identity maps, the empty scheme, zero modules, and the zero ring: it only
applies functors to isomorphisms and imposes neither conservativity nor a nonempty-site
hypothesis. A noncanonical c causes no problem because both modules use the same scalar
restriction. The original statement was checked mechanically against the repository
source and is byte-identical.

Final remote lcompile.py --all completed without errors or warnings: 29.0 seconds
for CoefficientSliceRestrictionIso and 42.3 seconds for the assigned module. Both
are below the 60-second limit. Profiling and trace options were removed. The earlier
kernel timeout was isolated to specialization of an isomorphism-valued pullback wrapper;
proving the general compatibility as a private proposition lets its callers compose
abstract isomorphisms and avoids reducing that concrete construction.

## No longer needed

The specialized constant-sheaf pullback from the profinite point,
def-sfb-constant-sheaf-scheme-pullback-comparison, is not needed by this proof. Constant
sheaf pullback is instead obtained directly on the coefficient-sized scheme sites from
the general Mathlib comparison and the explicit terminal identity scheme object.

Removed det-def-sfb-constructible-local-model from the proof dependencies: none of its
constructibility assertions is used. It remains a statement dependency and its existing
public imports are preserved. Weakly etale localization remains needed inside the new
geometric comparison; it is not claimed pruned.

No existing module is withdrawn and no original public import is removed. Exploratory
proof imports not retained are Sheaf.Paper.FiniteDiscreteSchemeRing,
Sheaf.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback,
WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence, and
Sheaf.SixFunctors.ProEtale.InternalCompletionSectionTransport. The first two were only
used for elementary terminal-object and finite-limit facts, now proved directly from
existing Mathlib equivalences. Point composition uses the generic proved
mapModCompExtendScalarsIso. Its private existence lemma is proved for arbitrary scheme
maps, so specializing it to the AsSmall slice object does not unfold the concrete
pullback construction while composing isomorphisms. Small-site reconstruction uses the existing section-module
equivalence and pushforwardPushforwardEquivalence directly.

## Where the brief, the DAG or earlier work was wrong

The old one-step proof plan bundled a geometric naturality square with the entire
finite-presentation calculation. The sectionwise equivalence by itself does not provide
that square. Existing SectionModuleAlgebraicInverseImage,
InternalModuleInverseImageComparison and ProEtaleWeaklyEtaleLocalization provide its
pieces, but their interfaces do not directly state the coefficient-slice comparison.
The new node records precisely that remaining geometric step, while the combination
with finite free terms and cokernels is Lean code in the assigned module.

InternalCompletionSectionTransport was quarantined during this session (the current
rework row names an unrelated imported projective-line module). Its archive and all its
attachments were preserved. This delivery does not import it: a private proof composes
the existing section equivalence with AsSmall and the existing pushforward equivalence.
No quarantine file is restored, deleted or replaced by this delivery.

The newest integral-models blueprint statement and proof were read in
literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-integral-models/.
The unit's route and its realized nodes are unchanged. This work is below the unit and
only isolates a step of its discrete residue local-model argument.

## New nodes

lem-sfb-coefficient-slice-restriction-iso, in
Sheaf.AlgebraicGeometry.CoefficientSliceRestrictionIso, records invariance of the
coefficient-slice model under an isomorphism of internal restrictions. Its source is
Stacks Tags 03CY and 00YV, localization in Section 00XZ, and weakly etale composition
and permanence in Tags 094T and 0951. Its proof is reconstruction/inverse-image
comparison, scalar restriction, weakly etale slice localization, and application to
the given isomorphism. Actual leansearch, loogle and grep queries are recorded. There
are no definition or statement change records because existing interfaces are unchanged.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
