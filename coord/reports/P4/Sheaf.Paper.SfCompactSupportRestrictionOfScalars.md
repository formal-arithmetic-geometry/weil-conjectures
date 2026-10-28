## What changed

Prove AlgebraicGeometry.Scheme.sfCompactSupportRestriction_comp with its original
signature. Apply the already proved open-extension cocycle. For direct image,
apply the proved private rightTower calculation to the all-complex unit
normalizations of the specified comparisons, checking the ordinary coefficient
square on sections. Invert the resulting inverse-comparison cocycle. Pasting the
two equations uses the naturality of the phi direct-image comparison at the psi
open comparison, functoriality, and associativity.

Move the ten existing public comparison declarations to the new
Sheaf.Paper.SfCompactSupportRestrictionData module. Their names, types, attributes,
and definition bodies are preserved; the realization-isomorphism proof uses a
private map helper to avoid repeated expansion during kernel checking. The generic
private realization proof is isolated in SfCoefficientRealizationAux so the
comparison definitions compile independently of its kernel check. The item
keeps its original public imports and publicly imports the data module.
ProEtaleOpenScalarRestrictionCoherence and CompactSupportScalarDirectNormalization
replace their import of the item with the data module. The open-coherence module
is further split into ProEtaleOpenScalarRestrictionData (four unchanged public
definitions), ProEtaleOpenScalarRestrictionAux and
ProEtaleOpenScalarRestrictionRealizationAux (proved private calculations),
and the original public coherence theorems. This addresses its measured
86-second compile without weakening any declaration or raising the time limit.
The original transitive
public API of CompactSupportCoefficientPresentation is retained by explicitly
importing the item. These existing adapted modules were unclaimed when inspected. Five further
unclaimed consumers of private coherence lemmas add the private import matching
the extracted lemma: IntrinsicCompactSupportRestriction,
CompactSupportRestrictionIdentity, CompactSupportQuotientInputLaws,
FiniteOpenScalarRealizationTransport, and FiniteOpenScalarSiteTransport.
Their declarations and proof bodies are unchanged.

The normalization node now cites the definition node, rather than the parent
composition theorem, in its statement and dependencies. Its mathematical
statement, source, proof, and Lean declaration are unchanged. The parent DAG proof
records the open cocycle, the published normalization, rightTower, and pasting.
The existing intrinsicCompactSupportRestriction proof is retained.

The nine core files compile cleanly through lcompile.py, one file at a time in
import order. The item takes 18.6 seconds; all extracted helpers and data modules
are below 60 seconds (50.7, 18.9, 50.3, 14.6 and 6.6 seconds in the measured
uncached runs). All 34 direct importers were checked against the overlay: 31 compile cleanly
within 60 seconds, including all five private-import adaptations. The unchanged
FiniteTorStability measured 54.5 seconds in the diagnostic run, 60.4 seconds
after profiling was removed, and 45.6 seconds in an isolated published-artifact
baseline. SupportedEtaleTensorOrigin exceeded the limit both with the overlay
(63.1 seconds) and with published artifacts (64.5 seconds). The unchanged
FiniteRealizationRestrictionCube also exceeds the limit in the published-artifact
baseline (62.6 seconds); its original overlay run took 69.3 seconds. These
three existing timing concerns are left to deliver3.py's mandatory comparison
against main; no profiling option or temporary importer copy is delivered. A parser comparison
across the packet finds no missing public declaration, changed public signature,
changed public definition body, or new public name. The overlaid
module graph is acyclic. The unchanged theorem includes the original separated,
finite-type, compactification, and prime-invertibility hypotheses; the argument
requires no preservation of K-injectives by restriction. Zero input, identity
coefficient maps, arbitrary nonflat coefficient maps, and empty schemes are
covered by the same normalization and naturality calculation.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.sfCompactSupportRestriction_comp
(node lem-sf-compact-support-restriction-of-scalars).

Added zero holes. No sorry remains in the item or any file added or adapted in
this packet. There are no split-off proof obligations. The private direct-image
cocycle calculations and the final pasting are complete proofs.

## No longer needed

No mathematical module or node is withdrawn. No original public import of the
item is removed. The two helper modules replace their import of the parent
composition module with the definition-data module to permit the proof import.
The old direct proof-dependency entries
lem-weil-pbc-ring-sheaf-change-adjunction and
lem-weil-pbc-exact-functor-derived-factorization are supplied transitively by the
retained normalization and rightTower proofs; neither is claimed pruned.
The standalone fixed-scalar DirectImageScalarRestrictionCocycle module is not
needed: this proof works directly in the specified intrinsic constant-ring
coordinates, using the existing all-complex normalization.

## Where the brief, the DAG or earlier work was wrong

The current shared snapshot had no queue row for this module; the live queue was
read remotely and classified it as an ordinary one-hole proof item, with no
build-error repair file. The module was not already complete.

The parent node's primary Lean attachment is the companion intrinsic comparison
module. Its already recorded sfCompactSupportRestriction_comp declaration still
had the assigned hole in this item. The same normalized-pasting argument proves
that equation in its actual sfAmbientCompactSupportCandidate coordinates.

The earlier open-coherence note correctly warned that importing it into the
parent would close an import cycle. Separating the unchanged comparison data
resolves this layering problem. The normalization node also depended on the
parent only for sfDerivedImageRestriction's definition; correcting that ownership
to the data node avoids introducing a DAG cycle. No unit route is bypassed and
no target statement, hypothesis, map, or conclusion is changed.

## New nodes

Three proved helper nodes record the private calculations isolated for compilation:
lem-sf-realization-restriction-linear-lift (SfCoefficientRealizationAux),
lem-sf-open-scalar-realization-calculations
(ProEtaleOpenScalarRestrictionRealizationAux), and
lem-sf-open-scalar-mate-calculations (ProEtaleOpenScalarRestrictionAux).
Their proofs are complete and introduce no new obligations.

The definition-only node def-sf-open-scalar-restriction-data owns the four
existing open normalization and identity comparison definitions extracted from
ProEtaleOpenScalarRestrictionCoherence. The original module publicly reexports
them and retains every original theorem and proof. Its private mate calculations
are compiled separately without new public declarations or proof obligations.

The definition-only node def-sf-compact-support-restriction-data owns the ten
existing comparison declarations moved to SfCompactSupportRestrictionData.
It states no compact-support composition law and adds no theorem hole. Its
source is the existing sectionwise, adjunction-unit, and K-injective
normalization construction. The change record is
coord/changes/P4-compact-support-restriction-data.md.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 29, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionAux": "4f814cb074220bbb8420c69094992f4ffb9d7043", "Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence": "63b193bb2bd4852758c458e185f2056cfdb53f1b", "Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionData": "df611d1d2c01a37132303de872d0a76ed9221f0f", "Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionRealizationAux": "8e220046780702ac5d20a7170db5dc8a4fa03886", "Sheaf.Paper.CompactSupportCoefficientPresentation": "d9fcde31c7d6766b2ade41080c5286a6b5547fd2", "Sheaf.Paper.CompactSupportQuotientInputLaws": "a24d5985a50c5007934ccdc76d02cb3e5c000497", "Sheaf.Paper.CompactSupportRestrictionIdentity": "50e0d3e545c61b029f353b6e1129ca10ecd4ef39", "Sheaf.Paper.CompactSupportScalarDirectNormalization": "5824607b7b6ae032adc94aeb2b7354e1f8b8f3b7", "Sheaf.Paper.FiniteOpenScalarRealizationTransport": "8d188ccf9d22396b7e0984db797b2defc30a9140", "Sheaf.Paper.FiniteOpenScalarSiteTransport": "8396e5721772e6952991467546a8723e8cec3408", "Sheaf.Paper.SfCoefficientRealizationAux": "ca075c64bf6c6fc4197462a2efb589a1d780089d", "Sheaf.Paper.SfCompactSupportRestrictionData": "4370d881365085d28e6eb08b3e77d65162b77144", "Sheaf.Paper.SfCompactSupportRestrictionOfScalars": "3c26d7d27f087d80939bdef01af722af68416336", "Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction": "09c6dbac3003eaf501f50982c758bbad1ea09ce8"}, "own_failed": ["Sheaf.Paper.CompactSupportQuotientInputLaws", "Sheaf.Paper.FiniteOpenScalarRealizationTransport", "Sheaf.Paper.FiniteOpenScalarSiteTransport", "Sheaf.Paper.SfCompactSupportRestrictionOfScalars", "Sheaf.Paper.CompactSupportCoefficientPresentation", "Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction", "Sheaf.Paper.CompactSupportRestrictionIdentity"], "results": {}, "time": "2026-10-28T03:11:26+0800", "transitive": 0, "version": 1}
```

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
