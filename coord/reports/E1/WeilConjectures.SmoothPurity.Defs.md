## What changed

Partial proof work in WeilConjectures.SmoothPurity.Defs. The complete assigned source was
restored from its quarantine path before editing. Every existing declaration, signature,
attribute, public import and non-theorem body is preserved. Six completely proved private
helpers implement additional steps of the existing geometric route:

- smoothTrace_representingTranspose_isIso proves invertibility of the actual adjunct of a
  realized representing pairing, using its Hom bijections and Yoneda. The generic proof
  is applied to the live adjunction before the disputed instance and does not assume a
  comparison isomorphism. Keeping the categorical proof generic avoids costly unfolding
  of the live derived-category functors during elaboration.
- smoothTrace_from_representing_pairing lifts the ambient Tate identification through the
  full constructible inclusion, constructs the comparison from that actual adjunct and the
  exceptional image of the target-unit identification, and proves its counit formula.
- isIso_smoothPurityMap_of_representing_pairing identifies the actual purity map with that
  constructed comparison once the actual trace's geometric formula has been supplied.
- smoothTrace_conjugate_adjunct proves the Hom-equivalence identity for a mate of a left
  comparison by the actual mate-counit identity and naturality.
- smoothPurityMap_comp_of_trace_transitivity applies that identity to the live shriek
  compositor, obtaining the actual purity-map square from a trace transitivity equation.
- smoothPurityIso_comp_of_trace_transitivity retains the canonical open-unit map, cancels
  the two actual invertible purity maps, and proves exactly the original ambient formula.
  Both invertibility proofs are explicit hypotheses of this helper.

The two attached route nodes record exactly these partial steps. No new import or public
API is introduced. Change record: coord/changes/E1-smooth-purity-representing-trace.md.

Validation: the final module compiled through lcompile.py in 57.8 seconds, exit code 0,
with no errors or warnings. Profiling options were removed before this final check.

## Proved and sorry left

Original holes closed: 0 of 4. Holes added: 0. Split off: 0. This is partial proof work,
not a completed trace-definition repair or a claim that an original hole is reduced to
new admitted statements. All six added helpers are completely proved.

The four original holes remain:

- AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace (def-route-smooth-trace).
  The normalized finite data still need to be assembled into the actual matching
  Context/Datum, realized pairing, Tate comparison and target-unit comparison, and
  their counit composite installed as this definition.
- AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap
  (lem-route-is-iso-smooth-purity-map). Its existing missing-smoothness dispute remains.
  For the intended smooth case, the new helper constructs the comparison from the
  representing Hom pairing; the geometric inputs and trace identification remain.
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion
  (lem-route-smooth-purity-iso-zero-of-is-open-immersion). Identifying the actual
  normalized trace with the open counit is still required.
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_comp_openImmersion
  (lem-route-smooth-purity-iso-comp-open-immersion). The native mate calculation and
  final inversion are now complete, conditional on the actual trace transitivity
  equation and legitimate invertibility proofs. The geometric trace equation remains.

No arbitrary comparison is selected from an existence theorem, no new data definition
is introduced, and the disputed instance is not used to derive a contradiction.
The representing-pairing and purity-map mate proofs precede that instance. The final
inverse proof receives both invertibility witnesses explicitly.

## No longer needed

None. No imports, nodes, modules, declarations or dependencies are withdrawn. In
particular the finite geometric comparison, normalized tower, coefficient compatibility,
Tate realization, exceptional reconstruction and compositor realization inputs remain
needed to construct the actual pairing and prove trace transitivity. The helpers
remove an isomorphism hypothesis from the formal assembly, not the geometric work.

Searches: msearch.py LeanFinder for the normalized trace/exceptional-counit construction,
Loogle for Adjunction.homEquiv_counit, grep for smoothTrace/smoothPurityMap/
ReconstructionResult, and local searches of Mathlib and both library roots. Mathlib
supplies the adjunction, mate and Yoneda primitives used. No existing independent
constructor for the normalized native trace was found.

## Where the brief, the DAG or earlier work was wrong

The archived source already certifies that the elaborated isIso_smoothPurityMap
signature is false: SmoothOfRelativeDimension d f.left is absent, and the identity
of a separably closed point with proposed dimension one is a counterexample,
independently of the trace choice. No applicable upstream-statement exception
permits changing it. Its STATEMENT-DISPUTED annotation is preserved.

The actual remaining difficulty is not that dependencies have admitted proofs. The
native tower input already uses their declarations. The missing work is construction
of the normalized Context/Datum and canonical coefficient/site identifications tying
the actual Tate reconstruction to the realized pairing, followed by the actual trace
and its transitivity equation. This packet proves further formal assembly steps and
records those remaining inputs without claiming they have been constructed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
