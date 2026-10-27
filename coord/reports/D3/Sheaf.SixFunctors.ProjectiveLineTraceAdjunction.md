## What changed

Proved `AlgebraicGeometry.Etale.exists_presentedFiniteP1TraceAdjunction` from the
existing geometric declarations, preserving its complete public signature, including
the explicit compactification instance. The proof uses the actual transported datum:
its two integral comparisons give the kernel adjunction. A constructed coefficient
automorphism normalizes its trace; transporting the right adjoint through this
automorphism and tensor symmetry produces the prescribed inverse-projection counit.

All added definitions are actual constructions. In particular `kernelDatumWithTrace`
replaces the trace field without choosing any data from an unproved existence theorem.
No target, existing shared definition, public import, source declaration or attribute
was changed. Proof dependencies are private imports.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Etale.exists_presentedFiniteP1TraceAdjunction`.
There was one hole in the assigned module. No holes are added by this delivery.
The following added helper theorems are also proved (all in
`AlgebraicGeometry.Etale`):

- `presentedFiniteP1Datum_integral_comparison`
- `exists_presentedFiniteP1Datum_integrals`
- `exists_presentedFiniteP1KernelAdjunction`
- `exists_derivedTraceAdjustment`
- `exists_moduleTraceAdjustment`
- `exists_presentedFiniteP1RawAdjustment`
- `exists_presentedFiniteP1TraceNormalization`
- `kernelCounit_traceChange`
- `finiteP1TraceCounit_kernel_comparison`

No `sorry` remains in any of the ten delivered modules.
Existing imported geometric theorems remain proof dependencies, as stage 3 requires.

## No longer needed

No original dependency or module is pruned. The original public import is preserved. The finite Tate-line interface,
arbitrary-base integral identities and coordinate trace contractions remain needed
through the proved kernel-integral and kernel-adjunction modules. Using the existing
`SfDiagonalKernel.triangles` theorem packages the original unit route; it does not
prune that theorem's contraction dependencies. No module or DAG node is withdrawn.
Scratch imports used only for diagnosis are absent from the delivery. The first
packet mistakenly cited `prop-sf-pf-coherence` for a native source lemma. That node
is the later full six-functor package and reaches this adjunction. Its provisional
edge is replaced by the precise, already-proved source leaf
`lem-asd-source-proper-projection-coincidence`; no coherence package is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The first server preflight refused one newly introduced DAG cycle. The existing
native theorem `projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar`
is independent of the later node `prop-sf-pf-coherence`, despite sharing its blueprint
tag. A new source-leaf node records that exact declaration. Its independent axiom
probe returned only `propext`, `Classical.choice` and `Quot.sound`; its source file
and proof are unchanged. All nine new helper nodes now also record actual
LeanSearch queries, completing LeanSearch, Loogle/LeanFinder and Mathlib grep.

The existential integral-transport interface does not retain an equation specifying
its trace, so it is insufficient by itself for a prescribed-counit theorem. The proof
instead compares both integrals of the explicitly constructed `SfP1Transport.datum`.
The two coefficient identifications used in geometric transport and in the prescribed
trace need not be asserted equal: full faithfulness lifts their discrepancy to a
coefficient automorphism, and transport of the adjunction corrects the counit.

Concrete derived-category expressions carry different cached proof arguments.
Private proof automation constructs ordinary heterogeneous congruence proofs using
proof irrelevance, reducing only the named boundary definitions when necessary.
The Lean kernel checks the generated proof terms; no axiom or trusted shortcut is
introduced. Explicit object formulas for composition, flipped bifunctors and right
tensoring prevent expansion of large functor definitions; a proof cache reuses
repeated congruences. Generic categorical calculations precede geometric specialization to
avoid unfolding the large derived-functor constructions.

## New nodes

`lem-asd-presented-projective-line-datum-integrals`: comparison of both compact-support
integrals of the actual transported datum with conjugates of the ordinary integrals.

`lem-asd-presented-projective-line-kernel-integrals`: choose the supported class from
the diagonal property and deduce both compact-support integral identities.

`lem-asd-presented-projective-line-kernel-adjunction`: apply the lisse Tate-line kernel
triangle theorem to the actual datum, retaining its specified kernel counit.

`lem-asd-derived-trace-adjustment`: lift the discrepancy of coefficient comparisons
through a direct-image equivalence and compare the two derived trace composites.

`lem-asd-module-trace-adjustment`: specialize this calculation to module sheaves,
using the pull-push unit and equivalence along the presentation isomorphism.

`lem-asd-presented-projective-line-raw-trace-adjustment`: specialize the coefficient
calculation to the shifted Tate line and the explicit projective-line trace factors.

`lem-asd-presented-projective-line-trace-normalization`: unfold the two actual trace
formulas and identify the constant-complex unit comparison to obtain normalization.

`lem-asd-kernel-counit-trace-change`: construct the datum with a replaced trace and
prove its counit-change equation by projection naturality.

`lem-asd-finite-trace-counit-kernel-comparison`: proper projection coherence, braiding
naturality and the unitors identify the adjusted kernel counit with the ordered
inverse-projection counit.

`lem-asd-source-proper-projection-coincidence`: the fully proved generic native
proper projection-coincidence square already in
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence`. This is an
attachment to an existing source declaration, with no new Lean module or hole;
it is a closed source leaf rather than the later complete coherence package.

The nine new helper theorems are proved, not split-off holes. The proof-scope
commands of the item are recorded in
`coord/changes/D3-projective-line-trace-adjunction-proof-scope.md`. They are local
and export no interface change; the sole direct importer is checked unchanged.

Validation: all ten delivered modules passed the complete compile check. The item
and its unchanged sole direct importer also passed together (43.1 s and 47.7 s
reported respectively). The native source leaf passed its independent axiom probe.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
