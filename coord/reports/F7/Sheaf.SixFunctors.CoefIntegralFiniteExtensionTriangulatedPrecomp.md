## What changed

Proved `WeilConjectures.IntegralFiniteExtension.comparison_precomp_triangulated`
for the corrected, source-intended existential shift statement. The former statement
asserted exactness for every coherent shift, which is false. The replacement constructs
an exact shift rather than inferring exactness from coherence alone.

The private `scalar_homotopy_exact` identifies the concrete scalar complex with the
shifted cone of the ordinary module-product endomorphism `1-s`. The new, fully proved
`CochainComplex.termwiseCone_homotopy_exact` realizes that cone as evaluation of a two-term
complex of additive functors and applies the adopted total-bifunctor triangulation theorem.
The main proof uses flat-term K-flat resolutions, scalar quasi-isomorphism preservation,
`Functor.leftDerived_from_resolvingClass`, and the normalized uniqueness clause of
`integralScalarExtensionWellDefined`. Transporting the exact shift along the resulting
isomorphism proves the requested precomposition exactness.

Adapted the unclaimed module
`Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibilityTriangulated`:
its intermediate descent theorem now takes exactness of the precomposition for the same
chosen shift, and its final existential theorem obtains that shift from the item.
The final existential declaration retains its signature verbatim. No existing definition,
public import, target statement, or adopted source-library file was changed.

Validation: the helper, item, adapted parent, and unchanged direct consumer
`Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility` compiled in import order,
without warnings, in 18.2 s, 40.7 s, 7.6 s and 6.7 s respectively. The unchanged consumer
copy was removed from the delivery after compilation. All delivered Lean lines are at most
100 characters. The required delivery preflight performs the independent declaration checks.

## Proved and sorry left

Original item holes: 1, in
`WeilConjectures.IntegralFiniteExtension.comparison_precomp_triangulated`.
Current item holes: 0. Added holes: 0. Split-off unproved statements: 0.
This is a correction and proof of the intended existence assertion, not a proof of the
false discarded arbitrary-shift assertion.

The new public theorem `CochainComplex.termwiseCone_homotopy_exact` is fully proved,
including the natural cone comparison; its concrete `termwiseCone` definition contains
no missing data or proofs. The private `scalar_homotopy_exact` is fully proved.
Both parent theorems remain fully proved. There is no `sorry` left in any delivered file.
The existing `HomotopyCategory.instIsTriangulatedIntUpObjFunctorBifunctorMapHomotopyCategory`
is attached to a new DAG node; its source file is not edited and it already has a complete proof.
No data are selected in a definition from an unproved existence theorem.

## No longer needed

The item's old direct proof dependencies `lem-pur-derived-change-of-rings` and
`lem-weil-pbc-ringed-strict-tower-homotopy-limit` are replaced by the actual module-level
Roos cone comparison, general termwise-cone exactness, and resolving-class derivation.
The conditional descent lemma no longer needs a proof-dependency edge to precomposition
exactness: it takes that assertion as a hypothesis. The final existential parent now
cites the precomposition existence theorem directly and no longer selects an arbitrary
coherent shift from `integralScalarExtensionWellDefined`.

No whole library module is withdrawn or claimed globally unnecessary: the former direct
dependencies remain relevant transitively elsewhere, including in scalar well-definedness.
No existing import was removed. Redundant explicit imports of MappingCone, AdditiveFunctor,
and ContainsZero were removed from the new helper after its proof compiled; the remaining
imports supply its actual signatures and proof APIs. All proof-only imports are private.
The blueprint unit's route is retained.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old item and the old intermediate parent asserted exactness
for an arbitrary coherent `CommShift`. Twist an exact shift comparison by `(-1)^n`.
For identity scalar extension at l=3 on complete coefficient modules at a point, consider
the nonsplit sequence Z_3 --3--> Z_3 --> F_3. Its nonzero connecting class delta has
order 3. The twisted shift leaves the first two triangle maps fixed and replaces delta
by -delta. Those triangles cannot both be distinguished: a comparison with identity on
the first two vertices has to be identity on F_3, whereas delta is not -delta.
Thus a compatibility or exactness assertion for the selected shift is indispensable.
The blueprint's claim is existence of an exact shift, which is what the final parent
already states. That public existential interface and every target statement are preserved.

The node proof's instruction to prove exactness with an arbitrary selected shift was
therefore incorrect. The delivery supplies a genuine chain-level argument and localization
transport, not another renaming of that obligation. Change record:
`coord/changes/F7-integral-finite-extension-exact-shift.md`. The two statement corrections
carry the old statements and complete base-citer audits in `statement_change`.
The `by` field follows the tool's required `<group> stage 2` correction-record syntax;
this work and delivery are stage 3.

## New nodes

`lem-sf-termwise-cone-homotopy-exact` records the fully proved general cone lemma and
its concrete functor in `Sheaf.Algebra.Homology.TermwiseConeHomotopyExact`. It handles
unbounded complexes and zero functors without abelian or flatness assumptions; countable
coproducts supply the totalizations used by the existing API. Its naturality is checked on
the two cone inclusions, including the shifted source. It introduces no unproved obligation.

`lem-sf-total-bifunctor-homotopy-exact` attaches the existing fixed-argument triangulatedness
instance in `WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated`; its generated
name was checked with `#synth`. This records the actual general theorem used by the helper,
without copying or editing the adopted source. Both new nodes have source proofs,
blueprint origin and actual LeanSearch, LeanFinder/Loogle, and grep search records.
Blueprint searches for mapping cones, additive functors and scalar extension found no
existing blueprint assertion of either generic lemma.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Algebra.Homology.TermwiseConeHomotopyExact": "0b0c02be19da45ceb6c21cd8826075d2701fa6ef", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibilityTriangulated": "056cb0b955ee63af2d231fb8578c48a1e21ccaec", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionTriangulatedPrecomp": "ea8ce6f8f49c9d0fe633c8b3685afb771f2d61a4"}, "results": {"Sheaf.Paper.ConcreteIntegralProjectionCone": {"hash": "f3d4832ddb372eed3cdf9a1d5fbab9b893d2bf7c", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility": {"hash": "bc6d2cee3ee60dda8a76937e86a1e840f78ccc55", "status": "OK"}, "WeilConjectures.WeilSheaf.VerdierDual": {"hash": "cbd782ced4a4ed0d3932076da1a163a61a8db8c5", "status": "OK"}}, "seconds": 213, "time": "2026-10-28T12:22:01+0800", "transitive": 2, "version": 1}
```

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
