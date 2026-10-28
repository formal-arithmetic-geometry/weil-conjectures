## What changed

Implemented the finite condensed realization from the existing normalized continuous realization
and its section-module encoding. The finite functors are constructed, their full and faithful
instances are proved, and their scalar comparisons are obtained by adjunction transport and the
normalized coefficient square. An auxiliary finite field is constructed from a prime greater than
ell; no base-field structure on the scheme is assumed.

Moved the existing native scalar equivalence and comparison structure, unchanged, into the new
publicly reexported LocallyFiniteAdicCondensedStageData module. This prevents an import cycle with
the integral normalization lemma. The assigned theorem retains its original signature. It extends
an integral natural isomorphism uniquely through raw scalar localization and proves the full
representative formula by factoring through isoToStage and using naturality.

The remaining integral tensor normalization is stated separately, with the integral common-field
equation. It does not assert finite full faithfulness, rational naturality, or the general
representative formula. These parts are proved in this delivery. Explicit functor associators
avoid expensive kernel reduction across composed derived tensor functors; the final finite
construction compiled in 20.4 s and the assigned theorem in 20.9 s, below the unchanged 60 s
per-file limit.

Validation: all four delivery modules compile individually within 60 seconds. The unchanged direct
importer Sheaf.Paper.LocallyFiniteAdicFunctorDescentHom compiled against the delivered main module
in 10.7 seconds; its temporary sandbox copy was removed and is not part of the delivery.

## Proved and sorry left

Closed the original hole in
WeilConjectures.LocallyFiniteAdicRealization.condensedStageComparison_exists, from the existing
stated dependencies and one strictly smaller integral normalization lemma.

Added one hole: WeilConjectures.LocallyFiniteAdicRealization.finiteCondensedIntegralNormalization
(node lem-sf-locally-finite-adic-condensed-integral-normalization). The assigned module has zero
holes; the new normalization module has one. This is a decomposition of one hole into one, not a
net proof gain. No definition contains a hole.

Proved finiteData_exists, derivedExtendIso_isEquivalence, finiteRawFunctor_isEquivalence,
finiteCondensedEncoding_functor, finiteFunctor_fullyFaithful, finiteCondensed_constructible,
finiteCondensedFunctor_full, finiteCondensedFunctor_faithful, and the scalar comparison
constructions coefficientExtensionSquare, finiteSectionScalarComparison,
finiteCondensedScalarEncoding, finiteCondensedScalarComparison and
finiteCondensedClosureTransition. The private representative_of_stage_normalization supplies the
colimit calculation. Dependencies imported from the existing plan may themselves remain unproved.

## No longer needed

No mathematical module is withdrawn. The import Sheaf.Paper.AdicClosureScalarCoherence and its
node lem-sf-adic-closure-scalar-coherence are unnecessary for this finite-stage construction; no
claim of global unreachability is made. The finite rational realization route still uses integral
identity, inverse-completion coherence, rational realization, scalar coherence, constructibility,
and internal/section encoding. Only Core, ScalarData, ClosureData and finite_sections are needed;
the new FiniteCondensedData omits unused closure coherence fields. The original direct proof
dependencies lem-per-continuous-rational-derived-realization and
lem-sfb-internal-section-scalar-adjunction are replaced here by the existing rational realization
and scalar-adjunction APIs; no claim is made that these nodes are globally unused.

The original module's public imports are reexported through LocallyFiniteAdicCondensedStageData;
its two proof imports move with the definitions that use them. The main proof needs only the
integral normalization module and ScalarLocalizationNaturalIso. The proof does not apply
Hom-descent or essential-image results at the algebraic closure. The source TwoColimit module
remains imported for its finite scalar functors and specified tensor associators.

## Where the brief, the DAG or earlier work was wrong

The planned steps were mathematical descriptions rather than existing composable finite condensed
functors. This delivery constructs those functors and their normalized scalar comparisons from
existing declarations. The integral coefficient normalization remains the substantive missing
comparison. The unit route and every existing statement are preserved. The new lemma is restricted
to integral objects and integral naturality; the rational and colimit steps are actual Lean
proofs, so this does not merely rename the original obligation.

The private Core/image argument follows the existing AdicFiniteRealizationCocone proof. Its public
cocone theorem has additional geometric assumptions and its module imports closure tower
coherence. The finite construction retains only the needed argument; the original source module
and all its declarations remain intact.

## New nodes

The definition node def-sf-locally-finite-adic-condensed-stage-comparison-data records the
unchanged native scalar equivalence and comparison structure extracted into their own module.

The definition node def-sf-locally-finite-adic-finite-condensed-realization records the explicit
finite functor and its scalar construction. The proof uses the existing normalized continuous
realization data and the section-module equivalence.

The statement node lem-sf-locally-finite-adic-condensed-integral-normalization isolates the
integral portion of steps 3 and 4 of the assigned node, with the coefficient normalization and
balanced tensor argument written out in its docstring and DAG proof. Blueprint searches found no
duplicate.

Change record: coord/changes/locally-finite-adic-condensed-comparison-extraction.md.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LocallyFiniteAdicCondensedIntegralNormalization": "fd9e5a745689879c5b6a715630aa22c06b3b4b0f", "Sheaf.Paper.LocallyFiniteAdicCondensedStageComparison": "032fa1c593eef43898bbacf162330bef25c40998", "Sheaf.Paper.LocallyFiniteAdicCondensedStageData": "b53264faff77e91778819060681a622f8add65d7", "Sheaf.Paper.LocallyFiniteAdicFiniteCondensedRealization": "8925c282b87fc0013f5bb2746d6e6876c133b7ac"}, "results": {"Sheaf.Paper.LocallyFiniteAdicFunctorDescentHom": {"hash": "e8e156c1f20b1c6e526da58674687dde7dc723bb", "status": "OK"}}, "seconds": 45, "time": "2026-10-28T12:44:26+0800", "transitive": 0, "version": 1}
```

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
