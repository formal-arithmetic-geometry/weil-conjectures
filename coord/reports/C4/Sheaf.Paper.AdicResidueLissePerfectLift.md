## What changed

Restored the assigned quarantined module; the main theorem signature is textually identical
to the archived signature. Its proof now constructs an invertible-residue compatible family
in the actual reduction Hom tower, lifts it to a morphism, applies residue conservativity,
and restricts the resulting isomorphism to arbitrary members of the covering sieve.

Moved all six original coefficient definitions, textually unchanged, to
Sheaf.Paper.AdicResidueLiftComparisons, publicly reexported by the assigned module.
That companion constructs the actual scalar-reassociation comparison, conjugated Hom
successor, Hom tower and compatible section. Every definition is constructed; none contains
an admitted field. The comparison uses the proved adicFiniteExtendComp of
Sheaf.Paper.AdicConstructibleFiniteReductions, without adapting that module.

Sheaf.Paper.AdicCompleteHomSections proves compatible-section lifting. It derives the
surjective half of the Milnor Hom sequence from coyoneda_exact₂ and product projection
identities, transports sections using the normalized scalar adjunctions, and checks that
the lift has exactly the given reductions. It needs no boundedness, perfectness or ML
condition on the source. The main file also proves stable-image selection and preservation
of invertibility under all normalized reduction transitions as private helpers.

Four genuine source results are isolated in their own modules: finite local models,
perfect-reduction Hom ML, the normalized completion cone, and complete-object residue
conservativity. The original eight-step source route remains; its geometric and completion
parts are assigned separate obligations. No target, parent dependency or unit is bypassed.

Validation: all seven sandbox modules compiled together in import order through lcompile.py,
without warnings. The main file took 3.8 seconds in the last complete run. Textual checks
verified the original theorem signature and all six moved definition bodies. Edge cases
checked against the sources: empty X (empty covering), J=0 (constant quotient tower), J=A
(zero completed coefficients), zero perfect complex, and arbitrary sieve refinements.
Neither finite quotient sets nor perfectness of A/J^n over A is assumed.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.Scheme.adicResidueLissePerfectLift
(lem-sfb-adic-residue-lisse-perfect-lift), by a complete combining proof.
Also proved the new AlgebraicGeometry.Scheme.adicResidueHomSection_surjective
(lem-sfb-adic-complete-hom-section-surjective), including its Milnor-surjectivity helper.
The stable-image and successor-isomorphism private helpers are fully proved.

Added four holes, each an entire named public theorem with a source and complete proof
in words, and each strictly a separate part of Stacks 09C6:

- AlgebraicGeometry.Scheme.adicResidue_finite_local_models —
  lem-sfb-adic-residue-finite-local-models, Sheaf.Paper.AdicResidueFiniteLocalModels.
  Only individually isomorphic finite reductions and their local algebraic model; no
  compatible family, morphism, or completed-coefficient isomorphism is concluded.
- AlgebraicGeometry.Scheme.adicResidueHomTower_mittagLeffler —
  lem-sfb-adic-perfect-reduction-hom-ml, Sheaf.Paper.AdicPerfectReductionHomML.
  Stabilization of the actual Hom tower; no lifting conclusion.
- AlgebraicGeometry.Scheme.adicResidue_complete_reduction_cone —
  lem-sfb-adic-complete-reduction-cone, Sheaf.Paper.AdicCompleteReductionCone.
  Structural quotient homotopy-limit presentation with its actual adjunction units;
  no compatible-family lifting conclusion and no perfect model hypotheses.
- AlgebraicGeometry.Scheme.adicResidue_isIso_of_residue —
  lem-sfb-adic-complete-residue-conservative, Sheaf.Paper.AdicCompleteResidueConservative.
  Derived Nakayama for a given morphism between complete objects; no existence of morphisms.

The assigned module contains zero remaining sorry occurrences; the delivered packet has
four. This is a decomposition of one original hole into four separate source obligations,
not a claim of a net proof gain. The main theorem remains transitively dependent on admitted
results. No sorry is inside a definition, private theorem, or a partial proof.

## No longer needed

The route no longer uses lem-weil-pbc-ml-sets-tower-limit-nonempty or its source module
WeilConjectures.AlgebraicGeometry.MLSetsTowerLimitNonempty. The stable-image selection is
proved directly with Mathlib eventual ranges and surjective projection from their tower.
The obsolete approval entry is removed from the item's top-level tool_uses list.
No source declaration or module is withdrawn; this is pruning from this proof route only.

The original private proof imports below are removed from the item itself. Apart from the
ML-sets lemma just identified, their underlying source inputs are retained in the new
subnodes' proof plans as appropriate; they are not claimed globally unnecessary. The
original public statement imports are relocated to the publicly imported comparison module.
The main file now has precisely its four used proof imports and the Mathlib images import.

- Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence
- Sheaf.Algebra.Homology.KFlatTelescopeClosure
- WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
- Sheaf.Paper.ConstantModuleSectionProperties
- WeilConjectures.AlgebraicGeometry.MLSetsTowerLimitNonempty
- Sheaf.Paper.NilpotentReductionLissity
- Mathlib.RingTheory.Ideal.Quotient.Defs
- Sheaf.Algebra.Homology.KFlatCoefficientUniverse
- Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
- Sheaf.Paper.PbcActualScalarPullback
- Sheaf.RingTheory.RlimPerfectComplete
- Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
- Mathlib.RingTheory.Ideal.Quotient.PowTransition
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
- Sheaf.Algebra.Homology.DerivedChangeOfRings
- Sheaf.Paper.TorsionLimitSheafCompleteness
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
- Sheaf.Paper.AdicConstructibleFiniteReductions
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.Paper.WContractibleConstantReductionsML
- Sheaf.SixFunctors.ConnectedEtalePerfectConstant

## Where the brief, the DAG or earlier work was wrong

The missing live file is a quarantined restoration item, not an unused statement. Its archive,
Lean attachment, original statement, DAG parent and unit route are preserved.
The already proved ResidueLissePerfectLift theorem uses a coefficient datum requiring
finite and perfect quotients, and cannot discharge this arbitrary Noetherian-coefficient item.

A covering sieve contains arbitrary refinements of the weakly contractible covering
objects; those refinements need not themselves be weakly contractible or affine. The new
finite-model statement therefore supplies the original affine weakly contractible V and
a restriction functor to U with the two required object comparisons. The main proof lifts
on V and then restricts the isomorphism to U. This makes the source's covering-family
argument match the existing covering-sieve conclusion exactly.

The normalized completion cone and perfect-duality-to-actual-Hom identifications are not
themselves stated by the broad source dependencies with these coefficient-sized slice
objects and scalar actions. They are recorded as separate source-backed obligations rather
than silently identifying arbitrary choices of derived objects or finite-level markings.
No existing statement is marked disputed. No other group's module is adapted.

## New nodes

- def-sfb-adic-residue-lift-comparisons: unchanged original coefficient definitions plus
  the constructed local reduction comparisons and actual Hom tower.
- lem-sfb-adic-residue-finite-local-models: the geometric and algebraic finite-model half
  of Tag 09C6, with completeness and restriction to covering-sieve refinements.
- lem-sfb-adic-perfect-reduction-hom-ml: the dual perfect complex and exact-section
  calculation needed to apply Tag 09C5 to the actual Hom tower.
- lem-sfb-adic-complete-reduction-cone: quotient completion with normalized scalar
  adjunction units and successor maps on the actual slice.
- lem-sfb-adic-complete-hom-section-surjective: proved representable lifting from that cone.
- lem-sfb-adic-complete-residue-conservative: the general complete-cone/Nakayama final step.

All new nodes inherit sec-six-functors-basics and sk-lem-integral-models, point back to
det-lem-integral-models-stacks through the original item's ancestry, record the actual
searches, and cite the source passages they isolate. Blueprint searches for 09C6,
quotient homotopy, perfect constant and derived Nakayama found no equivalent arbitrary
Noetherian-coefficient statement; the existing derived-Nakayama blueprint results use DVR
coefficients. The main node now records the actual four-step combining proof and its direct
dependencies; the geometric source obligations remain reachable through the new nodes.

Change record: coord/changes/C4-adic-residue-lift-comparison-location.md.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
