## What changed

Proved `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_primeQuotient_injective_acyclicity`
in `Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange`, preserving its entire
signature and all public imports. Only the assigned Lean module and its existing DAG
node are changed. No definitions, instances, target statements, or consumer modules change.

The shortest usable route is the existing
`hasTorsionBaseChange_of_hasInjectiveAcyclicity` in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients`. Its implementation
already performs the planned injective-resolution argument, prime-factor induction,
and filtered-colimit passage. The additional work here is real coefficient-comparison
glue: transport the given abelian acyclicity to module-valued acyclicity over each
prime quotient, characterize the torsion hypothesis, apply the coefficient theorem,
and transport its specified exchange through the canonical compatibility equation.
The last transport includes the isomorphism commuting forgetting with `singleFunctor`.
The theorem docstring and node proof now describe these exact steps.

The LeanFinder search returned unrelated module/injectivity lemmas; Loogle returned
no match; the launcher grep search returned no match. Local source search found the
coefficient theorem and the canonical comparisons. Read their full declarations and
implementations, the original dependencies, Stacks 0A4B, and the current unit
`sk-thm-iff`. The reused theorem retains its injective-resolution, prime-factor, and
filtered-colimit route. Import-direction checks for the new proof imports passed;
none of the five new direct DAG dependencies has a path back to this item.

Validation: the complete proof compiles through the required `lcompile.py` with no
warnings or errors (latest run 21.8 seconds). All new lines are within 100 characters.
The acyclicity transport requires no nonzero-ring, characteristic, nonempty-scheme,
or nonzero-sheaf assumption: it applies unchanged to the zero quotient ring, the
zero sheaf, and empty schemes. The torsion bridge uses local torsion, not the false
assertion that all section groups have a uniform annihilator.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_primeQuotient_injective_acyclicity`
(node `lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change`).

Proved 1 of 1 original sorries; 0 sorries remain in the item; 0 holes added;
0 intermediate statements split off. Existing dependencies may still depend on
other library holes; this delivery adds none. This is a proof from existing named
declarations, not a decomposition or a proof of the entire transitive closure.

## No longer needed

Removed these eleven proof-only imports from the assigned module:

- `Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageColimits`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The module's import closure no longer contains these five project modules:
`Sheaf.AlgebraicGeometry.DerivedExchangeBoundedComparison`,
`Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`,
`Sheaf.AlgebraicGeometry.DerivedExchangeUnboundedTransport`,
`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`, and
`Sheaf.AlgebraicGeometry.KInjectiveResolutions`.
This is module-local pruning; other target branches may still need them.

All seventeen original proof dependencies are no longer direct dependencies of
this node. Resolution/termwise comparison is supplied by the existing coefficient
theorem, so this item does not separately use
`lem-weil-pbc-module-sheaves-enough-injectives`,
`def-weil-pbc-direct-image`, `def-weil-pbc-kinjective-resolutions`,
`lem-weil-pbc-kinjective-hom-derived`, `lem-weil-pbc-derived-exchange-termwise`,
`lemma-weil-pbc-underived-exchange-naturality`,
`lemma-weil-pbc-leray-acyclicity`, or `lemma-weil-pbc-proper-underived-exchange`.
Likewise its inherited devissage proof removes the need to apply separately
`lemma-weil-pbc-prime-torsion-devissage`,
`lemma-weil-pbc-direct-image-filtered-colimit`,
`lem-weil-pbc-inverse-image-preserves-colimits`,
`lemma-weil-pbc-derived-exchange-replacement`,
`lem-weil-pbc-derived-plus-iso-on-cohomology`,
`lemma-weil-pbc-five-lemma-transfer`, `lem-weil-pbc-five-lemma`,
`lem-weil-pbc-derived-exchange-triangulated`, and
`lemma-weil-pbc-prime-factor-induction`.
Several remain transitive prerequisites of the reused library theorem; none is
claimed unnecessary throughout the project. The node now records the five direct
dependencies actually used. Withdrew its two obsolete direct `tool_uses` entries,
`lem-weil-pbc-inverse-image-preserves-colimits` and
`lem-weil-pbc-module-sheaves-enough-injectives`.

## Where the brief, the DAG or earlier work was wrong

The planned proof was mathematically usable, but unnecessarily repeated theory
already implemented by the library coefficient theorem. The node's old lead note
also describes an outdated source interface: the current coefficient theorem does
accept prime-quotient injective acyclicity. Its hypothesis is module-valued; the
assigned statement's hypothesis is abelian-valued, so the canonical direct-image
and inverse-image comparisons are necessary and are proved in the local glue.
The recorded module for `hasTorsionBaseChange_of_hasInjectiveAcyclicity` on
`lemma-weil-pbc-property-iff-acyclicity` is stale (`BaseChangeProperty`); the actual
defining module imported here is `BaseChangeTheorems.Coefficients`. That node is
not modified in this delivery.

No statement was disputed or weakened. No new nodes or change records are needed.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
