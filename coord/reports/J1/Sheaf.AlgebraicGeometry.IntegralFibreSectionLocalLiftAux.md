## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Etale.exists_integralStrictLocalFibreComparison` with a complete Lean
assembly. Its signature, public imports and existing docstring are unchanged.
The proof uses the existing strict-henselization local structure and pointed-map theorem.
It constructs t as Spec.map of the pointed ring map, proves its structural-map equation
from a limit-leg identity, proves its closed-point equation, constructs i by pullback.lift,
and proves the geometric-fibre square by pullback pasting. It then proves invertibility
of a constructed module restriction by combining the general integral closed-fibre
comparison with inverse-image composition and terminal-section isomorphisms. The final
compatibility theorem supplies exactly the required neighbourhood formula.

Added two new modules, each with one public theorem left sorry:
`Sheaf.AlgebraicGeometry.IntegralStrictHenselianGeometricFibreSections` and
`Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility`.
The latter also defines `strictLocalFibreRestriction` by an explicit composite of existing
maps and isomorphisms. It contains no choice from an unproved existence assertion and no
sorry in its data. All existential witnesses used from the pointed-map theorem occur
only inside the original theorem proof.

The two obligations separate the algebraic section-isomorphism argument from the purely
categorical compatibility argument. The first has no strict-henselization, stalk or
neighbourhood statement. The second has no integral or local-ring hypothesis and makes
no invertibility assertion. The main proof combines both and constructs the intervening
scheme maps itself. No existing statement, definition, visibility or target changed;
no forced adaptations or change records are needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.exists_integralStrictLocalFibreComparison`
(node `lem-sbc-integral-strict-local-fibre-comparison`). No sorry remains in the assigned module.

Added these two named holes, each in its own new module with a source and proof docstring:

- `AlgebraicGeometry.Etale.isIso_integralStrictHenselianGeometricFibreRestriction`
  (node `lem-sbc-integral-strict-henselian-geometric-fibre-sections`).
- `AlgebraicGeometry.Etale.strictLocalFibreRestriction_compatibility`
  (node `lem-sbc-strict-local-fibre-restriction-compatibility`).

This is a decomposition: one upper hole closed and two lower holes added, net minus one
before subsequent proofs. It does not claim a sorry-free mathematical proof.
The new definition `AlgebraicGeometry.Etale.strictLocalFibreRestriction` is a real
construction. All three modules compile through lcompile.py in import order.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.RingTheory.IntegralOverHenselianPair`
- `Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension`
- `Sheaf.AlgebraicGeometry.EtaleModuleSetPullbackComparison`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero`

Their nodes remain required by the general closed-fibre isomorphism argument and their
modules are imported by that new module. The old direct dependencies
`lem-weil-pbc-integral-over-henselian-pair`, `lemma-weil-pbc-etale-degree-zero`,
`lem-weil-pbc-sections-base-field-extension`, and
`lem-sc-etale-module-set-pullback-comparison` now occur below that intermediate node.
The qcqs restriction node remains below the compatibility node and its public import
still supports the assigned theorem's signature. The strict-henselization limit and
structural map remain needed by the pointed-map construction. No original planned node
or entire module is claimed pruned from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The planned mathematical argument is valid, but its ring-to-scheme transports and
inverse-image-unit coherence do not fit directly into the existing declarations as
one short proof. The two new interfaces isolate those strictly separate obligations.
The existing `strictHenselizationModuleFibre_factorization` interface could instead
supply a stalk-based assembly, but its olean is absent from the shared compiled build.
I did not copy or restate it. The final route uses the available pointed-map theorem and
explicit pullback construction, and needs no continuity or neighbourhood-representative
existence theorem.

The existing `strictHenselianIntegralSections_injective` states only injectivity, rather
than the invertibility needed here. Proper geometric-fibre comparison assumes a proper
morphism and an algebraic closure of the residue field, whereas an integral morphism need
not be finite and Omega may be transcendental. Thus neither interface alone closes the
new general isomorphism statement. The henselian-pair identity comparison and arbitrary
separably closed field-extension theorem supply the stated route.

Read the source-library global-section composition and inverse-image-unit coherence
identities. Mathlib searches with msearch.py: LeanFinder gave etale ring-locus and local
ring-map results, Loogle and grep gave no exact section comparison; LeanSearch returned
Internal Server Error and is recorded as unavailable. Local rg over the two library roots
found the degree-zero henselian theorem and the general composition identities, but no
exact replacement for the two assembled interfaces.

The local Stacks TeX named by the existing node is absent. Checked the official pages
[09XK](https://stacks.math.columbia.edu/tag/09XK),
[09ZH](https://stacks.math.columbia.edu/tag/09ZH),
[0A3I](https://stacks.math.columbia.edu/tag/0A3I), and
[0EYP](https://stacks.math.columbia.edu/tag/0EYP). The first three justify the henselian
closed-fibre route. The published proof of 0EYP uses finite approximation; the assigned
DAG already selects the henselian alternative below the unit level.

Edge cases checked: B=0 gives the empty affine scheme and zero section modules; the
coefficient ring may be zero; a transcendental Omega is allowed by 0A3I; the compatibility
statement requires only the specified leg equations and two pullback projections, so
it applies without integrality and even to empty schemes. Compatibility is asserted for
the explicitly constructed restriction map, never for an arbitrary module isomorphism.
The unit `sk-lem-universal-datum` has empty realization lists for its statement and steps;
no unit statement or realized step is bypassed or changed.

## New nodes

`lem-sbc-integral-strict-henselian-geometric-fibre-sections` is the algebraic closed-fibre
isomorphism step, with a general strictly henselian base. Its proof follows integral
henselian pairs, the degree-zero henselian identity comparison, base-field-extension
invariance, module/set comparison, and global-section composition.

`lem-sbc-strict-local-fibre-restriction-compatibility` describes the explicit composite
`strictLocalFibreRestriction` and its compatibility. Its proof follows naturality and
coherence of inverse-image units, terminal-object transports, the pointed leg identity,
and uniqueness of the two iterated pullback lifts. Both node files live under
`dag/nodes/sec-smooth-base-change/`. The assigned node's proof, proof_deps and proof_origin
now follow the actual Lean assembly. No change records.

## Second reading by J1

1. I compared the delivered assigned module with the repository version. The existing theorem signature and statement are byte for byte unchanged; only its proof and proof imports changed. The two added modules introduce the declarations recorded by the two new DAG nodes.

2. I compiled all three modules with `lcompile.py --all`. They compile without errors. The assigned theorem has no `sorry`; the two split-off theorem declarations are the only remaining `sorry`s, and neither definition contains `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`.

3. I checked the two split-off statements against their docstrings and DAG nodes. The geometric-fibre theorem states exactly the integral strictly henselian restriction isomorphism needed by the main proof, while the compatibility theorem states only the explicit restriction formula and has no extra integrality or invertibility assumptions. Local search found no pre-existing declaration with either name or statement.

4. I checked the proof route from the target downward. The main proof constructs the strict-local map from the pointed-map theorem, establishes the structural and closed-point equations, lifts into the pullback, applies the integral geometric-fibre interface, and uses the explicit compatibility interface. Removed direct proof-only imports are listed above; the remaining imports support signatures or this route. The unit and its realized route are unchanged.

5. The DAG node proof, proof dependencies, and proof origin match the declarations and calls in the delivered Lean. The two added nodes contain sources, proof steps, searches, and matching `lean` records. No statement or definition was changed.

I changed only this report by adding the required second-reading record. No Lean source or DAG content required repair.
