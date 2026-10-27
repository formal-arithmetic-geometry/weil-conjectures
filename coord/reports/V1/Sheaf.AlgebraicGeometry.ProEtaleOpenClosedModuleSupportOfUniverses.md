## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.proEtaleOpenClosedModuleSupportOfUniverses` without changing its
statement, universes, hypotheses, or public imports. All added imports are private proof imports.

For vanishing, the inverse-image and sheafification adjunctions identify maps out of the
closed pullback with maps from the actual direct-sum presheaf into closed direct image.
Each summand has empty closed fibre, so every such map vanishes. This proves that the
closed pullback is initial and therefore zero. It needs only disjointness.

For detection, the affine basic-open/closed-localization cover from Stacks 09AH works with
sections in `max u (t+1)`. The ring-retraction evaluation theorem already allows that universe.
The proved independent-universe abelian specialization theorem makes the actual closed
units bijective on the closed-localization pieces. Naturality detects bijectivity of the
module map there. Evaluation of the slice restriction does so on the open pieces.
Local bijectivity gives an isomorphism of abelian sheaves, and forgetting modules reflects it.

The private covering helpers adapt the geometric argument of
`ProEtaleRingedLocalizationSequence`; only section universes change. They invoke the
existing ring-extension, localization, and evaluation declarations directly. No existing
shared module, definition, instance, or interface was changed. The DAG proof and proof
dependencies now describe this argument. The unit's statement and realized steps stay intact.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.proEtaleOpenClosedModuleSupportOfUniverses`
(node `lem-sf-open-closed-module-support-of-universes`).

One hole closed; zero holes added; zero holes left in the delivered module.
Remote single-file compilation passed cleanly in 10.7 seconds.
Every private helper is proved. No split-off statement or module is introduced.

## No longer needed

No original import was removed: the public imports provide the statement's constructions
and the independent-universe sheafification instances. Every added proof import supplies a
construction or theorem used by the proof.

The following former proof dependencies are unnecessary for this item:

- `lem-weil-pbc-proetale-shriek-specialization-zero`, module
  `Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero`: the adjunction Hom argument
  proves vanishing directly, without specialization of shriek sections.
- `lem-weil-pbc-proetale-module-specialization-unit`, module
  `Sheaf.AlgebraicGeometry.ProEtaleModuleSpecializationUnit`: detection needs the underlying
  abelian unit only; the independent-universe abelian theorem supplies it.
- `lem-weil-pbc-proetale-ringed-localization-sequence`, module
  `Sheaf.AlgebraicGeometry.ProEtaleRingedLocalizationSequence`: local bijectivity replaces
  constructing and comparing module short exact sequences.
- `lem-weil-proetale-weakly-etale-localization`, module
  `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`: the actual slice restriction
  can be evaluated directly, so an equivalence with the site's presentation over U is unused.

These are removals from this item's proof route, not assertions that the modules are unused
elsewhere. No library module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan cites module-specialization and localization-sequence statements whose
Lean signatures tie the coefficient universe to the scheme universe. They cannot directly
be specialized to this item's independent universes. The abelian specialization theorem
`lem-u9-proetale-abelian-specialization-universes` and the already universe-polymorphic
ring-retraction evaluation theorem avoid both a new module inverse-image construction and
a new localization-sequence obligation. No mathematical statement was weakened or disputed.

The empty source, empty closed fibre, empty covering or direct sum, zero ring, and identity
closed immersion use the same proofs. No nonemptiness, quasi-compactness of X, or separation
hypothesis is introduced.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
