## What changed

Proved `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_integralSurjective_target`
in the assigned module, with its signature and public imports unchanged. The proof specializes
`_hprev` to the base change `f'`, then applies the existing arbitrary-coefficient fixed-base
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective`
from `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange`.
The natural-to-integer inequality is discharged by `omega`; `π.surjective` supplies the
underlying-map surjectivity. The two squares paste in exactly the orientation required by
the source theorem. Updated the theorem docstring and the node's proof, proof dependencies,
and proof origin to this route, withdrawing its obsolete top-level tool approvals.

The source theorem's proof uses the adjunction unit, integral pushforward arrow comparison,
critical-map injectivity, and vanishing of the cokernel. It retains the current blueprint's
integral-surjective target-change argument within the universal-datum unit. There is no
new intermediate theorem or circular application. `import_direction.py may` returned yes.
The assigned file compiled cleanly through `lcompile.py` in 10.8 seconds.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_integralSurjective_target`
(node `sbc-lem-bc-integral-surjective`). Zero local holes remain; zero holes were added;
zero statements were split off. This is a proof from an existing library theorem, not a
new decomposition. This does not assert that all transitive input theorems are axiom-free.

## No longer needed

Removed the following 11 direct proof imports. The source theorem already packages the
unit/cokernel and derived-pasting argument, so repeating those inputs here is unnecessary.
Some remain transitively needed by the reused source theorem; no whole-library module
withdrawal or global unreachability is claimed.

- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Integral.BaseChange`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.ExchangeIdentityPasting`
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`
- `Sheaf.AlgebraicGeometry.IntegralEtaleDirectImageExact`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

The old direct proof dependencies below are no longer used directly by this node. They are
replaced by `lem-sbc-module-bc-integral-surjective`, whose existing Lean attachment is the
source theorem. Several remain dependencies of that theorem; this is direct-edge pruning.

- `pqf-lem-integral-univclosed`
- `lem-weil-pbc-affine-morphism-permanence`
- `lem-weil-pbc-universally-closed-base-change`
- `def-weil-pbc-inverse-image`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `lem-weil-pbc-geometric-stalks-detect-mono`
- `prop-weil-pbc-inverse-image-modules-exact`
- `def-weil-pbc-direct-image`
- `sbc-lem-bc-injectivity`
- `lem-sbc-integral-underived-exchange`
- `sbc-lem-integral-etale-direct-image-exact`
- `lem-weil-pbc-exact-functor-derived-functor`
- `sbc-def-base-change-map`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-exchange-identity-pasting`
- `lem-weil-pbc-exact-functor-complex-cohomology`

All eleven old top-level `tool_uses` entries are withdrawn, since none is directly used by
the new two-step proof. The four public statement imports are preserved so downstream
visibility is unchanged.

## Where the brief, the DAG or earlier work was wrong

The expanded seven-step plan overlooked an existing exact generalization in the source
library, already attached to `lem-sbc-module-bc-integral-surjective`. Its fixed-base
hypothesis follows immediately from this item's universal hypothesis. No statement repair
is required. The current blueprint update is respected: integral-surjective descent is
still the operation being applied, and the reused proof follows its unit/cokernel route.

Read Stacks `etale-cohomology.tex`, Tag 0F04, `lemma-base-change-q-integral-top`,
and the source theorem and its arrow-comparison helper. The source text has a harmless
extra inverse-image symbol in its first sentence; the Lean unit correctly has target
`π_* π^* F`. The boundary cases q = 1, n = 1 (zero coefficient ring), identity π,
and empty schemes are all admitted by the unchanged theorem and its general input.

Searches run through `msearch.py`: LeanFinder for integral-surjective detection returned
geometric base-change permanence and ring lemmas only; Loogle `"IsIntegralHom", "IsIso"`
returned only the normalization isomorphism; grep for the source theorem's name returned
no Mathlib result. Direct `rg` on the source library found the exact theorem.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
