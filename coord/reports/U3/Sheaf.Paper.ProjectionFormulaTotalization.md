## What changed

Reduced `SheafOfModules.ringedProjectionFormula_totalization` to forward compatibility,
and proved its inverse equations using the existing signed ordinary total mate and its
specified inverse. Added the general forward representative
identity in `Sheaf.Paper.ProjectionFormulaRepresentative` and updated the totalization
node to follow the Lean proof. Both existing public imports and every existing statement
are unchanged. Proof-only imports that the proof does not use were removed.

The main proof constructs the same canonical `eC`, `eB`, `t`, and `s` as the arrow
interface. It substitutes `pi ≫ eB.hom = eC.hom ≫ Q(t)`, localizes each ordinary
inverse equation, and cancels the representative isomorphisms. The second identity
is proved after postcomposing with the monomorphism `eB.hom`.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.ringedProjectionFormula_totalization`
(node `lemma-weil-pbc-projection-formula-totalization`).

Added one hole:
`SheafOfModules.ringedProjectionFormula_mixed_representative`
(node `lem-weil-pbc-projection-formula-mixed-representative`).

This is a decomposition: one upper hole closed, one strictly intermediate hole added;
net zero holes closed. The new statement only identifies the forward counit mate with
its localized chain representative. It assumes neither a finite-perfect package nor
invertibility of that chain map, and asserts no inverse equation. The main theorem's
finite-perfect inverse argument is complete Lean code.

The remaining lemma needs the mixed pullback comparison square and the naturality
of mixed tensor representatives. The detailed proof in its docstring and node resolves
the arbitrary first factor, uses the defining two-K-flat square for the canonical tensor
comparison, and transposes with `canonicalAdj` at K and its K-injective tensor target.
Zero coefficients and empty bounded support give zero complexes and satisfy this
forward equality; the comparison needs no chosen splitting or boundedness.

## No longer needed

Removed these direct proof-only imports:

- `Sheaf.Paper.StrictPerfectCoefficientPackage`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`
- `Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Algebra.Homology.KFlatResolutionGeneral`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Paper.ProjectionFormulaProjectiveSummand`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`

The former node's proof dependencies not used directly are:

- `prop-pur-kinjective-resolutions-exist`: K and its representing isomorphism are inputs.
- `lem-weil-pbc-kinjective-total-derived`: `computeR` is an input.
- `def-weil-abstract-derived-category`: localization functoriality is already available
  through the public arrow interface; it remains relevant to the new representative lemma.
- `def-weil-pbc-strict-perfect-coefficient-package`,
  `lem-pc-bounded-above-flat-kflat-site`, and `def-pc-flat-sheaf-modules`:
  the existing `StrictPerfectCoefficientPackage.isKFlat_flat` interface supplies the result.
- `lem-pc-kflat-resolution`, `def-pc-tensor-complex-sheaves`, `def-pc-kflat-complex`,
  `lem-weil-pbc-site-derived-tensor-descent`, and `lem-pur-quasi-iso-cone-acyclic`:
  no explicit resolutions or cone argument occur in the final inverse calculation;
  the new forward-representative lemma uses the needed resolution interfaces.
- `lem-weil-pbc-split-perfect-tensor-kinjective`: the existing arrow-interface
  `tensorAdjunctionTotal_target_isKInjective` supplies this assertion.
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`,
  `lem-weil-pbc-termwise-adjunction-homotopy`, and
  `lem-weil-pbc-right-adjoint-preserves-limits`: the existing ordinary total mate and
  its inverse supply the chain-level signed totalization; termwise adjunction remains
  relevant to the new forward-representative lemma.
- `lem-weil-pbc-ringed-topoi-derived-pullback` and
  `lem-pc-pre-derived-adjoint-functors-general`: the supplied `computeL`, `computeR`,
  and `canonicalAdj` interfaces determine the computations needed here.
- `lemma-weil-pbc-projection-formula-projective-summand`: the ordinary total inverse
  already packages its summand construction; the derived single-term theorem is not used.

These removals concern this proof's direct dependencies. Public dependencies of the
arrow interface remain reachable through that interface. No blueprint unit statement
or unit step is bypassed: lemma 1267 is not itself a realized unit step.

## Where the brief, the DAG or earlier work was wrong

The existing arrow interface already states the ordinary signed total isomorphism,
its uniquely determined inverse, the summand formula, and K-injectivity of its target.
The main inverse calculation therefore need not restate their construction or assume
that V(K) is K-flat. The remaining identification is a forward-arrow compatibility
problem, rather than another inverse assertion.

## New nodes

`lem-weil-pbc-projection-formula-mixed-representative` records the forward representative
identity from steps 9--11 of lemma 1267 in the main-20261015 blueprint. Its module is
`Sheaf.Paper.ProjectionFormulaRepresentative`. All search records are actual
U3 search calls. It leaves exactly the compatibility problem described above.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
