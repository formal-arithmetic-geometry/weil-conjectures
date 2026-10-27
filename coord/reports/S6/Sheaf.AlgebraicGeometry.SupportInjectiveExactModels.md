## What changed

Filled `AlgebraicGeometry.ProEtale.supportInjectiveExactModels` in
`Sheaf.AlgebraicGeometry.SupportInjectiveExactModels`, preserving its statement and all
six public imports. Private proved helpers identify the two supported-kernel
presentations, transfer the existing closed adjunction, construct the open-section
comparison, and construct the supported-section comparison with its specified inclusion
normalization. A private generic composition helper proves the three-unit identity
using a private explicit composition isomorphism, the published composition
factorization, the identity composition comparison,
and naturality of the derived unit; this avoids unfolding concrete sheaf functors.
The main proof assembles the exact row, lower bounds, injectivity,
right-derived comparisons, section restriction surjectivity, and chain-map naturality.

The route uses the existing ordinary-coefficient pro-etale APIs in
`Derived.SupportsExact`, the public `LowerShriek.Open.Defs` API, and
`RightDerivedFunctor.PlusComp`. The DAG proof and proof dependencies are updated to
match this route. No definitions or public signatures are changed. No other module is
adapted, and no source-library declaration is changed.

`coord/changes/support-injective-models-local-elaboration.md` records the local
reducibility attributes, which the delivery classifier treats as command changes.
They control this proof only and export no changes to consumers.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.supportInjectiveExactModels`
(`lem-pur-support-injective-exact-models`). Added zero holes. No `sorry` remains in the
item, and there are no new modules or split-off statements.

The statement was compared textually with the repository version and is unchanged.
All private helpers have complete proofs or explicit isomorphism constructions.
The complete proof compiled through `lcompile.py`. Profiling identified costly
kernel unfolding of the assembled derived comparison; it is now held in a private
irreducible definition with its proved factorization API. Delivery performs the
clean compile and axiom checks.

## No longer needed

Removed the following proof imports and their corresponding proof dependencies:

- `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint`
  (`lem-sf-ringed-closed-kernel-adjoint`): the ordinary-coefficient closed adjunction
  already exists; evaluation preserves the kernel and transfers that adjunction to
  `finiteClosedUpperShriek`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`
  (`lem-weil-pbc-proetale-ringed-open-comparison`): the published
  `upperStarIsoOpenImmersionRestriction` supplies the comparison directly.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
  (`lem-weil-proetale-weakly-etale-localization`): no separate slice equivalence is
  needed beyond the published ordinary restriction adjunction.
- `Sheaf.CategoryTheory.RingedSiteInjectiveMonoRestriction`
  (`lem-pur-ringed-site-injective-mono-restriction`): the existing split epimorphism
  theorem for the injective open unit gives surjectivity after applying global
  sections and the comparison isomorphisms.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
  (`lem-weil-pbc-ring-sheaves-grothendieck`): published ordinary coefficient sheaf
  Grothendieck instances already supply enough injectives.

Also removed the redundant explicit import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Exact`: its
finite-limit-preservation instance and adjunction are already supplied publicly by
`LowerShriek.Open.Defs` through `Derived.SupportsExact`.

Also removed the redundant explicit imports
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`,
`Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective`,
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`, and
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`. The statement imports and
bounded-below composition theorem already provide the relevant APIs.

Also removed the proof dependencies
`def-weil-proetale-inverse-image`,
`lem-weil-pbc-exact-functor-complex-cohomology`,
`lem-weil-pbc-bounded-below-injectives-kinjective`, and
`lem-weil-pbc-kinjective-hom-derived`: the theorem is stated in bounded-below derived
categories, and its canonical units and composition isomorphisms are provided by
Mathlib and the existing composition theorem. No unbounded replacement comparison
or separate quasi-isomorphism-preservation argument is required.

Removed the obsolete top-level `tool_uses` approvals for the eight unused ringed-site,
localization, and unbounded-comparison dependencies listed above. Retained
`lem-pur-support-exact` and the historical split/review records unchanged.

These are dependencies unused by this proof, not requests to withdraw their
modules. Existing source declarations, their imports and all unit statements and
routes are preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG's ringed-site transport route was longer than necessary for this
ordinary `Sheaf ... (ModuleCat A)` statement. Its bounded-below conclusion can also
be proved directly without passing through unbounded K-injective replacements.
The imported statement and canonical maps are correct and are unchanged.

The ordinary-coefficient APIs replace the ringed open/closed preservation dependency
`lem-weil-pbc-proetale-ringed-open-closed` as well. These are tools for the same
injective support argument; no unit statement or unit proof step is bypassed.

The terminal-object and open-object isomorphisms in the open-section calculation
are used in their inverse directions before taking opposites. Explicit kernel
comparison equations and locally controlled reducibility avoid unfolding large
site and chosen-limit constructions during elaboration.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
