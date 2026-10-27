## What changed

Filled `AlgebraicGeometry.Etale.compactSupport_unbounded_amplitude` with its exact original
statement. No definition, public import, or source-library declaration was changed. The theorem-scoped
instance command has change record
`coord/changes/E3-compact-support-amplitude-shift-instance-scope.md`; the downstream check
reports zero consumer modules and the unchanged signature needs no adaptation.
The geometry uses finite type over the dimension-zero field point, then the existing
finite-type fibre-bound theorem. The derived open-extension adjunction proves coproduct
preservation in arbitrary indexing universes, and proper pushforward supplies the second
factor. Exact extension by zero and left t-exact derived direct image give the lower bound.

For the sharp upper bound, compare the supplied compactification on heart objects with
the compactification of `EtaleCompactSupportAmplitude`, then apply bounded-heart amplitude.
Reuse `exists_isLE_rightDerivedLowerShriekOfCompactification_obj` for a coarse bound N.
For K≤a, truncate at m=min(a,a+2d−N). The lower term has image ≤m−1+N≤a+2d;
the upper term is bounded in [m,a], so its image is ≤a+2d. Extension closure in the
standard t-structure bounds the middle term. The interval conclusion combines both bounds.

Updated the item's DAG proof, proof dependencies and proof origin, and removed obsolete
top-level tool approvals in their original order. Added a node attaching the existing
proved coarse-bound source theorem; no new Lean theorem or module is introduced.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.compactSupport_unbounded_amplitude`
(node `lem-pur-etale-support-unbounded-amplitude`).

The item's module has zero remaining `sorry`. Holes added: zero. Split-off holes: zero.
The proof uses existing declarations, including their current transitive dependencies;
this report does not claim that every dependency is free of `sorry`.

## No longer needed

The single truncation argument replaces the planned brutal-truncation telescope. Removed
these direct proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.CategoryTheory.DerivedCategory.ExactFunctorCoproducts`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit`
- `Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit`
- `WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits`
- `Mathlib.CategoryTheory.Triangulated.HomologicalFunctor`

Removed these dependencies from the item's proof route:

- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `prop-weil-pbc-kinjective-resolutions-exist`
- `lem-pur-exact-derived-coproducts`
- `lem-weil-pbc-kinjective-total-derived`
- `def-kun-truncations`
- `lem-kun-complex-colimit-hocolim`
- `lem-kun-functor-preserves-hocolim`
- `src-weil-homology-preserves-exact-colimits`
- `lem-sp-long-exact-of-triangle`

The following obsolete top-level `tool_uses` approvals were withdrawn:

- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `prop-weil-pbc-kinjective-resolutions-exist`
- `lem-weil-pbc-kinjective-total-derived`
- `def-kun-truncations`
- `lem-kun-complex-colimit-hocolim`
- `lem-kun-functor-preserves-hocolim`
- `src-weil-homology-preserves-exact-colimits`
- `lem-sp-long-exact-of-triangle`

These are removals from this item's direct proof route only. Existing modules and source
library declarations remain in the library, including dependencies imported transitively
by preserved source proofs. No module is withdrawn and no DAG node is deleted.

## Where the brief, the DAG or earlier work was wrong

The telescope plan is mathematically valid but longer than necessary given the existing
source coarse bound. A sharp fibre bound for the compactification's proper map is not
needed: its coarse bound is used only below a cutoff. The sharp bound continues to use
the original morphism's fibres, exactly as in the unchanged statement.

The proof covers empty schemes, empty coproduct index sets, the zero coefficient ring,
d=0, and unbounded-below inputs. In particular, no nonemptiness assumption was added.
The unit's own statement and realized proof steps are unchanged.

The earlier attempt lacked the published Mathlib object. The resumed service supplied
proof-body diagnostics, allowing the syntax, instance-selection and unit-map calculation
errors to be fixed. The final proof compiled cleanly with no warnings in 39.4 seconds. The unchanged
hypothesis `hp` is used to deduce primality of p in the coefficient argument. The delivery
command rechecks the final source and its axioms. An earlier delivery compile hit its
60-second wall limit and pushed nothing; the subsequent standalone final-source check passed.
The proof scopes out the competing etale pushforward shift instances for this declaration
and uses the generic right-derived-functor instances already selected in its original type.
No source-library statement, attribute, public import or definition is changed.
Several service requests produced no answer (exit 124); they supplied no proof feedback.
The first delivery retry was still waiting for a slot when interrupted after proof revision,
and had not compiled or pushed anything. No launcher script or configuration was modified.

## New nodes

`lem-pur-etale-compact-support-coarse-upper-bound` attaches the already-proved theorem
`AlgebraicGeometry.Etale.exists_isLE_rightDerivedLowerShriekOfCompactification_obj`
in `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow`. It states an
unspecified uniform upper shift for the fixed compactification over a compact base,
without a lower bound on the complex. It is strictly weaker than the sharp 2d bound
proved here, and is not a renaming or repackaging of the item. It introduces no hole.
The source is Stacks Project, more-etale.tex, lemma-derived-lower-shriek-bounded (3).

This node is not a duplicate of `lem-pur-bounded-heart-amplitude`: the latter is a
bounded-input devissage result for an arbitrary triangulated functor with a specified
heart bound. The new attachment concerns arbitrary bounded-above input, a specific
geometric functor, and an unspecified coarse shift. Searches found no existing DAG
attachment for the source declaration. The scoped instance-elaboration command is recorded in
`coord/changes/E3-compact-support-amplitude-shift-instance-scope.md`; no statement or
definition was altered.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
