## What changed

Proved `AlgebraicGeometry.Etale.compactSupportProjectionMap_comp` from the canonical
right-factor projection identity on a proper/open tower, then naturality of tensor symmetry
and the exact-pullback comparisons. Its conditional inverse identity follows by inversion.
The existing comparison proof is retained; its proof description now matches that proof.
Both original public definitions and both theorem signatures are unchanged.

Added `OpenImmersionProjectionComposition` for the canonical derived open projection
compositor, and `CompactificationProjectionComposition` for the compatible proper/open
tower. Both follow genuine parts of the original plan. Generic private categorical lemmas
handle mates, pasting and coefficient transport without unfolding derived constructions.
No source-library declaration, definition or public import is changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.compactSupportProjectionMap_comp`, including its conditional
inverse clause. The original
`AlgebraicGeometry.Etale.compactSupportProjectionMap_comparison` was already proved and
its proof is retained. No holes were added or split off. Both new public lemmas and all
private helpers are proved; the three delivered modules contain zero `sorry` declarations.

`lcompile.py --all` compiled the open-composition module, tower module, and item module
against one another in 38.1, 31.3, and 16.9 seconds respectively, within the original
60-second file limit. Afterwards, removed harmless linter findings (two unused simp arguments and unused private section
instances); delivery preflight checks the final text.
Both original definition bodies, both theorem signatures, and all original public imports
were compared with the shared source and are unchanged.

`#print axioms` for the new open-composition theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`. The tower theorem and both original public theorems
also inherit `sorryAx` from existing library dependencies. Those inherited holes are not
new holes in this delivery; this is a complete proof of the item from the existing named
declarations, rather than a claim that the targets' entire dependency closure is finished.

## No longer needed

Removed these redundant direct proof imports from the item module:

- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.ProperOpenSection`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.RingedProjectionTensorComposition`
- `Sheaf.Paper.UnboundedProperOpenInterchange`
- `WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`

The new proof uses the already proved
`projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso`.
Consequently the separate clopen-refinement route is unnecessary here: the nodes
`lem-weil-pbc-proper-open-section`, `lem-weil-pbc-proper-open-p-proper`,
`lem-weil-pbc-etale-sheaf-clopen-product`,
`lem-weil-pbc-localization-universal-property`,
`lem-weil-pbc-exact-functor-derived-functor`, and
`lem-weil-pbc-right-adjoint-preserves-kinjective` are removed from this proof's dependencies.
The general ringed-topos projection, pushforward and exchange packages
`lem-sfb-ringed-projection-tensor-composition`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, and
`lem-weil-pbc-ringed-exchange-tensor-coherence` are unnecessary: their needed ordinary
etale special cases are already proved in the source library. The locality node
`lem-amb-etale-adjoint-locality` is unnecessary because the mixed square follows formally
by taking mates of the proved open base-change tensor square.

The corresponding eight obsolete top-level `tool_uses` approvals are removed, preserving
the order of the remaining approvals. No module is withdrawn. Removed direct imports can
remain needed transitively by retained definitions or by other targets; in particular the
compact-support comparison module still imports `UnboundedProperOpenInterchange`.
The open tensor and open compositor results remain needed, through the new tower and
open-composition proofs. There is no change to the unit route (`sk-prop-an` has no realized
node assigned to this item).

## Where the brief, the DAG or earlier work was wrong

The original plan repeats a noncartesian refinement/clopen calculation that the existing
source-library compactification-independence projection theorem already proves. Reusing
that theorem removes those tasks without changing the specified comparison isomorphism.
The open-composition and explicit tower calculations were not already supplied by the
imported Lean declarations; they are now isolated as genuine source results.

Instance paths for the sheaf braiding and reducibility of compactification wrappers must
match the source APIs. Let-bound aliases for the chosen functors made kernel conversion
very expensive; direct expressions and component equations avoid that problem. An explicit
heterogeneous transport of the compactifying scheme and its two maps prevents kernel
unfolding of projection data when specializing the tower component formula. Public
definitions are preserved, and compilation uses the original 60-second file limit.

## New nodes

`lem-amb-open-projection-composition`, in
`Sheaf.AlgebraicGeometry.OpenImmersionProjectionComposition`, realizes original step 2.
It proves composition of the actual inverse open tensor isomorphisms via derived unit
normalization, pullback tensor coherence and adjunction projection-map mates.

`lem-amb-compactification-projection-composition`, in
`Sheaf.AlgebraicGeometry.CompactificationProjectionComposition`, realizes the explicit
compatible-tower part of original steps 3, 4, 12 and 13. It pastes the mixed, proper and
open tensor squares and checks the remaining pullback coefficient path.



The supporting local essentially-small instances added to the item module are recorded in:

- `coord/changes/Q1-ShriekTensorComposition-essentiallySmall_etale_shriekTensorMain.md`
- `coord/changes/Q1-ShriekTensorComposition-essentiallySmall_etale_tensorConvention.md`

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
