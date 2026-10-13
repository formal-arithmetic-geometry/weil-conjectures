## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsDerivedModel`
with a complete Lean assembly, preserving its signature and existing public imports.
The explicit terminal-section complex is reconstructed by a smaller chain-level lemma.
Its complex isomorphism, mapped through Q and composed with `he`, supplies the model
hypothesis of the existing `affine_kFlat_residuePullback_model` theorem. The given
K-flatness is passed unchanged. A new, fully proved natural scalar-transport
comparison identifies that theorem's prime-residue-field extension and field
restriction with extension along `W.evaluation`. Mapping this natural isomorphism
and the two functor-composition isomorphisms to complexes, tilde and Q gives exactly
the requested representative, before homology.

Added proof imports of `AffineFreeTerminalSectionsReconstruction`,
`AffineResidueScalarTransport`, and `AffineKFlatResiduePullbackModel`.
Added the first two modules and their nodes; updated the item's proof route.
No definitions, existing statements or public visibility changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.affineFree_residueSections_derivedModel`.
This is a complete proof from the existing lower residue-model theorem; its
existing hole remains below the item. There is no new decomposition hole.

Proved `AlgebraicGeometry.Scheme.affine_residue_scalar_transport` entirely from
Mathlib. Its ring identity uses chart evaluation naturality, the explicit open
stalk isomorphism and compatibility of germs with restriction. The functor
isomorphism follows from the extension/restriction adjunction and uniqueness of
left adjoints. This module contains no `sorry`.

Proved `AlgebraicGeometry.Scheme.affineFree_terminalSections_reconstruction`.
Its proof composes the fully faithful tilde adjunction with the affine chart/slice
equivalence. Every finite free term lies in the left adjoint's essential image,
so its counit is invertible. A proved private natural comparison identifies the
right adjoint with actual terminal evaluation. Mapping this comparison and the
counit to complexes reconstructs K, including its differentials. It uses Mathlib
and the already proved structure-module comparison in
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`.
No new holes were added; no `sorry` remains in any of the three delivered modules.

The existing dependency
`AlgebraicGeometry.Scheme.affine_kFlat_residuePullback_model`
(node `lem-sc-affine-kflat-residue-pullback-model`) still contains its existing hole;
it is reused without modification. Its section model is now specifically the
actual terminal-section complex, rather than a chosen existential witness.

The delivered modules are checked together through `lcompile.py --all` and the
required delivery dry run; see the compiler and dry-run outputs. Rank zero, the zero complex, unbounded complexes and zero
rings require no exceptions for reconstruction or scalar functor comparison;
the residue comparison assumes a point of U and hence cannot have empty U.

## No longer needed

No existing public imports were removed: they are used in the statement's types
and instances. No unused proof imports were added. The exploratory import of
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` was reduced to
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`, which supplies the
structure-module comparison actually used.

The following planned direct dependencies are replaced and their modules are not
imported by this item:

- `lem-pc-affine-kflat-pullback-chart-comparison`
  (`Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison`): the existing affine
  residue-model interface already provides the needed ambient object comparison.
- `lem-pc-affine-projective-sections-sheafification`
  (`Sheaf.AlgebraicGeometry.AffineProjectiveSectionsSheafification`): its flatness,
  finite-presentation and projectivity conclusions are unnecessary here. The new
  reconstruction is proved directly from the affine tilde/Gamma adjunction.
  `lem-pc-affine-sections-complex-counit` and its module
  `Sheaf.AlgebraicGeometry.AffineSectionsComplexCounit` are also unnecessary.
- `lem-pc-ringed-spaces-derived-pullback-composition`
  (`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`): the global unit and
  associativity coherence package is unnecessary for this proof; the existing
  residue-model interface uses the required open restriction comparison.

`lem-pc-affine-localized-site-derived-transport` is no longer a direct dependency,
but remains imported by `AffineKFlatResiduePullbackModel`; it is not claimed pruned.
`def-weil-residue-field` remains used by the scalar-transport node and statement.
These are branch-specific pruning claims, not claims that a module is globally
unreachable from every target.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature correction was needed. The original route omitted
an explicit natural comparison between terminal slice evaluation and the affine
section functor; the reconstruction module proves this interface glue explicitly.
The existing affine residue-model theorem already handles the open factorization
and derived pullback argument, so repeating that argument through the more general
chart comparison is unnecessary.

Searches used LeanFinder, Loogle and grep, with LeanSearch attempts recorded as
unavailable (Internal Server Error). LeanFinder returned free-sheaf APIs; Loogle
returned scalar adjunction APIs. Repository searches found the affine residue model
and affine counit modules. No existing node states the exact terminal-slice
reconstruction or the exact natural residue scalar comparison. Blueprint searches
for sections, reconstruction, scalar transport and 01IB found no exact duplicate.
Stacks Tags 01IB and 0098 were read on the Stacks website; their contents respectively
justify the affine counit and the stalk-based residue compatibility.

## New nodes

`lem-sc-affine-free-terminal-sections-reconstruction`, in
`dag/nodes/sec-abelian-varieties/`, states the actual chain-level reconstruction from
terminal slice sections and fully proves its counit/interface comparison.
Its Lean module is `Sheaf.AlgebraicGeometry.AffineFreeTerminalSectionsReconstruction`.

`lem-sc-affine-residue-scalar-transport`, in the same chapter, states the natural
scalar functor comparison and is fully proved in
`Sheaf.AlgebraicGeometry.AffineResidueScalarTransport`. It has no derived or
finite-free hypotheses. Both inherit the item's unit and blueprint ancestor.

## Second reading by D4

1. **Interfaces: pass.** Compared every delivered module with the read-only
   repository. The two helper modules are new. The existing module differs only
   by three plain proof imports and replacement of its sole `sorry` proof body;
   its existing declaration signature, docstring and public imports are byte for
   byte unchanged. There are no definitions or changed interfaces in this delivery,
   and no change record is required.
2. **Proofs: pass, with an existing lower hole.** Compiled all three modules in
   import order through `lcompile.py --all`, and compiled a separate scratch axiom
   check importing the compiled sandbox modules. Both new public theorems use only
   `propext`, `Classical.choice`, and `Quot.sound`. The existing item's theorem uses
   those plus `sorryAx`, through the unchanged named lower theorem
   `AlgebraicGeometry.Scheme.affine_kFlat_residuePullback_model`. No delivered
   module contains `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or
   `extern`. The proof chooses only supplied or proved isomorphisms; the section
   complex is constructed by actual terminal evaluation, not by an arbitrary
   witness from an open existence theorem. One original hole is closed, zero
   holes are added, and zero new statements are left split off with `sorry`.
3. **New statements: pass.** Read both helper proofs and their full signatures.
   Reconstruction uses the affine tilde adjunction, essential-image counit
   invertibility for free terms, and an explicit natural identification of its
   right adjoint with terminal slice evaluation. Componentwise invertibility and
   counit naturality give a complex isomorphism, including differentials. Scalar
   transport proves the evaluation ring identity and uses scalar adjunctions to
   obtain an isomorphism natural on all modules. Neither helper restates the item:
   one is chain-level without derived categories or a point, and the other is a
   scalar functor identity without complexes or freeness. Rank zero, empty affine
   opens and zero rings do not obstruct reconstruction; a point excludes an empty
   open in scalar transport. Neither proof assumes boundedness. Independent
   searches used `Adjunction.rightAdjointUniq`, “global sections of a finite free
   sheaf reconstruct it on affine scheme”, and repository searches for terminal
   evaluation, section reconstruction, `fromTildeΓ` and scalar composition.
   The existing `AffineSectionsComplexCounit`, `AffinePerfectModuleModel` and
   `AffineProjectiveSectionsSheafification` were inspected: their conclusions
   use different section/chart models or require additional hypotheses. They do
   not eliminate the terminal-slice comparison supplied here.
4. **Route and pruning: pass.** Followed the item proof from its target down:
   terminal reconstruction supplies the explicit model to the existing residue
   theorem, and natural scalar transport supplies the exact evaluation map in the
   conclusion. Each new plain import is used. The new modules' public imports
   supply their statement types or additive instances; their remaining imports
   are plain proof imports. All old direct dependencies absent from the new route
   are accounted for under `No longer needed`, including the localized transport
   that remains indirect and the residue-field definition that is still used.
   The unit `sk-prop-av-cube` was read: its `realized.statement` and sole
   `realized.steps` entry are empty in the repository, and this item is not a
   recorded unit-step realizer. The delivery changes only the residue calculation
   below that unit; it does not bypass or change the cube theorem's unit route.
5. **DAG: pass after metadata repair.** The item's three proof steps and their
   dependency union match the three theorem applications in Lean. Both new nodes
   have sources, natural-language proofs, search records, creation and blueprint
   ancestry, unit/chapter fields and Lean attachments. Their proof routes agree
   with the adjunction and ring-identity arguments. Replaced the flattened
   `lean.statement` strings in both new nodes with the signatures verbatim from
   their Lean modules, as required by the standing brief. Existing node statement
   and statement dependencies remain unchanged.

Second reading changed only the two new nodes' verbatim Lean signature records
and this report. No Lean proof or import needed repair. The first scratch axiom
check was outside the sandbox's `lean/` root and could not resolve sandbox modules;
its corrected temporary check under that root compiled and produced the axiom
results above, and was removed before delivery.
