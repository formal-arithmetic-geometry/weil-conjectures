## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedTateRealization.encodedBalancedPower_existsUnique`
in `Sheaf.Paper.CondensedTateRealization`. Its statement and all existing definitions
and public attributes are unchanged; the old global additivity registration is now
local to this module because downstream consumers provide their own local
registration where needed. The proved private helpers `integralToQbar_factor`
and `transportSectionHom` establish the specified
integral-to-closure coefficient factorization and transport an internal module map
through a commuting square of section-ring isomorphisms. The transport helper uses
the section-module functor followed by restriction directly; these are the underlying
functors of the existing equivalences, so no construction is changed.

The coefficient factorization cancels the canonical lift/down maps before point
inverse image. `Mod.comapCongr` and `Mod.comapComp` then put the existing balanced
map over the two successive coefficient restrictions. `sectionModuleComapIso`
encodes that map. Precomposing the integral comparison square with its inverse and
postcomposing with the section comparison inverse identifies the scalar actions.
`PresheafOfModules.homMk` retains the original section maps, and extensionality
proves uniqueness. In particular the construction retains the balanced unit at
zero tensor degree. It uses no primitive root, cover, nonempty-scheme hypothesis,
or odd-prime hypothesis.

The existing node's Step 8 and proof-origin note record this proof. The additional
explicit dependency `def-weil-pbc-continuous-coefficient-module-encoding` already
owns `sectionModuleComapIso` and `ringModuleEquivalenceOfIso`; its module is already
publicly available through the retained definition imports. This is a generic encoding tool,
not a replacement for any step of the purity unit. No new node is introduced.

Local transparency controls keep `moduleEncoding` irreducible while registering
and using the encoding field instances, and restore irreducibility of
`integralEncoding` after its augmentation construction. The sectionwise encoding
proof locally unfolds both interfaces. This avoids repeatedly indexing or
inferring instances through the large equivalence bodies; their public
definitions, result types and instance attributes are unchanged.

Validation: the initial narrowed-import check compiled in 48.2 s; an artifact
build exposed a 68 s compile, and full-file profiling located a 7.28 s instance
attribute application and 20.3 s of typeclass inference. The final file with local transparency controls compiled alone in 50.3 s. The
unchanged consumer batch was attempted but the artifact-output build rejected the
main file at 66 s; the standalone server compile is within the 60 s limit.
`tools/import_prune_check.py` passed the import narrowing.
All diagnostic profiler settings have been removed.

## Proved and sorry left

Closed one of the three original holes:

- `AlgebraicGeometry.ProEtale.CondensedTateRealization.encodedBalancedPower_existsUnique`.

Added zero holes; split off zero statements. Two original holes remain unchanged:

- `AlgebraicGeometry.ProEtale.CondensedTateRealization.integralComparison_existsUnique`.
- `AlgebraicGeometry.ProEtale.CondensedTateRealization.condensed_tate_realization`.

All three declarations are attached to `lem-pur-condensed-tate-realization`.
The remaining holes retain their original statements and complete proof docstrings.
The filled proof uses the still unproved integral comparison theorem, so its
transitive axiom report includes `sorryAx`; the new proof contains no `sorry`.
Both new private helpers are fully proved without introducing any additional axiom.

## No longer needed

Narrowed `Sheaf.Paper.CondensedERealization` to its
`Sheaf.Paper.CondensedERealizationDefinitions` module and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` to
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`
as a proof-only private import.
Only their definitions and compatibility API are used; the broad realization and
2-colimit theorem implementations are not used by this module's current proofs.

Removed `Sheaf.Paper.IntegralUniformCoefficient` (no proof dependency of the node).

Reviewer correction (2026-10-26): the plan modules of the two remaining holes,
`Sheaf.Paper.CondensedERealization`, `Sheaf.Paper.PurTwistSheafLocallyFree`,
`Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`,
`Sheaf.Paper.CompletedCondensedCoefficients` (unit sk-prop-sfb-qlbar-colimit-x),
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, are kept as plain `import`s
(stage 3 §2: a plan import goes only when the proof compiles without it); only their
public re-export is removed. The six importers compile against the corrected module.

No node, module, declaration or unit step is withdrawn. The two remaining original
holes retain their coefficient, local-line, K-flat and derived-limit dependencies.
The import-interface change is recorded in
`coord/changes/A4-condensed-tate-realization-imports.md`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition repair was necessary. The DAG did not
explicitly name the existing continuous coefficient module encoding node for its
sectionwise restriction comparison; Step 8 and its dependency union now do.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
