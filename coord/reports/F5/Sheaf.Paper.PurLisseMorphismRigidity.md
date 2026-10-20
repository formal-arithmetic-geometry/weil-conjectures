## What changed

Completed `WeilConjectures.purLisseMorphismRigidity` without changing its type or the
meaning of the three public definitions. All new helpers are proved and private. The finite constant
models of the two sheaves are refined to one pro-etale cover. The constant-module Hom
comparison, finite presentation over the finite coefficient ring, and the injection of
linear maps into functions give finite Hom models. Point fibers give finite Hom stalks.
For rigidity, descend the morphism to finite locally constant etale sheaves, transport
stalk vanishing through the natural comparison, and reuse the existing etale rigidity
proof in `WeilConjectures.ConstructibleSheaf.Rigidity`. The connected assertion follows
by subtraction and additivity of the specified ringed-module stalk functor.

All public imports are retained. The proposition-instance binders in
`PurityVanishingAtComponent` use `let` in place of `letI`; the change record below
records this definitionally equal presentation. Imports with `all` reuse
proved private comparison and point-fiber constructions in existing modules. The node's
proof and proof dependencies now describe these constructions and the etale rigidity
reuse. The unit's internal-Hom and connected-component rigidity steps are retained.
The final proof reflects zero through the objectwise faithful scalar restriction directly,
avoiding an unnecessary construction of the full equivalence and the private instances
of the coefficient-encoding module. Lean compiled the full module and
reported only `propext`, `Classical.choice`, and `Quot.sound` for its theorem.

## Proved and sorry left

Closed: `WeilConjectures.purLisseMorphismRigidity`
(node `lem-pur-lisse-morphism-rigidity`), the item's single original hole.
Added: zero holes. Left in the delivered module: zero holes. Split off: zero statements.
This is a proof from existing library declarations, not a decomposition.

## No longer needed

Change record: `coord/changes/purity-vanishing-at-component-let-bindings.md`.

Removed direct proof imports (some remain available transitively):

- `Sheaf.Paper.ProEtaleLisseOrigin`
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`
- `WeilConjectures.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Mathlib.AlgebraicGeometry.Sites.Etale`
- `Mathlib.CategoryTheory.Sites.CoverLifting`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`

Also removed duplicate imports of
`WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk` and
`WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`.
The import of `Sheaf.CategoryTheory.SiteConstantModuleHom` is retained as `import all`
to access its proved constant-model constructions.

The updated route no longer directly calls
`lem-sf-proetale-locally-constant-origin`,
`lem-weil-pbc-finite-locally-constant-module-values`,
`def-weil-pbc-etale-site`, `def-weil-pbc-site-comparison-morphism`,
`lem-weil-pbc-comparison-pullback`, `def-weil-pbc-sheafification`,
`lem-weil-pbc-etale-cover-geometric-point-lift`,
`lem-weil-proetale-constant-sheaf-stalk`,
`lemma-constructible-hom-constant-locally`, `lemma-openclosed-stalk-upperstar`,
`lem-weil-pbc-constant-sheaf-geometric-stalk`, or
`lem-weil-pbc-etale-morphism-open-map`.
Finite-model descent and the existing etale rigidity proof encapsulate those parts of
the argument; constant stalks for the Hom models use the general site-point API.
These nodes are removed from this node's direct proof dependencies; this does not claim
their modules disappear from the targets' transitive import closure.
The obsolete tool-use entries removed are the lisse-origin theorem, finite-module-values
criterion, comparison-pullback theorem and pro-etale constant-stalk theorem.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original seven-step plan overlooked an existing proof of its etale rigidity clause:
`AlgebraicGeometry.Etale.eq_zero_of_sheafFiber_map_eq_zero`. Reusing that declaration
avoids repeating its clopen-locus and sheaf-separatedness proof. For Hom, finite models
can be refined on the pro-etale site directly; etale descent is needed only for rigidity.
The retained attempt needed an explicit finiteness proof for its linear-map model.
No false statement, definition repair, consumer adaptation or new axiom is used.
The `letI` binders of `PurityVanishingAtComponent` are written as `let` to satisfy
Lean's proposition-instance style linter; their types and elaborated meaning coincide.

The resumed delivery initially hit the 60-second compile limit. Profiling showed
expensive definitional equality checks in the constant-model comparisons and coefficient
instances. The file uses `backward.isDefEq.respectTransparency false` and retains local
let bindings with `cleanup.letToHave false`. Its coefficient-encoding import is now
ordinary: reflecting zero uses the underlying section maps directly, so the module's
private instance collection is unnecessary. These changes preserve all public types
and definitions. The complete proof compiled in 44.7 seconds in the resumed diagnostic
(`scratchpad/no-encoding-private.log`); earlier axiom checks reported only `propext`,
`Classical.choice`, and `Quot.sound`. The required delivery dry run checks the final
packet independently. No launcher script or gate was changed.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
