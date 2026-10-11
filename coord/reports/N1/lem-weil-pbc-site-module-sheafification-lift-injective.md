## Worker report

The module [SiteModuleSheafificationLiftInjective](lean/Sheaf/Paper/SiteModuleSheafificationLiftInjective.lean)
states the sheafification lifting result for modules on a Grothendieck site.  A site is represented by
`C`, `J`, and the required Mathlib sheafification hypotheses.  `R` is the sheaf of rings, `P` a
presheaf of `R`-modules, and `F` a sheaf of `R`-modules.  The morphism `f` has the node's local
injectivity as the typeclass `Presheaf.IsLocallyInjective J` on its underlying presheaf morphism.
The lift is the unique morphism supplied by
`PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)`.  The conclusion is injectivity on every
section (`∀ X : Cᵒᵖ, Function.Injective ...`) and, in particular, `Mono` of the lifted sheaf
morphism.

The hypotheses and clauses are rendered as follows.  The site and its covering axioms are the
Grothendieck topology `J` on `C`; the sheaf of rings is `R : Sheaf J RingCat`; and the module
objects and map are `P`, `F`, and `f` with the displayed `PresheafOfModules`/`SheafOfModules`
types.  The local-injectivity clause is the `Presheaf.IsLocallyInjective` instance on
`(PresheafOfModules.toPresheaf R.obj).map f`.  The sheafification map is the symmetric side of
`PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)`.  Sectionwise injectivity is the first
conjunct, and the final monomorphism clause is the second conjunct.

Dependency declarations used: `CategoryTheory.Sheaf` and `CategoryTheory.Precoverage` from
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` (recorded for
`def-weil-pbc-sites-and-cohomology`); `PresheafOfModules.sheafification` and
`PresheafOfModules.sheafificationHomEquiv` from
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` (for
`def-weil-presheaf-modules-sheafification`); and `SheafOfModules` from
`Mathlib.Algebra.Category.ModuleCat.Sheaf` (for `def-weil-sheaf-of-modules-category`).

Edge cases checked: arbitrary site object `X : Cᵒᵖ` (including empty or terminal sites), zero
modules and zero morphisms, and arbitrary universe levels are admitted by the explicit universe
parameters.  No additional nonemptiness or finiteness assumptions are introduced.

Searches made: `msearch.py leanfinder` and `loogle` for locally injective sheafification lifts;
`rg` over Mathlib and `WeilConjectures`; and `rg` over `lean/Sheaf`.  Mathlib provides the generic
chain `Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac`,
`Sheaf.isLocallyInjective_iff_injective`, and `Sheaf.mono_of_isLocallyInjective`, but no single
declaration with this module-sheafification statement.  Therefore a new statement module is
required.

## Earlier second reading (a previous round; superseded)

The declaration and node were reread together.  The binders for the site, sheaf of rings,
presheaf, target sheaf, and locally-injective morphism match the node.  The first conjunct states
injectivity at every object, and the second states that the sheafification lift is a monomorphism.
No mismatch was found.

## Second reading by N1

The node introduces: a category/site `(C, J)` with abelian-group sheafification; a sheaf of
rings `R`; a presheaf of `R`-modules `P` with its sheafification; a sheaf of `R`-modules `F`;
an `R`-linear presheaf map `f : P ⟶ F`; the local-injectivity hypothesis on every section
that maps to zero; and the unique sheafification lift `f#`.  Its conclusions are sectionwise
injectivity of `f#` for every object and that `f#` is a monomorphism.

The Lean declaration renders these respectively as `C : Type u₁`, `[Category C]`,
`J : GrothendieckTopology C`, `[HasWeakSheafify J AddCommGrpCat]`,
`[J.WEqualsLocallyBijective AddCommGrpCat]`, `R : Sheaf J RingCat`,
`P : PresheafOfModules R.obj`, `F : SheafOfModules R`, and
`f : P ⟶ (SheafOfModules.forget R).obj F`.  Local injectivity is exactly
`Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R.obj).map f)`.  The lift is
the symmetric morphism supplied by
`PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)`, and the conclusion is
`∀ X : Cᵒᵖ, Function.Injective (((SheafOfModules.toSheaf R).map ...).hom.app X)` together
with `Mono ...`.  Thus all objects, hypotheses, quantifiers, and both conclusion clauses
match the node; the typeclass assumptions are precisely those required by the recorded
sheafification dependency.

Edge cases are admitted: `X : Cᵒᵖ` ranges over every site object (including empty or terminal
sites), zero modules and zero maps satisfy the same statement, and universes are explicit.
There is no nonemptiness, finiteness, characteristic, or `n = 0` restriction.

I searched the project and upstream source with `rg`, and ran the prescribed `msearch.py`
LeanFinder/Loogle searches.  Mathlib has only the generic locally-injective/sheafification
chain (`Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac`,
`Sheaf.isLocallyInjective_iff_injective`, and `Sheaf.mono_of_isLocallyInjective`), not this
combined statement.  No existing project declaration duplicates it.  No mismatch was found,
so no source or statement changes were needed.  The module compiles cleanly with `lcompile.py`.
