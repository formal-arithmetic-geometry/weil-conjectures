## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAffineDerivedPushforwardConservative` states
`AlgebraicGeometry.AlgebraicSpace.affine_derivedDirectImage_preservesQCoh_and_reflectsIso`.
Its sole theorem has proof `sorry`. No definition, helper theorem, or dependency module is
added, and the natural-language statement is unchanged.

Source read: `literature/stacks-project/spaces-perfect.tex`,
`lemma-affine-morphism` (Tag 08II, lines 747 onward), including its proof, and
`lemma-quasi-coherence-direct-image` (Tag 08FA, lines 573 onward), part (1).
The former states reflection on D_QCoh, and the latter supplies landing for qcqs maps;
affine maps are quasi-compact and separated. These are exactly the two node clauses.

Hypotheses and clauses, in order:

- The universe convention is expressed by explicit `universe u wX wY`,
  `S : Scheme.{u}`, and independent `HasDerivedCategory.{wX} X.SmallModules` and
  `HasDerivedCategory.{wY} Y.SmallModules`. These are choices of localization, not
  geometric restrictions. Small ringed models preserve the original module universe.
- The base scheme, algebraic spaces over it, and their morphism are
  `{S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)`.
- Affineness is exactly `hf : MapIsAffine f`. Its existing definition quantifies over
  every affine scheme test and specifies an actual pullback square represented by an
  affine scheme. Representability for general scheme tests follows by gluing these
  affine tests, as in the standard definition; no separate stronger assumption is added.
- The module sheaves and structure sheaves are those of the existing small-model
  equivalences with the small etale structure-sheaf module categories.
  `X.DerivedModules` is the unbounded derived category of `X.SmallModules`.
- `X.derivedQCohProperty E` means that, for every integer n, the cohomology sheaf
  transported back through `X.smallModuleEquivalence.inverse` is quasi-coherent.
  This is the existing predicate, using `SheafOfModules.IsQuasicoherent`.
- Canonical Rf_* is `(smallModuleDirectImage f).rightDerivedFunctor`, with its type
  explicitly ascribed as `X.DerivedModules ⥤ Y.DerivedModules` at each occurrence.
  `smallModuleDirectImage` conjugates the existing compatible-chart-limit direct image
  by the actual module equivalences. The project's additive and K-injective-resolution
  instances give the canonical unbounded K-injective right derived functor. This is
  precisely the body of the recorded `derivedDirectImage`; using the body directly
  retains independently chosen source and target localization universes, whereas the
  convenience definition currently names a single level w. No new functor is defined
  or quantified over, and no equality of localization universes is required.
- Landing is the first conjunct: for every E with `X.derivedQCohProperty E`, the actual
  derived image satisfies `Y.derivedQCohProperty`.
- Reflection is the second conjunct: for arbitrary E and F satisfying the source
  predicate and arbitrary `v : E ⟶ F`, `IsIso` of its actual derived image implies
  `IsIso v`. Since D_QCoh is a full subcategory, these are exactly its morphisms and
  isomorphisms; the target isomorphism criterion agrees with the ambient category's.
- No boundedness, Noetherian, finite-type, quasi-compactness of X or Y, or surjectivity
  hypothesis occurs. There are no additional geometric hypotheses.

Dependency declarations used, with their source modules read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.Modules`, `structureSheaf`, `EtaleSite` and `IsRepresentableWith`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent abbreviation for Mathlib's existing `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, and its localization functor.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh`
  and the slice sheafification instances supporting `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImageModel` and `moduleDirectImage`; the
  normalized limit projections and uniqueness were read, not merely their names.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `DerivedQCoh`, `smallModuleDirectImage`, its additivity,
  `smallModules_hasKInjectiveResolutions` and `derivedDirectImage`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`:
  `CategoryTheory.Functor.rightDerivedFunctor` (publicly imported through the preceding
  module), the existing K-injective construction with independent localization choices.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine`.

The last two owning definition nodes,
`def-sfb-space-derived-module-calculus` and
`def-sfb-space-affine-quasifinite-properties`, already landed and are added to stmt_deps.
Their records and full relevant declaration docstrings were read. They supply the
shared canonical notions, so there is no new definition node and no interface repair.

Proof imports retain the modules of the recorded proof dependencies:
`WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`,
`WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardConservative`,
`Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
Mathlib's `AlgebraicGeometry.Morphisms.Affine`, `Morphisms.Separated`,
`AlgebraicGeometry.Limits`, and `Algebra.Homology.DerivedCategory.HomologySequence`.
The node `lem-sfb-space-affine-locality` and the scheme-etale comparison node
`lem-sfb-scheme-derived-etale-qcoh-comparison` currently have no recorded declaration
or module, so there is no proof import to add for them. They are used only in the
natural-language proof plan, not to form the statement. The module docstring and theorem
docstring give the four source proof steps, including each cited DAG input.

Edge cases checked before writing: empty X, empty Y (which forces empty X), zero
complexes and identity maps; no nonemptiness binder excludes them. Integer-indexed
unbounded complexes, including cohomology in arbitrarily negative degrees, are retained.
An affine map over a non-quasi-compact or non-Noetherian base is allowed. No finiteness
of the affine-chart covering is assumed. Independent localization levels were tested
by the successful polymorphic compilation, not silently identified.

Searches actually run for this item:

- msearch LeanFinder: "The unbounded derived pushforward of quasi coherent modules
  along an affine morphism of algebraic spaces preserves quasi coherent cohomology
  and reflects isomorphisms". Eight hits: ordinary scheme module pushforwards,
  pushforward composition, generic derived localization, and module sheaf pushforward
  functors. None states algebraic-space unbounded quasi-coherent conservativity.
- msearch Loogle: `"ReflectsIsomorphisms", "pushforward"`. Zero hits.
- msearch grep in Mathlib/AlgebraicGeometry:
  `affine.*(conservative|reflects)|pushforward.*ReflectsIsomorphisms|ReflectsIsomorphisms.*pushforward`.
  Zero hits.
- msearch LeanSearch: "Affine algebraic space derived pushforward preserves quasi
  coherent cohomology and reflects isomorphisms". Eight hits on ordinary scheme
  module functors, structure sheaf algebra maps and scheme affine-property invariance;
  none is the required statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id, affine conservativity,
  and pushforward reflection: found the scheme theorem only and the downstream
  `SpaceAffinePullbackPerfectDetection` proof-plan citation, not this statement.
- rg for `derivedQCohProperty`, `spaceDerivedDirectImage`, `SmallModules`,
  `DerivedModules`, `MapIsAffine`, and `derivedDirectImage` located the shared small
  ringed model and derived-module calculus, module operations and affine predicate.
- rg in `dag/lean_names_upstream.json` for affine/derived combinations and MapIsAffine
  found no duplicate space theorem. rg in `dag/nodes` for the full MapIsAffine name
  found the owning definition node cited above.

Validation: the single delivered module compiled through scompile.py in both sandbox
and library-module mode (2.0 s and 1.8 s), with no errors or non-sorry warnings.
No source or statement fault was found; no STATEMENT-DISPUTED flag is needed.

## Second reading by Q146

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
