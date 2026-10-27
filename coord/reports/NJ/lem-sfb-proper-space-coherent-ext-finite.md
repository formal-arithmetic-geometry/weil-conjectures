## Worker report

Module: `Sheaf.AlgebraicGeometry.ProperSpaceCoherentExtFinite`.
It states `AlgebraicGeometry.AlgebraicSpace.properSpace_coherent_ext_finite`, with
one postponed proof (`sorry`). The helper `properSpaceExtModule` constructs the
actual scalar action on the derived Hom group; its data contain no sorry and use
only the existing global-function action and restriction of scalars.

Source read: `literature/stacks-project/spaces-perfect.tex`, lines 1220–1275,
including lemmas coherent-internal-hom (0D0S), direct-image-coherent-bdd-below
(0D0R), and ext-finite (0D0T). The latter has exactly the asymmetric bounds of
this node. No statement correction, disputed statement, or new node is needed.
The source proof and the node's six expanded steps are included in the theorem
docstring. The existing small-model interfaces suffice.

Clause audit:

- The commutative Noetherian ring is `(A : Type u) [CommRing A]
  [IsNoetherianRing A]`; no field, nonzero, reducedness, or characteristic
  restriction is imposed.
- The algebraic space is `X : AlgebraicSpace (Spec (.of A))`, using the recorded
  algebraic-space full subcategory. The target `schemeSpace (Over.mk (𝟙 ...))`
  is the represented base. The explicit map `f` is its structure morphism (the
  represented base is terminal among spaces over that base).
- Properness is exactly `hf : MapIsProper f`. Its definition is separatedness,
  finite type and universal closedness. The first tests the relative diagonal
  by closed immersions, the second is quasi-compactness plus locally-finite-type
  chart tests, and the third tests closed maps on the existing point topology
  after every algebraic-space base change. This is the node's full expansion.
- `X.DerivedModules` is the ordinary unbounded `DerivedCategory X.SmallModules`.
  The small affine étale model is equivalent, by its specified restriction
  equivalence, to modules on the node's small étale ringed site; there is no
  change of section universe. `[HasDerivedCategory.{w} X.SmallModules]` leaves
  the chosen localization morphism universe arbitrary and independent of `u`.
- `hE` and `hF` require, in every integer degree, `IsQuasicoherent ∧ IsFiniteType`
  of the corresponding `DerivedCategory.homologyFunctor` object. These are
  Mathlib's existing predicates, preserved by the affine-basis equivalence.
  Proper finite type over a Noetherian affine base makes X locally Noetherian.
  Thus this condition is precisely the node's coherence: on every Noetherian
  affine étale chart Spec R, the sheaf is associated to a finite R-module N,
  with sections B tensor_R N on its affine étale refinements (Stacks 07UB).
  No assumption of coherence on arbitrary non-Noetherian ringed sites is used.
- `hE_upper : ∃ a, ∀ q, a < q → IsZero (H^q E)` is vanishing in all sufficiently
  large degrees. `hF_lower : ∃ b, ∀ q, q < b → IsZero (H^q F)` is vanishing in
  all sufficiently negative degrees. They do not bound E below or F above.
- `n : ℤ` includes negative degrees and zero. The group in the conclusion is
  literally `(E ⟶ F⟦n⟧)`, rather than Ext of module objects concentrated in
  degree zero. `Module.Finite` is finite generation, not finiteness of its set.
- The module parameter is explicitly `properSpaceExtModule A X f E F n`.
  `SheafOfModules.homLinear` acts by compatible functions on each chart;
  Mathlib's derived-category linear structure localizes this action.
  `Module.compHom` restricts it along `affineGlobalScalar`, which is constructed
  from ΓSpec and pullback along T → X → Spec A. Consequently the scalar action
  is exactly the structure-morphism action specified in the last sentence.
  There is no arbitrary linear structure or auxiliary action hypothesis.

Dependency declarations read and used (including the modules added to stmt_deps):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`,
  `isNoetherianRing_iff_ideal_fg`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleTopology`, `structureSheaf`, `Modules` and the representability predicates.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  the associated quasi-compactness definition is Mathlib's `QuasiCompact`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the transparent
  abbreviation for Mathlib's `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory` and its localization functor `Q`.
- `def-sfb-space-morphism-properties`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`,
  `MapIsSeparated`, `MapIsFiniteType`, `MapIsUniversallyClosed`.
- `def-sfb-space-small-ringed-model`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallModules`,
  `smallStructureSheaf`, `smallStructureRings`, `smallModuleEquivalence`.
- `def-sfb-space-derived-module-calculus`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`.
- `def-sfb-space-affine-global-sections`, module
  `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`: `affineGlobalScalar`,
  whose chart signature and construction were read in full.
- `def-trf-space-quasi-coherent-module`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the existing
  `SheafOfModules.IsQuasicoherent` match and its slice instances, no copied predicate.
- `def-weil-finitely-generated-module`, module
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- Scalar construction: `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule`
  (`SheafOfModules.homLinear`) and
  `Mathlib.Algebra.Homology.DerivedCategory.Linear` (localized linear structure).

The additional stmt_deps are all existing, landed nodes, added to cite the exact
shared interfaces the statement uses. No dependency node or definition was repaired.
The file imports the stated proof dependencies, with plain imports. The two
geometric proof inputs `lem-sfb-space-coherent-derived-internal-hom` and
`lem-sfb-proper-space-coherent-derived-image` have no Lean records yet, so there
is no corresponding module to import. Neither is needed to type this statement.
The rest are imported through their recorded Lean or Mathlib matches, including
the ringed-site sections, Leray, truncation, and evaluation-slice comparisons.

Edge cases checked mathematically: the empty space and zero complexes give the
zero Hom module; the zero base ring forces the empty affine base and causes no
extra nontriviality assumption. The integer bounds include all shifts and allow
infinite tails in opposite directions. The source proof uses only finitely many
terms in each total degree, not boundedness on both sides. Neither perfection of
E nor boundedness above of F is assumed. No universe equality is introduced.

Searches actually run through msearch.py for this item:

- LeanFinder, `Ext groups between bounded above and bounded below coherent
  complexes on a proper algebraic space over a noetherian ring are finite
  modules`: 8 hits, generic HasExt and derived-category Ext smallness, no match.
- Loogle, `ModuleCat.finite_ext, AlgebraicSpace, Module.Finite`: 0 hits, unknown
  identifier AlgebraicSpace. This is a failed name lookup, not evidence for
  absence of the project's notion.
- Mathlib grep, `AlgebraicSpace|proper.*coherent.*[Ee]xt`, subdirectory
  `AlgebraicGeometry`: 0 hits.
- LeanSearch, `Global Ext between coherent complexes on proper algebraic spaces
  is a finite module`: 8 hits, generic Ext and finite global functions for
  proper schemes, no theorem matching this item.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the item id and coherent
  Ext/finite Ext phrases: no matching proper-space coherent-complex theorem.
  Topic/file searches found and reused the shared algebraic-space interfaces
  above. `ModuleCat.finite_ext` is about modules over a ring, not these complexes
  on an arbitrary proper algebraic space.
- `rg` on both source trees and `dag/lean_names_upstream.json` for the two proposed
  declaration names found none. The complete msearch output is in the sandbox's
  wrapper-generated `searches.jsonl`.

Validation: compiled with the prescribed server scompile.py; final result and
preflight recorded below after the dry run. Only the theorem's expected sorry
warning is permitted.

## Second reading by NJ

This is the worker's final clause self-audit; the maintainer performs the
independent reading, as specified by the dispatcher brief. No other agent was
started. Re-opened the node and final file: A/Noetherian, X/proper, the ordinary
étale derived category, both coherent-cohomology predicates, opposite one-sided
bounds, all integer n, and the precise A-action match clause by clause as listed
above. The first compile exposed an explicit-argument ordering mistake in
`Module.Finite` and the helper's class-definition reducibility annotation; both
were corrected. No mathematical mismatch or node change was found. All six
proof steps are retained in the theorem docstring.

Final validation: scompile.py compiled both the sandbox and library module cleanly
(13.5 s and 10.1 s). `deliver2.py ... --no-push` printed
`OK (dry run): commit a144af8d823 passes the preflight and compiles; nothing pushed`.
