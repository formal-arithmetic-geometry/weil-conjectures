## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteFpModuleDirectImage` states
`AlgebraicGeometry.AlgebraicSpace.finite_fp_moduleDirectImage`, with its proof left
as `sorry`. It introduces no definitions or additional axioms. The accepted Q27
stage-1 split is preserved. Q27's 2026-10-24 02:16 landing has no `lean` record,
so this is the stage-2 handoff described in brief-stage2 section 0, not a re-split.

Hypothesis and clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`. The explicit universe `u`
  follows the recorded algebraic-space framework and its small-etale module section
  universe. There is no extra universe equality or smallness assumption.
- Algebraic spaces over S and their morphism are `{X Y : AlgebraicSpace S}` and
  `(f : X ⟶ Y)`. Their fppf sheaves, representable diagonals, and etale atlases
  are supplied by the recorded definition, rather than chosen as extra data.
- Finite means `hf : IsRepresentableWith (fun _ _ p ↦ IsFinite p.left)
  f.hom.hom`. This quantifies over every scheme test and supplies a representing
  scheme pullback whose projection is finite. `IsFinite` is Mathlib's recorded
  scheme definition, including affineness and finite affine ring maps.
- Finite presentation is `hfp : MapIsLocallyOfFinitePresentation f ∧
  MapIsQuasiCompact f.hom.hom ∧ MapIsQuasiCompact (pullback.diagonal f.hom.hom)`.
  The first conjunct is the universal compatible-etale-chart test. The second is
  quasi-compactness of the morphism, and the third is quasi-separatedness, exactly
  the stated quasi-compactness of its relative diagonal. It is not an absolute
  quasi-compactness condition on X or Y.
- The module is `(M : X.Modules)` on the existing small-etale structure sheaf.
  `[M.IsQuasicoherent]` is the existing Mathlib local-presentation predicate,
  specialized using the recorded algebraic-space slice instances.
- The direct image is exactly `(moduleDirectImage f).obj M`, the dependency's
  canonical compatible-section limit construction, with its prescribed scalars.
  No arbitrary pushforward or comparison is assumed.
- The first conclusion is `((moduleDirectImage f).obj M).IsQuasicoherent`.
- The second is `M.IsFinitePresentation ↔
  ((moduleDirectImage f).obj M).IsFinitePresentation`. Mathlib's predicate means
  locally the cokernel of a map between finite coproducts of the structure sheaf,
  exactly the finite free presentation in the node. The explanatory finite-type
  terminology adds no separate hypothesis or conclusion to this node.
- There are no Noetherian, flatness, or absolute quasi-compactness binders.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `EtaleSite`, `structureSheaf`, and `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`. This is publicly imported transitively through
  `AlgebraicSpaceMorphismProperties`; the relative diagonal uses the actual
  Mathlib sheaf/presheaf pullback, with the recorded fibre-product interpretation.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (through the chart-test module).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsLocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact` (publicly
  imported by the morphism-properties module).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `etaleModuleOverHasWeakSheafify`, `etaleModuleOverWEqualsLocallyBijective`, `QCoh`.
  The statement uses the underlying predicate of this full subcategory, namely
  `SheafOfModules.IsQuasicoherent` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`. The same Mathlib module
  supplies `SheafOfModules.IsFinitePresentation`; both full definitions were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImageModel`, `moduleDirectImage`, and its
  full compatible-chart section universal property.
- The size-convention dependency is metatheoretic, as its existing record says;
  explicit universe binders implement it without a fictitious Lean object.

The item gains the already landed statement dependencies
`def-sfb-space-morphism-properties` and `def-sfb-proper-curve-moduli`, whose exact
recorded predicates are used for finite presentation and quasi-compactness.
This is the landed-node addition expressly permitted by brief-stage2 section 5.
No dependency record changes and no statement correction are needed.

The existing proof-dependency modules are imported without `public`:
`SpaceLocalPropertiesChartTest`, `SpaceAffineModuleBaseChange`,
`AlgebraicSpaceEtaleModulePushforwardRestriction`,
`SchemeZariskiEtaleQuasiCoherentEquivalence`, and `ChartwiseEtalePermanence`.
Affine permanence has a Mathlib match, so its affine and separated modules are
also imported. The three proof nodes
`lem-sfb-scheme-etale-module-exact-finiteness-comparison`,
`lem-trf-finite-pushforward-preserves-finite-presentation`, and
`lem-trf-finite-pushforward-reflects-finite-presentation` have no recorded Lean
statement or Mathlib match at this handoff; there is no module of theirs to
import. They are proof inputs, not missing notions in this statement, and their
future stage-2 statements can be added as proof imports by the maintainer.

Sources checked: the local `literature/stacks-project/spaces-descent.tex`,
`lemma-finite-finitely-presented-module` (Tag 0610), states exactly the
finite/finitely-presented hypotheses and equivalence. The accepted split's
quasi-coherence clause is the affine direct-image clause of Tag 07U8. The proof
docstring follows all four accepted proof steps and records the scheme comparison
and atlas descent without silently strengthening the hypotheses.

Edge cases checked: zero modules and empty spaces are admitted; the identity
of a non-Noetherian, non-quasi-compact scheme is admitted; the nonflat finite
finitely presented closed immersion Spec(F_p) → Spec(Z) is admitted. No finite
atlas is required, so infinite disjoint unions cause no excluded cases. For a
non-finitely-generated ideal I of A, Spec(A/I) → Spec(A) is finite but its
structure-module direct image need not be finitely presented: this confirms that
the finite-presentation hypothesis on f must be retained. Both zero and finite
ranks are allowed by Mathlib's finite-presentation predicate.

Searches for an existing statement:

- `msearch.py ... leanfinder "A quasi-coherent module on an algebraic space is
  finitely presented if and only if its direct image by a finite finitely presented
  morphism is finitely presented"`: eight hits, chiefly the Mathlib sheaf
  finite-presentation definitions and scheme local-finite-presentation instance;
  no direct-image theorem for algebraic spaces.
- `msearch.py ... loogle "Module.FinitePresentation, Module.Finite"`: twelve hits,
  including finite-algebra module finiteness and finite-presentation results;
  these do not state the algebraic-space module direct-image assertion.
- `msearch.py ... grep
  "finitePresentation.*[Dd]irect|finite.*pushforward|finitePresentation_of_finite"
  Algebra/Category/ModuleCat`: zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for finite/direct-image and
  finite-presentation names found scheme/constructible-sheaf results and the
  algebraic-space closed-immersion structure-module special case, not this
  arbitrary-module assertion for arbitrary finite finitely presented maps.
- `rg` for the item id under `lean/WeilConjectures` found no attachment.
  Searching `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and
  `lean/Sheaf` for `finite_fp_moduleDirectImage` found no name collision.

No STATEMENT-DISPUTED flag or mathematical node fault was found. Initial server
validation through `scompile.py` passed for the sandbox and library module
(7.6 s and 6.8 s), with no reported errors or unexpected warnings.

## Second reading by N5

A separate rereading pass compared the finished signature against the node and
the full source definitions. It checked that `hf` tests ALL schemes (not only
etale charts), while `hfp` tests local finite presentation on etale charts and
retains both relative quasi-compactness conditions. It checked that M and its
direct image use the existing small-etale module categories, rather than the
Zariski categories used only in the proof plan. It checked that quasi-coherence
is a conclusion and that finite presentation is an equivalence. No missing or
extra clause was found, and no signature change was required by this pass.
This rereading is by the same dispatcher worker; no separate agents were started,
as the assignment expressly forbids them. The maintainer's independent review
remains the independent reading of this delivery.
