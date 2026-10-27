## Worker report

The delivery states Stacks 08FR, lemma-local-actual (1), in
`Sheaf.Algebra.Homology.StrictPerfectLocalActual`. Its only theorem,
`CategoryTheory.StrictPerfectLocalActual.exists_local_chain_map`, has proof `sorry`.
The two helpers contain real constructions: `rings` forgets commutativity, and
`restrict` transports the exact further restriction of a derived morphism through
Mathlib's canonical `mapDerivedCategoryFactors` comparisons. Neither chooses a map
or assumes a local lift. The node's mathematical statement and proof are unchanged.

Hypothesis and conclusion correspondence:

- The arbitrary site is `{C : Type c} [Category.{v} C] {J : GrothendieckTopology C}`.
  Its object and morphism universes are independent. The coefficient universe is
  `max c v r`, with independent excess size `r`; it is large enough for the site.
- A sheaf of commutative rings is `R : Sheaf J CommRingCat.{max c v r}`.
  `rings.{c, v, r} R` is its unchanged ring-valued underlying sheaf.
- The object of the site is `U : C`. The category of localized module sheaves is
  `ringedSiteModules.{max c v r} ((rings R).over U)`, the dependency's transparent
  abbreviation for Mathlib `SheafOfModules`; `Sheaf.over` uses `J.over U`.
- `P F : CochainComplex ... ℤ` are the two cochain complexes over this slice.
  There is no boundedness, perfectness, K-injectivity, or projectivity assumption on F.
- Vanishing outside finitely many degrees is precisely
  `hbounded : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j)`.
  A finite subset of ℤ is contained in a finite interval; the empty support is allowed.
- Each term being a direct summand of a finite free module is `hterms`: for every j,
  there is `n : ℕ` and `Nonempty (Retract (P.X j) (∏ᶜ fun _ : Fin n ↦
  SheafOfModules.unit ((rings R).over U)))`. A finite product of copies of the
  rank-one module is the finite free sheaf, with componentwise tuple sections.
  `Retract` supplies inclusion and projection whose composite is the identity on
  `P.X j`. No chain compatibility of these degreewise splittings is imposed.
  This uses existing Mathlib constructions, not a second strict-perfect predicate.
- The arbitrary derived morphism is
  `u : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj F`.
- The covering is `∃ S : Sieve U, S ∈ J U ∧ ...`. This is equivalent to a covering
  family by taking its arrows; conversely the generated sieve of a covering family
  covers. Further restriction of a representing chain map gives representatives
  on every arrow of that sieve, so no compatibility between chosen representatives
  is added by the sieve formulation.
- For every member `f : V ⟶ U` of S the conclusion supplies an actual chain map
  `t` between the images of P and F under
  `(SheafOfModules.overMap (rings R) f).mapHomologicalComplex (.up ℤ)`.
  This is restriction along `C/V → C/U`, using the dependency's relocalization.
- The equation `DerivedCategory.Q.map t = restrict R f u` is exactly equality
  with the restricted derived morphism. In detail `restrict` is
  `(mapDerivedCategoryFactors.app P).inv ≫ mapDerivedCategory.map u ≫
  (mapDerivedCategoryFactors.app F).hom` for this exact overMap. Thus its source
  and target are the localizations of the displayed termwise restrictions.
- The slice sheafification and local-bijectivity instances are the size/sheafification
  interfaces for the existing abelian module categories. The family of
  `HasDerivedCategory.{w}` instances selects the derived localization universe on
  the slices. These are the ambient choices from the recorded definitions, not
  mathematical finiteness assumptions. In particular no equality `c = v` is used.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  its exact underlying Mathlib `SheafOfModules`, its linear `Hom`, and the abelian
  instance from `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, and its factorization through homotopy.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and
  `Mathlib.CategoryTheory.Sites.Over`: `SheafOfModules.overMap`, `overFunctor`,
  `overFunctorMap`, `Sheaf.over`, and `GrothendieckTopology.over`.
- `Sheaf.Algebra.Homology.SitePerfectModelRestriction`:
  `SheafOfModules.overMap_exact_ofUniverses` and
  `SheafOfModules.sitePerfectOverMap_additive`. The two already landed DAG nodes
  `lem-sf-site-perfect-overmap-exact` and `lem-sf-site-perfect-overmap-additive`
  are added to stmt_deps because these interfaces construct the restriction map.
  No node is newly created or repaired.
- The available proof dependencies are imported: Mathlib's
  `DerivedCategory.left_fac` and fractions instances, exact functor
  `Functor.mapDerivedCategory` and `Functor.mapDerivedCategoryFactors`, and
  `Sheaf.CategoryTheory.LocalizedModuleExactForSystems` for
  `SheafOfModules.localizedSystemExact`. The general 08FQ local-lifting node has
  no recorded Lean or Mathlib declaration; it is a proof dependency only, so no
  unfinished module is imported. Its mathematical substitution is documented in
  the theorem docstring, preserving the accepted proof plan.

Read the local source `sites-cohomology.tex`, definition-strictly-perfect and
lemma-local-actual with its proof, including the unbounded target case.
The definition and theorem agree with the node; no statement correction or
STATEMENT-DISPUTED marker is needed.

Edge cases checked before writing: the zero complex admits arbitrary finite
bounds; rank n=0 is allowed; the zero coefficient ring is allowed; no support
ordering a≤b excludes the zero complex; an acyclic or unbounded F is permitted;
identity restriction uses the same canonical comparison; an empty covering sieve
is allowed exactly when it is covering, and then the memberwise assertion is
vacuous, as in the source's empty-cover case. No points, terminal object,
pullbacks, subcanonical topology, or projectivity in the abelian sheaf category
are assumed.

Searches actually made (the wrapper records the full outputs in searches.jsonl):

- msearch leanfinder, "Morphisms from strictly perfect complexes of sheaves on
  ringed sites are locally represented by chain maps": 8 hits, including
  DerivedCategory fraction lemmas, locally bijective sheaf Hom equivalences and
  local surjectivity. None states 08FR(1).
- msearch loogle, "DerivedCategory.Q, SheafOfModules.overMap": 0 hits.
- msearch grep, "StrictlyPerfect|strictlyPerfect|localActual": 0 Mathlib hits.
- msearch leansearch, "Morphisms from strictly perfect complexes on a ringed site
  locally lift to morphisms of complexes": 8 hits on liftExtend, liftCycles and
  localization factors, none stating 08FR(1).
- rg on both `lean/Sheaf` and `lean/WeilConjectures` for StrictlyPerfect,
  strictlyPerfect, strictPerfect, local_actual/localActual, 08FR and 08FQ:
  scheme-specific strict-perfect models, constant-coefficient results and the
  general degreewise finite-free splitting package were found. The package is
  data rather than this theorem; existing constructions `Retract`, finite products
  and `unit` express precisely its termwise existence clause here. No duplicate
  predicate is introduced. The constant-perfect local chain statement requires
  constant coefficients, and the scheme statements require a scheme; neither is
  the arbitrary ring-sheaf statement.
- grep for the exact item id in `lean/WeilConjectures`: no match. rg for the new
  namespace/declaration names in the project's two source trees: no match.
- Read `RingedSiteModules`, the derived-category, over-site and overMap interfaces,
  `StrictPerfectPackageOnSite`, `SitePerfectModelRestriction`, and existing derived
  restriction comparisons to choose the canonical constructions used above.

Validation: the server wrapper compiled the sandbox and its proper module name.
The first pass diagnosed an ambiguous max-universe inference for the helper
`rings`; explicit `.{c, v, r}` arguments resolve it without equating universes.
The subsequent pass compiled, and line-width warnings were repaired before the
final clean compile and delivery dry run.

## Second reading by Q27

No second agent was started, as instructed by the dispatcher. The maintainer's
independent delivery review is the independent reading. A final self-check with
the node and module open matched both complexes, both strict-perfect hypotheses,
the arbitrary derived morphism, covering, actual chain maps, and their exact
localization equality as detailed above. It also checked the orientation of the
canonical comparison (inverse at P, forward at F), retained the unbounded F,
and confirmed that neither helper contains sorry. Only the theorem is postponed.
