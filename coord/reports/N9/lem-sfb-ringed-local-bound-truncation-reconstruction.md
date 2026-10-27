## Worker report

Item: lem-sfb-ringed-local-bound-truncation-reconstruction. The delivery states
`CategoryTheory.ringed_local_bound_truncation_reconstruction` in
`Sheaf.CategoryTheory.RingedLocalBoundTruncationReconstruction`; its only proof is `sorry`.
There are no new definitions, helper theorems, dependency repairs or statement corrections.
Only the item's `lean` record is changed. The signature is copied literally from the file.

Source read: `literature/stacks-project/sites-cohomology.tex`, situation-olsson-laszlo
and lemma-olsson-laszlo (Tags 0D6R/0D6S), together with lemma-olsson-laszlo-modified;
`literature/stacks-project/derived.tex`, remark-map-into-derived-limit-truncations
(Tag 0H72). The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was also read. This is the supporting ringed-site lemma, not that unit's own assertion.

Hypothesis and conclusion correspondence:

- A coefficient-relative small site: `{C : Type uC} [Category.{vC} C]
  [EssentiallySmall.{r} C]`, `J : Precoverage C`, and `_hJ : J.IsSiteForCoverings`.
  This is the dependency's actual-covering site interface; sheaves live on
  `J.toGrothendieck`. Object and morphism universes are independent of `r`.
- A sheaf of commutative rings: `R : Sheaf J.toGrothendieck RingCat.{r}` and
  `_hcomm : ∀ U a b, a * b = b * a`. This is exactly a commutative ring sheaf
  presented after forgetting to RingCat, as in the strict-tower dependency.
- The category Mod(O): `ringedSiteModules.{r, r, vC, uC} R`, the transparent
  dependency abbreviation of Mathlib `SheafOfModules`. `HasSheafify` and
  `WEqualsLocallyBijective` supply its ordinary Mathlib abelian structure; they are
  the standard small-site infrastructure, not new mathematical restrictions.
- The ordinary unbounded derived category: `DerivedCategory` with
  `[HasDerivedCategory.{w} (ringedSiteModules ... R)]`. The localization universe
  `w` is independent. No bounded or completed replacement is used.
- The strictly full weak Serre subcategory: `S : ObjectProperty ...` with
  `S.IsClosedUnderIsomorphisms`, `S.ContainsZero`, `S.IsClosedUnderKernels`,
  `S.IsClosedUnderCokernels`, `S.IsClosedUnderExtensions`. These are exactly the
  five conditions in the node, using existing classes rather than a second definition.
- D_S consists of objects with every cohomology sheaf in S:
  `_hE : DerivedCategory.homologyProperty S E`. Its upstream definition is
  `∀ n : ℤ, S ((DerivedCategory.homologyFunctor _ n).obj E)`.
  D^+_S is explanatory notation in the node's proof; no boundedness hypothesis on E
  is imposed. Each good truncation is automatically bounded below.
- The covering set is `B : Set C`. `_hcover` says every U admits a covering
  presieve P with every domain V in B. Arbitrary, including empty, covers are allowed.
- The local integer is `∃ d : ℤ` separately for every `V ∈ B`, in `_hlocal`.
  For every covering P it supplies a covering T refining P. The expression
  `∃ U g a, P g ∧ a ≫ g = f` is refinement by factorization, not inclusion of
  presieves. In particular a refining member need not itself be a member of P.
- The cofinal collection need not be selected as additional data: take all coverings
  whose members have the required vanishing. `_hlocal` says precisely that this
  collection is cofinal. Conversely any collection in the node supplies these T.
  The order of quantifiers is d, P, T, member W, p, F, resolution; hence T is uniform
  over all F in S and p>d, and d is uniform over this cofinal collection.
- `H^p(W,F)=0` is `IsZero` of the degree-p homology of the section complex of any
  K-injective resolution `ι : singleFunctor _ 0 |>.obj F ⟶ I`. Sections are the
  existing composite `SheafOfModules.toSheaf R ⋙ sheafToPresheaf ... ⋙ evaluation ...`.
  This computes the right derived functor of module sections, not derived evaluation
  in the category of abelian sheaves. It therefore needs no forgetful cohomology
  comparison. The strict-tower dependency guarantees K-injective resolutions, so
  quantification over these resolutions is not vacuous. Using p in ℤ rather than ℕ
  includes the automatically zero negative cohomology of F[0], without strengthening
  the nonnegative bound, including when d is negative.
- The lower truncations are the existing standard t-structure
  `(DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E`, n in ℕ.
  The transitions are `natTransTruncGEOfLE` for `-(n+1) ≤ -n`; the arrows from E
  are `truncGEπ`. These are the localized good truncations recorded by
  def-kun-truncations, not stupid truncations or arbitrary tower maps.
- The stipulated resolution-derived inverse limit has underlying data L, π, δ and
  `_hL : IsDerivedLimitTriangle ... L π δ`; its product is the displayed
  `HasProduct` binder. This is the exact underlying Roos-triangle interface exported
  by the recorded strict-tower theorem. Those binders express a choice of the limit
  already stipulated in the node, not an exact-products assumption or an arbitrary
  unconstrained map. No total derived functor is redefined. Tag 0H72 explicitly says
  that invertibility is independent of the choice of the homotopy limit and compatible
  comparison; the theorem can consequently consume the data of any such choice,
  in particular the fixed resolution-derived one.
- The first conclusion is an actual derived isomorphism `∃ e : E ≅ L`. Its equality
  `e.hom ≫ π ≫ Pi.π ... n = (truncGEπ ...).app E` is the compatibility with every
  canonical projection, for every n, not just sufficiently large n.
- The second conclusion says `IsIso c` for every specified c satisfying those same
  equations. This retains the assertion about the actual comparison induced by the
  truncation maps, rather than merely an unrelated isomorphism of objects. It is the
  choice-independent assertion explicitly explained in 0H72 and in proof steps 2–4.

Dependency declarations read and used:

- def-weil-size-convention: its convention-only record is rendered by the four explicit
  universes and coefficient-relative `EssentiallySmall`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` (full definition/docstring read).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (full abbreviation/docstring read), hence Mathlib `SheafOfModules` and its abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; signatures and docstrings read.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients` (full theorem
  signature/docstring read). Its conclusions supply the resolution computation,
  countable derived products and actual Roos data. It is publicly imported.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle` and `IsDerivedLimit`, full definitions read.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: the recorded composite
  def-kun-truncations module publicly imports the canonical Mathlib truncation
  constructions described in its module docstring. The main recorded
  `IsSequentialHomotopyColimit` is a different clause of that composite node and is
  not substituted for truncations.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`:
  `DerivedCategory.homologyProperty`; existing Mathlib ObjectProperty closure classes.
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`:
  `truncGE`, `truncGEπ`, `natTransTruncGEOfLE` of the standard t-structure.
- Proof-only leaves: `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.isIso_iff` (full signature read);
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
  `Triangle.coyoneda_exact₂`, `coyoneda_exact₁` and `comp_distTriang_mor_zero₁₂`
  (exactness signatures read; imported through the derived-limit module);
  `Mathlib.CategoryTheory.Limits.Shapes.Products`, `Pi.π`, `Pi.lift`, `Pi.map`,
  and `Shapes.Countable`, `HasCountableProducts` (recorded signatures read).
- lem-sfb-ringed-local-bound-stationary-limit-cohomology currently has no Lean record
  or Mathlib match. It is a proof-only dependency, not needed to type this statement;
  its mathematical statement was read and the full assembly proof is in the docstring.
  There is no module to import yet. This delivery does not duplicate that theorem.

Edge cases checked against the source before writing: zero E; the zero weak Serre
subcategory; n=0 (τ≥0, retained in all projection equalities); negative cohomological
j and eventual index max(0,-j); negative d (the bound includes degree zero as required);
empty covering families (member conditions are correctly vacuous); empty B when objects
are covered by empty covers; disconnected sites; site object universe larger than the
morphism universe; coefficients independent of both. No uniform d, lower bound on E,
countable product exactness, point/stalk hypothesis or Noetherian hypothesis is added.

Searches for duplicates (2026-10-24):

- `msearch.py ... leanfinder`: “On a ringed site with local finite cohomological
  dimension for a weak Serre subcategory a complex is recovered from the derived inverse
  limit of its lower truncations”: 8 hits about representatives/truncation support,
  none stating the local-bound reconstruction theorem.
- `msearch.py ... loogle '"DerivedCategory", "truncGE"'`: 0 hits.
- `msearch.py ... leansearch`: “A complex of sheaves on a ringed site is the derived
  inverse limit of its lower truncations under local cohomological bounds”: 8 hits
  about ordinary sheaf/complex limits, not this derived reconstruction statement.
- `msearch.py ... grep 'olsson|laszlo|left.?complete|trunc.*[Ll]imit|[Ll]imit.*trunc'`:
  14 hits, Witt vectors, ordinary simplicial limits and a truncation homology kernel;
  no match for this item.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` for the declaration name: no existing declaration.
  Searches for weak Serre/homologyProperty locate the reused upstream object property.
  Search for the exact blueprint id in WeilConjectures and Sheaf: no existing declaration.
- Concept searches over both project source roots found
  `site_truncation_isDerivedLimitTriangle` (Tag 0D6P), which assumes one uniform bound
  for negative cohomology over a fixed covering basis; it does not express the present
  varying-d_V/cofinal-refinement hypothesis. `pointwise_truncation_limit_exists` and
  its companion apply to ringed topological spaces with pointwise neighbourhood bounds,
  not arbitrary ringed sites and weak Serre subcategories. Their interfaces were read.

Validation: `scompile.py N9 lem-sfb-ringed-local-bound-truncation-reconstruction <file>`
passed both sandbox and library-name checks (2.1 seconds each), with no diagnostics.
No auto-bound implicit variables, local notation, private declarations or data choices.
No STATEMENT-DISPUTED finding or source/node fault.

## Second reading by N9

A second local pass compared the completed signature with the node and the cited
0D6R/0D6S/0H72 source passages. This is a self-audit; the maintainer supplies the
independent reading, as required by this dispatcher's brief. No other agent was started.
The checks focused on the d-before-cover-before-F quantifiers, refinement by actual
factorization, all five weak Serre conditions, independent universes, ordinary module
rather than abelian-sheaf derived sections, and compatibility for all n. The second
conclusion ensures a specified compatible comparison is invertible; the first provides
the derived isomorphism explicitly. No mismatch requiring a node correction was found.
