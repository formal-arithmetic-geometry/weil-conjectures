## Worker report

The module `Sheaf.Algebra.Homology.LocalizedBoundedHomComparison` states
`CategoryTheory.LocalizedBoundedHom.isIso_comparison` and all the node's more
precise clauses in its recorded companion declarations. All seven theorem
proofs are `sorry`; definitions have actual canonical data. There is no change
to the mathematical statement, proof, or proof dependencies. The existing
coefficient-action and Hom-projection nodes are added to `stmt_deps` because
their declarations occur in the statements.

Hypothesis and conclusion correspondence:

* The small site is `{C : Type u} [SmallCategory C]` with
  `{J : GrothendieckTopology C}`. This is the Grothendieck-topology presentation
  of the site used by Mathlib and the recorded Hom-complex declaration.
* The commutative coefficient ring and element are `(A : Type v) [CommRing A]`
  and `(t : A)`. The ring sheaf is `R : Sheaf J CommRingCat.{u}`.
  Its A-algebra structure is the ring homomorphism
  `a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)`:
  equivalently, a compatible family of unital coefficient maps on all objects.
  No nonzero, reduced, invertibility, or projectivity condition is imposed.
* Module sheaves are exactly `SheafOfModules` over the forgotten commutative
  ring sheaf. Complexes `P`, `M`, `N` are the recorded `CochainComplex ... ℤ`.
  The map `f : M ⟶ N` is arbitrary, including unbounded target complexes.
* The derived category is the recorded `DerivedCategory`, with an explicit
  `[HasDerivedCategory.{w} ...]` binder. The levels u, v, w are explicitly bound.
  A common small site/module universe is chosen as allowed by the size
  convention; the coefficient ring and derived Hom universes remain independent.
* The action on D(R) is precisely `scalarLocalizationDerivedLinear A R a`.
  The dependent lambda supplies that instance to the proposition; it neither
  quantifies over arbitrary coefficient actions nor introduces a `let` binder.
  `ScalarLocalization.localization A _ t` is exactly Q_t of the recorded node.
* The support interval is `(b₀ b₁ : ℤ)` with
  `∀ n, n < b₀ ∨ b₁ < n → IsZero (P.X n)`.
  There is no requirement `b₀ ≤ b₁`.
* `comparison R V f` is the actual postcomposition map
  `((homComplexFunctor (R := R)).obj (op V)).map f`.
  `hterms` says its image under `DerivedCategory.Q` and Q_t is an isomorphism
  for `(HomologicalComplex.single _ (.up ℤ) 0).obj (P.X n)` for every
  `b₀ ≤ n ≤ b₁`. The conclusion is the same `IsIso` for the actual source P.
* The canonical sequence of source tails is the existing
  `P.shortComplexStupidFiltrationGE r (r+1) rfl`. Its first map is the
  inclusion of the next tail, and its second map is projection to P^r in degree r.
  Its terms are the actual stupid truncations and the existing single complex,
  representing P^r[-r] with zero differential.
* `row_zero` and `row` form the Hom short complex with actual precomposition
  by that projection and inclusion, not unspecified isomorphic arrows.
  `row_shortExact` states its exactness. The upstream source sequence has
  the existing `shortComplexStupidFiltrationGESplitting` in every degree.
* `row_comm` states the two squares for postcomposition by f. `rowMap` has
  exactly the three comparisons as its components. Its data are explicit;
  only the named square proofs are postponed.
* `triangleMap` is the actual `DerivedCategory.triangleOfSES.map` of that
  morphism. Thus all three squares commute as part of its type.
  `triangles` states both rows' derived triangles are distinguished and records
  the connecting equality explicitly, using the canonical
  `DerivedCategory.triangleOfSESδ`, not a chosen triangle filler.
* `localized_triangles` states that both actual image triangles are distinguished
  and gives the connecting equality in the localized category. The other two
  squares and the triangle morphism are the actual
  `(ScalarLocalization.localization A _ t).mapTriangle.map (triangleMap ...)`.
  The structural instance binders express an exact triangulated enhancement of
  this same Q_t; existence is already provided by
  `ScalarLocalization.exists_triangulated_scalarLocalization`. They impose no
  additional condition on the site, coefficient action, P, or f. The main
  invertibility theorem does not require any such enhancement as an input.
* `signed_single_shift` supplies a natural isomorphism between Hom(P^r[0],-)[r]
  and Hom(P^r[-r],-), using the existing single complex in degree r.
  Its explicit naturality equality holds for every target chain map, hence includes this f.
  Using the canonical `shiftFunctorObjXIso`, product projections, and
  `singleObjXSelf` identification,
  its degree-q component is exactly `(r*q).negOnePow •` the degree-(q+r)
  component on the degree-zero side. This specifies the same normalization
  for M and N, including negative and odd degrees.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` (the recorded site interface;
  the actual coefficient/Hom APIs take its associated Grothendieck topology).
* `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
* `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
* `WeilConjectures.Algebra.Homology.HomComplex`:
  `CategoryTheory.homComplexFunctor`, `CategoryTheory.homComplex`.
* `Sheaf.CategoryTheory.ScalarLocalization`:
  `CategoryTheory.ScalarLocalization` and `.localization`.
* `Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions`:
  `CategoryTheory.scalarLocalizationDerivedLinear`; its canonical section action
  and restriction of scalars were read in full.
* `WeilConjectures.Algebra.Homology.HomComplexComponents`:
  `CategoryTheory.homComplexπ`, built from the recorded
  `CategoryTheory.homComplex_projections_exists` of
  `WeilConjectures.Algebra.Homology.HomComplexProjections`.
* `WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns`:
  `CochainComplex.shortComplexStupidFiltrationGE` and its actual inclusion,
  projection, and `shortComplexStupidFiltrationGESplitting`.
* `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`:
  `triangleOfSES`, `triangleOfSES.map`, `triangleOfSESδ`, and their naturality.
* Proof interfaces read: `exists_homComplex_stupid_tail_shortExact` in
  `WeilConjectures.Algebra.Homology.StupidTailHomShortExact`;
  `homComplex_shift_left` in
  `WeilConjectures.Algebra.Homology.HomComplexShiftLeft`;
  `ScalarLocalization.exists_triangulated_scalarLocalization` in
  `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`;
  `DerivedCategory.instLinear` and the Q/shift linearity instances in
  `Mathlib.Algebra.Homology.DerivedCategory.Linear`;
  `CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.

Source check: read Stacks sites-cohomology.tex at `lemma-RHom-triangulated`
(08JC): its proof explicitly says ordinary sheaf Hom takes termwise split
short exact sequences to termwise split short exact sequences. Also read the
current blueprint `prop-sf-dualizable` statement and proof. The signed ordinary
Hom and finite-tail details belong to the reviewed auxiliary node, not a
replacement by derived internal Hom on arbitrary representatives.

Edge cases checked: P=0; a>b (vacuous term hypothesis and every source term
zero); a=b; a two-term source with a nonzero differential; odd and negative r
and q; f=0 or identity; unbounded M and N; empty site; zero coefficient ring;
t=0, nilpotent, or a unit. The sign equation is
`s_(q+1)*(-1)^r=s_q` and the sign squares to one. The source filtration
splittings need not be chain maps, so the construction does not introduce a
splitting of complexes or require source projectivity.

Searches made on 2026-10-22:

* `msearch.py ... leanfinder` with “Internal Hom from bounded complex comparison
  is an isomorphism after scalar localization if each source term comparison
  is an isomorphism”: eight hits, concerning small localized shifted external
  Hom, derived roofs, quasi-isomorphism localization, or t-structure bounds;
  none gives scalar-localized ordinary internal sheaf Hom or the signed clause.
* `msearch.py ... loogle 'CochainComplex.internalHomObj, IsIso'`: zero hits;
  the service did not recognize the upstream internalHomObj identifier.
* `msearch.py ... grep 'stupidTrunc|internalHom' Algebra/Homology/Embedding`:
  seven hits, all on the existing stupid-truncation infrastructure, which is
  reused through the existing upstream canonical stupid-filtration sequence.
* `msearch.py ... leansearch` with “Termwise scalar localized internal Hom
  comparison for a bounded source complex”: eight hits on graded algebra
  localization, small external shifted Hom, short-complex comparison, and
  scalar structures; none states this node.
* `rg` over the project and upstream for localized bounded Hom found no existing
  target declaration. Searches for Hom tails and shifts found and led to reading
  `StupidTailHomShortExact`, `HomComplexShiftLeft`, `HomComplexComponents`, and
  the upstream canonical filtration construction, all reused here.
* `grep -rn 'lem-sf-localized-bounded-hom-comparison' lean/WeilConjectures`
  found no existing module attached to the node.

No new independent notion or dependency repair is needed. No statement is disputed.
All compiles and delivery checks use the prescribed wrappers only.

Validation: the prescribed scompile.py compiled the full final file cleanly
in sandbox mode (13.8 s) and actual module mode (11.6 s), with no errors or
warnings. Explicit ring universes avoid the earlier unresolved-universe search,
and the normalized shift formula uses the actual shift evaluation isomorphism.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
