## Worker report

The new module `Sheaf.Algebra.Homology.FixedTensorLocalizationComparison` states
`SheafOfModules.FixedTensorLocalization.fixed_tensor_localization_comparison`.
Its only postponed theorem is this theorem, with proof `sorry`; the module and theorem
carry the source and the complete nine-step proof plan. All helper definitions contain
real data, or transparently package the conclusions of this one DAG statement. No
statement correction, new DAG node, dependency repair or live-file change is needed.

Hypothesis-by-hypothesis correspondence (names below are in
`SheafOfModules.FixedTensorLocalization`):

* A site small relative to module coefficients is `{C : Type u} [Category.{v} C]
  [EssentiallySmall.{r} C] {J : GrothendieckTopology C}`. The universes `u`, `v`, `r`
  are independent. `R : Sheaf J CommRingCat.{r}` is the commutative ring sheaf.
* `Modules R` is the dependency's `CategoryTheory.ringedSiteModules.{r}` at R's
  underlying ring sheaf, definitionally Mathlib's `SheafOfModules`. `Complexes R`
  uses all integer-indexed cochain complexes; `Homotopy R` is Mathlib's
  `HomotopyCategory ... (.up ℤ)`. `[HasDerivedCategory.{w} (Modules R)]` selects
  the morphism universe, without identifying it with any site universe.
  `Derived R` and `Q R` are `DerivedCategory` and `DerivedCategory.Qh`.
* `totalTensor R` is the existing commutative sheaf tensor's `.map₂CochainComplex`,
  i.e. the direct-sum total tensor. The imported CochainTensorUniverses instances
  supply its independent-universe monoidal, additive and coproduct structures;
  this module neither defines nor assumes a replacement tensor.
* `resolving R` is the exact predicate chosen by
  `site_derived_tensor_descent_independentCoefficients.{u,v,r,w,0,0}`.
  Its membership equivalence is K-flatness plus termwise site-flatness.
  `tensorK R`, `chainComparison R` and `resolvingComparison R` project the
  published homotopy bifunctor and its two specified natural comparisons from
  that same theorem. `tensorD R` curries the already published
  `siteDerivedTensorIndependentCoefficients`, using the same fixed final
  auxiliary universes `0,0`. Thus c and T are projections of the same package;
  no independent existential witness, resolution or arbitrary map is supplied.
* The fixed complex is `(A : Complexes R)`, K-flatness is `hA`, and termwise
  flatness is `hAf : ∀ n : ℤ, IsFlatOnSite ... (A.X n)`. `resolvingObject` inserts
  exactly those proofs into the published membership equivalence.
* The two fixed homotopy operations are the left and flipped-right evaluations
  of the published `Functor.curry.obj (tensorK R)` at `(quotient R).obj A`.
  Their two `Additive` and two `IsTriangulated` instance binders are precisely
  the assumed additive exactness. Their `CommShift ℤ` binders carry all zero
  and addition laws. `hUL` and `hUR` are exactly inversion of all homotopy
  quasi-isomorphisms by H followed by Q; neither requires H to be a localization.
* `hSL` states that the left homotopy operation's coherent comparisons restrict
  to the canonical signed `CochainComplex.mapBifunctorShift₂Iso`; `hSR` uses the
  unsigned `mapBifunctorShift₁Iso` in the right operation. Both equations insert
  the quotient's canonical shift comparison and conjugate by the specified
  `chainComparison`. These are the stated signed-shift normalization hypotheses,
  not assumptions of a derived shift structure on the published tensor.

Clause-by-clause conclusions:

* The conjunction supplies `NormalizedDescent` for each side. This is a Prop
  definition spelling out this node's conclusions once, with H, T's fixed
  argument functor F, and the published c as parameters. It is not an independent
  replacement tensor or a separate mathematical assertion.
* Its `∃ (G : Derived R ⥤ Derived R) (s : G.CommShift ℤ)` supplies each G and
  coherent integer-shift structure. `G.Additive ∧ G.IsTriangulated` is additive
  exactness, with the connecting arrow: Mathlib's `mapTriangle` maps w to G(w)
  followed by s_1. This applies to every distinguished triangle, not just cones.
* `η : H ⋙ Q R ≅ Q R ⋙ G` is the required natural factorization. `ShiftCompatible`
  writes the full square
  η_(X[n]); G(q_n(X)); s_n(QX) = Q(h_n(X)); q_n(HX); η_X[n].
  The next universal clause says every other coherent s' satisfying it equals s.
  Thus the signed normalization hypotheses descend to the unique shift structure.
* `∃ d : G ≅ F` gives a natural comparison on the entire derived category.
  The normalization `η_P ≫ d_(QP) = (c P).hom` is universal over the full published
  resolving subcategory. The next clause quantifies over every alternative d'
  and proves its equality with d under exactly the same normalization.
* The resolution clause quantifies over EVERY resolving P, EVERY homotopy object B,
  EVERY r:P→B and EVERY proof of its quasi-isomorphism property. It states literally
  e_B = (QH(r))^{-1}; c_P; F(Q(r)). Here `invertedMapIso` is `asIso` of that exact
  QH(r), using hUL/hUR, not a freely supplied inverse. On the left F(Qr) is
  T(1,Qr), and on the right it is T(Qr,1), by Mathlib's currying formulas.
  The same e_B occurs for all choices, giving resolution independence without
  a chosen resolution or an extra comparison hypothesis.
* Since η and d are natural isomorphisms of the whole indicated categories,
  their composite is natural on homotopy arrows, and d on EVERY derived arrow
  (including inverse denominators and composites). In particular the claimed
  derived naturality d_N G(v)=F(v)d_M is part of the type `G ≅ F` itself.
* The final universal clause considers any other factorization G', coherent s',
  η', and normalized d'. There is a UNIQUE natural isomorphism θ:G≅G' satisfying
  `η_X ≫ θ_(QX) = η'_X`, `NatTrans.CommShift θ.hom ℤ`, and `θ_M ≫ d'_M = d_M`.
  This expresses uniqueness of the factorization together with signed shifts and
  normalized comparisons. It even applies without separately re-assuming the
  other factorization's additivity/exactness, which follow from compatibility.
* No bounds, flat cohomology, nonzero-object assumption, or chosen resolution
  occur anywhere. The size binders retain sites with different object and Hom
  universes, in particular the small pro-etale site.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  also read Mathlib `SheafOfModules`, its linear morphisms and abelian instance.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Qh`, their additive, localization,
  shift and triangulated instances, and the distinguished-cone characterization.
* `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  `mapBifunctorShift₁Iso`, `mapBifunctorShift₂Iso` and the `CommShift₂Int` instance;
  read their signed summand formulas and coherent fixed-argument instances.
* `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients` and
  `siteDerivedTensorIndependentCoefficients`, including full signatures/docstrings
  and the published constructions of B, T and comparisons.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` (all acyclic test complexes).
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` (exactness of canonical sheaf tensor).
* `Mathlib.CategoryTheory.Triangulated.Functor`: `Functor.CommShift`,
  `Functor.IsTriangulated`, `Functor.mapTriangle`, `NatTrans.CommShift`.
* Proof imports: `Mathlib.CategoryTheory.Localization.Predicate` (`lift`, `fac`,
  `liftNatIso`, `liftNatTrans`, `natTrans_ext`, fully faithful whiskering);
  `Mathlib.CategoryTheory.Shift.Localization` (coherent localization shifts);
  `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated` (homotopy triangulated
  instance); `Sheaf.CategoryTheory.AdditiveLocalizationDescent`
  (`Functor.additive_of_additive_localization`, read via scompile --source because
  the local checkout did not yet contain it); and
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
  (`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`).

Edge cases checked against the displayed formulas: n=0 reduces to the canonical
zero comparison; negative n use the same integer shifts; a resolving identity
r=id recovers c; zero complexes and the empty site are allowed; B and A may be
unbounded in both directions. No flatness of B, its terms, or its cohomology is
assumed. The same formula for any two resolutions gives equal values, without
requiring a map between those resolutions. Arbitrary derived morphisms are
covered by the type of d rather than just by chain-level squares.

Searches for an existing statement:

* `msearch.py ... leanfinder "Exact localization of fixed K flat tensor with signed
  shifts and unique natural comparison to derived tensor on resolving complexes"`:
  eight hits, mostly Tor/Tor' and `Functor.isHomological_of_localization`; none
  supplies the resolving comparison and uniqueness/formula clauses.
* `msearch.py ... loogle "CategoryTheory.Functor.commShiftOfLocalization,
  CategoryTheory.Functor.IsTriangulated"`: zero hits.
* `msearch.py ... grep "commShiftOfLocalization|isTriangulated_of_precomp"
  CategoryTheory`: eight hits in Triangulated/Functor and Shift/Localization;
  these are generic exactness and shift-descent tools, not this statement.
* `msearch.py ... leansearch "Localization of exact fixed K-flat tensor with unique
  normalized resolving natural comparison"`: eight flat-module/localization hits,
  none about the normalized unbounded sheaf tensor.
* `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for fixedTensor/fixed_tensor/FixedTensor/the item id and the new namespace:
  found the related `KFlatFixedTensorTriangulated` and unrelated fixed tensors.
  Read that module fully: its theorem gives the parent's two-variable exactness
  and representative comparisons, but omits this node's factorization uniqueness,
  uniquely normalized d and inverse-resolution formulas. Its DAG proof depends on
  this item, so it is not imported here. No exact existing match or name collision.

Sources opened: Stacks sites-cohomology.tex, the construction preceding
`definition-derived-tor` (06YU) and its symmetry paragraph; categories.tex,
`lemma-properties-left-localization` (04VG) and
`lemma-properties-right-localization` (04VK); the current main-20261015 blueprint
perfect-projection-formula proof, first paragraph (exactness under shifts/cones).

Validation: server compilation and delivery preflight results recorded below.

## Author check by Q30

This is the dispatcher's single-worker delivery; no other worker was started.
The maintainer performs the independent review. I checked the statement again
against the node, explicitly tracing the orientation of η, c, d and the inverse
of QH(r), and the two different signed shift comparisons. The initial compile
found unmatched parentheses in the shift hypotheses; these were repaired before
validation. The theorem proof is `sorry`, with no other postponed declaration.

The corrected complete module compiled cleanly against current server sources in
44.0 seconds, within the unchanged 60-second limit (scompile.py exit 0). The
wrapper first timed out on its sandbox pass and confirmed the clean result
against current server sources; no compiler warnings were reported.

`deliver2.py Q30 lem-weil-pbc-fixed-tensor-localization-comparison --no-push`
passed the server preflight and per-file compilation: `OK (dry run)` at
`80a9b30ecfa`. Only the item node, its module and this report were staged.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
