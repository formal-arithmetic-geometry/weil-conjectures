## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion` as
`AlgebraicGeometry.Etale.boundedBelow_truncation_criterion`. Its only theorem proof is
`sorry`, with the node's complete three-step proof in the docstring. No mathematical
statement correction and no new notion is needed. The old `lead_note` identifies the
same `Function expected at hypercohomologyCouple` error reproduced during this work.
There is no item repair-note JSON in the shared checkout.

Sources read: the item's full DAG node and every statement dependency, their source
signatures and docstrings; the recorded master blueprint node (order 1439); and its
current `main-20261015` counterpart under `sk-thm-sbc-derived` (order 1494), including
the separate proof file. The current blueprint states the same criterion.

Hypothesis and clause correspondence:

- Schemes `T,S,X` and maps `g:T→S`, `f:X→S` are the corresponding explicit binders,
  with one arbitrary scheme universe `u`.
- `Y`, `e:Y→T`, `h:Y→X`, and `_sq : ChosenCartesianSquare e h g f` express the chosen
  fibre product square. The structure includes its identification with the pullback
  and both projection equations; allowing the chosen isomorphic fibre product is
  precisely the square dependency's convention.
- `P : Set ℕ` records the set of allowable primes. As in the recorded allowable-torsion
  definition, nonprime members do not affect its meaning; no extra restriction on P
  is required. `K : AbelianDerivedCategoryPlusTorsionOfPrimes T P` expresses bounded
  below and allowable-torsion cohomology on the small étale site, with coefficients
  `AddCommGrpCat.{u+1}`. `K.obj` is its underlying unbounded derived object.
- `n : ℤ` permits every integer degree, including negative degrees.
- `((DerivedCategory.TStructure.t.truncLEι n).app K.obj)` is the canonical inclusion
  `τ≤n K → K`, rather than an arbitrary arrow or an unspecified isomorphism.
- The first `IsIso` applies `hypercohomologyFirstFunctor g` to that inclusion and then
  `DerivedCategory.homologyFunctor _ n`: exactly `H^n(Rg_*τ≤nK) → H^n(Rg_*K)`.
- The second `IsIso` uses `hypercohomologyBaseChangeFunctor g f`, the composite
  `Rg_*` then exact derived `f⁻¹`; this is exactly the displayed pulled-back map.
- The third uses `hypercohomologySecondFunctor h e`, exact derived `e⁻¹` followed
  by `Rh_*`; it is exactly the third displayed map, with the same truncation inclusion.
- The last conjunct quantifies over every `L : CochainComplex.Plus` representing K,
  using `Nonempty (DerivedCategory.Q.obj L.obj ≅ K.obj)`. It requires, for every
  page `r ≥ 2` and `q > n`, vanishing (`IsZero`) of the terms with bidegree `(n-q,q)`
  in all three `CategoryTheory.hypercohomologyCouple` constructions. Thus their total
  degree is n and no cohomology sheaf above n contributes. The published
  `BigradedExactCouple.page` uses `pageCouple (r-2)`, so this includes E₂ and every
  later page, with the intended indexing. The representative isomorphism is used
  only to specify which object's spectral sequence is being discussed, not to
  choose a resolution or impose an extra hypothesis on K.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including its chosen pullback iso.
- `Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories`:
  `AlgebraicGeometry.Etale.AbelianDerivedCategoryPlusTorsionOfPrimes`, defined by
  `allowableTorsionPlusProperty` as allowable torsion intersected with `t.plus`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t` (the standard t-structure), together with
  `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT` for `truncLEι`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` and `upperStar`; the recorded hypercohomology
  functors use their total derived direct image and exact `mapDerivedCategory`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryPlus`, `mapDerivedCategory`,
  `mapDerivedCategoryHomologyFunctorIso`, and `isGE_mapDerivedCategory_obj`.
  The hypercohomology functors are the compatible unbounded implementations of
  the node's bounded-below functors; K is still restricted to D+.
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`:
  `CategoryTheory.hypercohomologyCouple`, `hypercohomologyE`, and
  `AlgebraicGeometry.Etale.hypercohomologyFirstFunctor`,
  `hypercohomologyBaseChangeFunctor`, `hypercohomologySecondFunctor`.
- Proof imports retain the published negative-vanishing theorem in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
  `Functor.rightDerivedFunctorPlusCompatibility` in the corresponding
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`,
  and exactness in `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`.
  `DerivedCategory.HomologySequence.exact₂` and its companions are publicly
  imported through the hypercohomology module.
- The remaining proof dependencies are the published
  `WeilConjectures.CategoryTheory.TruncationCouple` (`TruncationCouple.cohomologyComplex`
  is the single complex in degree q) and `WeilConjectures.CategoryTheory.ExactCouple`
  (`BigradedExactCouple.derived` and `pageCouple`). Their current server source was
  read with `scompile.py --source`, since the older checkout lacks these files.

Edge cases checked before writing: K=0; the empty scheme; identity morphisms; P empty
(which leaves only zero stalk cohomology, since an allowable positive annihilator
must be 1); arbitrary P including nonprime members; n negative or zero; q=n (excluded
from the support vanishing assertion, as required); q=n+1; r=2; and all later pages.
The isomorphisms need no smoothness, properness, finite cohomological dimension,
quasi-compactness, or bounded-above condition. A bounded-below representative may
have acyclic tails; vanishing uses the cohomology single complex, not its raw terms.

Searches performed on 2026-10-17 (full service responses are in sandbox searches.jsonl):

- LeanFinder via msearch: "Cohomology of derived direct image is unchanged in degree n
  by canonical truncation above n, and hypercohomology spectral sequence terms vanish
  for q greater than total degree n". Eight results, including smart truncation
  quasi-isomorphisms and `DerivedCategory.isZero_of_isGE`; no whole-statement match.
- Loogle via msearch: `rightDerivedFunctor, truncLEι`. Zero hits; the index reports
  unknown identifier `rightDerivedFunctor`.
- Mathlib grep via msearch:
  `truncLE.*rightDerived|rightDerived.*truncLE|boundedBelow_truncation`. No hits.
- LeanSearch via msearch: "Cohomology of derived direct image unchanged by truncation
  above n". Eight results on smart truncations and the abstract t-structure; no match.
- `rg` in upstream `WeilConjectures` for the same grep expression, and `grep -rn`
  for the item id, found three truncation-map lemmas in
  `SixFunctors/Etale/SmoothBaseChange/Derived.lean` and the generic D+ truncation
  criterion in `CategoryTheory/DerivedCategory/PlusDevissage.lean`. Their full
  signatures and docstrings were read. The étale lemmas use module-sheaf coefficients,
  and none states the spectral-sequence support clause; they do not give an exact
  existing declaration for this abelian-sheaf statement.
- `rg` in `lean/Sheaf` finds the withdrawn file for this very node and general tools
  in RightDerivedFunctorTruncationIso and LeftExactUpperTruncationComparison, not
  another declaration of this full statement. `dag/lean_names_upstream.json` has no
  `boundedBelow_truncation_criterion` declaration.

No `STATEMENT-DISPUTED` issue remains. All changes are in the sandbox.

## Dependency modules

`def-weil-pbc-hypercohomology-filtrations`: lean-only interface repair in its owning
module `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`. The source already
contains the intended real construction, but the published compiled declaration
has type `{B} → [Category B] → [Abelian B] → BigradedExactCouple B 0`, as checked by
the compiler. It has neither F nor K, and both positional and named applications
fail. Recompiling this dependency source alongside the item resolves the failure;
compiling the item alone reproduces it. The delivery makes F, its shift and
triangulated structures, and K explicit binders of `hypercohomologyCouple` and
rebuilds the owning module. No canonical map, spectral sequence, or filtration
is replaced by an arbitrary object. The dependency node changes only its `lean`
record, with the required diagnostic `note`.

The dependency module retains its complete statement, with real data: D and E
are cohomology of images of the truncation and cohomology complexes; alpha, g and
boundary are the actual truncation-triangle maps; `hypercohomology_maps_exact`
states their exactness; `hypercohomologyCouple` bundles those data; and
`hypercohomologyFiltration` is the image filtration of the actual abutment maps.
`hypercohomologyFiltrations_spec` retains every hypothesis (chosen square, bounded
below representative and its iso to L, torsion cohomology, lower cohomology bound a,
and vanishing representative terms below a) and all clauses: finite filtrations,
vanishing pages in the specified half-plane, convergence and normalized colimit
and filtration identifications for each of the three functors; all three bridge
map equations; the three E₂ identifications; exact inverse image preserving
representative bounds, truncation inclusions, and cohomology; canonical comparison
of the first and pulled-back couples with all differential squares and page-zero
normalization; and the canonical abutment and filtration comparison. Every
postponed theorem retains its source, blueprint id and complete proof docstring.
The inherited local proof imports are preserved. No new axiom, definition with
`sorry` data, or unrecorded postponed theorem is introduced.

## Second reading by Q37

I read the node `sbc-lem-bounded-below-truncation-criterion`, its blueprint source
place (order 1439), the Stacks truncation triangle in `derived.tex`
(`remark-truncation-distinguished-triangle`), and the bounded-below spectral-sequence
context in `sites-cohomology.tex`. I also opened every recorded statement dependency
and both delivered modules.

The node's objects and hypotheses match the Lean as follows.

- The schemes and maps are `{Y T X S : Scheme.{u}}`, `g : T ⟶ S`, `f : X ⟶ S`,
  `e : Y ⟶ T`, and `h : Y ⟶ X`. The chosen square argument
  `_sq : ChosenCartesianSquare e h g f` supplies the node's fibre-product square,
  commutativity, chosen pullback identification, and projection equations. Verdict:
  same square notion, with the project's chosen-square convention and no extra
  geometric hypothesis.
- `P : Set ℕ` and `K : AbelianDerivedCategoryPlusTorsionOfPrimes T P` render the
  allowable-prime set and the bounded-below allowable-torsion object of
  `D(T_et)`. The dependency's stalk condition treats nonprime members of `P` as
  irrelevant, as the node does. Verdict: same coefficient object and no added
  torsion, finiteness, properness, or smoothness assumption.
- `n : ℤ` renders the arbitrary integer degree, including zero and negative degrees.
- The canonical map in the first clause is
  `((DerivedCategory.TStructure.t.truncLEι n).app K.obj)`; it is mapped by
  `hypercohomologyFirstFunctor g` and then by
  `DerivedCategory.homologyFunctor _ n`. Verdict: exactly
  `H^n(Rg_* τ≤n K) → H^n(Rg_* K)`.
- The second clause maps the same canonical inclusion by
  `hypercohomologyBaseChangeFunctor g f`, then takes degree `n` homology. Verdict:
  exactly the pullback map `H^n(f⁻¹ Rg_* τ≤n K) → H^n(f⁻¹ Rg_* K)`.
- The third clause maps it by `hypercohomologySecondFunctor h e`. Verdict: exactly
  `H^n(Rh_* e⁻¹ τ≤n K) → H^n(Rh_* e⁻¹ K)`.
- The final clause quantifies over every bounded-below representative
  `L : CochainComplex.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})`
  with `Nonempty (DerivedCategory.Q.obj L.obj ≅ K.obj)`, every `r` and `q`, and
  assumes `2 ≤ r` and `n < q`. It requires `IsZero` at bidegree `(n-q,q)` for
  `hypercohomologyFirstFunctor g`, `hypercohomologyBaseChangeFunctor g f`, and
  `hypercohomologySecondFunctor h e`. Since `page r` is `pageCouple (r-2)`, this
  includes E₂ and every later page. Verdict: this is the node's statement that
  only `H^q(K)` with `q ≤ n` contributes on total degree `n`; no page or functor is
  omitted and no conclusion is weakened.

Edge cases checked: the zero object and zero maps, empty schemes, identity maps,
empty `P` and arbitrary nonprime elements of `P`, `n = 0`, negative `n`, `q = n`
(correctly excluded), `q = n+1`, `r = 2`, and all later pages. The single universe
`u` is the universe used by the recorded Scheme and chosen-square declarations;
there is no additional universe equality or characteristic hypothesis. No
quasi-compactness, separatedness, properness, smoothness, or finite-dimensionality
assumption occurs in the node or Lean.

Searches for an existing complete notion or theorem were repeated with LeanFinder,
Loogle, LeanSearch, `rg` over `lean/Sheaf` and the upstream `WeilConjectures`, and
Mathlib grep for truncation/right-derived/hypercohomology combinations. They found
only truncation ingredients and unrelated module-sheaf lemmas; no declaration of
`boundedBelow_truncation_criterion` or an equivalent abelian-sheaf theorem exists.
The withdrawn same-name file in the shared checkout is the stale pre-sync copy, not
an existing usable declaration.

The one interface mismatch is in dependency
`def-weil-pbc-hypercohomology-filtrations`: the published compiled
`CategoryTheory.hypercohomologyCouple` had only the implicit coefficient category
and could not be applied to a functor and representative (the lead's
`Function expected at hypercohomologyCouple` failure). The delivered dependency
module repairs that interface by making the triangulated functor `F` and complex `K`
explicit, while retaining the actual truncation terms, maps, exactness, and image
filtrations from the dependency node. I found no further mismatch in the target
statement or its dependencies, so the target Lean file was left unchanged.

Validation: `scompile.py Q37 sbc-lem-bounded-below-truncation-criterion` compiled
both sibling files separately with no diagnostics other than permitted `sorry`
declarations; all lines are at most 100 characters and the target node's `lean.statement`
is verbatim the theorem signature.
