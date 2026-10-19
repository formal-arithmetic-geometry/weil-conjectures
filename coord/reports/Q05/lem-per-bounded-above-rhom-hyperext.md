## Worker report

The delivery states `CategoryTheory.exists_boundedAbove_rhom_hyperExt` in
`Sheaf.Algebra.Homology.BoundedAboveRHomHyperExt`, with its only theorem proof `sorry`.
The two real-data transparent helper abbreviations are `ringedSiteRHomCohomology`
(the functor T^n = H^n RHom(K,-)) and `ringedSiteHyperExt` (T^p after the degree-zero
single functor). These are the formulas introduced in this item's own statement, not
new independent notions or copies of derived Hom. Each has the owning node's source
and blueprint docstring. The theorem docstring includes all nine proof steps of the node.

The shared node now has the reviewed Q88 stage-1 split and no Lean record; the prior
worker's split/dispatch conflict does not apply to this stage-2 statement task. No
stage-1 fields, source statements, dependency records, proof plans or citers changed.
Only this item's `lean` field is changed.

Clause-by-clause correspondence:

- Small ringed site and size convention: `{C : Type uC} [Category.{vC} C]`,
  `J : GrothendieckTopology C`, `R : Sheaf J CommRingCat.{max uC vC u}`.
  The sheafification and locally-bijective instances in that coefficient universe
  are exactly the recorded generic derived-Hom interface's size prerequisites;
  they hold for small sites relative to the coefficients. No equality between site
  object and morphism universes is imposed. `HasDerivedCategory.{w}` chooses the
  ambient universe for derived morphisms. All four universe levels are explicit.
- Mod(O) and D(O): `ringedSiteModules.{max uC vC u}` of the ring sheaf obtained by
  forgetting commutativity, and Mathlib `DerivedCategory` of that same category.
  `ringedSiteModules` is the recorded transparent abbreviation of `SheafOfModules`.
  The abelian structure is Mathlib's; no structure is chosen or reconstructed.
- K and the bound H^j(K)=0 for j>r: `K : DerivedCategory (...)`, `r : ℤ`,
  `_hK : K.IsLE r`. Mathlib `DerivedCategory.isLE_iff` identifies this exactly
  with the node's vanishing, for all integers above r.
- L and H^j(L)=0 for j<c: the functor's domain is
  `ObjectProperty.FullSubcategory (fun L : DerivedCategory (...) ↦ L.IsGE c)`.
  An object L contains both the derived object `L.obj` and precisely this bound.
  `DerivedCategory.isGE_iff` gives the stated cohomology vanishing. This domain
  includes every eligible L and every derived morphism between them.
- Sheaf Ext for all integer p: `ringedSiteHyperExt J R K p` is
  `DerivedCategory.singleFunctor _ 0 ⋙ ringedSiteRHomCohomology J R K p`.
  It is an actual functor, using the recorded derived internal Hom construction
  and Mathlib cohomology, with no independent variable for its values or maps.
- Spectral sequence of module sheaves and differential bidegree (s,1-s):
  `E : (...) ⥤ E₂CohomologicalSpectralSequence (...)` uses Mathlib's
  `SpectralSequence`, with `ComplexShape.up' (s,1-s)`, starting at page 2.
  Its own `iso` field enforces page cohomology = next page.
- E2^{p,q} = Ext^p(K,H^q L): `e2 L p q` is an isomorphism from
  `((E.obj L).page 2).X (p,q)` to the explicit sheaf Ext value on
  `(DerivedCategory.homologyFunctor _ q).obj L.obj`.
  The square with `((E.map f).hom 2).f (p,q)` identifies its morphism map with
  Ext applied to H^q(f), not merely an arbitrary isomorphism of objects.
- Naturality in L: E is a functor into the category of spectral sequences,
  so maps commute with differentials and page-cohomology identifications and
  obey identities/composition. The E2 square, the equation
  `(a n f).hom = (ringedSiteRHomCohomology ... n).map f.hom`, and the conv square
  express naturality of the E2, abutment, filtration and graded identifications.
  Each `a n f : FilteredObject.HomPreservingSteps ...` is exactly a restriction
  of that actual abutment map to every filtration step. Such restrictions are
  unique through the monic target inclusions; identity/composition follow.
- Additivity: the equality for `E.map (f+g)` is componentwise on every page,
  so it expresses addition in spectral-sequence morphisms without introducing
  a separate preadditive instance on the spectral-sequence category. Further
  equalities for `FilteredObject.restrictionSteps` and `gradedMapSteps`
  enforce addition on filtration steps and graded maps. Their inclusion and
  quotient squares, and the whole-object filtration step, also give addition
  on the underlying abutment map. Zero maps follow by cancellation.
- Support p>=-r and q>=c: every page s>=2 satisfies
  `p < -r ∨ q < c → IsZero (((E.obj L).page s hs).X (p,q))`.
  This includes the initial page, and later-page support is the same subquotient
  consequence stated in the node's proof.
- Finite exhaustive separated abutment: `F L n` is a `DecreasingFiltration`
  on the actual T^n(L), with `IsFinite`, `IsExhaustive`, and `IsSeparated`.
  It also has `(F L n).F (-r) = ⊤` and its step n-c+1 is `IsZero` as an
  object of the SAME module category. For a subobject in an abelian category,
  this is exactly equality with the bottom subobject. Using `IsZero` avoids
  an unconstrained-category metavariable in the bottom notation; it changes
  no mathematical condition.
- Graded pieces E_inf^{p,n-p}: `conv L s hs p q hst` identifies every page
  beyond `max (q-c+1) (p+r)` with `(F L (p+q)).gr p`. This explicit stable
  page description is equivalent to E_infinity because both incoming and
  outgoing differential vanish there by the support bounds. The first
  conjunction equates `iCycles ≫ conv_s` with `homologyπ ≫ E.iso ≫ conv_(s+1)`;
  thus the isomorphisms agree with the canonical page-to-next-page comparison.
  The conv morphism square identifies stable-page maps with the canonical
  `gradedMapSteps`, so convergence is natural as well as objectwise.
  This is finite convergence in the sense of def-sp-convergence; no infinite
  lattice choices are needed. A finite separated filtration is complete too.
  The recorded `BigradedExactCouple.ConvergesTo` concerns the additional exact
  couple presentation, while the node's conclusion is a spectral sequence
  with a finite filtered abutment. The statement uses its finite equivalent
  rather than assuming an additional exact couple as input. Its recorded
  module is imported and used as the proof-plan convergence interface.
- Only c<=q<=n+r in total degree n: the explicit final support assertion
  has `p+q=n` and nonzero E2 imply `c ≤ q ∧ q ≤ n+r`; all later pages obey
  the same bounds by the all-page support assertion. This finite interval
  covers negative bounds as well as the usual first quadrant.
- RHom(K,L) has no cohomology below c-r: the last conjunct explicitly says
  `n < c-r → IsZero ((ringedSiteRHomCohomology ... n).obj L.obj)`.
- No constructibility, finite Tor amplitude or cohomological dimension:
  none appears in any binder. The targets L have no upper bound, and K has
  no lower bound.

Dependency declarations read and used:

- def-weil-size-convention: metatheoretic convention, encoded by the four
  universe binders and `HasDerivedCategory.{w}`; there is no Lean object.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  full abbreviation signature and docstring read from the shared library.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.singleFunctor`; and
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor`: source signatures and docstrings read.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`,
  `DerivedCategory.TStructure.t`, `IsLE`, `IsGE`, `isLE_iff`, `isGE_iff`:
  source signatures and docstrings read, including arbitrary integer bounds.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses`: full generic signature,
  localization construction, replacement and representative comparisons read.
  The helper uses this recorded primary declaration, not a private copy or
  the specialized ordinary-etale derivedHom.
- `Mathlib.Algebra.Homology.SpectralSequence.Basic`,
  `CategoryTheory.SpectralSequence`, `SpectralSequence.Hom`,
  `E₂CohomologicalSpectralSequence`: full structures read in pinned Mathlib.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`,
  `CategoryTheory.DecreasingFiltration`, `.F`, `.gr`: fetched current source
  with `scompile.py --source` because the older source checkout lacks it.
  It is publicly imported by the compatibility modules. The existing
  `Sheaf.CategoryTheory.Filtration` supplies its finite/exhaustive/separated
  vocabulary, and `Sheaf.CategoryTheory.FiniteFiltrationInduction` supplies
  `FilteredObject.HomPreservingSteps`, `restrictionSteps`, `gradedMapSteps`.
  Their full source was read. No second filtration is defined here.
- `WeilConjectures.CategoryTheory.ExactCoupleConvergence`,
  `CategoryTheory.BigradedExactCouple.ConvergesTo`: current source fetched
  using `scompile.py --source`, including regularity, abutting, inverse-limit
  definitions. This API's own PBC filtration presentation is only a proof
  interface; it is never confused with the recorded DecreasingFiltration.

Proof dependencies whose statements exist are imported privately, as the plan
for stage 3: RhomIntoKInjectiveLocal; DerivedInternalHomShiftRight;
LocalizedModuleExactForSystems; ExactCoupleMorphism; upstream DerivedCoupleExact,
TruncationTriangle and HalfPlaneConvergence; Mathlib TruncLEGT and exact module
sheafification. Representable triangle exactness is already a transitive public
Mathlib import through DerivedCategory, so no extra redundant import is needed.
The theorem docstring gives the reindexing P=p+r and abutment transport explicitly.

Edge cases checked before writing:

- K=0 or L=0: E2, all pages and the actual abutment are zero; top=bottom for
  the zero object's subobjects, so finite filtration conditions are consistent.
- Empty site and zero coefficient ring: zero module category is allowed, with
  no nonempty or nontrivial hypothesis.
- n+r<c: the support interval is empty, n<c-r, so the abutment is zero and
  the overlapping top/zero filtration bounds are consistent.
- r,c,p,q,n may be negative. In particular positive shifts of a degree-zero
  module allow negative sheaf Ext degrees; p is an integer, not a natural.
- Boundary n=c-r has exactly q=c and p=-r, with one potentially nonzero
  graded piece. No unjustified vanishing is imposed at that boundary.
- K may be unbounded to the left, and L unbounded to the right. The only
  finiteness is on individual total-degree diagonals, not the whole sequence.
- Independent object, morphism, coefficient and derived-morphism universes
  compile; no site-universe equality is imposed to fit a specialized API.
- Identity, composite, sum and zero target maps are represented. Uniqueness of
  monic step restrictions ensures compatibility with the actual abutment map.

Searches for an existing statement (2026-10-18 UTC):

- msearch.py / LeanFinder: "Hyper Ext spectral sequence for internal Hom from
  a bounded above complex to a bounded below complex": 8 hits, led by
  HasExt small-localized-Hom bounds, Ext and fractions. No matching spectral
  sequence with finite natural filtered abutment.
- msearch.py / Loogle: `"SpectralSequence", "DerivedCategory"`: 0 hits.
- msearch.py / grep: `spectralSequence|HyperExt|hyperExt`, Algebra/Homology:
  25 infrastructure hits in Mathlib spectral sequence/complex-shape modules.
- msearch.py / LeanSearch: "spectral sequence Ext of cohomology sheaves
  converging to cohomology of derived internal Hom": 8 hits, Ext and sheaf
  cohomology declarations, no matching theorem. The raw results are preserved
  by the launcher in the sandbox searches.jsonl.
- rg on upstream WeilConjectures and shared lean/Sheaf for the item id,
  `hyperExt|HyperExt|hyper.?Ext|bounded.*[Rr][Hh]om`: no existing theorem.
  The parent's `ConstructibleRHomCoproductContinuity` mentions the item in its
  proof only. Bounded-free RHom models and coherent/global Ext spectral
  sequences have different hypotheses or conclusions.
- rg on Mathlib, upstream WeilConjectures and shared lean/Sheaf for the three
  proposed declaration names: no hits. Read upstream SpectralSequence.Basic's
  natural-index abutment interface: it is first-quadrant only and does not
  encode these arbitrary lower bounds and target-morphism squares.

Validation: scompile.py compiled both sandbox and actual module namespaces
cleanly with independent universes (6.7 s / 6.4 s, no warnings). An earlier
experiment used a common site universe; it was generalized before delivery.
The only `sorry` is the theorem required by the item. No new nodes, dependency
repairs or statement corrections were required. No STATEMENT-DISPUTED issue.

The worker does not fabricate an independent second reading. The current
launcher delivers directly and the maintainer performs its independent review.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
