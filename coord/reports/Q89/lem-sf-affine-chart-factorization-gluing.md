## Worker report

The module `Sheaf.Paper.SfAffineChartFactorizationGluing` states
`AlgebraicGeometry.exists_sf_affine_chart_factorization_gluing`, with `sorry` as its
entire proof. No definition, helper theorem, additional node, dependency repair or
statement correction is introduced. The statement and eight-step proof read are the
current stage-1-reviewed node, including the inverse-image and bounded-constructible
references added in that review. The mathematical source read is the opening and final
paragraphs of main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-rf-shriek-preservation/sk-prop-sf-rf-shriek-preservation.proof.md.

Hypothesis and clause correspondence:

- A field k is `(k : Type u) [Field k]`. Schemes X,Y are `Scheme.{u}` with
  `Over (Spec (.of k))` structures. Each structure map has `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` instances: the source's separated
  finite-type k-schemes, using the recorded definition of finite type.
- The morphism is `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`, with `IsSeparated f`,
  `LocallyOfFiniteType f`, `QuasiCompact f`. The over-instance says the map is a
  morphism of the displayed k-schemes; it imposes no additional geometric property.
- The finite target cover is `n : ℕ`, `V : Fin n → Y.Opens`, with `IsAffineOpen (V i)`
  and `∀ y, ∃ i, y ∈ V i`. The finite source cover over V_i is `N : Fin n → ℕ`,
  `U : (i : Fin n) → Fin (N i) → X.Opens`, with `IsAffineOpen (U i j)`, the
  containment `hUV : U i j ≤ f ⁻¹ᵁ V i` and pointwise covering of that inverse image.
  Thus the source opens are genuinely opens of X, not arbitrary subschemes with
  set-theoretically contained images.
- Relative dimensions are natural numbers `m i j`, so zero is permitted and no
  positivity hypothesis is added. Affine space is the dependency's existing
  `AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme` and its canonical `↘` map.
  `c i j` is a map from `(U i j).toScheme` into that specific scheme.
  `IsClosedImmersion (c i j)` and the equality of its composite with the projection
  to `f.resLE (V i) (U i j) (hUV i j)` give the requested factorization.
- The projection has `SmoothOfRelativeDimension (m i j)` and `IsSeparated`.
  Smoothness is included in Mathlib's smooth-of-relative-dimension notion; its
  implication `SmoothOfRelativeDimension.smooth` was read in Smooth.lean.
- Every V_i, U_ij and affine-space scheme is explicitly separated and finite type
  over k: the next two conjuncts assert `IsSeparated`, `LocallyOfFiniteType` and
  `QuasiCompact` for the corresponding composite structure morphisms. For affine
  space the structure map is projection followed by V_i's inclusion and Y's map.
- Coefficients are `(A : Type (u + 1)) [CommRing A] [Finite A]`; the complex is
  `(K : Etale.DerivedCategoryModule A X)`. This is the universe convention of the
  recorded ordinary small-etale derived category, not pro-etale coefficients.
- Endpoints `r s a b : (Σ i : Fin n, Fin (N i)) → ℤ` are the four finite families.
  For every i,j, `upperStar (ModuleCat A) (U i j).ι` followed by `mapDerivedCategory`
  is exactly termwise inverse image on complexes, descended to the derived category.
  The local assumptions assert constructibility of every homology sheaf, vanishing
  for `q < r ⟨i,j⟩ ∨ s ⟨i,j⟩ < q`, and the recorded `hasTorAmplitudeIn` predicate
  with endpoints `a ⟨i,j⟩`, `b ⟨i,j⟩`. Constructibility outside the interval adds no
  condition: those sheaves are zero, which admits the empty/constant-zero
  stratification. No flat-model hypothesis or constant-sheaf-only Tor test is used.
- The conclusion first asserts `isBoundedConstructible A X K`, with exactly the
  recorded constructibility predicate on all cohomology sheaves.
- Under `Nonempty X`, the existential `rmin smax amin bmax` is constrained by
  `IsLeast (Set.range r)`, `IsGreatest (Set.range s)`, `IsLeast (Set.range a)` and
  `IsGreatest (Set.range b)`. These uniquely characterize the stated minimum and
  maximum endpoints. The same witnesses bound the global cohomology and Tor
  amplitude. Covering ensures the finite sigma type has a member when X does;
  no default value for the minimum of the empty set is used.
- Under `IsEmpty X`, `IsZero K` renders K=0 invariantly in the derived category.
  The universal `∀ r₀ s₀ a₀ b₀ : ℤ` asserts both the cohomological and Tor interval
  clauses for every interval. The bounded-constructible conjunct remains present.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, `AffineSpace.over`;
  coordinates `ULift (Fin m)` are exactly the specialization in mathlib_match.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and `.Separated`: `IsSeparated`
  (only separatedness from the proper-morphism dependency is needed).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`,
  `SmoothOfRelativeDimension.smooth` (the latter is explanatory, not proved here).
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, `DerivedCategory.homologyFunctor`,
  `Etale.DerivedCategory.hasTorAmplitudeIn`.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`;
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  its exactness instances and adjunction; the derived restriction uses
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, `Functor.mapDerivedCategory`.
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Hom.resLE` and open inclusions.

The current published sources of DerivedCategories, IsConstructibleEtaleModuleSheaf
and BoundedConstructibleComplexes were read through `scompile.py --source`, since
those upstream-synced files are absent from the older local checkout. Bounded Tor
amplitude deliberately uses the existing declaration in Coefficients, as the
EtaleTorAmplitude node's lean.note instructs; the latter module only adds the
lower-bounded variant, unused here. The module also imports the recorded, stated
proof-dependency modules for affine-space smoothness, open restriction, module
inverse-image exactness, qcqs affine locality and derived tensor pullback. Mathlib
geometric proof dependencies are available through the public geometric imports.

Edge cases checked against the informal statement and the signature: n=0 (forces
Y and therefore X empty); N i=0 for an empty inverse image; empty source charts on
a nonempty X; X empty with nonempty Y; m=0, including identity factorizations;
the zero coefficient ring; K=0; reversed local endpoints r>s or a>b (allowed, they
force the relevant vanishing, and no ordering hypothesis was added); arbitrary
characteristic and field; arbitrary scheme universe u. All nonempty and empty
cases remain quantified. There is no STATEMENT-DISPUTED issue.

Searches actually run:

1. msearch.py leanfinder: “finite affine open cover finite type morphism closed
   immersion affine space and gluing cohomology Tor amplitude”. Eight hits,
   including AffineSpace's locally-finite-presentation instance and generic
   affine covers; no theorem combining these two assertions.
2. msearch.py loogle: `AlgebraicGeometry.AffineSpace, AlgebraicGeometry.IsClosedImmersion`:
   zero hits.
3. msearch.py grep: `affine.*[Cc]hart|hasTorAmplitudeIn|isBoundedConstructible`,
   AlgebraicGeometry: zero hits in the Mathlib search tool.
4. msearch.py leansearch: “finite affine open covers factor a finite type morphism
   through closed immersion into affine space”. Eight hits: affine covers,
   finite-type affine restrictions and affine closed immersions; no exact match.
5. rg in WeilConjectures and lean/Sheaf for the node id, affine chart names,
   `hasTorAmplitudeIn` and `isBoundedConstructible`: existing Tor and bounded
   constructibility predicates and consumer statements, none stating this node.
6. rg in dag/lean_names_upstream.json, WeilConjectures and lean/Sheaf for the node
   id and chosen full theorem name: no existing binding or duplicate name.
7. Read Mathlib AffineSpace, Restrict, ExactFunctor, and the recorded morphism
   classes directly to check the canonical maps and full signatures.

Validation: scompile.py Q89 lem-sf-affine-chart-factorization-gluing compiled the
sandbox module and library-path module cleanly (1.9 and 2.0 seconds), with no
errors or warnings. All universes and variables are explicitly bound.

## Second reading by Q89

This is the dispatcher's single-worker self-check; the maintainer's independent
reader reviews the delivery separately. I reopened the current node and the final
module and checked every hypothesis and conjunct against the correspondence above.
No source or node statement correction was needed. The stage-1 review's added
inverse-image and bounded-constructible dependencies are present in the copied node
and their actual declarations are used. I checked particularly that the covers are
of Y and of each inverse image (not merely a cover of X), that the factorization
uses the actual restricted map over V_i, and that the intermediate affine spaces
have the stated properties over k. I checked the nonempty branch uses extrema of
all chart endpoints, with no restriction to nonempty charts; and that the empty
branch asserts zero and all intervals without forming extrema. The local Tor
predicate retains its quantifier over every degree-zero module sheaf. The local
constructibility and global bounded-constructible predicates are the same recorded
notion. The only proof is `sorry`; no data are postponed. No mismatch was found in
this second pass and no further edits were needed.
