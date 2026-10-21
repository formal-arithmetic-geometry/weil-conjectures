## Worker report

The module `Sheaf.Algebra.Homology.LineUnboundedDerivedTensor` states
`SheafOfModules.LineUnbounded.line_unbounded_derived_tensor`. Its sole theorem has
proof `sorry`. All other declarations expose existing constructions and have real data.
No statement correction, new node, or dependency replacement is made.
`comparisonData` is a transparent packaging of the comparison/evaluation conclusion
in an abstract abelian category; the theorem instantiates every parameter with the
actual sheaf category, tensor and evaluation. `normalization` transparently packages
the displayed K-flat comparison equation. Neither predicate assumes the desired
conclusion or supplies unknown data. `scalars` and `coefficientLinear` expose the existing global-section action, and
`tensorAdditive` exposes ordinary tensor additivity; neither changes an action.
The scalar, site and coefficient universes of
all concrete helpers are supplied explicitly to avoid unresolved max constraints.

Hypotheses and clauses, in order:

- `X : Scheme.{t}` and `R : Sheaf (Scheme.ProEt.topology X)
  CommRingCat.{max a (t+1)}` are the scheme and commutative ring sheaf on its actual
  small pro-etale site. Object universe is t+1 and morphism universe t; these are
  never identified. The independent coefficient universe a can be arbitrarily large.
  `EssentiallySmall` expresses the standing site-size convention (a derivable
  smallness witness, not a geometric restriction). `HasDerivedCategory.{w}` is the
  recorded derived-category size choice. `Modules` abbreviates the dependency's
  category, ultimately exactly Mathlib `SheafOfModules`, not a new category.
- `P : Modules X R` with `[P.IsFiniteLocallyFreeOfRank 1]` is precisely local
  isomorphism to R on a covering; the upstream locally-free file proves the
  equivalence with one-element free bases and local unit isomorphisms.
- `dual X R P` is exactly `SheafOfModules.homObj (R := R) P (𝟙_ _)`.
  The site object/Hom universes are absorbed by max a (t+1), so this is the same
  sheaf Hom in the same module universe; no arbitrary dual object is selected.
- The first two conjuncts are `IsFlatOnSite` for P and its dual, the recorded
  exact-tensor definition. The explicit finite-limit and finite-colimit clauses for
  `tensor`, the localization tensor's `tensorRight`, express their exact termwise
  functors. The existing comparison identifies this tensor with `siteSheafTensorRight`
  used in `IsFlatOnSite`.
- `hP` and `hD` assert the recorded `IsKFlatIndependentCoefficients` for the
  degree-zero singles. `hPf` and `hDf` supply their flat terms: the degree-zero
  term is the stated flat line, all other terms are zero. These technical witnesses
  let the representative comparisons name their actual published proof arguments.
- `derived X R P` is exactly the right-fixed published
  `KFlatFixedTensor.derivedTensor R` at `Q(single P)`. It introduces no second derived
  tensor and chooses no new resolutions.
- `F` and `G` name the two fixed derived functors, with explicit equalities
  `hF : F = derived P` and `hG : G = derived (dual P)`. They cannot be arbitrary
  functors. These names avoid repeatedly unfolding localization choices.
- `cP` and `cD` are natural isomorphisms `Q ⋙ derived ≅ C(tensor) ⋙ Q` on ALL
  integer cochain complexes. This is the localization formulation of the functors
  induced by termwise tensor; uniqueness of factorization identifies them with
  Mathlib `tensor.mapDerivedCategory`. The two normalization clauses specify their
  components on resolving complexes as transport by hF/hG, `representativeIso.symm` followed by
  `Q.mapIso collapse`. The latter is exactly the existing degree-zero total-tensor
  collapse `CochainComplex.map₂HomologicalComplexFlipObjSingleIso`.
- The `CommShift ℤ` witnesses, `IsTriangulated` clauses and
  `NatTrans.CommShift` of cP/cD express coherent integer shifts and preservation of
  distinguished triangles including their connecting maps. No cohomology-flatness
  condition is introduced.
- `e : P ⊗ dual P ≅ 𝟙_ _` is uniquely pinned down by its value on every sheafified
  pure tensor: `e(p ⊗ φ) = φ.app (op (Over.mk (𝟙 U.unop))) p`.
  Thus for a basis p with φ(p)=1 its value on `(a • p) ⊗ (b • φ)` is ab.
  The next clause explicitly gives `e.inv a = (a • p) ⊗ φ` whenever φ(p)=1;
  for a locally free line such a pair trivializes it. `pureTensor` is the existing
  tensor-sheafification unit followed by the existing tensor comparison, not a
  freely chosen map or an element of a different tensor object.
- `cancellation` is the canonical composite `tensorRightTensor.symm`, evaluation,
  and the right unitor. `comparisonData` applies it degreewise using Mathlib
  `Functor.mapHomologicalComplexCompIso` and the identity comparison. The natural
  isomorphisms α and β are exactly the images of those degreewise cancellations,
  under cP/cD, as specified by their equations at every `Q K`. The reverse order
  uses the actual symmetry `(β_ (dual P) P) ≪≫ e`. Localization determines their
  components on all derived objects and morphisms.
- The following two equations are the TWO inverse-pair triangle identities with
  unit α.inv and counit β.hom. Hence the very specified maps give inverse
  equivalences, rather than mere abstract equivalence of categories. α and β
  themselves commute with shifts.
- `∀ i : ℤ, Nonempty (derived P ⋙ homologyFunctor _ i ≅
  homologyFunctor _ i ⋙ tensor P)` gives the natural cohomology isomorphism for
  every integer i and arbitrary derived K.
- The four `Functor.Linear Γ(R)` clauses state ordinary and derived tensor
  linearity for P and its dual. The action is the canonical componentwise action
  from `SheafOfModules.homLinear` and Mathlib's induced derived linear structure.
  This exactly covers the universal conditional B-linearity assertion: a sheaf of
  B-algebras specifies B → Γ(R); restrict these scalar actions along that map.
  Conversely B=Γ(R) is one of the allowed B-algebra structures. The evaluations
  are R-module-sheaf morphisms, hence B-linear on sections, and their derived
  counterparts are the displayed images under the linear Q, followed by morphisms
  in its linear category. No unspecified linear structure is assumed.
- All complex binders use `CochainComplex ... ℤ` without any bound. The extra
  K-flat/flat-term hypotheses on K occur ONLY in the normalization on resolving
  representatives, not in the termwise comparison or evaluation clauses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  via `SheafOfModules.KFlatFixedTensor.Modules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and the existing shift/triangulated structures.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `siteDerivedTensorIndependentCoefficients`, through the recorded fixed-factor API.
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`: `ordinaryTensor`,
  `totalTensor`, `derivedTensor`, `representativeIso`, and the proof-plan theorem
  `kFlat_fixed_tensor_triangulated`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: `homObj`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the existing independent-universe monoidal, symmetric, additive tensor instances;
  ultimately `SheafOfModules.monoidalCategory`, `symmetricCategory` and
  `tensorObjIsoSheafification`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`: `tensorClosed`
  is imported for the recorded proof plan. The statement uses its already available
  tensor constraints via the independent-universe tensor dependency; no new closed
  structure is defined or hypothesized.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.CategoryTheory.Triangulated.Functor`: `Functor.IsTriangulated`;
  `Mathlib.Algebra.Homology.BifunctorShift`: existing total tensor and shift comparisons.
- `Mathlib.CategoryTheory.Linear.LinearFunctor`: `Functor.Linear`.
- Proof leaves: `Functor.homologyFunctorIso` in
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`;
  `Functor.mapDerivedCategoryFactors` and its `CommShift`, `IsTriangulated`,
  linearity instances in `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
  `Localization.lift`, `liftNatTrans`, `natTrans_ext` in
  `Mathlib.CategoryTheory.Localization.Predicate`; derived linearity in
  `Mathlib.Algebra.Homology.DerivedCategory.Linear`.
- Existing additional helpers: `IsFiniteLocallyFreeOfRank` in
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`;
  `SheafOfModules.homLinear` in the upstream `Sheaf.HomModule` module;
  degree-zero collapse in `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`.

Edge cases checked mathematically: empty scheme/empty covering members; zero ring
and its zero unit module; P=R; a nontrivial unit change of basis (dual changes by the
inverse unit); negative cohomological degrees and shifts; unbounded complexes in
both directions; coefficients larger than the site's universe. None needs a new
hypothesis, a geometric stalk argument, or nonzero scalars.

Searches (2026-10-21): prescribed msearch LeanFinder query "Tensor by an invertible
sheaf of modules is an exact equivalence on unbounded derived categories computed
termwise" returned eight generic exact-derived/linear/Tor statements, no match.
Loogle `SheafOfModules, DerivedCategory` returned zero hits. Mathlib grep
`invertible.*derived|derived.*invertible|tensor.*mapDerivedCategory|mapDerivedCategory.*tensor`
returned zero hits. Direct rg in WeilConjectures and Sheaf for the same patterns,
`IsInvertible|IsFiniteLocallyFreeOfRank|line.*Tensor`, and the blueprint id found the
existing ordinary notions and narrower signed/coefficient-line results, but no full
statement. `SignedLineTensorEquivalence` is only a signed-power ordinary-tensor
statement; `IntegralLineTensorComparisonRepresentative` is coefficient-specific
and has no general unbounded equivalence/triangles/cohomology assertion. Their
private line evaluations are not a public general-derived theorem. Name checks in
Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json found no collision.

Source read: Stacks sites-cohomology.tex around 06YT/06YU, derived.tex 015F, and the
current blueprint Tate-twist local-freeness proof (3). No statement fault found.

## Second reading by NS

Worker self-check (no second agent was started, as the dispatcher explicitly
forbids it; independent review is performed by the maintainer). Reopened the node
and the finished module and matched every clause above. In particular checked
composition order of α/β, both triangle equations, the reverse evaluation's
symmetry, and that only representative normalization restricts its input to K-flat
complexes. Replaced an initially unnormalized representative comparison with the
published `representativeIso` followed by the canonical degree-zero collapse.
No mathematical statement changed.

## Validation

The prescribed `scompile.py NS lem-pur-line-unbounded-derived-tensor` compiled the
file both as a sandbox module (12.1 seconds) and at its library module name
(11.5 seconds), with no errors or warnings. All source lines have at most 100
columns. The node differs from the live original only in `lean`; its recorded
signature and all 14 declarations were regenerated from the finished source.

The prescribed `deliver2.py NS lem-pur-line-unbounded-derived-tensor --no-push`
returned OK: preflight and per-file compilation passed.
