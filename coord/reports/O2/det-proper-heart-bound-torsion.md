## Worker report

The delivery states `AlgebraicGeometry.ProEtale.properHeartBoundTorsion` in
`Sheaf.Paper.ProperHeartBoundTorsion`. Its only postponed proof is that theorem,
whose docstring contains all eight steps of the DAG proof with their dependencies.
Every helper has real data. No statement correction, new DAG node, or dependency
module was necessary. The resolved stage-1 repair note was read; its instruction
to retain the statement and proof route is respected.

The source is the current main-20261015 blueprint's
`sec-six-functors-basics/sk-lem-proper-heart-bound/sk-lem-proper-heart-bound-torsion.md`,
read in full, together with the node's expanded statement and eight-step proof.
The statement's three parts are a natural isomorphism, a degree-zero classical
constructible quotient, and the bound over an arbitrary affine weakly contractible
pro-etale object. They are the two outer conjuncts and the inner universal clause
of the theorem. Nothing is claimed proved at stage 2.

Hypothesis and clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The finite extension is
  `(E : Type u) [Field E] [Algebra (Padic ℓ) E]
  [FiniteDimensional (Padic ℓ) E]`. These are section variables explicitly bound
  before the declarations. The coefficient ring and chosen uniformizer are the
  recorded `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer`; no second choice is made.
- The positive characteristic field is `(k : Type u) [Field k]` with
  `hchar : ringChar k ≠ 0` and `hell : ringChar k ≠ ℓ`.
  A field has prime characteristic or zero, so this is exactly characteristic
  p > 0 different from ℓ, with no perfectness or algebraic-closure condition.
- `X` and `Y` have their existing `Over (Spec (.of k))` instances. On both
  structure maps the instances `IsSeparated`, `LocallyOfFiniteType` and
  `QuasiCompact` express separated finite type over k. The supplied `p : X ⟶ Y`
  has `[p.IsOver (Spec (.of k))]` and `[IsProper p]`.
- `d : ℕ` is the nonnegative integer bound. `hd` quantifies every `y : Y` and
  bounds `topologicalKrullDim` of the actual scheme pullback along
  `Spec (AlgebraicClosure (Y.residueField y)) → Y` by
  `(d : WithBot ℕ∞)`. This is the scheme-theoretic geometric fibre, rather than
  the set of lifts of a geometric point. It follows the recorded
  `def-pc-base-change` convention, using its chosen pullback expression.
- `V : Y.ProEt` supplies its scheme `V.left`, map `V.hom : V.left ⟶ Y`, and
  weakly etale structure. `[IsAffine V.left]` and
  `hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V` are exactly
  affineness and categorical weak contractibility. In particular no
  Noetherian or ring-theoretic contractibility hypothesis is imposed on V.
  The actual base change is `pullback p V.hom`, with projection to V given by
  `pullback.snd` and the map r to X by `pullback.fst p V.hom`.
- The factorization is `(j : S ⟶ Sbar) [IsOpenImmersion j]` and
  `(i : Sbar ⟶ X) [IsClosedImmersion i]`; j is the source's u, and
  a is their composite `j ≫ i`. Eliminating the redundant name a and its
  equality with this composite excludes no locally closed immersion.
  `torsionLocallyClosedExtension` is precisely the recorded module-object
  `openImmersionLowerShriek` followed by `lowerStar`: i_* j_!.
  S and Sbar acquire their k-structures through these arrows. They are not
  given additional standing hypotheses; the needed finiteness follows from
  the immersion into Noetherian X.
- The integral sheaf category is `pulledBackModuleObjects
  (DerivedNakayama.integerRing ℓ E) S`, which uses the existing
  `coefficientRing`/`condensedRingObj`: p_S^* of the continuous condensed
  valuation ring, not the constant discrete ring of integers.
- Lisse finite free means exactly the existing `IsLisseCoefficientModule`.
  The theorem uses its full subcategory and inclusion `ObjectProperty.ι`.
  That predicate allows ranks to vary on a pro-etale cover and includes zero.
  Its recently landed definition node `def-sfb-lisse-coefficient-module`
  is the only added statement dependency; no node or predicate is copied.
- `(n : ℕ) (hn : 1 ≤ n)` is exactly the positive level. The actual finite
  scalar ring is `Padic.coefficientExtensionRing ℓ E n`, lifted to the sheaf
  value universe by `ULift.{u+1,u}`. Its `Finite` proof is supplied by the
  existing `Padic.finite_coefficientExtensionRing` inside the origin predicate,
  not assumed as an extra input. The quotient map is `Ideal.Quotient.mk` of
  the recorded `Padic.coefficientExtensionIdeal`.
- `torsionQuotient ℓ E S n` is ordinary relative tensor with the recorded
  pulled-back `DerivedNakayama.quotientModule`. This is L/pi^n L: for any
  module, tensor with R/(pi^n) is its canonical cokernel quotient. This
  construction uses the actual relative module tensor, not an arbitrary
  sheaf annihilated by pi^n and not a quotient defined as H^0 of the result
  to be proved. The existing `DerivedNakayama.reductionFunctor` is the
  corresponding K-flat derived relative tensor on the ambient derived
  category, with this same coefficient object in degree zero.
- The first conjunct is `Nonempty` of a **natural isomorphism of functors**
  on the full category of lisse integral modules, from
  L ↦ derived reduction of (i_* j_! L)[0] to
  L ↦ (i_* j_! (L/pi^n L))[0]. This retains naturality in all morphisms of
  lisse modules; it is not only an objectwise collection of isomorphisms.
  `DerivedCategory.singleFunctor _ 0` expressly puts the right side in degree zero.
- The second conjunct quantifies each lisse module L. Its first assertion
  `TorsionClassicalOrigin` chooses a fixed finite-coefficient module sheaf G
  and an additive-sheaf isomorphism e from G to the actual ordinary quotient
  extension. It **also** requires, for every b in O_E, the equation
  `e.hom ≫ torsionScalar N b = forget.map (torsionFixedScalar G [b]) ≫ e.hom`.
  Thus the isomorphism respects the coefficient action through the actual
  quotient map. The pulled-back finite quotient ring is locally generated
  by these constant scalars: its finite discreteness means every scalar
  section is locally constant, and O_E surjects onto A_n. Therefore these
  equations express A_n-linearity of e, including for arbitrary local scalar
  sections. The existing integral action on this tensor quotient already
  factors through that ring, so no new module action is chosen.
- `torsionIntegerMultiply` constructs multiplication on the continuous
  condensed coefficient sheaf sectionwise. `torsionScalar` pulls it back,
  composes it with the unit and the actual internal action. These are real
  canonical maps; no arbitrary scalar endomorphism is a hypothesis.
  `torsionFixedScalar` is the existing fixed-module action b times the identity
  on every section; its naturality is part of the concrete map construction.
- The remaining origin clause chooses F on `X.smallEtaleTopology`, requires
  the exact recorded `Scheme.IsConstructibleEtaleModuleSheaf F`, and requires
  an isomorphism `comparisonUpperStar (ModuleCat (ULift A_n)) X |>.obj F ≅ G`
  **in the category of A_n-module sheaves**. This is the inverse image in the
  recorded `proEtaleSiteComparisonModules` adjunction. In particular an
  arbitrary underlying-set or abelian origin is not substituted for module
  constructibility.
- The last clause quantifies `q : ℤ` with `(2*d : ℤ) < q` and states `IsZero`
  of homology q of the existing `rightDerivedGlobalSections Ab` applied to
  the degree-zero canonical inverse image of the quotient extension's
  underlying abelian sheaf along r. This is exactly pro-etale H^q(X_V,r^*...)
  as an abelian group, using the recorded `proEtaleSheafInverseImage` with
  abelian values. Exact forgetting of finite module structures identifies it
  with finite constant-coefficient inverse image. There is no cohomology
  definition or separate comparison map chosen in this module.

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the imported coefficient ring,
  ideal and uniformizer constructions in `CoefficientExtension`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the recorded standing scheme/compactification convention; the theorem uses
  its separated finite-type k-scheme hypotheses explicitly.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the pullback
  and geometric-fibre conventions, with the published source read using
  `scompile.py --source` because that module is absent in the older local clone.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`:
  `GrothendieckTopology.IsWeaklyContractible`, published source read using
  `scompile.py --source`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.SixFunctors.IntTensorProjection`:
  `CondensedRing.locallyClosedImmersionTensorProjection`, proof input.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`.
- `Sheaf.Paper.ModuleObjects`: `pulledBackModuleObjects`, built from `Mod`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  the recorded relative derived tensor/Hom convention; its Tensor import is
  the actual `CondensedRing.derivedTensor` used by reductionFunctor.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules` and its specified left adjoint
  `ProEtale.comparisonUpperStar`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf` (finite values on a constructible
  locally closed partition).
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage`, the specified Kan/sheafification functor.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`:
  `ProEtale.rightDerivedGlobalSections`, found through the closed upstream
  audit for `def-sfb-finite-derived-global-sections` whose lean record lacks
  module/declaration fields. Published full source read by `scompile.py --source`.
- `Sheaf.Paper.CoefficientHeartCommonStratification`:
  `IsLisseCoefficientModule`, bound by `def-sfb-lisse-coefficient-module`.
- `Sheaf.Paper.DerivedNakayamaResolution`: `integerRing`, `quotientModule`,
  `pullback`, `reductionFunctor`, and the coefficient exactness/cone theorem.
  These already recorded helpers are used directly rather than redefined.

All recorded proof-dependency modules are imported, with proof-only imports
non-public. Mathlib leaves contribute their existing modules (Noetherian,
Separated, QuasiCompact, Pullbacks, PullbackCarrier and Constructible). No
new or repaired prerequisite is needed. The full proof route remains in the docstring.

Edge cases checked before formulation: empty X, empty S, empty V, empty
geometric fibres (dimension bottom), d = 0, n = 1, zero lisse module, rank-zero
local models, varying local ranks and disconnected covers. No nonempty or
constant-rank assumption appears. The cohomological boundary is strictly
q > 2d, not q ≥ 2d. Positive n is retained; n = 0 is not introduced. V may
be non-Noetherian. Nonreduced X and immersed strata are permitted. Schemes
have arbitrary universe u, their small sites have object universe u+1 and
morphism universe u, and additive/fixed-module values are in u+1; no equality
between site object and morphism universes is imposed. Field E is allowed in
the scheme universe, with its valuation topology supplied by the recorded
spectral absolute value, as in the existing resolution module.

Searches (msearch.py, group N2, item det-proper-heart-bound-torsion):

- LeanFinder: `lisse lattice derived reduction finite coefficient proper cohomology
  bound weakly contractible base` — eight unrelated hits, including
  `Condensed.finFree`, the Nobeling exactness theorem, affine-limit section
  vanishing and singular homology; none states the node.
- Loogle: `AlgebraicGeometry.IsProper, topologicalKrullDim` — zero hits.
- Mathlib grep: `proper.*torsion|heart.*bound|lisse` in `AlgebraicGeometry` —
  zero hits.
- LeanSearch: `proper torsion proetale cohomology vanishes above twice geometric
  fibre dimension weakly contractible base` — eight hits, including proper
  base-change stability, smallEtaleTopology and unrelated algebraic H1
  vanishing; none states the node.
- Ripgrep in upstream WeilConjectures and project Sheaf searched
  `properHeart|proper_heart|torsion.*bound|Lisse|lisse|finiteFree|FiniteFree`.
  The hits include rational proper-heart bounds and coefficient local models,
  but not this combined torsion theorem. Searching the exact node id in
  upstream found no declaration. A focused search for
  `lisseFiniteFree|LisseFiniteFree|lisse finite free|lisse finite-free` found
  the rational-bound docstring; searching actual predicate names found the
  existing `IsLisseCoefficientModule` and its landed definition node, reused.
- Exact proposed declaration-name grep in `dag/lean_names_upstream.json`,
  project Sheaf and upstream WeilConjectures found no conflicts; the only
  substring hit was an unrelated scheme torsionQuotient theorem in another
  namespace.

Validation: `scompile.py N2 det-proper-heart-bound-torsion` compiled the module
cleanly both in the private sandbox and at its library module path. The first
pass diagnosed an alias-hidden monoidal instance, reversed naturality equation
and an invalid adjunction field; these were repaired using the existing full
`Mod` type, the correctly oriented scalar linearity identity, and the actual
recorded left-adjoint functor. Subsequent full-file compilation with all
proof imports passed in about four seconds for each checked path. All variables
and universes are explicitly bound; there are no file-local instances, notation,
private definitions, axioms, or structural data placeholders. The only sorry is
the named theorem, with the matching DAG node and complete proof docstring.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
