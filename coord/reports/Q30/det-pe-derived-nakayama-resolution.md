## Worker report

The module `Sheaf.Paper.DerivedNakayamaResolution` states
`AlgebraicGeometry.ProEtale.derived_nakayama_resolution`. Its only postponed theorem
is that declaration; its proof is `sorry`. All nine helper declarations have real data.
There are no new nodes, repaired dependency records, or changes to the natural statement.

The source read was the main-20261015 blueprint's
`sec-proetale-coefficients/sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-resolution.md`
and its `.proof.md`, together with the node's seven expanded proof steps. The module's
proof docstring carries those seven steps and their inputs. The proof-only dependency
modules are imported without `public` in accordance with the stage rule.

Hypotheses and clauses, matched individually:

- The prime is `(l : ℕ) [Fact l.Prime]`. A finite extension is `(E : Type) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. This is the small coefficient
  field convention of the existing condensed continuous-function framework: all finite
  extensions admit such a representative, and the scheme/site universe `u` is arbitrary.
  No embedding into an algebraic closure, extra topology, completeness condition on K,
  or invertibility of l on X is hypothesized. The topology is the existing spectral
  normed-field topology, restricted to the dependency's integer subring.
- The integer ring, its chosen uniformizer and quotient rings are exactly
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, and `coefficientExtensionRing`. No replacement DVR is used.
  The ideal is `(span {π})^n`, equivalent to `span {π^n}`.
- Every scheme is `(X : Scheme.{u})`. `NakayamaModules l E X` expands to
  `CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1})
  (condensedRingObj (nakayamaIntegers l E) X)`. The actual small pro-etale site has object
  universe u+1 and morphism universe u; neither is identified with the other.
- `nakayamaIntegers` and `nakayamaFiniteCoefficients` specialize
  `Profinite.continuousMapRingObj`. The latter uses the actual ideal-quotient topology,
  which is discrete at positive levels. They are not constant sheaves or completed sheaves.
  `nakayamaPointMultiply` and `nakayamaPointReduction` are actual postcomposition maps on
  continuous sections, constructed by `nakayamaCondensedAddMap`.
- The rank-one free module is `𝟙_ (NakayamaModules l E X)`, definitionally `Mod.regular`
  of the pulled-back ring. The equality on `s.hom` identifies s with the actual
  inverse image of multiplication by π. Hence `s ^ n` is multiplication by π^n.
- The existential `(B, q, e)` packages module structures on the actual coefficient
  sheaves: `e n : (B n).X ≅ p_X^*(underline(O_E/π^n))`, and
  `(q n).hom ≫ (e n).hom = p_X^*(reduction)`. These are conclusions of the theorem,
  not extra assumptions. At positive levels q is epi by the following exactness clause.
  Its epimorphism and the displayed equality force the canonical quotient module action:
  after precomposing the action comparison by `R ⊗ q`, the two actions agree by
  R-linearity of q and of the actual pulled-back reduction. Tensor preserves epis.
  Thus e is necessarily the module identification with the pulled-back quotient action;
  arbitrary module structures cannot satisfy the conclusion.
- The restriction `n ≥ 1` is `∀ n : ℕ, 1 ≤ n →`. The assertion
  `∃ w : (s ^ n) ≫ q n = 0, (ShortComplex.mk (s ^ n) (q n) w).ShortExact`
  includes exactness in the middle, injectivity of the first map, and surjectivity of
  the second. This is precisely the sequence with zero endpoints in the node.
- For any unbounded derived K, `nakayamaReductionFunctor l E X (B n)` is tensor on the
  right with `B n[0]`. It is the same `curriedTensor` as the recorded
  `CondensedRing.derivedTensor`, not a second derived tensor structure.
- `nakayamaConeFunctor` is right derived tensor with the actual complex
  `mappingCone ((HomologicalComplex.single _ (.up ℤ) 0).map (s ^ n))`.
  This is `[R --π^n--> R]` in degrees -1 and 0, the fixed two-term tensor/cone model
  specified explicitly by step 5 of the node. `Nonempty (reductionFunctor ≅ coneFunctor)`
  is a natural isomorphism of endofunctors on the entire unbounded derived category,
  including naturality for derived morphisms, rather than separately chosen object isos.
- The statement also supplies natural transformations β and γ giving, for every K,
  a distinguished triangle `K --π^n--> K --> K_n --> K[1]`. This explicitly confirms
  that the model is a cone of the intended scalar endomorphism. `nakayamaDerivedScalar`
  transports the actual rank-one scalar map using the derived right unitor and `uR`.
  The latter is required to have hom equal to `Functor.LaxMonoidal.ε DerivedCategory.Qh`;
  it is the canonical identification `1_D ≅ R[0]`, not an additional hypothesis or
  an unspecified unit comparison. Its inverse is determined by that equation.
- For `1 ≤ m ≤ n` the binders are `∀ m n : ℕ, 1 ≤ m → m ≤ n →`.
  The first coefficient arrow i is uniquely specified by
  `q m ≫ i = (s ^ n) ≫ q (n+m)`: in quotient coordinates it is `[x] ↦ [π^n x]`.
  The second is uniquely specified by `q (n+m) ≫ r = q n`, namely reduction `[y] ↦ [y]`.
  Since q is epi, neither arrow is arbitrary. For every K the `Triangle.mk` uses precisely
  `K ◁ singleFunctor.map i` and `K ◁ singleFunctor.map r` and is in `distTriang`.
  Its vertices are K_m, K_(n+m), K_n. The existential δ supplies its last arrow.
- The particular triangle with m=1 is the instance `m := 1` of that last clause, for
  each positive n. Its middle vertex is B_(n+1), exactly as in the source.

Dependency declarations read and used:

- `def-weil-l-adic-coefficient-extension`: module
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, theorem
  `Padic.finite_coefficientExtensionRing`, importing the original coefficient constructions
  in `Sheaf.NumberTheory.Padics.CoefficientExtension`. All constructions listed above are
  retained, including the chosen uniformizer and its quotient ideal.
- `sk-def-sfb-condensed-ring`: its closed-upstream audit records
  `Profinite.continuousMapRingSheaf`, `continuousMapRingObj`, and
  `continuousMapRingSheafMap` from
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`, and the p-adic
  specializations from its `.EllAdic` module. Read the actual source, including through
  `scompile.py --source` when the older slopmaster2 path was absent. The source specifies
  the ULift to Ab.{u+1}; the helper uses that same ULift and pointwise operations.
- `sk-def-sfb-pulled-back-coefficients`: the published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, and
  `upperStarFromPoint`. Read this exact side-overlay source and
  `coord/pefw-upstream-framework.md`. Its coefficientRing is mapMon of the actual
  strong monoidal inverse image.
- `sk-def-sfb-module-objects`: its closed-upstream audit points to Mathlib's
  `CategoryTheory.ModObj`, `Mod`, `Mod.forget`, and `Mod.regular` in
  `Mathlib.CategoryTheory.Monoidal.Mod`. Their action laws, morphisms, and signatures were
  read; the module uses exactly this category.
- `def-weil-abstract-derived-category`: Mathlib's `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, and `singleFunctor` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. The cone is Mathlib's actual
  `CochainComplex.mappingCone`.
- `def-sfb-derived-tensor-modules`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`,
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor`, with
  `CategoryTheory.Mod.derivedMonoidalCategory` and the K-flat total-left-derived
  identification in `WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`.
  Its full signature is the curried tensor on exactly the module derived category here.
- `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`
  in `Mathlib.AlgebraicGeometry.Sites.Proetale`, read at their definitions.
- `sk-def-sfb-derived-categories`: the recorded
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, was read with its
  additive-functor/abelian-category/resolution parameters. Its note explicitly uses
  `DerivedCategory (Mod ...)` for layer B. No specialized constant-coefficient derived
  category is substituted. The convention interface is imported.

All recorded proof-dependency modules are imported, including the ordinary quotient
perfectness theorem, exact site inverse image, internal/sectionwise module equivalence,
flat and K-flat interfaces, site tensor descent, short-exact-sequence triangles, and
triangulated K-flat tensor. There are no omitted dependency imports.

Edge cases checked before and after writing:

- Positive level n=1 gives the residue coefficient sheaf and the first reduction cone.
- The m=1 and m=n endpoints are included. `m ≤ n` together with `1 ≤ m` supplies `1 ≤ n`.
- Exponent zero has a real quotient definition (the zero ring). Packaging B and q at n=0
  introduces no extra mathematical assumption; the resolution, cone, and triangle
  assertions remain restricted to the positive levels in the node.
- The zero derived object and the empty scheme are allowed. No nonemptiness, boundedness,
  finite-type, characteristic, or completeness assumption occurs.
- Empty profinite S gives the zero group of sections, and all section maps are defined.
- The quotient-power maps have the correct source and target; scalar multiplication on
  B_m alone would be the wrong arrow and is not used.
- The natural cone is a functor, avoiding a nonfunctorial arbitrary cone choice in a
  triangulated category.

Searches, made through the prescribed `msearch.py` wrapper and direct source reads:

- LeanFinder: "For a finite l-adic extension the pulled back condensed integer ring modulo
  uniformizer powers has a two term free resolution and derived reductions are mapping
  cones". Eight hits: BDeRhamPlus, BDeRham, Condensed.profiniteFree,
  Profinite.NobelingProof.succ_exact, Condensed.profiniteSolid, CondensedMod.IsSolid,
  localCohomology.diagram, instCommRingBDeRhamPlus. None states this result.
- LeanSearch: "A quotient of a condensed ring by a nonzero divisor has a two term free
  resolution and derived tensor with that quotient is naturally a mapping cone".
  Eight hits: condensed AB4/AB4Star, RingCon.Quotient/toQuotient, ordinary tensor-quotient
  equivalences, and DerivedCategory.quotientCompQhIso. No matching sheaf theorem.
- Loogle: "mappingCone, ShortComplex" returned zero hits and an unknown-identifier
  diagnostic for mappingCone. This query is inconclusive, not evidence of absence;
  the semantic searches and source inspection settle the match question.
- Mathlib grep via wrapper: `uniformizer|two.term|derivedTensor` in `Condensed` returned
  zero hits.
- Direct rg in upstream `WeilConjectures` and side `lean/Sheaf` for the node id,
  Nakayama/cone/quotient-triangle terms, and each new declaration name. The existing
  `FiniteExtensionReductionConeBound` concerns completed coefficient sheaves and a
  bounded cohomology interval; `DerivedCategory.quotPowTriangle` uses constant coefficient
  sheaves. Neither states the pulled-back condensed theorem. Generic scalar-cone and
  tensor-mapping-cone constructions were read and reused conceptually through their
  existing mappingCone/tensor definitions, without duplicating a tensor structure.

No STATEMENT-DISPUTED issue or source correction was found.

Validation: `scompile.py Q30 det-pe-derived-nakayama-resolution` checked this single module
in both sandbox and library paths, with all final imports. Both passed without errors or
warnings (22.9 s and 18.7 s, each below the unchanged 60 s limit). No global build was run.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
