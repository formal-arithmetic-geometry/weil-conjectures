## Worker report

The module `Sheaf.Paper.ConstructibleRHomCoproductContinuity` states
`AlgebraicGeometry.Etale.isIso_sigmaComparison_derivedHom_of_constructible`, with its
sole proof `sorry`. It introduces no definitions or additional theorem assumptions.
The node statement is unchanged. Its `stmt_deps` gains the already recorded
`def-constructible-finite-locally-constant`, whose exact predicate is used below.

Hypothesis and conclusion correspondence:

- A commutative Noetherian coefficient ring is `(A : Type (u + 1)) [CommRing A]
  [IsNoetherianRing A]`. This allows infinite coefficient rings, fields of any
  characteristic, the zero ring, and singular rings with infinite global dimension.
- A Noetherian scheme is `(X : Scheme.{u}) [IsNoetherian X]`. Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` identifies this with the specified
  finite cover by affine schemes whose coordinate rings are Noetherian.
- The ordinary unbounded derived category is `DerivedCategoryModule A X`, literally
  `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))`. A sheaf of
  ordinary A-modules is the fixed-coefficient presentation of an A_X-module sheaf.
  Neither completion, a constructible full subcategory, nor a pro-etale category
  replaces this ambient category.
- The upper cohomology bound on K is `_hK : ∃ r : ℤ, K.IsLE r`. The standard
  derived t-structure identifies this with H^j(K)=0 for j>r.
- For each j the hypothesis `_hc` gives `S : Scheme.FiniteLocallyClosedStratification X`.
  The recorded structure contains a finite disjoint locally closed partition covering
  X and immersions realizing its strata. The quantifier is inside `∀ j : ℤ`, so the
  partition may depend on j; no single stratification for all degrees is assumed.
- The pullback of H^j(K) to every stratum is
  `(upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj
  ((DerivedCategory.homologyFunctor _ j).obj K)`. Its
  `Scheme.IsFiniteLocallyConstantSheaf` hypothesis extends both
  `IsLocallyConstantSheaf` (etale local constancy as a module sheaf) and
  `IsFiniteSheaf` (finitely generated geometric stalks). The latter uses
  `ConcreteCategory.IsFinitelyGenerated`, which is `Module.Finite A` for ModuleCat,
  as its source docstring explains. This is finite generation, not finite underlying
  cardinality over an arbitrary A. The generic recorded
  `SheafOfModules.IsLocallyConstantFiniteTypeModules` is imported, but its equal
  site-universe SheafOfModules presentation is not imposed on the mixed-universe
  small etale site or substituted for the existing etale stalk predicate.
- `I : Type (u + 1)` is any set in the coefficient universe. There is no
  nonemptiness, finiteness or countability hypothesis.
- `L : I → DerivedCategoryModule A X` and `_hL : ∃ c : ℤ, ∀ i : I, (L i).IsGE c`
  give exactly the common lower bound. No upper bound, finite generation,
  constructibility or Tor hypothesis is present on L. There is no finite Tor
  amplitude condition on K and no uniform upper bound on the Hom objects.
- The conclusion asserts `IsIso` of Mathlib's actual `sigmaComparison` for
  `((derivedHom (ModuleCat.{u + 1} A) X).obj (op K))` and L. Its source is the
  coproduct of the individual RHom objects, its target is RHom of the coproduct,
  and its definition is `Sigma.desc (fun i ↦ F.map (Sigma.ι L i))`.
- There is no global `HasCoproducts` instance for this derived category. The
  conclusion therefore packages `∃ hcoprod : HasCoproducts.{u + 1} ...` and uses
  its two `HasColimitsOfShape.has_colimit` projections explicitly in
  `sigmaComparison`. This supplies existing coproducts, not an added hypothesis
  or a choice of an arbitrary morphism. `HasCoproducts` and `HasColimit` are
  propositions, so proof irrelevance makes this independent of the witness.
  `lem-kun-grothendieck-derived-coproducts` computes precisely these ordinary
  derived coproducts by sums of representatives. The packaging neither restricts
  the families nor asks for an additional mathematical property.

Dependency declarations and source inspection:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, all ideals finitely generated.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, through imports.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded derived-category
  module, read through `scompile.py --source`; its public coefficient module supplies
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, whose full abbreviation was read.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  sheafification of the constant presheaf, underlying the fixed-coefficient presentation.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, used directly, including empty partitions.
- `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`:
  `SheafOfModules.IsLocallyConstantFiniteTypeModules`, recorded generic definition.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, finite generation predicate.
- `WeilConjectures.ConstructibleSheaf.Defs`:
  `Scheme.IsFiniteLocallyConstantSheaf` with its two parent classes, added as an
  already recorded statement dependency. All three signatures and docstrings were read.
- `def-weil-size-convention` has no declaration: explicit universe u for schemes,
  u+1 for coefficients, module stalks and index sets implements its convention.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the recorded module
  publicly exposes the original `AlgebraicGeometry.Etale.derivedHom` and
  `derivedTensorHomAdjunction`; the original Hom module's full signature and
  monoidal-closed/internal-Hom construction were read, and the former is used directly.
- Proof-only imports: `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
  (`DerivedCategory.isColimit_mapCocone_grothendieckSum`, source fetched through
  `scompile.py --source`); `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
  (`SheafOfModules.grothendieckAbelian_with_localized_generator`, also fetched);
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` (`CochainComplex.IsKInjective`);
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` (`DerivedCategory.isIso_iff`).
  The category-colimit node's Mathlib module is already public through Products.
  The two proof nodes `lem-per-bounded-above-rhom-hyperext` and
  `lem-per-constructible-ext-filtered-colimit` have no recorded module yet, so
  their modules cannot be imported; their complete intended uses remain in the docstring.

Edge cases checked mathematically against the signature: I empty gives the zero-to-zero
map; K=0 gives zero-to-zero; all L_i=0 do likewise. X empty permits the empty
stratification (and all stalk conditions are vacuous as appropriate). Arbitrary integer
bounds and shifts are allowed, without an ordering between r and c. K may be unbounded
below and L_i unbounded above. The common c is quantified before i, and may be arbitrary
for the empty family. Finite stalks mean finitely generated modules, including A itself
when A is infinite. No characteristic or torsion constraint is introduced.

Searches (all for this group and item):

- `msearch.py leanfinder`: "Derived internal Hom from a bounded above constructible
  complex on a noetherian scheme etale site commutes with coproducts of uniformly
  bounded below complexes". Eight results: derived fraction lemmas, Sheaf.H,
  derived t-structure bounds and condensed internal projectivity; no exact match.
- `msearch.py leansearch`: "Derived sheaf internal Hom with a constructible bounded
  above first argument preserves coproducts of uniformly bounded below complexes".
  Eight results: ordinary sheafHom, finite colimit preservation and Ext/derived
  infrastructure; none is this constructible-etale continuity theorem.
- `msearch.py loogle`: "AlgebraicGeometry.Etale.derivedHom, PreservesColimit,
  CategoryTheory.coproductComparison". No hits; derivedHom is a project declaration
  unknown to the Mathlib service. Local source inspection found the project declaration.
- `msearch.py grep`: "coproductComparison|RHom|derivedHom", CategoryTheory. Twenty-five
  infrastructure hits, no assertion of this theorem. Direct Mathlib rg found the
  exact map `CategoryTheory.Limits.sigmaComparison` in Products.lean:668.
- `rg` in upstream WeilConjectures and side lean/Sheaf for constructible/coproduct
  and derivedHom/coproduct combinations found generation, global compactness and
  the universal-coefficients consumer, not this internal-Hom continuity theorem.
  The consumer `Sheaf.Paper.HomUniversalCoefficients` was read and uses this item
  precisely for copies of one bounded-below complex; it confirms the ambient encoding.
- `grep -rn` of the item id in upstream WeilConjectures found no occurrence.
  Exact proposed declaration-name rg in Mathlib, upstream, side Lean and
  dag/lean_names_upstream.json found no collision.

The actual ILO PDF was read with pdftotext (printed p. 325, section 10.1). It states
that the Ext functors for a D^-_c first argument commute with filtered inductive
limits, hence RHom commutes with representable direct sums in D^+. The common lower
bound in this node is precisely the representability condition for those sums.
No statement correction, new nodes, dependency-module repairs or dispute is needed.

Validation: scompile.py compiled both the isolated sandbox and the actual module
individually, with no errors or warnings (2.5 s and 2.7 s). Earlier drafts exposed the
missing global coproduct instance and were replaced by the explicit conclusion packaging.

## Second reading by Q85

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
