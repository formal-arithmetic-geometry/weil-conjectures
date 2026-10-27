## Worker report

The delivery states `TopCat.SheafCotangent.exists_standardCotangentAugmentation`
in `Sheaf.Topology.StandardSheafCotangentAugmentation`. Its only postponed theorem
has proof `sorry`. The theorem asserts `Nonempty (StandardCotangentAugmentation C S)`
for the recorded standard ring coherence `C` and sheaf comparison `S`. The structure
is the complete assertion, with maps characterized on all standard local tensors;
no definition chooses an object or map from this existence theorem. The other
helpers are explicit submodule expressions, single complexes and coordinate maps.
There is no statement correction, new DAG node, or dependency repair.

Sources read: cotangent.tex, `definition-cotangent-complex-ring-map` (08PN),
`lemma-identify-H0` (08QF), `lemma-H0-L-morphism-sheaves-rings` (08UR), and the
ringed-space specialization (08UV); sites-modules.tex,
`lemma-differentials-sheafify` (08TP) and `lemma-pullback-differentials` (08TQ).
The node's eight proof steps are recorded in the theorem docstring, including the
explicit standard-face and monomial proof rather than a claim that sheaf cokernels
are computed on sections.

Hypothesis and clause correspondence:

- A topological space and a map of sheaves of commutative rings are
  `T : TopCat.{u}` and `f : Arrow (T.Sheaf CommRingCat.{u})`. The fields quantify
  over every such `T` and `f`. All universes and variables are explicitly bound,
  with `autoImplicit false`. The sole inherited typeclass binder supplies derived
  categories of ring modules, as required by the existing `Coherence` interface;
  it is categorical size infrastructure, not a hypothesis on the ring map.
- The standard polynomial resolution and its augmentation are `C.standard`,
  `C.standard_spec`, `C.differentials`; its sheafification is the already recorded
  `standardSheafComplex C S f = sheafComplex (S.sheaves T f).sections`. No second
  polynomial resolution or cotangent complex is introduced.
- The sheafification of sectionwise differentials, with the universal derivation,
  is the existing `CategoryTheory.SheafDifferentials.omega f.hom` and
  `.derivation f.hom`. `sheafOmegaComplex f` merely places that module in degree
  zero using `HomologicalComplex.single`.
- The canonical chain map is `StandardCotangentAugmentation.map f`, with target
  `sheafOmegaComplex f`. Its `formula` field sends the sheafification of the
  actual `complexGenerator ... 0 r p` to `r • d (epsilon p)`, after the canonical
  `sheafOmegaZero` coordinate. The `negative` field explicitly makes its
  components zero in every negative degree. The ring `formula` and `negative`
  fields state the identical formulas before sheafification. These formulas
  determine the maps on generators, so the maps are canonical, not arbitrary.
  The existing tensor convention puts the scalar first (`r ⊗ dp`), the symmetric
  order of `dp ⊗ r` in the node.
- The H0 isomorphism is the `h0` field: the actual induced homology map of the
  chain augmentation is invertible. Composing its `asIso` with Mathlib's
  `HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (omega f.hom)` gives
  precisely `H0(K) ≅ omega f.hom`. Thus this is the induced isomorphism, not an
  unrelated existential isomorphism. The same assertion is stated for rings.
- The explicit ring cokernel uses `cotangentSymbols f = f.right →₀ f.right`,
  i.e. the free B-module on all labels b. `RingCotangentAugmentation.symbols`
  identifies it with the actual degree-zero standard complex and
  `symbols_formula` fixes `δ_b` as `variableDifferential C f 0 b = dx_b ⊗ 1`.
- `cotangentFaceRelation f p` is `δ_(epsilon p)` minus the finite sum over
  `p.vars` of `epsilon (pderiv b p) • δ_b`. Outside `p.vars` the derivatives
  vanish, so this is exactly the displayed sum. `first_differential` states
  the value of the actual first differential on every degree-minus-one variable
  differential, with the opposite sign dictated by d0-d1. `image` states that
  its actual image is `cotangentFaceRelations f`; it is not merely an inclusion.
- `cotangentDerivationRelations` is the span of the three sets of additivity,
  product and base-ring relations. `relations` states equality with the face
  relation span. `cokernel` states that the degree-zero augmentation is the
  categorical cokernel of the actual first differential. Together with
  `symbols_formula` and `formula`, this identifies the quotient with Kähler
  differentials and sends the class of δ_b to db, exactly as in the node.
- `section_augmentation` identifies the degree-zero sheaf augmentation on EVERY
  sectionwise element with the existing module-sheafification unit applied to
  the ring augmentation. It connects the explicit ring presentation to the
  sheaf assertion and fixes the original universal derivations.
- For all commutative squares, including squares over continuous maps,
  `differential q` is a chain map between the underlying additive omega complexes
  in pushforward-adjoint form. `differential_formula` fixes db to d(beta b), and
  `differential_scalar` states semilinearity with coefficients restricted along
  beta. `naturality` is equality of the two full chain composites with the
  recorded standard map `(S.maps q).map`. `h0_naturality` is the corresponding
  equation of induced degree-zero homology maps. It therefore states naturality
  of the H0 identifications as well as of the augmentations.
- Continuous inverse image uses exactly `inverseImageArrow`,
  `inverseImageSquare`, `pullbackComplex`, `inverseAdjunction`, and
  `inverseStandardMap` from the recorded comparison/model modules.
  `inverse_differentials` states invertibility of the adjoint differential
  comparison. `inverse_naturality` is the full chain square after taking the
  adjoint, with the normalized standard inverse-image comparison. Taking H0,
  and using exactness of the already recorded inverse-image module functor,
  yields the stated compatibility under the canonical H0 comparisons. Inverse
  image of modules and their coefficient sheaf is meant here, not arbitrary
  scalar extension asserted to be exact.
- `scalar` states the ordinary coefficient-extension chain square. It quantifies
  over the recorded `DerivedChangeOfRingsCochainModel D` and a normalized
  `StandardLinearization l`; the source functor `D.E` is ordinary sheaf module
  scalar extension by its `obj_eq`, not derived scalar extension. The bottom
  chain map `b` is normalized on every `r ⊗ ds` to `r • d(beta s)`. The equality
  `(D.E.mapHomologicalComplex ...).map (map f) ≫ b = l.map ≫ map g`
  is the entire square of chain maps. For A→B→C, specialize `q` to the square
  with identity on A and the given B→C. This is exactly the square in the node.
  The same formula is valid for a general square, already covered by the
  preceding naturality clause. No flatness, injectivity, surjectivity, finite
  generation or nontriviality assumption is present.

Dependency declarations read and used:

- `Sheaf.Topology.StandardSheafCotangentFlatModel`:
  `TopCat.SheafCotangent.standardVariables`, `standardVariable`,
  `variableDifferential`, `standardSheafComplex`, `scalarExtensionSection`,
  `StandardLinearization`, `inverseStandardMap`, `FlatFunctorialModel`, and
  `exists_flatFunctorialModel`. The fields use its actual standard model and
  normalized linearization interface, not an arbitrary chosen map. Flatness
  itself is not needed in the augmentation theorem.
- `Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel`:
  `CategoryTheory.SheafifiedDifferentials.sheafified_differentials_cokernel`;
  read its relation formulas and representing property, and its uses of the
  existing relative differential presheaf. This is the sheafification and
  universal-derivation input for proof step 5.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`;
  and their bundled ring-map interface `CommRingCat.KaehlerDifferential`, `.d`
  from `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic`.
- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Coherence`, `standardAugmentation`,
  `complexGenerator`, `standardComplex` and the standard face formulas.
- `Sheaf.Topology.SheafCotangentComparison`:
  `TopCat.SheafCotangent.Comparison`, `sectionArrow`, `sectionElement`,
  `RingSquare`, `pushforwardComplex`, `pullbackComplex`, `inverseAdjunction`,
  `inverseImageArrow`, `inverseImageSquare` and the `S.maps` comparison.
- `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`:
  `CategoryTheory.SheafDifferentials.ring`, `omega`, `derivation`, and the
  normalized inverse differential comparison theorem and its square maps.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationAdjunction`; the latter is
  explicitly instantiated at all four universes in `section_augmentation`.
- Proof imports also retain
  `Mathlib.RingTheory.Kaehler.Polynomial` (`mvPolynomialBasis` and its coordinate
  derivative formula), and
  `WeilConjectures.AlgebraicGeometry.InverseImageModuleFunctor`
  (`TopCat.Sheaf.inverseImageModuleFunctor_exact`). All recorded proof
  dependency modules are imported directly.

Edge cases checked before and during writing:

- Empty T is allowed. Every quantified section and point condition is meaningful;
  there is no inhabitance binder. Ring sheaves and their zero modules remain valid.
- Zero rings and identity maps are allowed. There is no `Nontrivial` binder;
  the free module and its relation quotient still make sense, and differentials
  of an identity map vanish.
- Constant polynomials have empty variable set. The finite derivative sum is zero,
  giving exactly base annihilation, including constants 0 and 1.
- Coincident labels b=c and repeated variables are not excluded by an index
  distinctness condition. The Finsupp addition and partial derivatives count
  multiplicities, including in characteristic two.
- Infinite sets of ring elements are allowed: symbols are finitely supported
  functions, and only each individual polynomial has finite variable support.
- All negative degrees, including -1, and degree zero are explicitly covered.
  Positive source terms are already zero in the recorded standard model.
- Scalar extension along a nonflat quotient (e.g. Z→Z/2) is included: the square
  uses only balanced tensors and linear maps; it asserts no tensor exactness.
- The ring/sheaf coefficient universe is the inherited arbitrary universe u;
  no equality with a smaller test universe, finite bound, or point assumption
  was introduced to resolve compiler inference.

Searches actually run:

1. msearch leanfinder: `standard sheaf cotangent complex augmentation to Kahler
   differentials zeroth cohomology natural`. Eight hits, including
   `Algebra.Extension.toKaehler` and `Algebra.Extension.cotangentComplex`.
   These concern a ring extension's naive two-term cotangent construction;
   none is the full standard simplicial sheaf augmentation and its naturality.
2. msearch loogle: `KaehlerDifferential, CochainComplex, homology`.
   It returned zero hits and the diagnostic `unknown identifier 'homology'`;
   this query is not evidence that a valid homology-pattern search has no match.
3. msearch grep in Mathlib RingTheory:
   `cotangent.*[Aa]ugment|[Aa]ugment.*cotangent|[Hh]0.*cotangent`.
   Zero hits.
4. msearch leansearch: `The zeroth homology of the standard cotangent complex is
   the module of Kahler differentials`. Eight hits, including
   `Algebra.Extension.exact_cotangentComplex_toKaehler`, the formally etale H1
   criterion and unrelated group homology H0 declarations. None states this
   sheaf augmentation result.
5. Direct rg over `lean/WeilConjectures` and `lean/Sheaf` for this node id and
   `cotangent.*[Aa]ugment|[Aa]ugment.*cotangent`. Hits included unrelated
   polynomial augmentation calculations, downstream uses in
   `EtaleSourceAdjunctionLine` and `LciDeterminantDescentSmooth`, and the
   ring/sheaf comparison construction. None declares this node's statement.
   Direct rg for all new declaration names in Mathlib/project upstream names
   and the existing source modules found no previous declaration.

The compiler initially diagnosed a namespace typo in `relativeDifferentials'`
and then an underconstrained module-sheafification universe. Reading the complete
Mathlib signatures and an explicit module-mode `#check` probe resolved these by
using the full namespace and `sheafificationAdjunction.{u,u,u,u}`. No mathematical
universe restriction was added. A local compile ran out of device space; the
prescribed wrapper fell back to the server and compiled the complete file in
37 seconds, finding only an unused square-parameter warning. That parameter was
renamed `_q` (its indices determine the target type); the final server compile passed cleanly in 49.2 seconds, with no warnings.
The prescribed `deliver2.py --no-push` dry run then passed the server preflight
and per-file compilation (dry-run commit 8a40ec70cdd). The node differs from its
base only in `lean`; its recorded signature matches verbatim; all twelve public
declarations are listed; the delivered module has one `sorry`, no unbound
variables, and no lines over 100 characters.

## Second reading by Q143

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
