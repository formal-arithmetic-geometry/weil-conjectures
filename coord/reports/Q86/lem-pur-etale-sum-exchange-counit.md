## Worker report

Item: `lem-pur-etale-sum-exchange-counit`. The module
`Sheaf.AlgebraicGeometry.EtaleSumExchangeCounit` states
`AlgebraicGeometry.Etale.etaleSumExchangeCounit`, with one `sorry` and no proofs.
It also constructs the canonical constant-object identification
`etaleSumExchangeConstantIso` from existing comparison isomorphisms; it has real data
and no postponed proof. Both declarations are listed in the node's Lean record.
The node's statement, dependencies, proof and other existing fields are unchanged.

Sources read: Stacks `etale-cohomology.tex`, lemma-shriek-base-change (03S6),
including its proof comparing right adjoints; the recorded dependency statements,
Lean signatures and docstrings; Mathlib's adjunction mates and composite adjunctions;
and the current blueprint's `thm-pur-composition-coherence` statement and proof,
Step 1. The original CompactObject example module is now withdrawn; its node is
an existing-declaration record, so the active modules' module/public-section format
is used here.

Hypotheses and objects, matched with the node:

- Finite commutative coefficient ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is the existing constant-module coefficient convention, with schemes in
  universe `u` and module values in universe `u + 1`.
- Schemes and arbitrary morphism: `{U X X' : Scheme.{u}}`, `e : U ⟶ X`,
  `w : X' ⟶ X`. There is no smoothness, flatness, properness or etaleness
  hypothesis on `w`.
- Separated etale of finite type: `[Etale e] [IsSeparated e] [QuasiCompact e]`.
  Etale already implies locally of finite presentation, hence locally of finite
  type; quasi-compactness supplies the remaining finite-type condition.
- Noetherian schemes: `[IsNoetherian U] [IsNoetherian X] [IsNoetherian X']`.
  Mathlib's `isNoetherian_iff_of_finite_affine_openCover` identifies this with the
  node's finite affine cover by spectra of Noetherian rings. No dimension bound
  or finite base field is imposed.
- Cartesian square: `pullback w e`, with `e' = pullback.fst w e` and
  `w' = pullback.snd w e`. This is X' times_X U, canonically U times_X X',
  exactly the projection ordering of the recorded beta. The square is
  `(IsPullback.of_hasPullback w e).toCommSq`. Its canonical pullback comparison
  `squareUpperStarIso (ModuleCat A) ...` goes from e* then w'* to w* then e'*,
  thus is the node's chi, in the stated direction.
- Module sheaves: `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)` throughout,
  not pro-etale sheaves or structure-sheaf modules. Derived inputs are
  `DerivedCategoryModule A X`, the whole unbounded category.
- H, J, R and R' are the existing `upperStar` functors for w, snd, e and fst;
  L and L' are `etaleLowerShriek` for e and fst. Units and counits are those of
  `etaleLowerShriekUpperStarAdjunction`, not separately chosen adjunctions.

The conclusion has six conjuncts, matching all assertions:

1. `etaleLowerShriekBaseChangeMap A w e = ((mateEquiv ...).symm
   (TwoSquare.mk ... chi.hom)).natTrans`: the specified sheaf beta is the inverse
   mate of chi. Beta is the dependency's actual inverse-conjugate definition:
   its conjugate under the two composite adjunctions is the actual module-valued
   `baseChangeMap`, not an arbitrary map or isomorphism supplied as a hypothesis.
2. The `∀ M` equality expands beta as L' of J of the specified sum unit,
   followed by L' of chi at LM, followed by the specified L' counit at HLM.
   Lean composes with `≫`, so the order is the reverse of the node's displayed
   right-to-left composition notation and is exactly the same arrow.
3. The `∀ N` equality is beta at RN followed by H of v_N, equal to L' of chi_N
   followed by v'_HN. It is an equality of module-sheaf maps.
4. `exactEtaleSumExchange A e w =
   (Functor.mapDerivedCategorySquareIso (asIso beta)).symm`, with the explicit
   `isIso_etaleLowerShriekBaseChangeMap` proof passed to `asIso`. The existing
   `exactEtaleSumExchange` is the specified bSigma; `mapDerivedCategorySquareIso`
   applies the isomorphism degreewise and conjugates by the canonical exact
   composition comparisons. Thus this asserts precisely bSigma = D(beta^-1),
   without choosing a different base-change isomorphism.
5. The `∀ K : DerivedCategoryModule A X` equality uses the inverse component of
   this same `exactEtaleSumExchange` at D(e*)K, followed by D(w*) of the actual
   `derivedEtaleLowerShriekUpperStarAdjunction` counit. The other side is D(L')
   of the exact-derived chi component, followed by the actual derived e' counit.
   The existing derived sum adjunction is constructed by localizing the sheaf
   adjunction on complexes; these are exactly the required evaluation maps.
6. At the constant sheaf `constantSheaf ... |>.obj (ModuleCat.of A A)` in degree
   zero, the final equation is chi followed by D(e'*) of c_w, then c_e', equal
   to D(w'*) of c_e, then c_w'. All c's are the constructed
   `etaleSumExchangeConstantIso`. Since both constant identifications are
   isomorphisms, this equality says that chi becomes the identity of A_U'.
   The helper is just `mapDerivedCategorySingleFunctor 0` followed by the
   single functor applied to `Scheme.upperStarConstantSheafIso`. It introduces
   no independent notion and replaces none of the dependency constructions.

Dependency declarations used, by recorded modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, via
  `Mathlib.AlgebraicGeometry.Noetherian` and `AlgebraicGeometry.IsNoetherian`.
  The morphism-properties dependency is a convention record with no declaration;
  its separated/finite-type conventions are the existing `IsSeparated` and
  `QuasiCompact` plus Etale's locally finite-type implication.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: the chosen-square convention;
  it reuses `Etale.squareUpperStarIso` from
  `WeilConjectures.SixFunctors.BaseChange.Square`, used directly here on the
  standard chosen fiber product. The latter also gives `Etale.baseChangeMap`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, using Mathlib's derived category.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `etaleLowerShriek`, `etaleLowerShriekUpperStarAdjunction`, and exactness;
  `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection`:
  `derivedEtaleLowerShriekUpperStarAdjunction`.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`: imported for the recorded
  exactness/whole-derived-adjunction proof dependency, with the existing derived
  adjunction above used directly in the signature. No ambient Brown right
  adjoint or compactification is introduced into the statement.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `etaleInverseImageModulesExact`, the recorded constant-ring module inverse-image
  interface; the sum framework uses its already existing module-valued
  `Etale.upperStar` and `upperStarLowerStarAdjunction`.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`:
  `etaleLowerShriekBaseChangeMap`; and
  `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`:
  `isIso_etaleLowerShriekBaseChangeMap`.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`;
  `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `conjugateEquiv`,
  `iterated_mateEquiv_conjugateEquiv`, `mateEquiv_counit`.
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`:
  `etaleUnderivedExchange_moduleLinear`, a proof dependency; no replacement
  module-linear exchange is defined here.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData`:
  `exactEtaleSumExchange`, the already constructed specified derived sum exchange.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`;
  `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`:
  `Functor.mapDerivedCategorySquareIso`;
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `Adjunction.mapHomotopyCategory`;
  `Sheaf.CategoryTheory.ExactDerivedTransformationPasting`:
  `ExactDerivedPasting.exact_derived_transformation_pasting`.
- `WeilConjectures.AlgebraicGeometry.EtaleConstantRingInverseImageComparison`:
  `etaleConstantRingInverseImageComparison`; `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `constantSheafAdj`; `WeilConjectures.ConstructibleSheaf.Defs`:
  `Scheme.upperStarConstantSheafIso`.

Edge cases checked before writing and in the signature review:

- w = identity and e = identity are allowed; comparisons retain the canonical
  identity-functor identifications rather than replacing them by arbitrary maps.
- U empty is allowed, as are empty schemes in the square; no Nonempty assumption
  is made on the fibers, schemes, sites or module values.
- Zero modules, the zero derived object and the zero coefficient ring are allowed;
  no Nontrivial A or nonzero-object assumption occurs.
- A split two-sheet cover gives a fold evaluation on both sides, with no extra
  scalar, inverse degree or sign. No invertibility of the degree is assumed.
- Derived K is arbitrary, with no lower/upper bound, constructibility, torsion,
  flatness or K-injectivity hypothesis. Degree zero is only used in the final
  constant-object normalization.

Searches (the wrapper records queries and hit summaries in searches.jsonl):

- `msearch.py ... leanfinder "The etale sum extension base change transformation
  is the inverse mate of pullback composition and preserves the derived evaluation counit"`:
  eight hits: generic module-pullback composition comparisons, chosen-pullback
  counit identities, and unrelated etale differential results; no exact statement.
- `msearch.py ... leanfinder "etale sum base change inverse mate preserves evaluation counit"`:
  eight hits, including `mateEquiv_counit`, its symmetric form, `mateEquiv`, and
  `iterated_mateEquiv_conjugateEquiv_symm`. These are generic identities and do not
  identify the specified sheaf beta or the constant-object normalization.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.conjugateEquiv"`
  and `... loogle "CategoryTheory.mateEquiv"`: generic mate correspondence,
  unit/counit identities and iteration; no existing full node statement.
- `msearch.py ... grep "mateEquiv_counit|iterated_mateEquiv" CategoryTheory/Adjunction`:
  five hits in Mathlib's Mates module, used for the proof plan rather than copied.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
  `etaleLowerShriekBaseChange`, sum/counit/base-change combinations, and the item's id:
  existing specified sheaf beta and its invertibility, existing
  `exactEtaleSumExchange`, graph comparison normalizations, and the distinct
  open-immersion compatibility theorem. None states the six-part node statement.
- `rg` of Mathlib and the upstream source identified the existing square, derived
  square, single-functor, constant-sheaf, and sum-adjunction constructions. The
  general exact-derived square API is used directly. Searches for constant
  pullback/derived constant isomorphisms found
  `leftDerivedUpperStarSingleConstantSheafIso` (for the left-derived rather than
  exact-derived inverse image) and private bounded-below helpers; the helper here
  writes only the canonical specialization needed for this node using existing APIs.
- `rg` of `dag/lean_names_upstream.json`, `lean/WeilConjectures` and `lean/Sheaf`
  for the two new declaration names found no collision.

Validation: `scompile.py Q86 lem-pur-etale-sum-exchange-counit` accepted the module
in sandbox and library naming modes with no errors or disallowed warnings. Explicit
`set_option autoImplicit false` binds all variables and universes. The module has
one theorem with `sorry`, one fully constructed helper definition, and no line over
100 characters. No statement fault, statement correction or disputed statement.

## Second reading by Q86

No second reading by a worker: the dispatcher brief requires direct delivery and
forbids starting other agents. The maintainer's independent review reads the delivery.
A final self-review matched every hypothesis and all six conjuncts as described above;
this is not represented as an independent review.
