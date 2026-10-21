## Worker report

The new module `Sheaf.Paper.SignedTateCoefficientExponentNormalization` states
`AlgebraicGeometry.ProEtale.signedTateCoefficientExponentNormalization`, with one
postponed theorem proof and no new definitions. Its docstring carries the complete
12-step node argument, grouped into nine paragraphs. No statement correction or
new dependency/node is needed; only the item's `lean` field changes.

Hypothesis and clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`; the scheme is `(T : Scheme.{u})`;
  invertibility is `[∀ x : T, Invertible (ℓ : T.residueField x)]`.
- Finite commutative coefficient rings are `{A B : Type u} [CommRing A]
  [CommRing B] [Finite A] [Finite B]`; the unital coefficient map is `f : A →+* B`.
- Positive exponent indices are shifted: Lean `n` means node exponent `n+1`.
  The binder `a : ZMod (ℓ ^ (n+1)) →+* A` is exactly annihilation by that
  exponent, not additional coefficient data: a unital ZMod map is unique, exists
  iff the modulus kills 1, and killing 1 is equivalent to killing all elements.
  The B map is `f.comp a`, so it is also annihilated. For any node common exponent
  m and n ≥ m, this supplies the unique a at n; conversely each quantified a is
  the node's case m = n+1. The resulting families depend only on the root level,
  not on the chosen lower bound m. For comparisons the lowest level k (and j for
  composition) supplies a, and all higher levels use its canonical quotient
  composites. Hence all and only the node's common-exponent cases occur for A,B.
- `scalarExtensionTateLine T ℓ A n a r` is the existing actual root sheaf tensored
  with the constant A sheaf, followed by `coefficientTwistLine`: degree 0 is
  `SheafOfModules.unit`, positive degrees are the recursive sheaf tensor powers,
  and `Int.negSucc k` is internal Hom of power k+1 into the unit. The ULift in
  the existing interface changes universes, not coefficients or root objects.
- `ScalarExtensionTateMaps` is a family of A-linear sheaf morphisms into the
  restriction of the B-line along `proEtaleConstantRingMap f`. This is precisely
  additivity and f-semilinearity, with naturality on every object built in.
- The first `∃! c` states existence and uniqueness. Its existing predicate
  `IsCanonicalScalarExtensionTateMaps` has exactly four clauses: degree-zero f;
  degree-one root tensor formula; successor tensor formula for positive powers;
  and the negative evaluation equation. The latter evaluates the actual internal
  Hom section on the identity object of each slice, for every base object U.
  Applying this at every U gives the local-section formula on all slices.
- The two `IsFiniteLocallyFreeOfRank 1` conjuncts express the node's invertible
  signed lines, with the existing dependency's rank-one convention, for A and B.
- The first block's `∃! e` gives the B-linear ordinary scalar-extension
  isomorphism. Its formula is `e(b tensor x) = b • c(x)` for every U,b,x, using
  `reductionTensorSection`. The interface writes B tensor A-line, canonically
  the node's A-line tensor B. Uniqueness records the tensor universal property;
  it adds no mathematical assertion beyond that induced map's invertibility.
- The next three conjuncts cover A, and the following three cover B with
  `f.comp a`. Each `∃! e` quantifies all signed degrees and uses the existing
  `IsCanonicalScalarExtensionTateLevelMaps`, whose four clauses are identity on
  degree zero, the actual `proEtaleRootsOfUnityTransition` in degree one,
  recursive tensor powers, and inverse-dual evaluation. Its roots transition
  is raising to `(ℓ^(n+1))/(ℓ^(k+1)) = ℓ^(n-k)`, exactly the node's exponent.
- The identity conjunct for each coefficient says the canonical comparison
  n→n is the identity. The composition conjunct says n→k followed by k→j
  equals n→j. HEq only transports the line indexed by `a.comp castHom` back
  to the equal coefficient map a; all ring maps from ZMod are unique. These
  HEqs are conclusions, never hypotheses hiding an impossible equality.
- The penultimate conjunct is the semilinear coefficient/exponent square:
  c_n followed by restriction of e_B equals e_A followed by c_k, for all r.
- The final conjunct is the ordinary scalar-extension square. The functor
  `proEtaleRingExtension` maps e_A, and the same published canonical
  `scalarExtensionTateIso` appears on both levels. All comparisons therefore
  use the very families uniquely normalized in the earlier clauses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`: weakly etale small site.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`:
  sheafification of the constant presheaf.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`:
  exact abbreviation for Mathlib `SheafOfModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnityModule`, and
  `proEtaleRootsOfUnityTransition`: actual kernel of the power map and its
  Kummer transition, not an arbitrary rank-one replacement.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`; its public tensor implementation and
  `siteSheafTensorTmul` provide the sheafified section tensor used in the predicates.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`: slice-wise linear morphisms with their actual action.
- `Sheaf.Paper.TateTwistLocallyFree`: `tateFiniteCoefficient`, `tateFiniteScalar`,
  `tateFiniteLine`, `tateFiniteTensor`, `TateSignedLine`, `tateTwist_locallyFree`.
  Read the full theorem, including its finite coefficients and signed-line clauses.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: reuses
  `scalarExtensionTateLine`, `ScalarExtensionTateMaps`,
  `IsCanonicalScalarExtensionTateMaps`, `scalarExtensionTateMaps`,
  `scalarExtensionTateIso`, `IsCanonicalScalarExtensionTateLevelMaps`,
  `scalarExtensionTateLevelIso`, and their existsUnique theorem signatures.
  The existing final exponent-naturality theorem gives only the scalar-extended
  square, not this node's full identity/composition and semilinear assertions.
  No private copy or additional choice of a map is introduced.
- Proof-only imports: `exists_localizedSiteTensorRestriction` from
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`;
  `SheafOfModules.tensorClosed` from its WeilConjectures module;
  `SheafOfModules.tensor_bilinear_universal` from its WeilConjectures module;
  `SheafOfModules.scalarExtensionDualMap`, its slice evaluation and extensionality
  from `Sheaf.Paper.ScalarExtensionDualEvaluation`. Full signatures/docstrings
  were read. These keep the prescribed node argument available for stage 3.

Import-cycle note for the maintainer: the existing signed-line interface lives in
`ScalarExtensionFunctor`, the module of the citing parent
`det-sp-scalar-extension-functor`. This module must import that existing interface
under the one-definition rule. Do not auto-add an import of this new module back
into `ScalarExtensionFunctor`: that would close an import cycle. The stage rule
explicitly permits omitting that proof import and reporting it. A later extraction
of those existing helpers can remove that source-layout issue; no DAG edge to the
parent is added here.

Edge cases checked mathematically: empty T; A or B the zero ring; ℓ=2; lowest
exponent 1 (Lean index 0); n=k=j; degree 0, degree 1 and degree -1; arbitrarily
large positive/negative powers; non-flat quotient Z/ℓ²→Z/ℓ; non-surjective
F_ℓ→F_ℓ[ε]. No nontriviality, flatness or surjectivity binder excludes these cases.
The coefficient map forces B's same annihilator, including the zero-ring cases.
Every universe is explicit; ProEt object/morphism universes remain distinct.

Searches actually run with `batch2/msearch.py`:

- leanfinder: `Signed Tate sheaf coefficient maps uniquely normalized by root
  tensor products and dual evaluation commute with Kummer exponent transitions`:
  eight results, including Hilbert90, AdicCompletion.transitionMap_comp_eval,
  cyclotomicCharacter and RootPairing; none states the sheaf theorem.
- loogle: `SheafOfModules, TensorProduct`: zero results.
- grep (Mathlib CategoryTheory): `Tate|Kummer|rootsOfUnity`: 25 substring hits,
  principally unrelated occurrences of “statement”; no exact match.
- leansearch: `Signed finite Tate twist coefficient maps commute with change of
  Kummer exponent and are uniquely normalized by tensor products and dual
  evaluation`: eight results (coevaluation, graded tensor, PiTensorProduct dual,
  IsBaseChange, KummerDedekind); no exact signed sheaf theorem.
- rg in `lean/WeilConjectures` for scalarExtensionTate/coefficientTwistLine and
  grep there for this node id: no signed coefficient/exponent theorem.
- rg in `lean/Sheaf`: found the existing normalization predicates, existence,
  scalar-extension isomorphism and scalar-extended naturality in
  `SecSmoothPurity/ScalarExtensionFunctor.lean`. Read the whole module. Its
  missing identity/composition and semilinear-square clauses prevent an exact
  `existing: true` attachment for this full node.

Validation: scompile.py checked the module as both sandbox and intended library
module. An intermediate documentation line-length warning was repaired; the final
compile and deliver2 dry run are recorded by the prescribed tools.

## Second reading by Q07

This is the worker's final self-check; the dispatcher's independent maintainer
review is still required. No other agent was started, as the worker brief forbids.
I reopened the node and final module and checked the hypotheses and each conjunct
against the correspondence above. During this reading I restricted B's standalone
exponent quantifiers to maps `f.comp a`, so both rings use the node's common
annihilating exponents rather than asserting extra B-only comparisons below them.
I checked the order of composition (Lean `≫` follows execution order), all signed
indices, the identity and iterated quotient-map transports, and that the final
squares use the same canonical maps and isomorphisms. No node statement correction,
missing notion, hollow definition or disputed mathematical assertion remains.
