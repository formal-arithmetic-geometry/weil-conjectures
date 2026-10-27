## Worker report

Reused `AlgebraicGeometry.Scheme.InfinitesimalLifts.exists_derivationAction` in
`Sheaf.AlgebraicGeometry.EtaleLocalLiftDerivationAction` (source file
`lean/Sheaf/AlgebraicGeometry/EtaleLocalLiftDerivationAction.lean`, theorem at line 213).
The owning node is `lem-sfb-etale-local-lift-torsor-quasi-coherent`. Parsed both JSON
files and checked that their complete natural-language statements are string-equal.
Read the entire existing module, including the helper definitions, comparison
normalizations, action fields and proof docstring. Accordingly this delivery changes
only the item's `lean` field, with `existing: true`, and contains no new Lean module,
no new definitions and no new postponed theorem. The recorded signature preserves
its source whitespace verbatim, excluding the proof assignment.

Sources read: `spaces-more-morphisms.tex`, Tags 061A (`lemma-sheaf`), 061C
(`lemma-action-sheaf`), 061D (`remark-special-case`), and the coefficient
quasi-coherence paragraph of 04AM (`lemma-smooth-formally-smooth`). In 061D the
source target thickening is the identity, so its conormal compatibility condition
is automatic. The source explicitly describes a pseudo torsor before separately
addressing existence of sections; the reused theorem likewise asserts no existence.

Hypothesis and clause correspondence (helper names below are in
`AlgebraicGeometry.Scheme.InfinitesimalLifts`):

- The four schemes are `{V W T₀ T : Scheme.{u}}`, for an explicit arbitrary
  universe `u`. The given morphism is `(f : V ⟶ W)`, with precisely
  `[LocallyOfFinitePresentation f]`. Smoothness, flatness and finite presentation
  of the whole morphism are not assumed.
- The first order thickening is `(i : T₀ ⟶ T)` with
  `(hi : IsFirstOrderThickening i)`. Its definition is
  `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`. Thus the ideal is the actual defining
  kernel ideal, rather than an unrelated module.
- The diagram is `(a₀ : T₀ ⟶ V) (b : T ⟶ W)` with
  `(comm : a₀ ≫ f = i ≫ b)`, exactly `f a₀ = b i` in diagrammatic order.
- `idealOnReduction i` is `(tensorPullback i).obj i.ker.toModules`, the canonical
  conormal module `I/I²`. Under the square-zero hypothesis it is canonically `I`
  with its quotient scalar action. This does not choose arbitrary module data.
- The module `E` is `((tensorPullback a₀).obj f.relativeDifferentials)`.
  `coefficients f i a₀` is exactly `(pushforward i).obj
  (SheafOfModules.homObj E (idealOnReduction i))`. Internal Hom's sections are
  module-sheaf maps on the corresponding opens. Pushforward supplies scalars via
  the quotient structure-sheaf map, as required for the specified `O_T`-module.
- The theorem's first conjunct `(coefficients f i a₀).IsQuasicoherent` is the
  quasi-coherence conclusion for this particular constructed `H`.
- The site is `T.Etale` with `T.smallEtaleTopology`. For an object `U`, its scheme
  and structure map are `U.left` and `U.hom`. `IsLift` imposes the two equations
  `a ≫ f = U.hom ≫ b` and
  `pullback.snd i U.hom ≫ a = pullback.fst i U.hom ≫ a₀`.
  Thus `pullback i U.hom` is precisely `U₀ = T₀ ×_T U`, with the correct two
  projections and reduction condition.
- `liftSubfunctor` cuts out those maps inside the restricted representable
  presheaf, and `liftPresheaf` is its actual subtype-valued functor. Its
  restrictions are precomposition with the test-scheme morphism, not arbitrary
  functions. The second conjunct
  `Presheaf.IsSheaf T.smallEtaleTopology (liftPresheaf f i a₀ b)` asserts the
  required sheaf condition for precisely that presheaf.
- The third conjunct `Nonempty (DerivationAction f i a₀ b)` asserts existence
  of the action structure, not existence of any lift. Its `act` is defined on
  `Γ((tensorPullback U.hom).obj (coefficients f i a₀), ⊤)`, exactly the section
  group defining `H_et(U)` in `etaleTensorSectionsSheaf`. The fields `zero_act`
  and `add_act` specify an additive group action.
- The field `naturality` uses `etaleTensorSectionsRestriction` on coefficients
  and the actual `liftPresheaf.map` on lifts. It is the requested compatibility
  with every morphism in the small étale site.
- `simply_transitive : ∀ U a, Function.Bijective (fun h ↦ act U h a)` gives
  precisely each orbit bijection, conditional on the given lift `a`.
- `same_base` fixes the continuous map of each translated lift. The `formula`
  field evaluates its ring-sheaf map on arbitrary local sections: the original
  image plus the image under the coefficient Hom of the pulled-back universal
  relative differential. It uses `relativeDifferentialsDerivation.d`, tensor
  composition, and the ideal inclusion. This is `a^sharp + D` with the positive
  sign specified in the node. `CoefficientComparison.ideal_eval` and `hom_eval`
  normalize the two comparison isomorphisms on local pulled-back sections, so
  the formula cannot be changed by an arbitrary automorphism of coefficients.

Recorded statement dependencies read and used by the existing module:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-sbc-first-order-thickening`:
  `WeilConjectures.AlgebraicGeometry.Thickening`,
  `AlgebraicGeometry.IsFirstOrderThickening`.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` and its
  public upstream `tensorPullback`, with the canonical `tensorPullbackSection`.
- `def-sc-relative-differential-sheaf`:
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, together with the
  corresponding universal relative derivation.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes
  `SheafOfModules.IsQuasicoherent`, the clause relevant here. The coherence and
  finite-type clauses of that dependency impose no extra hypothesis here.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst` and `pullback.snd`.
- `def-sc-etale-qcoherent-module`:
  `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf`,
  `AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf`; the action uses
  its actual section groups and `etaleTensorSectionsRestriction`.

Edge cases checked against the full definitions: `I = 0` gives the zero
coefficient module and singleton lift sets wherever a lift exists; `f = id`
has zero differentials and unique compatible lifts. An empty set of lifts is
allowed: every action map on it is empty, and the orbit condition quantifies
only over existing lifts. There is no `Nonempty (liftPresheaf.obj ...)`, no
local covering with sections, and no smoothness hypothesis. The empty test
scheme is allowed by `T.Etale`. No characteristic or affine hypothesis is
introduced. All schemes can be taken in any common containing universe.

Searches actually run with `msearch.py` for this group and item:

- LeanFinder: "The sheaf of square zero lifts is a pseudo torsor under the quasi
  coherent sheaf Hom of relative differentials into the ideal". Eight hits on
  presheaf differentials and universal derivations; none is the complete scheme
  lift sheaf/action assertion.
- Loogle: `Derivation, KaehlerDifferential`. Twelve hits, including
  `KaehlerDifferential.linearMapEquivDerivation` and `Derivation.liftKaehlerDifferential`;
  these are algebraic universal properties, not the whole theorem.
- Mathlib grep: `derivationAction|[Ll]ift.*[Dd]erivation|[Dd]erivation.*[Ll]ift`
  in `AlgebraicGeometry`. Zero hits.
- LeanSearch: "The sheaf of lifts across a square zero closed immersion is a
  pseudo torsor under derivations". Eight hits, including
  `derivationToSquareZeroEquivLift` and `liftOfDerivationToSquareZero`; these
  establish ring-level comparisons after fixing an algebra structure.
- Project/source `rg` for `exists_derivationAction`, `InfinitesimalLifts` and
  the item identifier, and the prescribed identifier grep in
  `WeilConjectures`: the exact match is the existing Sheaf module above;
  no upstream theorem was found under these names. The DAG's review note also
  identifies the duplicate node; direct JSON statement comparison confirmed it.

No statement correction, dependency repair, new node, or disputed statement is
needed. The existing module retains its stage-2 postponed proofs; this delivery
records its interface and makes no claim to have proved them.

Validation: `deliver2.py Q83 lem-per-etale-local-lift-torsor-quasi-coherent
--no-push` returned OK: the existing declaration checks compiled through the
server's 60-second per-file wrapper, and the server preflight accepted the
node/report-only packet. No warning or error was reported.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
