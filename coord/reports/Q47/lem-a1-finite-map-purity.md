## Worker report

The module `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` states
`AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_lowerStar_of_isFiniteEtale`,
with its proof postponed by `sorry`. It introduces no definition.

Statement correspondence:

- The finite field convention is `{k₀ : Type u} [Field k₀] [Finite k₀]`.
  A finite field has cardinality p^a with positive a. The geometric fibre uses
  the existing algebraic closure of k₀, not a different geometric construction.
- The coefficient prime is `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`.
  `PadicAlgCl l` is the existing algebraic closure of Q_l.
- The specified coefficient isomorphism is `(ι : PadicAlgCl l ≃+* ℂ)`.
  Its underlying ring homomorphism `ι.toRingHom` is passed to the recorded
  purity predicate; using an arbitrary embedding here would strengthen the statement.
- The real weight is `{w : ℝ}`; no integrality, sign, or nonzero restriction is imposed.
- The source and target are `{X Y : Scheme.{u}}` with their `.Over (Spec k₀)`
  structures. The morphism is `(π : X ⟶ Y)` with `[π.IsOver (Spec k₀)]`.
- "Finite etale" is `[IsFinite π] [Etale π]`. These are the existing scheme
  morphism properties; the deprecated alias `IsEtale` is not used.
- Finite type of the target over k₀ is the pair
  `[LocallyOfFiniteType (Y ↘ Spec k₀)] [QuasiCompact (Y ↘ Spec k₀)]`.
  The finite morphism then gives finite type of the source over k₀ as well.
  No separatedness or independent quasi-separatedness assumption is added.
- The constructible Q_l-bar Weil sheaf is `{F : WeilSheaf k₀ l X}`.
  This existing type is a full subcategory of actual constructible pro-etale sheaves
  on the geometric fibre with an invertible geometric-Frobenius structure.
- The hypothesis of punctual purity is
  `(h : F.IsPunctuallyPureOfWeight ι.toRingHom w)`.
- The direct image is `(WeilSheaf.lowerStar π).obj F`: its underlying sheaf is
  the actual direct image on the geometric fibres and its Weil structure is the
  canonical Frobenius-exchange isomorphism followed by direct image of F's structure.
- The conclusion is that this sheaf satisfies the same
  `IsPunctuallyPureOfWeight ι.toRingHom w`, preserving the identical real weight.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` has a convention-only record and no module.
  Its finite and etale properties are Mathlib `AlgebraicGeometry.IsFinite` and
  `AlgebraicGeometry.Etale`.
- `def-weil-punctual-weights`: import
  `WeilConjectures.DeligneLaumon.Reduction.Weights`, using
  `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight`, whose defining module is
  `WeilConjectures.WeilSheaf.Stalk`. Its definition quantifies over finite/closed
  points and applies `FrobeniusModule.IsPureOfWeight` with the actual residue cardinality.
  That predicate quantifies over eigenvalues and asserts the complex norm equality.
- `WeilConjectures.WeilSheaf.Category`: `AlgebraicGeometry.WeilSheaf`, the actual
  constructible sheaf representation used by that recorded purity predicate.
- `WeilConjectures.WeilSheaf.LowerStar`: `AlgebraicGeometry.WeilSheaf.lowerStar`,
  whose full signature requires a quasi-compact, quasi-separated, locally finite-type
  morphism and a target locally of finite type over k₀. All the morphism requirements
  follow from finiteness here. The defining object and Frobenius formulas were read.
- `def-weil-weil-sheaf-complex`: the recorded
  `Sheaf.Paper.SfWeilSheafComplex` is imported. Its `sfWeilComplex` and
  `sfCommonStageWeilComplex` repair the derived category of fixed pairs; its
  `sfWeilSheaf` and `sfCommonStageWeilSheaf` are the full subcategories with heart carrier.
  This theorem is a sheaf assertion and uses the existing actual-sheaf representation
  required by the separately recorded purity predicate. It does not use the old
  derived category of Weil sheaves as a substitute for a category of derived fixed pairs.
- `def-weil-derived-direct-image`: the recorded
  `Sheaf.Paper.SfDerivedDirectImage` is imported. Its `SfIntegralDirectImage`
  describes the integral Roos tower and its `sfDirectImageReductionComparison`
  is the scalar-adjoint projection. The present assertion only involves ordinary
  degree-zero direct image of sheaves, so the actual `WeilSheaf.lowerStar` is used;
  no arbitrary derived map or uncharacterized functor is introduced.

The proof-only nodes `lem-a1-finite-etale-weil-fibre-comparison` and
`lem-a1-finite-weil-sections-decomposition` have no Lean records or Mathlib matches
in the current DAG, hence no proof imports are available. Their complete mathematical
argument is carried in the theorem docstring: stable finite blocks, the nonzero
eigenvector component giving λ^e=α, q_x=q_y^e, and the positive-root norm calculation.
Neither prerequisite is needed to type this statement.

Edge cases checked: the empty scheme, empty fibres and zero sheaves give no eigenvalues;
non-surjective finite etale maps therefore need no added hypothesis. At an identity map
the return exponent is one. Over a degree-e residue extension the eigenvalues acquire
e-th roots but q_x=q_y^e exactly compensates, including negative and nonintegral w.
Jordan blocks cause no issue: the argument uses an eigenvector, not diagonalization.
Nonreduced base schemes and disconnected schemes are included. There is no lissity,
surjectivity, semisimplicity, smoothness, connectedness, or positivity hypothesis.

Searches:

- `msearch.py`, leanfinder, "Finite etale pushforward of a punctually pure Weil sheaf
  preserves its weight": eight ordinary module pushforward and natural-isomorphism
  hits, none stating the Weil eigenvalue assertion.
- `msearch.py`, loogle, `"Weil", "Pure"`: zero hits.
- `msearch.py`, grep, `punctually|PunctuallyPure|WeilSheaf|lowerStar_of_isFinite`:
  zero Mathlib hits.
- `msearch.py`, leansearch, "A finite etale direct image preserves punctual purity of
  l-adic sheaves": eight hits on etale algebras/morphisms and finite implies proper;
  no purity-preservation theorem.
- `rg` on the source project, the upstream-name inventory, and `lean/Sheaf` found
  the existing `WeilSheaf.IsPunctuallyPureOfWeight.lowerStar_of_isFinite`, in
  `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage`; its current full
  source was read with `scompile.py --source`. It omits etaleness, accepts an
  arbitrary coefficient ring embedding, and has a quasi-separatedness assumption
  on the target. It is a broader result, not the exact finite-etale signature here.
  No exact declaration was found. The newly chosen declaration name has no hit.

The item's statement, statement dependencies, proof and proof dependencies are unchanged.
The only node field changed is `lean`. No new nodes or dependency modules are delivered.
All variables and the universe are explicit, with `autoImplicit false` in the module.

Validation: `scompile.py Q47 lem-a1-finite-map-purity` passed the delivered file,
both sandbox and library-module compilation, with no errors or warnings. The library
module invocation took 13.9 seconds, within its 60-second limit.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

Independent second reading by Q47 (2026-10-18): I read the immutable item node and source place, the master and main-20261015 blueprint statements/proof, and the delivered module. Clause-by-clause, the Lean theorem introduces a finite field `k₀`, prime coefficient `l` distinct from `ringChar k₀`, a ring isomorphism `ι`, arbitrary real weight `w`, schemes `X,Y` over `Spec k₀` in the same universe, an over-morphism `π`, finite and étale instances, and the finite-type target encoded by locally finite type plus quasi-compactness. It assumes exactly the node hypothesis that `F` is punctually `ι`-pure of weight `w`, and concludes that the canonical `WeilSheaf.lowerStar π` has the identical purity predicate and weight. No conclusion clause is omitted or strengthened; no lissity, properness, connectedness, smoothness, semisimplicity, surjectivity, or positivity assumption is added. The explicit finite-type instances are the Lean encoding required by the recorded `lowerStar` interface and the source convention that the target is finite type over the finite field.

I opened the recorded declarations for `def-weil-punctual-weights`, `def-weil-weil-sheaf-complex`, `def-weil-derived-direct-image`, and the scheme conventions, and checked the exact `IsPunctuallyPureOfWeight` and `lowerStar` definitions. The imports use those existing notions; no private replacement or pro-etale substitute is introduced. The module and theorem docstrings identify the source place and blueprint and give the three proof steps (finite Frobenius blocks, eigenvector power relation, and the residue-cardinality norm calculation). The theorem proof is only `sorry`, as required for stage 2, and `autoImplicit false` leaves no unbound variables.

Edge cases checked include empty schemes/fibres and the zero sheaf (vacuous eigenvalue condition), the identity map (`e=1`), arbitrary positive residue degree, disconnected and nonreduced schemes, negative or nonintegral real weights, and non-semisimple Frobenius (the proof uses one eigenvector and does not assume diagonalisation). The finite-field relation `q_x=q_y^e` and positive-root argument cover every `e≥1` case.

I searched the project and source clone for duplicate purity/direct-image declarations and inspected the existing finite direct-image purity theorem. It is a different, broader finite-morphism theorem with a different coefficient-map and quasi-separatedness interface, so the delivered finite-étale declaration is not a duplicate. The two proof-only prerequisites named in the proof are not DAG/Lean declarations; they are carried as the theorem's documented proof route and do not alter the statement.

Reproduction: `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q47 lem-a1-finite-map-purity snapshot/lean/Sheaf/DeligneLaumon/Reduction/FiniteMapPurity.lean` compiled both sandbox and library modules successfully, with no errors or warnings. No lake/global build, live Lean write, git mutation, or project-clone edit was performed. The only correction is this complete independent second-reading report section, replacing the prior placeholder.
