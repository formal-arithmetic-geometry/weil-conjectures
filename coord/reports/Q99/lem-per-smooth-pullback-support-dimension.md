## Worker report

This delivery states `AlgebraicGeometry.Scheme.pbcSmoothPullbackSupportDimension` in
`Sheaf.Paper.SmoothPullbackSupportDimension`, with `sorry` as its entire proof. It
states the standard cohomology comparison for smooth shifted pullback and the
literal support-dimension inequality of the item. No mathematical statement of the
item was changed, and no proof was attempted. Two dependency interfaces are extended
under section 1(B). Their old declarations remain publicly imported. The existing
landed `lem-per-adic-heart-pullback-fibres` is added to `stmt_deps` because its `Base`
record is used to bundle exactly the finite-type separated scheme hypotheses.

Hypothesis and clause correspondence:

- A field k is `{k : Type u} [Field k]`; `X Y : PerAdic.Base k` contain schemes in
  universe u with their maps to `Spec k`, locally finite type, quasi-compact, and
  separated structure morphisms. These are exactly separated finite-type k-schemes.
  `PerAdic.baseNoetherian` and `PerAdic.baseDimension` supply the consequences needed
  to form the recorded coefficient categories, without further hypotheses.
- The coefficient prime, its primality, its Q_l, and the algebraic closure are
  `l : ℕ`, `[Fact l.Prime]`, `ℚ_[l]`, and `Ω : Type w` with its field, Q_l-algebra
  and `IsAlgClosure` instances. Universe w is independent of u.
- `iX` and `iY` express invertibility of l in all local rings. These are precisely
  the scheme-level hypotheses already imposed by def-weil-pbc-qbar-category and
  used by its integral finite stages. No invertibility in the base field is added.
- The morphism is `f : X.scheme ⟶ Y.scheme`; `d : ℕ` and
  `[SmoothOfRelativeDimension d f]` are the recorded constant smooth relative
  dimension. The node's d is nonnegative. It is explicitly cast to ℤ in shifts and
  cohomological indices, and to `WithBot ℕ∞` in dimension arithmetic.
- The bounded constructible Qbar category is literally `pbcQbarCategory l Ω` on
  the two schemes. The theorem quantifies over all its objects K and all i : ℤ.
- `pbcQbarCompletedPull l Ω f` is the actual completed integral pullback restricted
  to constructible objects, rationalized using the recorded functor, with the
  normalized scalar comparison, and descended to the same common-stage category.
  It is not an unspecified functor and is not pullback of a discrete Qbar sheaf.
- The first conjunct says this pullback preserves both halves of the standard
  t-structure at every integer bound. Thus it restricts to the ordinary degree-zero
  inverse image of the constructible heart and, being triangulated pullback, is
  exact there. `pbcQbarStandardT` is uniquely determined by the strictly full images
  of the existing integral standard classes, so these are exactly the standard
  cohomological halves and not an arbitrary t-structure.
- The second conjunct is a natural isomorphism of functors, for each i, between
  `Lf* ⋙ [d] ⋙ H^(-i)` and `H^(-i+d) ⋙ Lf*`. Its components give exactly
  H^(-i)(Lf*K[d]) ≅ f*H^(-i+d)(K), with the cohomology objects placed in degree zero
  inside the standard heart. The proof docstring specifies the canonical
  construction: the unique identity-on-the-middle-term comparisons of canonical
  truncation triangles, followed by the ordinary shift comparison. Naturality
  includes all common-stage arrows, not just a pointwise isomorphism of fibres.
- The final conjunct uses `pbcQbarCohomologySupport` from the recorded
  def-per-support-condition, applied to the explicitly shifted pulled-back object
  and to K at degree `-i + (d : ℤ)`. Its conclusion is exactly
  `topologicalKrullDim support_left ≤ topologicalKrullDim support_right + d`.
  `topologicalKrullDim : WithBot ℕ∞` represents dimension -infinity by bottom.

Dependency declarations read and used:

- `Sheaf.Paper.PbcQbarCategory`: `Scheme.pbcQbarCategory`, its actual finite-stage
  scalar system, and its recorded common-stage shift/triangulation.
- `Sheaf.Paper.PbcSupportCondition`: `Scheme.pbcQbarCohomologySupport`, the closure
  of the nonzero adic geometric-cohomology-fibre locus. Its imported
  `PbcCohomologySheaves.pbcQbarCohomologyFibre` is retained unchanged.
- `Sheaf.Paper.PbcCohomologySheaves`: `pbcStageCohomology`,
  `pbcRationalCohomology`, and the completed/rational geometric fibre declarations.
  They use the ambient `DerivedCategory.homologyFunctor` exactly as recorded.
- `Sheaf.Paper.PbcActualStrictPullback`: `pbcActualStrictCompletedPull` and its
  unit-compatible comparison `pbcActualCompletedPullback_tower` to
  `PbcCompletedPullbackActual.pbcActualCompletedPull`.
- `Sheaf.Paper.PbcDescentFunctors`: `pbcDescentPullback` and
  `PbcPullbackBetaSpec`; the latter fixes the actual completed scalar beta maps.
- `Sheaf.Paper.IntegralTStructure`: `pbcIntegralTStructure` on each finite integral
  category; `Sheaf.Paper.LocalizedTStructure.pbc_localized_tstructure` supplies the
  strictly full rational images, rather than cohomology vanishing on every lattice.
- `Sheaf.Paper.AdicHeartPullbackFibres`: `PerAdic.Base`, `baseNoetherian`,
  `baseDimension`, and the documented cohomology, canonical common pullback, and
  geometric-fibre clauses of `adicHeartPullbackFibres`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension` (its
  full affine standard-smooth-chart signature and docstring were read).
  `def-weil-scheme-morphism-properties` is a convention record with no declaration;
  its finite-type/separated properties are the existing Mathlib classes in `Base`.
- Proof-only imports give the recorded constructible closure-dimension theorem,
  smooth local dimension theorem, reduced induced closed subscheme, dimension as
  the supremum of local dimensions, abstract heart short-exact triangles, smooth
  relative-dimension permanence, closed-immersion base change, noetherianity,
  constructible subsets, and topological Krull dimension.

Edge cases checked against the definitions and the source:

- Empty X or Y is allowed by `Base` and by the scheme-local invertibility binders.
  In particular, when char(k) = l, the allowed schemes are empty; this case is not
  excluded by an extra coefficient condition on k.
- Zero K and vanishing cohomology have empty support. Its dimension is bottom and
  bottom plus the finite relative dimension remains bottom, so the displayed
  inequality has the intended meaning even at negative cohomological indices.
- d = 0 is permitted, including etale maps, identities, and empty smooth maps.
  The index becomes -i and the added dimension is zero.
- f need not be surjective onto a support. Empty pulled-back support satisfies the
  inequality. No nonemptiness, connectedness, or smoothness of X or Y over k was
  imposed.
- Constructible support need not be closed. The recorded support is its closure;
  the proof uses the reduced closure and the constructible closure-dimension lemma
  over a field, never an unprovided reduced scheme structure on a nonclosed locus.
- All integer degrees and arbitrary coefficient universes are retained. A rational
  representative may have integral torsion in other degrees; using strictly full
  integral image classes avoids incorrectly excluding such representatives.

Searches performed before writing:

- `msearch.py ... leanfinder`, query: "For a smooth morphism of relative dimension d
  pullback of a constructible adic complex commutes with cohomology and raises
  support dimension by at most d". Eight results: smooth composition/base-change
  and module pullback facts; none states the cohomology/support estimate.
- `msearch.py ... loogle`, query:
  `DerivedCategory.homologyFunctor, SmoothOfRelativeDimension, topologicalKrullDim`.
  Zero hits; the service reported unknown identifier SmoothOfRelativeDimension.
- `msearch.py ... grep`, query:
  `support.*pullback|pullback.*support|cohomology.*[sS]mooth`, AlgebraicGeometry.
  One result in IdealSheaf/Functorial concerns ideal-sheaf support and does not
  concern constructible adic cohomology.
- `msearch.py ... leansearch`, query: "smooth inverse image of bounded constructible
  adic complex cohomology support dimension". Eight results: ideal-sheaf support,
  smooth loci, manifold support, and smooth composition; no matching statement.
- `rg` in all of the upstream WeilConjectures tree, Mathlib and the shared Sheaf
  tree for the proposed declaration names found no collision. Concept searches in
  upstream and side sources found the recorded PerAdic t-structures and pullback;
  their full signatures were read. They require a unit in k, rather than just on
  the scheme, so they cannot directly state the characteristic-l empty cases.
- Searching the upstream sources and `dag/lean_names_upstream.json` for the item's
  exact id found no existing declaration. The existing node's proof and the current
  blueprint first paragraph were compared directly with Stacks
  `morphisms.tex`, `lemma-smoothness-dimension` (Tag 0AFF).

No STATEMENT-DISPUTED claim or source-based statement correction is needed.

## Dependency modules

`def-weil-derived-cohomology-sheaves`: the recorded interface supplies ambient
integral cohomology and rational finite-stage cohomology/fibres, but has no
cohomology object functor with domain the common-stage `pbcQbarCategory`. The
existing `PerAdic.commonT` specialization requires l invertible in k, although the
item's coefficient category only requires invertibility on X and Y. The new
`Sheaf.Paper.PbcQbarStandardCohomology` publicly retains all the old declarations,
defines the same strictly full standard classes from the existing integral
classes, names the unique common-stage t-structure with those classes, and gives
its literal truncation-and-shift cohomology functor. The existence/uniqueness
statement has the complete descent proof in its docstring. The construction
introduces no arbitrary t-structure and no new coefficient category. Only this
dependency node's `lean` record is changed.

`def-weil-pbc-completed-pullback`: the recorded strict-tower construction is
integral and ambient. The actual Qbar functor is needed by the item's statement,
while the already provided `PerAdic.commonPull` again assumes l invertible in k.
The new `Sheaf.Paper.PbcQbarCompletedPullback` publicly imports that strict-tower
interface and defines the same operation on Qbar objects using the recorded
`pbcDescentPullback` and scalar comparison characterization. The constructible
restriction theorem and uniquely characterized coherent-family theorem carry
complete source/proof docstrings. The uniqueness includes all finite-stage
functors and every actual beta component, so no arbitrary compatible family is
selected. Both original and new interfaces remain available. Only this dependency
node's `lean` record is changed.

## Second reading by Q99

Independent reading by the maintainer's second reader (NT-cc review service, run 2,
2026-10-18), replacing the worker's self-check. The reader opened the node, its seven
stmt_deps, Stacks morphisms.tex lemma-smoothness-dimension (Tag 0AFF), and the three
delivered modules. It also opened the upstream declarations they use:
PerAdic.Base/commonT/commonPull, pbcDescentPullback, PbcPullbackBetaSpec,
pbcIntegralTStructure, pbcStageLocalization, pbcQbarCohomologySupport and
pbcQbarCohomologyFibre.

Node list and Lean, item by item:

- Field k: `{k : Type u} [Field k]`. Same.
- f : X -> Y between separated schemes of finite type over k: `X Y : PerAdic.Base k`
  (Over Spec k, LocallyOfFiniteType, QuasiCompact, IsSeparated; no nonemptiness) and
  `f : X.scheme ⟶ Y.scheme`. Same.
- Smooth of constant relative dimension d: `(d : ℕ) [SmoothOfRelativeDimension d f]`,
  the recorded Mathlib class of def-sbc-smooth-morphisms. Same.
- Coefficient categories of def-weil-pbc-qbar-category: `l`, `[Fact l.Prime]`,
  `Ω` with `IsAlgClosure ℚ_[l] Ω`, and `pbcQbarCategory l Ω`. Its requirement that l be
  invertible on the scheme is `iX`, `iY`. `iX` follows from `iY`, but it is harmless and
  needed for the category on X. No unit-in-k hypothesis is added. Same.
- "Derived pullback is exact on cohomology sheaves": conjunct 1 says that
  `pbcQbarCompletedPull` preserves `le n` and `ge n` of the standard t-structure for
  every n. That is t-exactness. Same.
- H^{-i}(Lf*K[d]) ≅ f*H^{-i+d}(K) for every i: conjunct 2 gives a natural isomorphism
  `Lf* ⋙ [d] ⋙ H^{-i} ≅ H^{-i+d} ⋙ Lf*`. The sign is correct, since H^{-i}(M[d]) =
  H^{-i+d}(M). `pbcQbarCohomology n = τ≤n ⋙ τ≥n ⋙ [n]` puts H^n in degree 0, so
  pulling a heart object back by Lf* is f* on the heart. Canonicity is rendered as
  Nonempty of a natural isomorphism. The proof docstring fixes the canonical one. Accepted.
- dim Supp H^{-i}(Lf*K[d]) ≤ dim Supp H^{-i+d}(K) + d: conjunct 3 uses
  `topologicalKrullDim` on `pbcQbarCohomologySupport` (def-per-support-condition: the
  closure of the nonzero adic geometric-fibre locus) plus `(d : WithBot ℕ∞)`. An empty
  support gives ⊥, and ⊥ + d = ⊥. Quantified over all K and i. Same.

Dependency modules: `pbcQbarStandardClass` is the strictly full image of the recorded
integral standard aisles/coaisles at finite stages. Every rational object with
cohomology ≤ n (resp. ≥ n) has such a lattice, by truncating an integral representative
(the cone is torsion). The t-structure is the unique one with these classes, so it is
not arbitrary. `pbcQbarCompletedPull` is the descended family. Its stage functors are
the recorded `pbcDescentPullback`, and its β maps are fixed by `PbcPullbackBetaSpec`.
These are generalizations of `PerAdic.commonT`/`commonPull` that drop the
`IsUnit (l : k)` requirement, so the characteristic-l (empty-scheme) case is not
excluded. They are not private copies, and the existing declarations stay in place.

Edge cases: empty X or Y, characteristic l (forces the schemes to be empty), d = 0, K = 0,
empty pulled-back support, non-closed constructible support (closure), negative indices,
independent universes u and w. All are covered.

Searches: the declaration names do not occur in Mathlib, upstream or the Sheaf tree. The
only near-duplicates are `PerAdic.commonT`/`commonPull`, discussed above.

Mismatches found: none in the Lean. The only change is to this report: this section
replaces the worker's self-check, which delivery-errors A11 does not accept as a
second reading.

## Validation

All three modules are compiled separately, in dependency order, using the prescribed
`scompile.py Q99 lem-per-smooth-pullback-support-dimension` wrapper. Delivery preflight
and final compile results are recorded below after the required dry run.

The initial separate compilation passed without errors or warnings: the two dependency
modules took approximately 4--5 seconds each and the item approximately 5 seconds.
The required `deliver2.py ... --no-push` returned:
`OK (dry run): commit c6ed30c2f9 passes the preflight and compiles; nothing pushed`.
It checked all three modules again separately. The delivered theorem remains a
stage-2 statement with sorry; the uniqueness and restriction helper theorems also
remain sorry as required.
