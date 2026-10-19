## Worker report

Item: `cor-sf-direct-image-ctf-proetale`, group NJ, stage 2, 2026-10-16.

The module `Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage` states
`AlgebraicGeometry.ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude`.
Its only declaration is a theorem with the proof `by sorry`; no definition, helper,
axiom, new DAG node, or dependency-node repair is introduced. The item's node copy
changes only `lean`. The theorem docstring records all six proof steps from the node.

Source read: the full statement and proof of blueprint
`sec-six-functors/sk-cor-sf-direct-image-ctf/cor-sf-direct-image-ctf-proetale.md`, order 2195,
from the local literature copy. Also read the complete assigned node, the statements
and recorded Lean interfaces of all eight statement dependencies, their source
declarations/docstrings, the stage-2 contract, its example CompactObject module/node,
and `coord/pefw-upstream-framework.md`. The proof docstring follows the corrected DAG
argument: quasi-separatedness follows from separatedness, rather than from finite type
alone as the original blueprint proof sentence asserted.

Each hypothesis and clause is rendered as follows:

| Node text | Lean rendering |
|---|---|
| The fixed global finite-field datum, including `p`, `q`, `k₀`, and the fixed algebraic closure `k` | `D : WeilConjectures.FiniteFieldDatum.{u}`; `D.k` is used in the base spectrum. Its recorded fields contain primality, the positive exponent, cardinality, and the algebraic closure structure. |
| A prime `ℓ ≠ p` | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`. |
| The finite extension `E/ℚ_ℓ` implicit in `A_{E,n}` | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. |
| Positive coefficient level `n ≥ 1` | `(n : ℕ) (hn : 1 ≤ n)`. |
| The coefficient ring `A = A_{E,n}` | Every object, predicate and functor uses the same `Padic.coefficientExtensionRing l E n`, the recorded quotient of the recorded valuation ring by the power of its chosen uniformizer. No unrelated coefficient ring is substituted. |
| Schemes `X,Y` over the algebraic closure `k` | `(X Y : Over (Spec (CommRingCat.of D.k)))`. Their schemes are `X.left` and `Y.left`, and the structure maps are `X.hom`, `Y.hom`. |
| `X,Y` finite type over `k` | `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` and the same two classes for `Y.hom`, precisely the recorded finite-type convention. |
| The morphism `f : X → Y` between those `k`-schemes | `(f : X ⟶ Y)` in the over category. Its underlying morphism is `f.left`, and the over-category commutativity is the structure-map compatibility. |
| `f` separated and finite type | `[IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]`. |
| The source dimension bound `dim X ≤ d` | `(d : ℕ) (hd : topologicalKrullDim X.left ≤ (d : WithBot ℕ∞))`, using the recorded extended dimension, including dimension minus infinity for the empty scheme. |
| The interval endpoints `a,b` | `(a b : ℤ)`. |
| An arbitrary complex on the small pro-étale site with coefficients `A` | `{K : Scheme.proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E n)}`. This is the recorded constant-ring-sheaf module category, with site objects at universe `u+1` and site morphisms at universe `u`. |
| Membership `K ∈ Dᵇ_ctf(X,A)` | `hK : WeilConjectures.finiteTorConstructible l E n hn X.left K`, the recorded conjunction of intrinsic bounded constructibility and finite Tor amplitude. |
| The specified input interval `[a,b]` | `hTor : Scheme.HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E n) K a b`. Its definition includes the ordered interval and tests every module sheaf in degree zero, on all K-flat representatives. |
| The actual finite-level `Rf_*K` | `(Scheme.proEtaleConstantDerivedDirectImage f.left (Padic.coefficientExtensionRing l E n)).obj K`, the recorded canonical sectionwise module pushforward's total right derived functor. |
| Output bounded constructibility on `Y_Proet` | The first conjunct is `Scheme.intrinsicFiniteTorsionConstructible l E n hn Y.left` applied to that image. It asserts finite support of cohomology degrees and intrinsic constructibility of every cohomology sheaf. |
| The exact output Tor interval `[a,b+2d]` | The second conjunct is `Scheme.HasProEtaleTorAmplitude Y.left ... ... a (b + 2 * (d : ℤ))`. The lower bound is unchanged, and the upper bound is exactly the source-dimension shift. |
| All intrinsic finite-Tor constructible objects, with no restriction to étale origin | `K` is universally quantified in the intrinsic category; neither a preimage on the étale site nor an origin isomorphism occurs among the hypotheses. The origin comparison is only in the postponed proof. |

The output's intrinsic constructibility and explicit Tor interval imply its membership
in the recorded finite-Tor constructible category. There is no additional output
clause. Neither properness nor separatedness of `X.hom` or `Y.hom`, a compactification,
a site-perfect model, nor a comparison isomorphism is assumed.

Dependency interfaces used, after reading their full signatures and docstrings:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum` and its recorded field/closure instances.
- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports
  `Padic.coefficientExtensionRing` from `CoefficientExtension` and supplies
  `Padic.finite_coefficientExtensionRing`; the intrinsic predicate supplies this
  finiteness internally from `hn`.
- `def-weil-finite-torsion-constructibility`:
  `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`,
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitude`,
  `WeilConjectures.finiteTorConstructible`; it imports the recorded
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude` from
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude` for the specified interval.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its imported QuasiCompact module,
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  using its reexported `AlgebraicGeometry.IsSeparated`, not `IsProper` as a hypothesis.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`.
- `def-weil-derived-direct-image`: `Sheaf.Paper.SfDerivedDirectImage` reexports
  `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage`, whose full signature
  accepts an arbitrary finite-level complex in the recorded category. The similarly
  named `sfFiniteDerivedDirectImage` applies to reductions of integral objects and is
  not substituted for direct image on an arbitrary finite-level `K`.

Proof-only imports include the recorded `Sheaf.Paper.ProEtaleConstructibleOrigin`
and the Mathlib modules supplying the properness/finite-presentation/immersion
permanence facts. The two proof dependencies `lem-sf-comparison-tor-amplitude` and
`cor-sf-direct-image-ctf-nonproper` have no recorded Lean module; neither is needed to
write this statement. They remain named explicitly in its proof docstring.

One recorded proof-only import cannot coexist with the statement dependencies:
`Sheaf.AlgebraicGeometry.ComparisonDirectImage` imports
`WeilConjectures.SixFunctors.ProEtale.Comparison`, then `Comparison.LowerStarAcyclic`,
then the legacy `ProEtale.UpperLowerStar.Defs`. The intrinsic predicates and canonical
image import the published `ProEtale.FiniteCoefficient.UpperLowerStar.Defs` through
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`. The compiler rejects both together:
`environment already contains 'AlgebraicGeometry.ProEtale.«term(_)_*[_]»'`.
This was confirmed both locally and on the server. Following the launcher's explicit
duplicate-import repair instruction, the final module imports the finite-coefficient
side needed by its statement and omits the incompatible legacy proof-only module.
The canonical comparison dependency and its role are retained in the proof docstring;
no replacement notion or arbitrary comparison is introduced. This is a proof-import
compatibility issue for the maintainer to retain when regenerating imports, not a
missing object needed in this statement.

Edge cases checked before finalizing the signature:

- The empty source scheme is allowed: dimension is bottom, and there is no
  nonemptiness assumption. The empty target is also allowed when the morphism exists.
- The zero complex is allowed. No nonzero cohomology or nontriviality assumption is
  imposed on the input.
- `d = 0` gives the same interval `[a,b]` on output.
- `a = b` and negative integer endpoints remain allowed. The interval-order condition
  is exactly the existing Tor-amplitude definition, not a new assumption.
- `n = 1` is included; `n = 0` is excluded exactly as in the source. Finite ramified
  extensions and every prime different from `D.p` remain available.
- Nonproper separated finite-type maps, such as open immersions between finite-type
  schemes, are allowed. There is no absolute separatedness assumption on either scheme.
- The recorded small-site object and morphism universes are retained. No independent
  universe restriction on test module sheaves or auxiliary geometric points is imposed.

Searches performed (2026-10-16):

1. `msearch.py ... leanfinder`: query
   `Derived direct image for a separated finite type map over an algebraically closed field preserves intrinsic bounded constructible pro-etale module complexes and Tor interval [a,b+2d]`.
   Result: eight unrelated hits, including finite-type/étale composition and an
   étale-locus theorem; no intrinsic derived direct-image theorem.
2. `msearch.py ... loogle`: query `"ProEtale", "torAmplitudeIn"`.
   Result: zero hits.
3. `msearch.py ... grep`: query
   `torAmplitudeIn|HasProEtaleTorAmplitude|boundedConstructible`, restricted to
   `AlgebraicGeometry/Sites`. Result: zero Mathlib hits.
4. `msearch.py ... leansearch`: query
   `Intrinsic bounded constructible complexes with finite Tor amplitude on the small pro-etale site are preserved by derived direct image for separated finite type scheme morphisms`.
   Result: service unavailable, Internal Server Error, as recorded by the search tool.
5. `rg` in the slopmaster2 `WeilConjectures` tree, the published `lean/WeilConjectures`
   tree, and `lean/Sheaf`: queried `finiteTorConstructible`,
   `intrinsicFiniteTorsionConstructible`, `HasProEtaleTorAmplitude`,
   `proEtaleConstantDerivedDirectImage`, and direct-image/bounded-constructibility names.
   Result: the recorded definitions and interfaces were found and reused, with no
   theorem on these intrinsic definitions stating this item.
6. Search for the item id in slopmaster2 found only the general preservation-summary
   documentation. The newer published
   `WeilConjectures.SixFunctors.ProEtale.Derived.Stability` contains
   `AlgebraicGeometry.ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar`.
   Its full signature and module docstring were read: the constructible condition there
   is defined as étale origin and uses a module-valued-sheaf presentation plus a
   generic invertible torsion exponent. It does not state this node using the recorded
   intrinsic predicates and quotient coefficients, so it is not an exact existing
   attachment. No private copy of any of its definitions is made.
7. Exact-name `rg` across both project roots and Mathlib found no prior declaration
   `finiteCoefficientDirectImage_boundedConstructible_torAmplitude`.

Validation: the final module passed `scompile.py NJ cor-sf-direct-image-ctf-proetale`
with exit 0 and no errors or warnings, compiling both the sandbox and the module in
its actual library path. All checks used the authorized wrapper, without a global
build. The signature is copied verbatim from `theorem` to before `:=` into `lean.statement`.
No statement correction or mathematical dispute was found. The mandatory dry run is
the final step; the independent second reading is left to the second worker.

## Second reading by NJ

I independently reread the node JSON, its blueprint source place, every statement
dependency record, and the declaration in the module. The node's objects, hypotheses,
and conclusion render as follows.

1. The fixed global finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{u}`;
   its `p`, `q`, `k₀`, and algebraically closed `k` fields are used exactly as recorded.
   Verdict: same object and conventions.
2. The coefficient prime is `(l : ℕ) [Fact l.Prime]` with `hl : l ≠ D.p`.
   Verdict: both primality and the distinctness hypothesis are present.
3. The finite coefficient extension is `(E : Type u) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, and the level is
   `(n : ℕ) (hn : 1 ≤ n)`; every occurrence uses
   `Padic.coefficientExtensionRing l E n`.
   Verdict: the same finite extension, chosen coefficient ring, and positive level.
4. `X` and `Y` are `Over (Spec (CommRingCat.of D.k))`, with
   `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` and the corresponding two
   instances for `Y.hom`.
   Verdict: these are precisely finite-type schemes over the fixed algebraic closure.
5. `f : X ⟶ Y` is a morphism in that over-category, with
   `[IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]`.
   Verdict: separated and finite-type hypotheses are present, with the over-map
   compatibility retained by the bundled morphism.
6. The dimension assumption is `(d : ℕ)` and
   `hd : topologicalKrullDim X.left ≤ (d : WithBot ℕ∞)`.
   Verdict: the recorded extended Krull dimension includes the empty scheme and the
   exact source bound.
7. The input is an arbitrary
   `{K : Scheme.proEtaleDerivedCategory X.left
   (Padic.coefficientExtensionRing l E n)}` with
   `hK : WeilConjectures.finiteTorConstructible l E n hn X.left K` and the specified
   `hTor : Scheme.HasProEtaleTorAmplitude X.left ... K a b`.
   Verdict: this is the intrinsic bounded constructible finite-Tor category together
   with the stated interval; no étale-origin restriction is introduced.
8. The conclusion is the conjunction of
   `Scheme.intrinsicFiniteTorsionConstructible ... Y.left` for
   `(Scheme.proEtaleConstantDerivedDirectImage f.left ...).obj K` and
   `Scheme.HasProEtaleTorAmplitude Y.left ...` for the same object in
   `[a, b + 2 * (d : ℤ)]`.
   Verdict: both output clauses, their quantifier order, the unchanged lower endpoint,
   and the exact `2d` upper shift agree with the node.

Edge cases checked: the empty source or target scheme is admitted; `d = 0`, `a = b`,
and negative endpoints are admitted subject only to the interval predicate; the zero
complex is admitted; `n = 1` is admitted while `n = 0` is excluded by the source;
all primes distinct from `D.p` and finite coefficient extensions remain allowed; and
the recorded small pro-étale site universes are used without an extra equality or
nonemptiness assumption.

Searches were repeated with `msearch.py` (LeanFinder, Loogle, and LeanSearch), exact
name and semantic `rg` searches through Mathlib, `WeilConjectures`, and `Sheaf`, and
inspection of the upstream `Stability.lean` theorem. The upstream theorem
`AlgebraicGeometry.ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar`
uses a different étale-origin/module-sheaf interface and therefore is not an exact
declaration of this intrinsic quotient-coefficient statement. No exact existing
declaration was found.

No mismatch was found and no source-based correction was needed. The module compiled
cleanly with the required `scompile.py` wrapper; its `lean.statement` is verbatim the
theorem signature through the conclusion.
