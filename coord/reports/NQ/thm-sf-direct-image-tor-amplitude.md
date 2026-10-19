## Worker report

The new module `Sheaf.Paper.DirectImageTorAmplitude` states
`AlgebraicGeometry.Etale.sf_directImage_torAmplitude`, with its sole proof `sorry`.
It states both conclusions of the node for the ordinary small-etale derived direct image.
No definition, dependency module, new node, or statement correction was needed.
The theorem docstring carries all seven steps of the node's proof.

Hypothesis and conclusion correspondence (names below are in `AlgebraicGeometry.Etale`
unless otherwise qualified):

| Node clause | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Prime l different from characteristic k | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ ringChar k)` |
| Finite extension E/Q_l | `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| Integer n at least 1 | `(n : ℕ) (hn : 1 ≤ n)`; natural numbers with this inequality encode exactly these positive integers |
| Integer ring, chosen uniformizer and quotient A | Every occurrence of A is `Padic.coefficientExtensionRing l E n`, the recorded quotient by `coefficientExtensionIdeal`, the nth power of the ideal of the recorded chosen uniformizer in the recorded integer ring |
| Finite-type k-schemes X and Y | `X Y : Scheme.{u}`, their structure maps `aX`, `aY` to `Spec (.of k)`, and `LocallyOfFiniteType` and `QuasiCompact` instances on each map |
| k-morphism f | `(f : X ⟶ Y) (_hf : f ≫ aY = aX)` makes the structure maps compatible |
| Separated finite-type f | `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`; `IsSeparated` means its diagonal is a closed immersion |
| Ordinary module-derived categories on the small etale sites | `DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X` and the analogous category on Y; these are the recorded derived categories of `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} A)` |
| Ordinary module-sheaf Rf_* | `rightDerivedLowerStar (ModuleCat.{u+1} A) f`, definitionally `(lowerStar (ModuleCat.{u+1} A) f).rightDerivedFunctor`; the unbounded functor restricts to the recorded bounded-below direct image, with the same K-injective computation |
| Integer N at least zero | `(N : ℤ) (_hN : 0 ≤ N)` |
| Uniform vanishing on every module sheaf M and every r>N | `_hUDV` quantifies over every `M : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A)` and every `r : ℤ`; `N < r` implies `IsZero` of degree-r homology of Rf_* applied to `singleFunctor _ 0` of M |
| The bound is for the present field k | `_hUDV` refers to this X, Y and f; there is no quantification over other fields, no finite-field datum and no constructibility restriction on M |
| Ordered integer endpoints | `(a b : ℤ) (_hab : a ≤ b)` |
| Bounded constructible K | `_hK` uses the recorded `DerivedCategory.isBoundedConstructible` on K |
| Tor amplitude [a,b] against every degree-zero module sheaf | `_hTor : DerivedCategory.hasTorAmplitudeIn A X a b K`; the definition quantifies over every module sheaf in degree zero and vanishing outside the given interval |
| Rf_*K bounded constructible on Y | First conjunct, `DerivedCategory.isBoundedConstructible` on the same derived direct image |
| Rf_*K has Tor amplitude [a,b+N] | Second conjunct, `DerivedCategory.hasTorAmplitudeIn A Y a (b + N)` on the same object |

The two constructibility occurrences supply the `Finite A` argument explicitly as
`Padic.finite_coefficientExtensionRing l E n hn`. This avoids adding a finiteness
hypothesis or installing a file-local instance. The fixed coefficient-universe convention
is exactly that of both recorded etale predicates: schemes in universe u, coefficients
and module sheaves in u+1. All universes and variables are explicitly bound.

Dependency declarations read and used:

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, together with its public import
  `Sheaf.NumberTheory.Padics.CoefficientExtension`, in particular
  `Padic.coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionIdeal` and `coefficientExtensionUniformizer`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; also recorded
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, whose
  separatedness clause is `AlgebraicGeometry.IsSeparated`, defined in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated` by the closed diagonal condition.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `AlgebraicGeometry.Scheme.Etale`,
  available through the public etale framework imports.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`,
  exposing the recorded `AlgebraicGeometry.Etale.DerivedCategoryModule` and Mathlib
  `DerivedCategory.homologyFunctor`; available through the public predicate imports.
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`, used through the existing unbounded wrapper
  `AlgebraicGeometry.Etale.rightDerivedLowerStar` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
- `def-weil-pbc-constructible-complexes`:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`. This tests the
  project's recorded finite-stratification constructibility, rather than substituting
  the different upstream `boundedConstructible` predicate.
- `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` exposes the
  bounded predicate `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` unchanged.
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`, used by that exact Tor-amplitude predicate.

The modules of all stated proof dependencies are imported non-publicly. The Mathlib
leaf `lem-weil-valued-dvr-finite-quotients` contributes
`Mathlib.Topology.Algebra.Valued.LocallyCompact`; its recorded
`Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField` was read.
The import plan includes the Grothendieck-abelian and left-exactness interfaces,
truncation spectral sequence, finite-type constructibility, finite-constant projection
formula and residue Tor test. No unrelated DAG theorem is stated in this delivery.

Edge cases checked: n=1 is included, while n=0 is excluded exactly as in the node;
N=0 is included and gives [a,b]; a=b and arbitrary negative a,b are included;
zero K and empty X or Y are allowed; the universal vanishing predicate does not exclude
nonconstructible test sheaves; every integer r>N is tested. No global dimension bound,
properness, finite base field, projective-dimension hypothesis on the residue field,
or additional Tor bound is imposed. Characteristic zero is included since a prime
is nonzero. The hypotheses and both conclusions use the same coefficient quotient,
site and direct-image functor. No statement fault or disputed clause was found.

Searches before writing (all through the prescribed search wrapper or read-only rg):

- LeanFinder query: "Derived direct image of an etale constructible complex with finite
  Tor amplitude and uniform cohomological dimension bound has Tor amplitude in the
  shifted interval". Eight hits, including `DerivedCategory.IsGE`, `IsLE`, and fraction
  factorizations; none states this result.
- Loogle query: `"rightDerived"`. Twelve hits defining and characterizing total right
  derived functors; none gives this Tor-amplitude bound.
- Mathlib grep query: `TorAmplitude|torAmplitude|tor_amplitude|cohomologicalDimension`.
  Zero hits.
- LeanSearch query: "A derived direct image of finite cohomological dimension preserves
  finite Tor amplitude". Eight hits about exact functors, preserving homology and
  finite colimits; no matching theorem.
- Read-only rg of `WeilConjectures` for the item id and of etale-derived coefficients,
  upper/lower-star modules, and `lean/Sheaf` for Tor-amplitude and direct-image names.
  The closest upstream result is `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`
  in `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage`. Its full signature
  was read: it assumes a dimension bound d and concludes [a,b+2d], uses the upstream
  constructibility/Tor predicates and generic coefficient category, and does not state
  the arbitrary assumed N bound or the conjunction here. It is not an exact existing
  declaration for this node. Existing pullback and site-comparison results also differ.

Validation: the prescribed `scompile.py NQ thm-sf-direct-image-tor-amplitude` compiled
this file cleanly, including its side-only projection-formula and residue-test imports.
The final delivery dry run is run after this report and the node record are complete.
The independent second reader will add its own reading and deliver; no push was made.

## Second reading by NQ

I independently read the sandbox node and module against the blueprint source
`sec-six-functors/sk-prop-sf-rf-shriek-preservation/thm-sf-direct-image-tor-amplitude.md`,
including its entire proof. I also read the source of the UDV definition in
`sec-smooth-purity/sk-prop-sf-fullcd-etale-origin/def-sf-uniform-direct-image-vanishing.md`.
That definition is written for the global finite-field datum; the present node expressly
spells out the same vanishing predicate for the present algebraically closed field.
The theorem correctly uses that displayed predicate and does not add a finite-field datum.
There is no statement_change, new node, or dependency module in this delivery.

My object/hypothesis/conclusion inventory and its correspondence with the Lean is below.
Names without a prefix are in `AlgebraicGeometry.Etale`; write A here for the literal
term `Padic.coefficientExtensionRing l E n`, not an additional Lean abbreviation.

| Node item | Lean rendering and verdict |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]`; exact. |
| Prime l different from char(k) | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ ringChar k)`; exact, including characteristic zero. |
| Finite extension E of Q_l | `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; exact field extension and vector-space finiteness, with no extra normed-field structure assumed. |
| Integer n at least one | `(n : ℕ) (hn : 1 ≤ n)`; exact encoding of positive integer levels. |
| Integer ring, chosen uniformizer, and A = O_E / uniformizer^n | Every coefficient is the same literal term A. I read `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionIdeal`, and `coefficientExtensionRing` in `Sheaf.NumberTheory.Padics.CoefficientExtension`: the ring is the recorded quotient by `(Ideal.span {uniformizer}) ^ n`; exact. The uniformizer is the one chosen by the dependency, not arbitrary new data. |
| Finite-type k-schemes X and Y | `{X Y : Scheme.{u}}`, structure maps `aX`, `aY` to `Spec (.of k)`, and `[LocallyOfFiniteType aX] [QuasiCompact aX]` and the analogous instances on `aY`; exact. |
| Morphism f over k | `(f : X ⟶ Y) (_hf : f ≫ aY = aX)`; exact compatibility of the structure maps. |
| Separated finite-type f | `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`; exact. I opened the Mathlib classes: separatedness is the closed-immersion diagonal, and finite type is locally finite type plus quasi-compact. Properness is not assumed. |
| Small etale sites | `X.smallEtaleTopology` and its Y analogue; I opened Mathlib's definition as `smallGrothendieckTopology @Etale`, with coverings given by jointly surjective etale families; exact. |
| Ordinary derived categories of A-module sheaves | `DerivedCategoryModule A X` and the corresponding Y category. I read the upstream abbreviation in `Derived.Coefficients`: it is `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))`; exact. |
| Module-sheaf derived direct image | `rightDerivedLowerStar (ModuleCat.{u + 1} A) f` throughout. I opened its definition in `Derived.UpperLowerStarCoherence` and the recorded `lowerStar` in `UpperLowerStar.Defs`: it is the total right derived functor of ordinary base-change precomposition on module sheaves. The bounded-below version is the same functor's `rightDerivedFunctorPlus`; exact on these bounded-below inputs. |
| Fixed nonnegative integer N | `(N : ℤ) (_hN : 0 ≤ N)`; exact, with no dimension bound imposed. |
| UDV for all sheaves M and all integers r>N | `_hUDV` universally quantifies over `M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` and `r : ℤ`, with condition `N < r`. Its value is `IsZero` of the r-th `homologyFunctor` of this direct image on `(singleFunctor _ 0).obj M`; exactly R^r f_*M = 0, without constructibility or finiteness conditions on M. |
| Ordered integer endpoints a,b | `(a b : ℤ) (_hab : a ≤ b)`; exact order and signs. |
| K in D(X_et,A) | `(K : DerivedCategoryModule A X)`; the same coefficient ring and site as in UDV. |
| K bounded constructible | `_hK : @DerivedCategory.isBoundedConstructible A _ (Padic.finite_coefficientExtensionRing l E n hn) X K`; exact. I opened the recorded definition: all cohomology sheaves satisfy the recorded finite-stratification constructibility predicate, and they vanish outside some ordered integer interval. The explicit finite-ring proof is supplied by the dependency, rather than an extra hypothesis. |
| Tor amplitude [a,b] against all degree-zero module sheaves | `_hTor : DerivedCategory.hasTorAmplitudeIn A X a b K`; exact. I read its upstream body: every module sheaf F and every integer q with `q < a ∨ b < q` gives `IsZero` of H^q of `derivedTensor K ((singleFunctor _ 0).obj F)`. |
| Ordinary etale derived tensor | The preceding predicate uses `derivedTensor (ModuleCat.{u + 1} A) X`. I opened `Derived.Tensor`: this is the curried tensor of the unbounded derived monoidal structure from K-flat left derivability; exact, with no perfectness or finite projective-dimension restriction on test sheaves. |
| Rf_*K bounded constructible on Y | First conjunct is `@DerivedCategory.isBoundedConstructible A _ (Padic.finite_coefficientExtensionRing l E n hn) Y` applied to the very same direct-image object; exact. |
| Rf_*K has Tor amplitude [a,b+N] | Second conjunct is `DerivedCategory.hasTorAmplitudeIn A Y a (b + N)` of that object; exact endpoints and quantifier order. |

I opened all nine statement-dependency nodes and their recorded declarations, not only
the signatures quoted by the first worker. In particular I read the mixed records for
derived categories and Tor amplitude and used their existing bounded-interval predicate;
the recorded public modules expose it without a private replacement. I also read the
coefficient finiteness theorem and the determining integer-ring/maximal-ideal conditions
of `Padic.extension_integers_dvr`. The integer ring and maximal ideal selected there are
determined by membership conditions; the chosen uniformizer is authorized by the
coefficient definition. The new module contains no definition and hence introduces no
hollow data.

For the source conventions I read Stacks `sites-cohomology.tex`,
`definition-tor-amplitude` (08FZ): a ringed site, arbitrary module test sheaves, ordered
integer endpoints. I read `derived.tex`, `lemma-two-ss-complex-functor` (015J): a left
exact functor of abelian categories and a bounded-below complex, with finite abutment
filtrations. I also read `sites-cohomology.tex`, `equation-projection-formula-map` (0B56):
the ordinary unbounded derived canonical map. The module docstring includes all seven
proof steps of the actual node, including the lower truncation, finite filtration
argument, coefficient arithmetic, bounded constructibility, finite-presentation
projection formula and residue test. It does not claim the residue field is perfect.

Edge cases: n=1 is included; n=0 is excluded by the node itself. N=0 and a=b are
included, as are negative endpoints a,b. Empty X and empty Y and the zero complex
require no Nonempty or nonzero hypotheses; a morphism to empty Y is only available in
the expected empty case. There is no index family to which a nonempty restriction
could be applied. Positive characteristic distinct from l and characteristic zero
are both included. UDV includes nonconstructible sheaves and every integer above N.
The site and coefficient universes are precisely those of the recorded ordinary etale
API (`Scheme.{u}` and coefficient/module universe u+1), with no additional equality or
smallness instance on the sites; all binders and universes are declared. Finite
extensions may be represented in that coefficient universe, so this does not impose a
new mathematical finiteness condition.

Independent searches, using different wording from the worker:

- LeanFinder through msearch: "The pushforward derived functor for etale sheaves with
  uniform higher direct image vanishing sends tensor cohomological amplitude a b into
  a b plus N". Eight hits, including IsGE, IsLE, bounded representatives and fraction
  lemmas; no matching theorem.
- LeanSearch through msearch: "A pushforward of finite cohomological dimension preserves
  the finite tensor amplitude of bounded constructible etale complexes". Eight hits
  about ordinary topological, scheme-module and site-module pushforwards, without this
  Tor-amplitude result.
- Loogle through msearch: `"Tor"`. Twelve broad substring hits, no relevant theorem.
  The more informative LeanFinder result above is the semantic search for this notion.
- Mathlib grep through msearch: `tor.?[Aa]mplitude|tensor.?[Aa]mplitude|cohomological.?[Dd]imension`;
  zero hits. Read-only rg of both the project's `lean/Sheaf` and upstream
  `WeilConjectures` for direct-image/Tor-amplitude names and the item id found the
  dimension-bound upstream theorem and the finite-field corollary.
- I opened the full signature of upstream `torAmplitudeIn_rightDerivedLowerStar`:
  it assumes a dimension bound d and gives [a,b+2d], with the upstream
  `boundedConstructible` and `torAmplitudeIn` predicates. I opened the project's
  `directImageCTFNonproper`: it fixes a finite-field datum, also gives [a,b+2d], and
  uses the upstream constructibility predicate. Neither states this node's arbitrary
  assumed N bound over the present algebraically closed field with the recorded
  constructibility predicate. The pro-etale stability theorem concerns a different
  site. None is an exact existing declaration for this node.
- Read-only rg for the proposed full declaration name in Mathlib, upstream Lean,
  the project's Lean and `dag/lean_names_upstream.json` found no collision.

Mismatch inventory: none. I changed no Lean, node statement, dependency list or
record; only this independent review was appended. There are no new nodes or
dependency modules requiring a further stage-1 or H13 audit, and no statement
correction requiring a citer audit. The one theorem remains `:= by sorry`, with
source/blueprint docstrings and no proved auxiliary statement. Its node's
`lean.statement` is verbatim its signature. The single-file wrapper compile passed
cleanly on 2026-10-16 for both the sandbox and library-path checks (2.7s and 2.8s),
with no warnings reported. Delivery preflight is run after this review.
