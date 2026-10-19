## Worker report

The module `Sheaf.Paper.SmoothPurityTowerBound` states
`AlgebraicGeometry.ProEtale.sp_tower_bound`, with one postponed proof. Its two
helper definitions contain real data: `spTowerShriekRealization` is the derived
equivalence induced by the section-normalized `SpTowerShriek.Base.realization`,
and `spTowerCompactSupport` is the recorded compactification operation conjugated
by those source and target equivalences. In particular, this is an operation on
the actual ordinary derived category of `spCoefficientTowers`, not an inverse
system in a derived category. No choice from mere existence is made here.

Hypothesis and clause correspondence:

- The primes p and ell are `p`, `l`, with `[Fact p.Prime]`, `[Fact l.Prime]` and
  `_hlp : l ≠ p`. The positive characteristic field is `(k : Type u) [Field k]
  [CharP k p]`; primality of p supplies p > 0.
- The schemes and their structure maps are `X Y : Over (Spec (CommRingCat.of k))`.
  The instances `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on both
  `X.hom` and `Y.hom` give exactly separated finite type over k. `f : X ⟶ Y` is
  a k-morphism. The same three instances on `f.left` spell out its separated
  finite-type property (already implied by this standing setting).
- The finite coefficient extension is the section variable `E : Type u` with
  `Field E`, `Algebra (Padic l) E`, and `FiniteDimensional (Padic l) E`.
  The integer ring and actual ell-power quotients are the dependency's
  `Padic.coefficientExtensionIntegers` and `SpTowerShriek.R`.
- The bound is `(d : ℕ)`. `_hd` is the disjunction of
  `SmoothOfRelativeDimension d f.left` and the general bound on every geometric
  fibre. The latter quantifies over every separably closed field Ω and geometric
  point `s : Spec Ω ⟶ Y.left` and uses
  `topologicalKrullDim (pullback f.left s) ≤ (d : WithBot ℕ∞)`.
  Separably closed geometric points suffice for this dimension bound; this is
  also the exact convention in the upstream finite-support vanishing theorem
  `Etale.isZero_homology_rightDerivedLowerShriek_singleFunctor`.
- The fixed factorization is `c : Compactification f.left`. Its fields `i`, `g`
  and `comm` give the open immersion, proper map, and equality f = i ≫ g.
- `b : SpTowerShriek.Base l E` and `o : SpTowerShriek.Operations l E b` are the
  published normalized construction interface, not extra geometric or Tor
  assumptions. Their existence is the recorded `tower_shriek_levels` theorem.
  Their ordinary operations are fixed by the section, restriction, transition,
  adjunction and comparison normalizations in that interface. No origin-witness
  or normalized-input hypothesis is imposed. `DX`, `DY` are the recorded
  `SpCoefficientTowersAbelian` presentations supplying the ordinary localizations
  and exact evaluations on X and Y. The theorem works for every such presentation.
- The displayed compactification functor is `spTowerCompactSupport l E b o c DX DY`:
  its central functor `SpTowerShriek.F` is, by definition,
  `openD ... (o.openOp c.i) ⋙ push ... (o.geometry c.g)`.
  Open extension is exact termwise extension by zero, and push is ordinary total
  right derivation. The first conjunct says its restriction to D+ lands in D+,
  expressed by existence of a lower canonical-t-structure bound on both sides.
- The second conjunct is existence of a natural isomorphism of entire functors,
  not just unrelated level-object isomorphisms. The source functors are restricted
  by `DerivedCategory.Plus.ι`. It identifies exact derived evaluation of compact
  support with evaluation followed by `SpTowerShriek.finiteF`, the finite-level
  compactification functor `Rp_* j_!` on precisely the ell-power quotient ring.
- The third conjunct takes exactly `spConstructibleTorTowers ... DX C` and
  concludes its input is bounded below and that the image satisfies exactly
  `spConstructibleTorTowers ... DY`. That existing predicate includes every
  level's bounded constructibility and finite Tor amplitude, a common ordered
  cohomological interval, and a common ordered Tor interval. Neither
  `IsSpNormalizedTower` nor its normalized subcategory appears.

Dependency declarations read and used:

- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`,
  `spEllIdeal`, and the constant ell-power coefficient tower and quotient maps.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with its underlying integer-ring and
  quotient constructions in `CoefficientExtension`; imported transitively by
  the tower module, not recreated.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spDerivedCoefficientTowers`,
  `spDerivedCoefficientEvaluation`, `spConstructibleTorTowers`; these fix exactly
  the original tower category, level categories, and Dctf predicate.
- `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `SpTowerShriek.Base`, `Operations`,
  `D`, `F`, `finiteF`, `Fcomparison`, and `tower_shriek_levels`.
- `Sheaf.Paper.SmoothPurityTowerLevels`: `sp_tower_levels` and its bounded-below
  right-derived direct image and exact evaluation, retained as a proof import.
- `Sheaf.Paper.ConstantModelTorAmplitude`:
  `constantModelConstructibleFiniteTor_wellDefined`; its imported finite-Tor
  conventions and tensor-unit argument are retained as a proof import. The item
  uses the finite-level predicate prescribed by `sk-def-sp-normalized-towers`.
- The setting node's `CondensedRing.compactificationOverField` was read in the
  exact published source through `scompile.py --source` (the local side source
  still has its older unbundled signature). This statement takes the supplied
  compactification c and writes out its scheme setting, so it does not call or
  rechoose that canonical compactification. The specific bounded-constructible
  condensed-category functors of that setting node are not tower functors and
  are not substituted here.
- `CategoryTheory.Equivalence.mapDerivedCategory` from the upstream exact-functor
  module supplies the derived equivalence, with its existing unit/counit data.

The proof docstring carries all four DAG proof steps: common input Tor bounds
imply bounded below by testing with the coefficient unit; clause (1) of tower
shriek levels computes finite evaluations; the finite uniform bound gives
[a,b+2d] independently of n using the ramification identification; testing again
with the unit gives common output cohomological bounds. The proof-only node
`det-sp-tower-bound-uniform` currently has no published Lean module, so there is
no import for it; its mathematical use is documented in the proof plan. It is
not needed to type this statement, and no duplicate theorem for it is introduced.

Edge cases checked: d=0 is retained by Nat; the empty source, empty target and
empty fibres are retained, with topological Krull dimension bottom <= d. Every
positive exponent is represented by natural n as exponent n+1, including n=0
(exponent one). Zero towers and arbitrary nonnormalized transition maps are
allowed. Cohomological and Tor intervals remain independent in the recorded
predicate; negative endpoints and all degrees are retained. Geometric-point
fields live in the scheme universe, as in the upstream finite-support theorem.
The pro-etale site still has object universe u+1 and morphism universe u; its
module coefficients are in u+1. Taking a common ambient u for E, k and the scheme
coordinates follows both recorded interfaces and allows arbitrary sizes by
universe enlargement, without identifying the site's two different universes.

Searches (full service responses in the sandbox's `searches.jsonl`):

- LeanFinder: "Compactly supported derived direct image preserves constructible
  coefficient towers with uniform Tor amplitude": 8 hits, on constructible images,
  strictly supported complexes, and t-structure bounds; no matching theorem.
- Loogle: `"pushforward"`: 12 hits on ordinary presheaf pushforward, none on
  constructible finite-Tor towers.
- msearch grep: `constructible.*tower|tower.*constructible`: no Mathlib hits.
- LeanSearch: "Compactly supported direct image preserves constructible inverse
  systems with uniform finite Tor amplitude": 8 hits on exact forgetful functors,
  topological compact support, and homology preservation; no matching theorem.
- rg in upstream `WeilConjectures` and project `lean/Sheaf`:
  `sk-lem-sp-tower-bound|[Tt]ower.*[Cc]onstructible|[Cc]onstructible.*[Tt]ower`.
  Upstream normalized integral coefficient reconstruction and several project
  adic-tower results concern different coefficient categories or normalized input.
  The relevant exact declarations here are the stated dependencies above.
- rg in Mathlib, upstream, project and `dag/lean_names_upstream.json` for all three
  new full declaration suffixes returned no existing declarations.

No statement correction, new DAG node, dependency repair, or statement dispute
is needed. The blueprint's existing 0F10 attribution issue is already recorded
by stage 1; the delivered proof plan uses the stated finite uniform-bound node.

## Second reading by Q24

This is the author's separate self-check under the dispatcher's direct-delivery
protocol; the maintainer performs the independent review. I reread the item node
and the complete module after writing it. The exact input and output predicates
are the dependency's `spConstructibleTorTowers`, and the functor conjugates the
recorded compactification operation by its actual section-normalized equivalence.
I checked each prime/characteristic/field/scheme/morphism/coefficient binder,
the smooth-or-general geometric condition, the supplied compactification, and
all three conclusion clauses against the source. During this reading I restricted
the natural comparison to D+ with `DerivedCategory.Plus.ι`, removing an initially
unnecessary unbounded comparison. No normalization or etale-origin witness was
added, no level was dropped, and no uniform interval was replaced by separate
bounds depending on the level. The two helper definitions use existing derived
and ordinary functors and contain no postponed data.

Validation: the final module passed `scompile.py Q24 sk-lem-sp-tower-bound`
in both the sandbox and library-path checks, without errors or warnings. The
final reported times were 40.9 s and 5.7 s. The node differs from its base only
in `lean`; its recorded signature matches the file verbatim. All Lean lines
are at most 99 characters. There is exactly one `sorry`, the theorem proof.
The sheafification-instance priority is restored at the end of the module, as in
the imported shriek-level module, so its temporary elaboration setting does not
change the dependency's exported priority for consumers.
