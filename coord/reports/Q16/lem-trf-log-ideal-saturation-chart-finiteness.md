## Worker report

The item is stated by `AlgebraicGeometry.logIdeal_saturation_chart_finiteness` in
`Sheaf.AlgebraicGeometry.LogIdealSaturationChartFiniteness`. Its only proof is `sorry`.
The new definition module `Sheaf.AlgebraicGeometry.LogIdealAffineAtlas` supplies the
fine-base affine presentation missing from the recorded fs-base cover interface. Its
constructions and predicates have real definitions and contain no `sorry`.

Sources read: the assigned node and every statement dependency; the full relevant
interfaces in `FineSaturatedLogBlowup.lean`, `FineLogEtaleDescentDatum.lean` and
`LogIdealChartPresentation.lean`; Mathlib's tensor definition, chosen pullback and finite
morphism definitions; ILO VIII 3.1.17--3.1.21 (printed p. 101), the finiteness sentence
in the proof of 3.2.9 (printed p. 104), and 3.3.8--3.3.9 (printed pp. 107--108).
The source defines saturation by positive powers, constructs ideal fraction charts,
and states strict-base-change compatibility of the log blowup construction.
The normality hypothesis of 3.2.9 concerns identification with normalization; this
item uses only its finite saturation map and does not impose normality on A.

Hypothesis correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`. There is no domain, normality,
  nontriviality, characteristic or Noetherian hypothesis.
- P finitely generated and integral: `(P : Type u) [CommMonoid P]`, `hfg : Monoid.FG P`,
  and `hP : Function.Injective (Algebra.GrothendieckGroup.of (M := P))`.
  The canonical `Algebra.GrothendieckGroup P` is G. Multiplication, division and powers
  render addition, subtraction and positive multiples in the node's additive notation.
- The chart alpha and finite nonempty E are `α : P →* A`, `E : Finset P`, `hE`.
  `M`, `c`, `hc` and `hα` express the associated base log structure: c is a chart,
  and its structural map is alpha under the canonical Gamma-Spec isomorphism.
- `X₀`, `Xₛ`, `N₀`, `Nₛ`, `b₀`, `bₛ` are the two log schemes over that base.
  General `EtaleLogMap` is necessary: the ordinary source is fine, not necessarily fs,
  and A is arbitrary. The fs-only bundled scheme interface is not imposed.
- `D₀` uses exactly `logIdealChartMonoid E e.val` and `logIdealChartInclusion`;
  `Dₛ` uses exactly the recorded `logIdealSaturatedChartMonoid` and inclusion.
  The latter is defined by closing the root set; in a commutative group the root set
  is already a submonoid (multiply positive witnesses), so it equals the node's Q_e^s.
- `LogIdealAffineAtlas.j` has domain the actual recorded `Spec (logIdealTensorRing ...)`.
  `openImmersion`, `covers` and `overBase` give the specified open cover over Spec A.
  `chart`, `isChart`, `chartAlpha`, `chartMap` give associated monoid log structures,
  their canonical tensor monomials and their maps from P.
- `difference_val` identifies `difference e f` with f/e in G. `overlap` gives the
  exact pairwise intersection as D(1 tensor z^(f/e)) in the e-chart. Interchanging
  e and f gives the other localization. Both charts lie in the same log scheme;
  `chartMap` fixes P, hence also the common fraction monoid, so the induced overlap
  identification is the specified monomial one. Its cocycle is inherited from the
  common ambient log scheme; no unrelated gluing automorphism is allowed.
- `principal` says, at every geometric point of the e-chart, each h in E is e times
  a log stalk element. Since e itself belongs to E, this says exactly that e generates
  the pulled-back log ideal. It does not require its ring image to be nonzero or regular.

Conclusion correspondence:

- `∃ s : EtaleLogMap Nₛ N₀` constructs the log comparison. The first conjunct of
  `FiniteComparison`, namely `Comparison`, includes `s.CompEq b₀ bₛ`, so the comparison
  is over the base including its log maps.
- For each chart, `Comparison` supplies an inclusion k with `(k q).val = q.val` and
  a tensor ring map phi normalized by `LogIdealTensorRingMap`: coefficients are fixed
  and every monomial goes to the same monomial. These conditions determine the actual
  map on all ring generators; neither an arbitrary map nor an unnormalized choice
  of morphism is substituted. The `sectionMap` equation gives the full log chart map.
- `D₀.GeneratorLoci` and `Dₛ.GeneratorLoci` say precisely that the e-chart is the locus
  where e divides every h in E in the geometric log stalk. This is equivalent to e
  generating the pulled ideal. Every ordinary point has a geometric lift, so this
  gives the same ordinary-point locus, not only a special collection of points.
- The second conjunct of `FiniteComparison` is
  `∀ e, s.base ⁻¹' Set.range (D₀.j e) = Set.range (Dₛ.j e)`.
  Its `Comparison` conjunct additionally asserts
  `IsPullback (Spec.map phi) (Dₛ.j e) (D₀.j e) s.base`, the exact square in the node.
- `LogIdealSaturationTranslates E e F` is the finite-translate equality, written
  `∀ q : Q_e^s, ∃ f ∈ F, ∃ p : Q_e, q.val = f.val * p.val`. The reverse inclusion
  holds because both factors belong to the saturated submonoid. Taking F as a
  `Finset Q_e^s` is precisely taking a finite subset of G contained in Q_e^s.
- `LogIdealSaturationSpanning α E` asserts existence of such a finite F for each e,
  and for EVERY such F asserts every z in the saturated tensor ring is
  `∑ f : ↥F, phi (a f) * logIdealTensorMonomial ... f.val` for suitable coefficients
  `a : ↥F → B_e`. This is exactly module generation by the specified `1 tensor z^f`,
  using restriction of scalars along the canonically normalized comparison.
- `IsFinite s.base` is Mathlib's recorded finite morphism. The last conjunct of
  `FiniteComparison` spells out, for every affine open U, both
  `IsAffineOpen (s.base ⁻¹ᵁ U)` and `(s.base.app U).hom.Finite`.
- Strict etale base change is quantified by arbitrary A', rho, M' and f with
  `f.base = Spec.map rho` and `f.IsStrictEtale`. This is the affine-piece formulation
  of change of the base chart, sufficient also for a nonaffine strict etale base
  by its affine cover; it imposes no surjectivity or faithfulness condition.
- `C₀` and `Cₛ : BaseChange ...` supply ordinary Cartesian log squares with strict
  projections, the identical Q_e tensor atlases over A', and normalized Cartesian
  chart squares fixing each q and mapping a by rho. Thus the actual charts, gluing
  and pulled-back log structures are retained. `s'` satisfies `FiniteComparison`,
  both generator-locus assertions, and the same all-F monomial-spanning predicate
  over A'. The two `CompEq` equations include equality of log composites; the final
  `IsPullback s'.base Cₛ.q.base C₀.q.base s.base` identifies the comparison with the
  ordinary base change of s. These conditions express compatibility of the maps,
  chart squares and finiteness, including their log maps.

Recorded dependency declarations used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtaleLogStructure`,
  `EtalePrelogStructure.stalk`, `.germ`, `EtaleLogStructure.IsChart`.
- `Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum`: the fine-log convention
  `EtaleLogStructure.IsFine`; the charts in the hypotheses give precisely this
  property, without adding it as an independent assumption.
- `Sheaf.AlgebraicGeometry.LogIdealChartPresentation`: `EtaleLogMap`, `.CompEq`,
  `.IsStrictEtale`, `logIdealChartMonoid`, `logIdealSaturatedChartMonoid`, both chart
  inclusions, `logIdealTensorRing`, `logIdealTensorBase`, `logIdealTensorMonomial`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, through the recorded
  tensor-ring construction. No new tensor product is defined.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: the chosen `pullback`
  underlying the square interface. `CategoryTheory.IsPullback` expresses its universal
  property without selecting additional arbitrary isomorphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`, `.finite_app`,
  `IsFinite.SpecMap_iff`, and the target-local finiteness infrastructure.
- New node `def-trf-log-ideal-affine-atlas`: the general atlas and its comparison,
  finite comparison, base-change, translates and spanning predicates.

The stated proof dependency `Sheaf.GroupTheory.FineMonoidFiniteSaturation` is imported
without `public`; its theorem is `fine_monoid_finite_saturation`. The lifting criterion
and affine-atlas-gluing proof dependencies currently have no Lean record or Mathlib
match, and their imports are consequently absent. They are named explicitly in the
seven-step proof docstring. Their proofs are not needed to elaborate this statement.
The Spec criterion and target-locality proof dependencies are the recorded Mathlib
matches, supplied by the finite-morphism imports.

Edge cases checked before finalizing:

- A = 0, a zero tensor chart, or empty intersections: affine charts may be empty;
  the cover, overlap and preimage statements remain valid. The finite-sum assertion
  uses no injectivity of B_e -> C_e.
- alpha(e) = 0 or a zero divisor: no cancellation in A or any tensor ring is assumed;
  cancellation occurs only in the integral monoid/log stalk in the proof plan.
- E singleton (including a unit generator): Q_e is P and saturation can still be
  nontrivial when P is not saturated. No blowup identity is incorrectly asserted
  for the saturation comparison.
- P with units, nonsaturated P, or torsion in G: no sharpness, saturation or
  torsion-free hypothesis was introduced. The canonical group completion is used.
- Empty F cannot cover the nonempty saturated monoid; the universal all-F assertion
  therefore has the intended domain. A zero chart ring causes no exception.
- Identity base change and strict etale open restriction are included. The source
  base change need not cover Spec A. No field or characteristic restriction is present.
- All universes and binders are explicit; the common u covers arbitrary choices by
  taking their common universe. The existing small-etale-site size convention is kept.

Searches for existing statements and definitions:

- `msearch.py ... leanfinder` with "Saturated logarithmic monoid ideal charts have finite
  Cartesian comparison maps compatible with strict etale base change": 8 hits about
  standard-etale lifts and etale maps; no saturation-chart comparison statement.
- `msearch.py ... loogle` with `Submonoid.saturation, Algebra.TensorProduct.map,
  AlgebraicGeometry.IsFinite`: zero hits for the combined query.
- `msearch.py ... grep` with `logIdeal|saturat.*[Mm]onoid|[Mm]onoid.*saturat`: monoid
  saturation infrastructure, not a logarithmic chart atlas/comparison. Mathlib's
  `Submonoid.saturation` is multiplicative-factor saturation, not this root saturation.
- LeanSearch and LeanFinder with "Affine tensor monoid log ideal chart atlases with
  canonical monomial localization overlaps and strict etale base change": 8 hits each;
  etale base change and localization tensor theorems, no matching atlas definition.
- Loogle with `AlgebraicGeometry.LogIdealAffineAtlas,
  AlgebraicGeometry.LogIdealTensorCover`: unknown first identifier, zero hits.
- Mathlib grep `logIdeal|LogIdeal|saturat.*[Mm]onoid`: only general saturation machinery.
- `rg -n 'logIdeal|LogIdeal|saturation.*[Cc]hart'` in the prescribed upstream and Sheaf
  roots: existing fs-base covers, coherent chart construction and fan applications.
  Their full signatures were read; none supplies this general fine-base atlas.
- `rg -n 'log-ideal-saturation-chart-finiteness' lean/WeilConjectures`: no matching
  declaration. The existing coherent-chart theorem has an fs locally Noetherian base,
  and does not state this node's general fine-monoid/all-F spanning assertion.
- `blueprint_refs.py search "saturation chart"` and `search "log ideal"`: zero matches.
  DAG text search finds the existing fs-base presentation and the unstated gluing
  theorem, but no node defining the general fine-base affine atlas. Full raw service
  and source-search outputs are recorded in the new node's `mathlib_searches`.

No statement correction, dependency repair or STATEMENT-DISPUTED finding is needed.
The item changes only `lean` and the permitted new-definition addition to `stmt_deps`.

## New nodes

`def-trf-log-ideal-affine-atlas` defines the affine tensor atlas for a general integral
fine base monoid and its generator loci, normalized chart comparison, finite comparison,
strict etale base change, finite translates and monomial-spanning predicates. Source:
ILO VIII 3.1.19, 3.2.9 (finiteness sentence), 3.3.5--3.3.9. The existing
`LogIdealTensorCover` requires `LogIdealAffineChart` on a `FineSaturatedLogScheme`;
its P is fs and its underlying base locally Noetherian. Using it here would add both
hypotheses. The new interface reuses every existing tensor/monoid/log construction,
while its data simply presents the open charts and their equations. The searches
above exclude a general existing definition; the existing gluing node is a theorem
of existence, not a definition of the needed presentation. All additional declarations
are recorded on this one definition node and carry its source/blueprint docstrings.

## Second reading by Q16

In a separate rereading pass, I reopened the node and both final module files and
expanded every conclusion predicate. This is a self-review; the dispatcher brief
prohibits starting a second agent, and the maintainer provides the independent review.

The comparison orientation is `Spec C_e -> Spec B_e`, and its `IsPullback` has top
arrow `Spec.map phi`, left arrow the saturated chart immersion, right arrow the
ordinary chart immersion and bottom arrow s. The final base-change square has top
s', left saturated projection, right ordinary projection and bottom s. I checked
these four maps against the source and corrected their order during drafting.

The generated ideal uses h = e as well as all other members of E; consequently
stalk divisibility means equality with the principal log ideal, not just containment
in a larger arbitrary ideal. Geometric membership uses the point of t, not a point
of an unrelated chart. The overlap monomial is f/e on the e-chart in both atlases.
The finite sum has coefficients in B_e and generators in C_e, mapped by normalized
phi. All finite F are quantified, and existence is a separate conjunct. The noetherian,
fs, sharpness and ring-image restrictions of adjacent interfaces have not leaked
into the theorem. The theorem includes every clause of the original statement.
No further mismatch was found in this rereading, and there is no node correction.

Validation: both delivered modules compiled individually through `scompile.py`, in
dependency order, with no errors or unexpected warnings. No global build or direct
live-source edit was performed. The required dry-run and delivery results follow
from the prescribed `deliver2.py` invocations.
