## Worker report

The module `Sheaf.Paper.DirectImageCtfOpenTor` states
`AlgebraicGeometry.Etale.sf_directImage_ctf_open_tor` (blueprint
`det-cor-sf-direct-image-ctf-open-tor`). It binds a separably closed field `k`, a
prime `l` different from `ringChar k`, a finite commutative `l`-primary ring
`A` (the displayed annihilation hypothesis `hA`), finite-type structure maps
for `U` and `X`, an open immersion `j`, an integer `d` bounding the recorded
morphism cohomological dimension, and a complex `K` with the required Tor
amplitude.

The first conjunct quantifies over every `A`-module `M` and renders the scalar
projection morphism by the component of
`Etale.rightDerivedLowerStarProjectionMap` at the constant sheaf on `X`, placed
in degree zero; `IsIso` is the asserted isomorphism. The second conjunct is the
interval `[a,b+d]` predicate for the etale direct image. The third conjunct is
the comparison isomorphism between the pro-etale right derived direct image of
the comparison pullback and the comparison pullback of the etale right derived
direct image, followed by the pro-etale Tor-amplitude predicate in the same
interval.

The module uses `AlgebraicGeometry.Scheme.Hom.torsionEtaleCohomologicalDimension`,
`AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`,
`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`,
`AlgebraicGeometry.Etale.rightDerivedLowerStar`,
`AlgebraicGeometry.ProEtale.comparisonUpperStar`,
`AlgebraicGeometry.ProEtale.lowerStar`, and
`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn`.
The Tor hypothesis uses the bounded-interval predicate recorded by
`def-kun-tor-amplitude`. No dependency record or dependency module is changed.
The coefficient-extension constructibility predicate
`WeilConjectures.finiteTorConstructibleEtale` is not this node's hypothesis.

Edge cases checked include `d = 0`, `a = b`, empty or zero module `M`, the zero
complex `K`, and the empty open scheme; no nonemptiness or strict inequality was
added. The annihilation condition allows the zero ring and all finite
ell-primary rings.

Searches made:

- `msearch.py ... leanfinder "scalar projection formula and Tor amplitude bound for open immersion"`:
  no matching project declaration; returned unrelated Mathlib open-immersion results.
- `msearch.py ... loogle "rightDerivedLowerStarProjectionMap, hasTorAmplitudeIn, torsionEtaleCohomologicalDimension"`:
  no Loogle hits (the names are project declarations).
- `msearch.py ... grep "rightDerivedLowerStarProjectionMap|hasTorAmplitudeIn|torsionEtaleCohomologicalDimension" WeilConjectures/SixFunctors`:
  no direct grep hit in the requested subdirectory.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` found the canonical projection,
  Tor-amplitude, comparison, and cohomological-dimension declarations cited
  above, but no declaration of this target theorem.

No `STATEMENT-DISPUTED` flag applies.

## Earlier second reading (a previous round; superseded)

I reread the node and module independently. The field, prime and annihilation
hypotheses, finite-type structure maps, open immersion, cohomological-dimension
bound, Tor interval, scalar projection components, etale Tor bound, comparison
isomorphism, and pro-etale Tor bound all occur in the displayed signature. The
canonical functors are the recorded etale and pro-etale lower stars and the
comparison upper star. No mismatch was found.

## Second reading by NI

I read the node statement and its source place first. The objects and hypotheses are rendered as
follows.

- The separably closed field is `k : Type u` with `[Field k] [IsSepClosed k]`.
- The prime is `l : ℕ` with `[Fact l.Prime]` and `_hl : l ≠ ringChar k`.
- The coefficient ring is `A : Type (u + 1)` with `[CommRing A] [Finite A]`; `hA` says that a
  power of `l` annihilates every element. This includes the zero ring and does not impose a
  nonzero or positive exponent.
- The finite-type `k`-scheme structure maps are `aU : U ⟶ Spec (.of k)` and `aX : X ⟶ Spec (.of
  k)`, with `[LocallyOfFiniteType]` and `[QuasiCompact]` instances for both. The equality `_hj : j
  ≫ aX = aU` makes `j : U ⟶ X` a morphism over `k`, and `[IsOpenImmersion j]` is the open
  immersion hypothesis.
- `d : ℕ` and `_hd` express `cd(j) ≤ d`. The latter now uses the canonical `QuasiCompact` and
  `QuasiSeparated` witnesses derived from the finite-type structure maps, written explicitly in
  the argument to `Scheme.Hom.torsionEtaleCohomologicalDimension`.
- `a b : ℤ`, the derived object `K` in `D(U_et,A)`, and `_hK :
  Etale.DerivedCategory.hasTorAmplitudeIn A U a b K` render the Tor-amplitude hypothesis.

The conclusion has the same three clauses and order as the node. First, for every `M : ModuleCat
A`, the component at the degree-zero constant sheaf on `X` of `rightDerivedLowerStarProjectionMap
A j` at `K` is `IsIso`; this is the canonical map whose target uses the pullback of the constant
sheaf, i.e. `j^*` of `underline M_X = underline M_U`. Second, `rightDerivedLowerStar A j` applied
to `K` has ordinary etale Tor amplitude in `[a,b+d]` on `X`. Third, the displayed `Nonempty`
natural isomorphism is exactly `Rj_{proet,*} ν_U^* K ≅ ν_X^* Rj_* K`, using `comparisonUpperStar`
and the etale/pro-etale lower stars, and the final conjunct applies
`ProEtale.DerivedCategory.torAmplitudeIn` to that pro-etale direct image in `[a,b+d]`. No
quantifier or clause is omitted or added.

The source place is the blueprint node `det-cor-sf-direct-image-ctf-open-tor`. Its assumptions are
a separably closed field, a prime distinct from the characteristic, a finite commutative primary
coefficient ring, finite-type schemes, an open immersion, a cohomological-dimension bound, and a
Tor-amplitude interval. The explicit structure-map presentation is the recorded
scheme-over-a-field convention. The earlier worker had added `[QuasiCompact j] [QuasiSeparated
j]`; these are consequences of the finite-type hypotheses for an open immersion, and are not
assumptions in the node. I removed those binders and supplied the canonical witnesses explicitly
in `_hd`, preserving the same cohomological-dimension notion and allowing exactly the node's
hypotheses.

I checked edge cases before and after the repair: `d = 0`, `a = b`, `a > b` (empty interval),
negative endpoints, the zero complex `K`, the zero ring and an arbitrary finite `l`-primary ring,
an empty source/open scheme, an empty or zero module `M`, and `j = 𝟙`. No nonemptiness, strict
inequality, characteristic restriction beyond `_hl`, constructibility, separatedness, or
finite-presentation hypothesis was added.

The first worker's searches were checked against the declarations, and I ran the independent
searches listed below. I opened the
declarations used by the signature: `Etale.rightDerivedLowerStarProjectionMap` is the generic
adjunction projection map, `Etale.DerivedCategory.hasTorAmplitudeIn` tests every module sheaf in
degree zero, `ProEtale.DerivedCategory.torAmplitudeIn` is the all-module pro-etale test,
`comparisonUpperStar` is the comparison inverse image, and
`Scheme.Hom.torsionEtaleCohomologicalDimension` is the recorded morphism invariant. Thus no second
definition is present and no dependency module is needed.

The mismatches and repairs are:

- H3: removed the redundant quasi-compact/quasi-separated binders on `j` and supplied their
  consequences explicitly inside the cohomological-dimension expression. The node's
  `lean.statement` was regenerated verbatim from the signature.
- H8: the three-sentence proof summary omitted the node's ten-step argument. I replaced it by the
  complete ten numbered steps and their dependency ids, with the blueprint and Stacks source
  places.
- H9/stage-2 imports: added the recorded statement dependency modules and the modules of every
  already stated proof dependency, with ordinary `import` for proof-only dependencies. The worker
  had omitted these even where their declarations arrived transitively.
- Report accuracy: the worker claimed a repair of `def-weil-finite-tor-amplitude`, but no such
  dependency record was present and that constructible coefficient-extension notion is not the
  hypothesis here. I corrected that paragraph. The item already cites the right
  `def-kun-tor-amplitude` on the base; there is no source statement correction, new node, or
  dependency module in this delivery.

Independent searches in this reading used LeanFinder for “derived pushforward of an open immersion
preserves Tor amplitude with cohomological dimension bound” (eight unrelated pushforward and
t-structure hits); Loogle `CategoryTheory.IsIso, CategoryTheory.constantSheaf` (three
constant-sheaf counit results, no projection theorem); LeanSearch “For an open immersion of finite
type schemes derived direct image of a complex has Tor amplitude bounded by cohomological
dimension” (eight ordinary open-immersion hits); wrapper grep `torAmplitudeIn` in
`WeilConjectures` (no hits), followed by direct `rg` over Mathlib, upstream, and `lean/Sheaf` for
`projection`, `open immersion`, `Tor`, `torAmplitudeIn`, and `rightDerivedLowerStarProjectionMap`.
The general dualizable-object projection theorem and the proper projection theorem have stronger
hypotheses and do not replace the node. `OpenDirectImageClassicalAmplitude` bounds cohomology but
does not state the scalar projection or the all-sheaf Tor conclusion. No exact existing theorem
was found.

I also read the locally constant coefficient realization in `ProEtaleFiniteModules`, the current
`proEtaleSiteComparisonModules` signature, and the current `CoefficientProEtaleTorAmplitude`
module (which publicly retains its original interface). The theorem uses their fixed-ring sheaf
presentation, canonically equivalent to modules over the finite coefficient ring sheaf, and the
existing framework Tor predicate; the empty-interval extension is explicitly part of the item's
own node. The recently generalized coefficient-size interface adds no restriction here. The small
etale/pro-etale sites retain their separate object and morphism universes; `A` and the module test
objects use the recorded common `u+1` coefficient universe.

The repaired module, including all added imports, compiles cleanly with `scompile.py` (overlay
checks included; final file compilation 3.1 seconds). The only theorem proof is `sorry`; no definitions,
axioms, private notions, local instances, or proofs were added. Every variable and universe is
explicitly bound. The Lean file has no line exceeding 100 columns.
