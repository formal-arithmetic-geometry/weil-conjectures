## Worker report

The module `Sheaf.Paper.TensorExchangeCtfDomains` states the three paragraphs of
`lem-sf-tensor-exchange-ctf-domains` as three named theorems, each with `sorry`.
There are no new definitions, extra nodes, dependency repairs or statement corrections.
Only the item's `lean` field changes. The primary record contains the first signature;
`lean.declarations` lists all three statements.

### Hypotheses and clauses

The common coefficient setup is `D : FiniteFieldDatum.{u}`, `l : ℕ`, `[Fact l.Prime]`,
`l ≠ D.p`, and `E : Type u` with its field, `Padic l` algebra and finite-dimensional
instances. These are the existing finite-field and coefficient-extension conventions;
`Padic.coefficientExtensionRing l E n` is the specified valuation-ring quotient using
its chosen uniformizer. No extra operation datum is assumed: the actual operations
are used directly. Site objects have universe `u+1` and arrows universe `u`; module
coefficients live in `u+1`, as in all the dependency definitions.

* Finite Hom (`tensorExchange_finiteHom_domains`): the positive level is `n`, `hn`.
  `W : Over (Spec (.of D.k))`, `LocallyOfFiniteType W.hom`, and `QuasiCompact W.hom`
  express an arbitrary finite-type k-scheme, with its actual structure map. No
  separatedness of that map is assumed. The natural number `d` and `_hd` express
  `dim W ≤ d`, including dimension minus infinity for the empty scheme.
  `a b c e : ℤ`, `_hab`, `_hce` express the ordered intervals. `P Q` are in the
  ambient intrinsic pro-etale derived category; `_hP`, `_hQ` impose exactly
  `D^b_ctf`, and `_hPt`, `_hQt` impose the given intervals. The first conclusion
  is `intrinsicFiniteTorsionConstructible` of the ambient `IntegralHom.hom` over
  `proEtaleConstantRing`. The second is `HasProEtaleTorAmplitude` of that same
  object in `[c-b-2*d,e-a+2*d]`. The theorem is global on W: it does not assume
  an affine cover as extra input, and its proof docstring records the finite
  affine-cover descent with the same d on every member. No site-perfectness
  premise occurs.
* Integral Hom (`tensorExchange_integralHom_domains`): W and its dimension and
  the four ordered endpoints are as above. `P Q` belong to the derived category
  of `scalarReductionSource`; `_hP`, `_hQ` are the exact derived-complete integral
  constructibility predicate. `_hPt`, `_hQt` quantify over every `n : ℕ` with
  exponent `n+1`, giving the two uniform Tor intervals for every positive
  reduction. The Hom is `IntegralHom.hom` over
  `completedIntegralCommRingSheaf l E W.left D hl`, whose underlying sheaf is
  the actual inverse limit of finite constant coefficient sheaves. The first
  three conclusions are derived completeness, membership in `D^b_c`, and
  membership in `D^b_ctf`. The fourth is equality of those integral object
  predicates, hence of the full subcategories. The fifth gives the required
  uniform interval for every reduction of that Hom. The last conclusion
  supplies a normalized `IntegralHom.TensorPresentation` and, at every level,
  a normalized `IntegralHom.ReductionPresentation`, with `IsIso` of the
  existing `IntegralHom.comparison`. That map is the defined transpose of
  reduced evaluation, not an arbitrarily chosen isomorphism. Presentations
  are supplied existentially, with their K-flat/unit normalization, rather
  than imposed as extra hypotheses. `IntegralHom.comparison` uses
  `integralDerivedReduction`, the same canonical scalar extension as
  `scalarReductionDerivedExtension`: unfolding the auxiliary global datum
  gives the identical completed ring, projection and derived-change-of-rings
  construction.
* Integral direct image (`tensorExchange_integralDirectImage_domains`): `X Y`
  are finite-type objects over the same field. `f : X ⟶ Y` is a k-morphism;
  `[IsSeparated f.left]`, `[LocallyOfFiniteType f.left]`, and `[QuasiCompact f.left]`
  express precisely separated finite type. No separatedness of X or Y over k
  is added. `d`, `_hd` bound dim X. The node's interval `[u,v]` is named `[a,b]`
  in Lean to avoid confusing the lower endpoint with the universe name.
  `_hK` is integral constructibility, and `_hKt` gives the common interval
  at all positive levels. `L : SfIntegralDirectImage ... K` is any presentation
  of the specified derived limit, with its actual Roos projection; the product
  instance is the product used in that presentation, not an additional
  geometric or finiteness requirement. The first four conclusions give
  completeness, both integral domains and equality of their predicates.
  `IsIso (sfDirectImageReductionComparison ...)` is exactly the canonical
  scalar adjunct of the n-th projection. The next two conclusions give Tor
  interval `[a,b+2*d]` and the same cohomological support interval for every
  reduction. The last equation is the quotient transition square after
  exact restriction of scalars into the completed derived category: the two
  vertical maps are restrictions of the actual reduction comparisons; the
  upper and lower transitions are `sfDirectImageTransition` and
  `sfDerivedReductionTransition`. This expresses compatibility for adjacent
  levels; composition gives compatibility for arbitrary quotient transitions.

### Dependency declarations read and used

* `Sheaf.Paper.SixFunctorOperationDatum`: `WeilConjectures.SixFunctorOperationDatum`
  and its intrinsic coefficient/operation conventions (public import).
* `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
* `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
* `Sheaf.Paper.FiniteTorAmplitudeSites` and its public `FiniteTorAmplitude`:
  `WeilConjectures.finiteTorConstructible`, `finiteTorConstructibleIntegral`;
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude` from its dependency.
* `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly reexports
  `CategoryTheory.derivedInternalHomOfUniverses`, the actual generic ringed-site
  Hom used by `IntegralHom.hom`. The primary ordinary-module abbreviation is
  not applied to sheaves; the recorded generic declaration is used.
* `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
* `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension`, `scalarReductionDerivedRestriction`.
* `Sheaf.Paper.IntegralHomReductionModels`: `IntegralHom.hom`,
  `TensorPresentation`, `ReductionPresentation`, `comparison` (existing helpers).
* `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`,
  `sfDirectImageReductionComparison`, `sfDirectImageTransition`,
  `sfDirectImageTerm`; its dependency `sfDerivedReductionTransition`.

All recorded proof-dependency modules are imported without `public` when not also
used for a statement interface: `ProEtaleFiniteCoefficientDirectImage`,
`IntegralHomReduction`, `IntegralResidueTor`, `ComparisonTorAmplitude`,
`SfCompleteDirectImageReduction`, `FiniteRingConstructibleDerivedOrigin`,
`ConstructibleHomComparison`, `EtaleHomFiniteTorAmplitude`. I read their theorem
signatures and proof docstrings. The module docstrings follow the current latest
blueprint location, `sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction`
and its separate proof file, rather than the older source path in the imported node.

### Edge cases

Empty schemes are included: `topologicalKrullDim` is bottom, so d=0 is allowed;
there is no Nonempty scheme or cover hypothesis. The zero objects satisfy every
ordered interval. The residue quotient is index 0 in integral reductions and
positive finite level 1, so no positive quotient is lost and the zero-th power
quotient is not introduced. Nonseparated W remains permitted, while only the
morphism f is required separated. At dimension zero the finite Hom bound reduces
to `[c-b,e-a]`; the direct-image upper shift is zero. Finite torsion inputs retain
their genuine extra finite-Tor premise (e.g. a residue field module over a
nonreduced higher quotient is not silently accepted as ctf). No site-perfectness,
uniform perfect model or arbitrary comparison map is assumed.

### Searches and validation

Prescribed msearch calls:

* LeanFinder: "Derived internal Hom preserves constructible finite Tor amplitude
  with uniform bounds and completed integral direct image commutes with finite
  reduction". Eight hits, about light condensed monoidal structures and generic
  Tor; none states this node.
* Loogle: `DerivedCategory, TorAmplitude`. Zero hits; unknown `TorAmplitude`.
* Mathlib grep: `constructible.*(internalHom|internal.hom|TorAmplitude)|TorAmplitude.*constructible`.
  Zero hits.
* LeanSearch: "Derived internal Hom constructible finite Tor amplitude on proetale
  site and integral direct image reduction". Eight generic derived-functor,
  condensed-Hom and algebraic-geometry hits; no statement match.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id, the prospective
  theorem names, and internal Hom/Tor/constructibility patterns: no existing
  statement of this combined node. This found the existing operation interfaces
  and the separately recorded proof lemmas reused above. The upstream name index
  also has no match for the node or proposed theorem names.

The wrapper recorded search results in `searches.jsonl` in the sandbox.
`scompile.py Q39 lem-sf-tensor-exchange-ctf-domains
lean/Sheaf/Paper/TensorExchangeCtfDomains.lean` passed both sandbox (5.2 s) and
library (4.9 s) modes, with no error or unexpected warning. All variables and
universes are explicit, and autoImplicit and relaxedAutoImplicit are disabled.

## Second reading by Q39

Author's second reading, performed with the item JSON and final module open;
no independent subagent was started, as the dispatcher expressly prohibits that.
The maintainer's independent reading remains the delivery review.

I checked each paragraph against its separate theorem: the finite result keeps
both input ctf conditions and both intervals, the integral result keeps both
constructibility assumptions and all positive reductions, and direct image keeps
exactly relative separatedness and finite type, plus the source dimension bound.
All displayed intervals have the same endpoint signs and factors of 2 as the node.
The integral Hom comparison is the defined evaluation transpose on normalized
presentations; the direct-image comparison is the defined projection adjunct.
I checked the types of both sides of the transition equation: both start at the
restricted level n+2 reduction of L and end at the restricted finite direct image
at level n+1. Adjacent transition equations include every quotient transition by
composition. The integral full-category equality is stated as equality of object
predicates, so it does not replace membership by an unspecified category equivalence.
No mismatch, node fault or STATEMENT-DISPUTED flag was found. No statement change
or extra data construction was required. All three proofs remain exactly `sorry`.
