## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing` as
`AlgebraicGeometry.Etale.isIso_ordinaryGlobalKunnethMap_finiteCoefficientRing`.
It asserts invertibility of the actual canonical exterior-product arrow in the
unbounded derived category of modules. Its proof is `sorry`; the docstring
contains all seven steps of the DAG proof. The module also defines the four
helpers for this absolute arrow, listed in `lean.declarations`. They contain
real canonical composites, with no postponed data or additional theorem.

Clause-by-clause correspondence:

- The fixed algebraically closed field is supplied by
  `(D : WeilConjectures.FiniteFieldDatum.{u})`, with base field `D.k` and
  its existing `IsAlgClosure D.k₀ D.k` structure.
- The prime coefficient characteristic is `(l : ℕ) [Fact l.Prime]`;
  `_hl : l ≠ ringChar D.k` states the unequal-characteristic hypothesis.
- The finite extension is `(E : Type (u + 1)) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
- The positive quotient level is `(n : ℕ) (_hn : 1 ≤ n)`.
- The ring A is exactly `Padic.coefficientExtensionRing l E n`, the
  dependency's quotient of its ring of integers by the nth power of its
  chosen uniformizer ideal.
- `X Y : Over (Spec (CommRingCat.of D.k))` are the two k-schemes;
  `X.hom` and `Y.hom` are their structure morphisms.
- `[IsSeparated X.hom] [IsSeparated Y.hom]` state separatedness.
- `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` and the corresponding
  pair for Y state finite type, with precisely the recorded convention.
- `K : DerivedCategoryModule ... X.left` and `M : DerivedCategoryModule ...
  Y.left` are arbitrary unbounded complexes. There is no boundedness,
  constructibility, properness, perfectness or flatness premise.
- The product and projections are Mathlib's `pullback X.hom Y.hom`,
  `pullback.fst X.hom Y.hom` and `pullback.snd X.hom Y.hom`.
- The source of `ordinaryGlobalKunnethMap` is the tensor in the existing
  unbounded `DerivedCategory (ModuleCat A)` of
  `(rightDerivedGlobalSections ... X.left).obj K` and the analogous value
  for M on Y.
- Its target is derived global sections on the product of the ordinary
  derived tensor of `L(p^*) K` and `L(q^*) M`. Here `curriedTensor` is the
  same monoidal structure used by the recorded `Etale.derivedTensor`,
  whose definition unfolds to `curriedTensor`. The canonical
  `leftDerivedUpperStarIsoMapDerivedCategory` identifies these pullbacks
  with the exact termwise inverse images of the node.
- `IsIso (ordinaryGlobalKunnethMap ... K M)` states invertibility of the
  canonical arrow itself. Expanding that definition gives the adjunct of
  the constant-sheaf tensor comparison and the tensor of the pulled-back
  global-sections counits.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`; the coefficient construction
  `Padic.coefficientExtensionRing` is imported from
  `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`, using
  `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- The convention node `def-weil-scheme-morphism-properties` uses the
  existing Mathlib `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`, and the existing derived tensor
  on ModuleCat. Both are ordinary uncompleted unbounded derived tensors.
- The current recorded declaration for `def-kun-kunneth-map` is
  `AlgebraicGeometry.Etale.kunnethMap` in
  `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`. I fetched
  its current source through `scompile.py --source` and read its full
  signature, docstring and defining adjunct. The theorem module imports
  this recorded module directly. The relative map is not redefined.

The absolute helpers belong to the arrow used in this item's conclusion.
`derivedConstantPullbackIso` derives the inverse of
`Scheme.upperStarConstantSheafIso` and applies the exact-functor composition
isomorphism. `ordinaryKunnethPulledCounit` composes it with the inverse image
of the derived constant/global-sections counit.
`ordinaryKunnethTensorMate` performs the tensor-of-counits composite and
adjunction Hom equivalence with abstract tensor bifunctors.
`ordinaryGlobalKunnethMap` specializes it to constant complexes versus
sections, giving the required D(ModuleCat) endpoints. No equivalence for the
etale point or unrelated endpoint isomorphism is chosen. The monoidal and
flat-preservation instances are the normalized existing structures from
`Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`. Generic coefficient
parameters on the helpers impose no extra hypothesis on the theorem:
all their instances are supplied for ModuleCat.

Available ordinary-etale proof dependencies remain imported without `public`.
The unused `Sheaf.Paper.ProEtaleCanonicalTensorPullback` import is removed,
as the independent reviewer requested. The node's generic ringed-topos
monoidal comparison is an input to the later proof, but this pro-etale
specialization contributes no object or declaration to this statement.
The now-published ordinary Kunneth module also exposes the generic
`thm-kun-0f1p` interface `isIso_kunnethMap_of_isSepClosed`.

Edge cases checked: n=1 and ell=2 are included; n=0 and ell=char(k) are
excluded exactly as in the node. Either scheme may be empty; either complex
may be zero or unbounded in both directions. Neither scheme needs to be
proper or nonempty. The absolute map is defined for arbitrary p and q,
and the theorem supplies the actual fibre-product projections. The module
uses explicit Scheme.{u} and ModuleCat.{u+1}, as in the recorded coefficient
encoding; every variable and universe is bound. The canonical-map helpers
make no torsion or geometric finiteness assumption.

Searches from the original worker and independent reader are retained in
`searches.jsonl`:

- LeanFinder: “The ordinary unbounded etale Kunneth exterior product over an
  algebraically closed field for finite coefficient rings is an isomorphism”.
  Eight hits concerned Kaehler differentials and formally etale rings.
- Loogle: `"kunneth"`; no hits.
- Mathlib grep: `kunneth|externalProduct` in AlgebraicGeometry; no hits.
- LeanSearch: “Canonical Kunneth exterior product in unbounded etale derived
  categories with finite coefficient ring”; Internal Server Error,
  recorded as unavailable rather than as a negative search.
- LeanFinder: “Kunneth morphism tensor of derived pushforwards defined as
  adjunct of the tensor of pulled back counits”; unrelated adjunction hits.
- Read-only ripgrep of upstream WeilConjectures and side Sheaf for Kunneth,
  externalProduct and the item id: earlier `nonempty_iso_kunneth` gives
  an endpoint isomorphism and cannot replace a canonical-arrow conclusion;
  `externalProduct` is the tensor object. The pro-etale variants concern
  other categories. No existing absolute canonical-arrow statement found.
- The independent reader's LeanFinder query “Isomorphism of the canonical
  cup product on derived global sections of two schemes over an algebraically
  closed field” returned scheme pullback identities. Loogle `"external"`
  and Mathlib grep `exterior.?product|cup.?product|k[uü]nneth` in
  AlgebraicGeometry gave no exact match. LeanSearch was unavailable.
- During this repair I reread the current dependency record and fetched
  `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` with
  `scompile.py --source`. It now supplies the relative `kunnethMap`, and
  is reused. A search of that source for the absolute helper names and
  global Kunneth maps found no canonical D(ModuleCat) arrow. Its
  `nonempty_iso_kunneth_of_isSepClosed` still has only a Nonempty endpoint
  isomorphism conclusion. Thus the four absolute helpers remain necessary.

No statement correction, new definition node, dependency-node override or
STATEMENT-DISPUTED flag is needed. The sole postponed theorem is
`isIso_ordinaryGlobalKunnethMap_finiteCoefficientRing`.

## Return repair

The return for immutable head `024b852a2498` reported a fix-layout failure:
`EtaleKunnethMap.lean` was supplied below `fixes/lean/Sheaf/` and treated as
a new module although it was already delivered. I read the saved independent
review and compared its replacement files with this sandbox. Its intended
source repair removed the unused
`import Sheaf.Paper.ProEtaleCanonicalTensorPullback`; the map replacement
was byte-for-byte unchanged. I applied the import removal directly here.

The current DAG meanwhile records the upstream relative map under
`def-kun-kunneth-map`. I removed the obsolete dependency-node override and
the duplicate relative-map module. The four required absolute-map helpers
are now in the item's own module, with its source/blueprint docstrings and
`lean.declarations`. The main theorem signature and all node statement,
statement-dependency and proof fields are unchanged. This is a source repair,
not an unchanged re-push or rebase.

Only `OrdinaryKunnethFiniteRing.lean` is delivered now. If a later reviewer
uses `--apply-fixes` for it, the replacement belongs at
`DIR/OrdinaryKunnethFiniteRing.lean`, as the return requires. It must not be
supplied as a new module below `DIR/lean/Sheaf/`.

Validation: `scompile.py Q40 lem-pur-ordinary-kunneth-finite-ring` compiled
the repaired sole module cleanly, including the sandbox and library checks
(15.2 s and 18.6 s), with no warnings or errors. The signature is verbatim
in `lean.statement`; every listed declaration is in the file; all Lean
lines have at most 100 characters; the only sorry is the theorem proof;
the node differs from the shared copy only in `lean`. The worker runs the
required `deliver2.py --no-push` dry run before handoff.

A fresh second reader will review this repaired layout; the previous second
reading is archived only in the sandbox scratchpad and is not represented
as a reading of this revision.

## Second reading by Q40

I independently reviewed the repaired one-module delivery, rather than treating the
archived reading of the old two-module packet as a reading of this revision. I opened
this node and every statement-dependency record, the dependency declarations listed
below, the complete delivered Lean module, and the original blueprint order-1937
Markdown on the project server (the literature files are absent from this local mirror).
I also read the Stacks `etale-cohomology.tex` statements at
`remark-define-kunneth-map` (0F1E), `lemma-kunneth` (0F1P), and
`lemma-pull-out-constant-mod-n` (0F12). The blueprint explicitly assumes separated
finite-type schemes, positive quotient level, and unequal characteristics. Stacks 0F1P
uses arbitrary unbounded complexes over a separably closed field; it adds neither
properness nor constructibility. Stacks 0F1E characterizes the map by the tensor of
pulled-back counits, and 0F12 uses a torsion ring and finite cohomological dimension.
Those latter hypotheses are checked in the node's proof, not added to the statement.

Here is my object, hypothesis, and conclusion list, with its Lean correspondence:

| Node item | Lean rendering and verdict |
| --- | --- |
| The fixed algebraic closure k of a finite field | `D : WeilConjectures.FiniteFieldDatum.{u}`, using `D.k`. Its fields give the finite base, prime-power cardinality, and `IsAlgClosure D.k₀ D.k`. Exact. |
| Prime ell different from char(k) | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ ringChar D.k)`. Exact. |
| Finite field extension E/Q_ell | `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Exact finite-dimensional extension, with no extra valuation or completeness premise. |
| Integer n at least one | `(n : ℕ) (_hn : 1 ≤ n)`. Exact. |
| A = O_E / varpi_E^n | `Padic.coefficientExtensionRing l E n`. The dependency defines the quotient of `coefficientExtensionIntegers` by `Ideal.span {coefficientExtensionUniformizer} ^ n`. Exact. |
| X and Y over k | `X Y : Over (Spec (CommRingCat.of D.k))`. Their underlying schemes and structure morphisms are `X.left`, `Y.left`, `X.hom`, `Y.hom`. Exact; no descent to the finite base is required. |
| Both schemes separated over k | `[IsSeparated X.hom] [IsSeparated Y.hom]`. Exact. |
| Both schemes of finite type over k | `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`, and the same pair for Y. This is the recorded finite-type convention. Exact. |
| Arbitrary K and L in the ordinary unbounded etale categories | `K : DerivedCategoryModule ... X.left` and `M : DerivedCategoryModule ... Y.left`. The abbreviation is `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u+1} A))`. Exact, with no boundedness, constructibility, flatness, or finite Tor amplitude assumption. |
| Product Z = X times_k Y and its projections | `pullback X.hom Y.hom`, inferred from `pullback.fst X.hom Y.hom` and `pullback.snd X.hom Y.hom`. Exact. |
| External product p_X^* K tensor^L_A p_Y^* L | The target of `ordinaryGlobalKunnethMap` tensors `L(upperStar ... p).obj K` and `L(upperStar ... q).obj M` using `curriedTensor` on the existing derived sheaf category. `Etale.derivedTensor` unfolds to this same bifunctor. The canonical `leftDerivedUpperStarIsoMapDerivedCategory` identifies each pullback with exact termwise inverse image. Exact. |
| Source RΓ(X,K) tensor^L_A RΓ(Y,L) | Tensor of the two `rightDerivedGlobalSections` values in `DerivedCategory (ModuleCat A)`. Exact ordinary, uncompleted tensor and sections. |
| Target RΓ(Z, external product) | `rightDerivedGlobalSections A Z` applied to that external tensor object. Exact. |
| The canonical exterior-product arrow is invertible | `IsIso (ordinaryGlobalKunnethMap ... K M)`. The map is the Hom adjunct of the constant-sheaf tensor comparison followed by the tensor of the pulled-back counits. Exact, including the arrow itself. |

I read `FiniteFieldFiber.lean`, `CoefficientExtension.lean`,
`CoefficientExtensionFinite.lean`, `DerivedCategories.lean`, the upstream
`Derived/Coefficients.lean` and `Derived/Tensor.lean`, and the relevant parts of
`Derived/UpperLowerStar.lean`. These are the recorded objects, not private replacements.
The finite-type and separated instances are the Mathlib notions recorded by
`def-weil-scheme-morphism-properties`.

For the map dependency, I fetched its current server source using
`scompile.py --source WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`.
I read `kunnethMap` and its defining adjunct: it uses the inverse-image composition
comparisons, derived tensor comparison, and the two counits, exactly as the
`def-kun-kunneth-map` node specifies. It is now an existing relative map, so the
worker correctly removed the old duplicate dependency module and node override.
Its `isIso_kunnethMap_of_isSepClosed` concludes in the etale derived category of
`Spec k`; `nonempty_iso_kunneth_of_isSepClosed` concludes only existence of an
isomorphism in D(A). Neither is this delivery's assertion about the canonical
absolute arrow in D(A).

I checked all four helpers directly. `derivedConstantPullbackIso` derives the inverse
of `Scheme.upperStarConstantSheafIso`, then uses `leftDerivedFunctorCompIso`.
The original constant-sheaf comparison is the canonical uniqueness isomorphism of
left adjoints, with the terminal-section comparison. `ordinaryKunnethPulledCounit`
follows this comparison by the pullback of the constant/sections counit.
`ordinaryKunnethTensorMate` composes the supplied tensor comparison, first-factor
map, and second-factor map, then applies the adjunction Hom equivalence.
`ordinaryGlobalKunnethMap` supplies the existing derived tensor bifunctors and the
constant/sections adjunction to that construction. Thus these are actual canonical
composites, with no sorry data, arbitrary chosen arrow, or new tensor definition.
The normalizations and instances in `EtaleConstantProjectionMap.lean` supply the
constant-sheaf monoidal and flat-preservation structures for all commutative rings;
the main theorem acquires no extra instance hypotheses from the general helpers.
There are no new definition nodes or dependency modules in this revision.

Edge cases: either scheme can be empty, and either complex can be zero. Complexes
can be unbounded in both directions. The case n=1 and prime ell=2 are included;
n=0 and ell=char(k) are excluded exactly as the node requires. There is no index
set or nonemptiness premise. Scheme universe u and coefficient/module universe
u+1 follow the recorded common-size convention; no equality of independent site
object and morphism universes is imposed. The coefficient extension may be taken
in that larger universe, and enlarging the common bound covers arbitrary sizes.
All variables and universe levels in the file are explicitly bound.

My fresh searches are recorded in `searches.jsonl`. LeanFinder query
“Tensor product of derived global sections and the canonical exterior cup product
on etale cohomology over a separably closed field” returned eight algebraic
Kaehler/cotangent hits, no etale Kunneth result. Loogle `"Kunneth"` returned no hits.
Mathlib grep `global.?sections.*tensor|kunneth|cup.?product` in AlgebraicGeometry
returned no hits. LeanSearch for the canonical exterior-product isomorphism was
unavailable with Internal Server Error, not a negative result. I additionally
searched the read-only upstream and project sources for external products, Kunneth
maps, and each helper's exact name. No exact absolute canonical-map declaration
or theorem was found. Upstream `externalProduct` is the existing tensor object;
relative and shriek results have different endpoints, and the ordinary endpoint
isomorphism result does not specify the absolute arrow. All five delivered full
names are absent from Mathlib, upstream, and the project's current Sheaf sources.

Mismatch found and repaired: the newly recorded proof dependency
`lem-pur-finite-field-derived-tensor-summand` was missing from the imports. I opened
its node and `Sheaf.Paper.FiniteFieldDerivedTensorSummand`: its theorem supplies the
finite-field diagonal projector and normalized balanced tensor comparison used in
proof step 3. I added its module as a non-public proof import, as stage 2 requires.
No mathematical statement, helper definition, or node field needed alteration.
The removed pro-etale-specific import remains omitted: that specialization is not
the generic ordinary-etale comparison used in this proof, as the worker report explains.

The theorem docstring carries all seven DAG proof steps: coefficient/geometric
hypotheses; restriction and sections; finite-field summand; scalar comparison;
compatibility of canonical arrows; reduction of the cone; and K-flat computation
with the finite nilpotent filtration. Every declaration has a source and blueprint
docstring. The only postponed proof is the named main theorem, with `sorry`.
There are no file-local notations, private definitions, local instances, or unbound
parameters. All Lean lines are at most 100 characters. The node copy differs from
the shared node only in `lean`, and `lean.statement` is verbatim the main signature.

Validation of this revision: the required `scompile.py Q40
lem-pur-ordinary-kunneth-finite-ring` passed with the repaired sole module and the
new proof-dependency overlay, with no errors or warnings. The wrapper separately
compiled the overlay (43.1 s), sandbox (21.7 s), and library module (19.4 s), retaining
the prescribed 60-second limit. I then ran the prescribed delivery dry run.
