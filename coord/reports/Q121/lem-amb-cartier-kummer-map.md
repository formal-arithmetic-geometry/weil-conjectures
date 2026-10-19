## Worker report

The delivery states `AlgebraicGeometry.Etale.cartier_kummer_map` and exposes the
canonical arrow as `cartierKummerMap`. Its postponed proof is the theorem
`cartier_kummer_map`. The ownership repair also retains the existing postponed
`finite_tate_site_descent` theorem in its repaired module. Its docstring gives the node's thirteen-step proof. All
helper definitions have actual data or are predicates; there is no data `sorry`.

Source read: the current main-20261015 blueprint,
`sec-six-functors-basics/sk-lem-geo-cartier/lem-amb-cartier-kummer-map.md` and
`lem-amb-cartier-kummer-map.proof.md`, all four paragraphs. The unchanged DAG
statement specifies the coefficient, site, exponent-independence and reduction
clauses in more detail. I also read its thirteen proof steps and the resolved
stage-1 repair note. That note requires keeping the statement unchanged and
records a stage-1 re-split; it does not withdraw a Lean interface.

The formalization matches the hypotheses and clauses as follows.

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| Valuation ring, chosen uniformizer, A=O_E/varpi^m | The published `Padic.coefficientExtensionRing l E (n+1)`, lifted by `Scheme.finiteTateCoefficient`; no new valuation ring or uniformizer is chosen. |
| Arbitrary m>=1 | `n : ℕ` denotes m=n+1, including n=0. There is no ramification-index divisibility binder. |
| T a scheme with ell invertible | `T : Scheme.{u}` and `hT : IsUnit (l : Γ(T, ⊤))`; for an integer section this is equivalently invertibility in every local ring. |
| Effective Cartier i:D->T | `i : D ⟶ T`, `[IsClosedImmersion i]`, `hI : i.ker.IsInvertible`, the recorded local regular-generator predicate. |
| L=O_T(D)=I_D dual | The reused `SupportedKummerBoundary` and `supportedKummerChern` use exactly `Scheme.Modules.dual i.ker.toModules` and the section dual to `i.ker.toModulesι`. |
| Original finite pro-etale coefficient twist | The published `Scheme.finiteTateProSheaf l E n T 1` is the fixed-scalar restriction of the original `finiteCoefficientTwist`. Its underlying sections, restrictions, and tensor construction are unchanged. |
| Ordinary unbounded pro-etale derived category | `DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u+1} A))`, the fixed-scalar presentation used by the recorded comparison interface. The published finite-coefficient realization identifies this with modules over the node's coefficient ring sheaf. No derived-complete or constructible subcategory is substituted. |
| Canonical morphism i_*A_D -> A_T(1)[2] | `CartierKummerFamily` is Ext in degree 2, realized canonically by `.hom`; `cartierSupported` is the actual pro-etale `lowerStar` of the constant sheaf, embedded in degree zero, with target `Scheme.finiteTateProSheaf` in degree zero shifted by integer 2. `cartierKummerMap` is selected from the existence-and-uniqueness theorem for the normalized pair of families. |
| Composite with A_T->i_*A_D | `CartierKummerChern` uses `(Ext.mk₀ (cartierSupportedUnit ...)).comp c` for this composite, and equates its comparison pullback with the normalized étale Chern class. The unit is the existing constant-section direct-image map. |
| c1 is the Kummer Chern class | `CartierKummerChern` normalizes the étale Ext class by `supportedKummerChern`, the actual `kummerδ₁` of the Picard class of the dual ideal. It then identifies the supported composite with its exact comparison image under `cartierConstantComparison` and q. |
| Relative Cartier boundary, rather than an unspecified lift | `CartierEtaleKummerNormalization` uses the existing `SupportedKummerBoundary`, which retains the frame torsor, its canonical section on the complement, and the relative extension boundary. |
| Every exponent ell^r killing A | `r : ℕ` represents positive exponent r+1, with the literal cast `((l^(r+1) : ℕ) : A)=0`. The theorem first asserts such an exponent exists at every quotient level. |
| Canonical projection-induced twist identification | `Scheme.IsFiniteTateSiteComparison`: q sends the comparison image of a tensor p_r(x) to x tensor a, equivalently the inverse root-projection formula. This is tested after every arrow from a pro-etale object to an étale object representing that finite root, using the actual Kummer kernel inclusion into units. Such test objects locally cover the root sheaf. |
| Independence of the auxiliary exponent | `CartierKummerRealization` identifies the image of every exponent witness with the SAME `c n i hI hT`; the supported comparison preserves the quotient unit and q preserves root projections. Comparing any two exponents thus gives equality in the displayed derived category. |
| Cartier-preserving arbitrary base change | `CartierKummerBaseChange` quantifies over every `IsPullback w i' i h` with both ideals Cartier. It states the Ext/derived-arrow square under invertible p and t. p preserves the pulled-back constant quotient; The published `Scheme.IsFiniteTateProPullback` fixes t on pure tensors by pullback of every root projection. No flatness or étaleness is assumed on h. |
| All reductions A_{E,b}->A_{E,a}, b>=a>=1 | `CartierKummerReduction` quantifies over all a<=b in zero-based level numbering. `cartierCoefficientReduction` is the actual ideal-power quotient factor. The supported constant map sends the actual `cartierSupportedGenerator` z to its reduction, the target map sends x tensor z to x tensor reduction(z), and their derived Ext square is stated. |
| Derived coefficient extension without flatness of A over Z/ell^r | `SupportedKummerScalar` on étale witnesses and `IsCartierDerivedScalarUnit` on the pro-etale source and target test the scalar adjunction against EVERY unbounded derived object. These are derived scalar units, rather than merely underived tensor identifications. |
| Ordinary étale witness mu_(ell^r) tensor^L A | `CartierEtaleKummerFamily` takes values in Ext with target the existing `Scheme.finiteEtaleTateLine`. The root module is a flat rank-one Z/ell^r-line under the invertibility hypothesis, so this degree-zero ordinary scalar extension is its derived scalar extension. `CartierKummerRealization` retains the supported étale class and its comparison image explicitly. |

Dependency declarations and signatures read:

- `Sheaf.Paper.CoefficientTwistsDetailed`: `WeilConjectures.finiteCoefficientTwist`,
  `coefficientTateTwists`; their concrete first line is
  `AlgebraicGeometry.Scheme.purTwistFiniteOne` in the publicly imported
  `Sheaf.Paper.PurTwistSheafLocallyFree`. I read its construction from
  `purTwistZlOne`, `purTwistIntegralOne`, and `purTwistIntegralQuotient`.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `IdealSheafData.IsInvertible.isInvertible_dual_toModules`,
  `Scheme.Modules.dual`, `IdealSheafData.toModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategory`,
  `finiteCoefficientDerivedComparison` and its fixed-scalar realization.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`, together with its imported unbounded exact
  comparison `comparisonUpperStar.mapDerivedCategory`. The Ext exact-functor
  operation in this file is the same termwise derived comparison, expressed on
  degree-zero source and target objects.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`, the
  unbounded K-flat-derived tensor, including its coefficient and scheme binders.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem` and its published
  definition modules: `SupportedKummerBoundary`, `supportedKummerChern`,
  `supportedConstantUnit`, `supportedConstantExchange`, `SupportedKummerScalar`,
  `OrdinaryFiniteTwistTransport`, `ordinaryFiniteConstant` and the integral
  generator. These notions were found in the existing library and reused.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleBaseChange`, `proEtaleConstantDirectImageMap`, and
  `proEtaleConstantInverseImageMap`; the generic `ProEtale.upperStar/lowerStar`
  are those this recorded interface reexports.

The existing additional statement dependencies are published
nodes: `def-asd-ordinary-supported-kummer-system`,
`def-asd-ordinary-supported-kummer-boundary`,
`def-asd-ordinary-supported-kummer-scalar`, `def-weil-proetale-inverse-image`, and
`def-pur-proetale-constant-module-unit`. The new pro-etale scalar and finite-Tate ownership definitions are described below. The descent theorem module is repaired by extraction as required by return L F1.
A read-only dependency traversal verified none reaches this item, including the finite Tate site-descent node (2264 reachable nodes inspected). All recorded
proof-dependency modules with Lean records are imported privately as required.

Searches actually performed:

- msearch leanfinder: `An effective Cartier divisor defines a supported Kummer
  class in degree two natural under pullback`. Eight hits, including
  `Scheme.Hom.ker` and ideal-sheaf/local-equation lemmas; no matching supported
  derived Cartier class with the original pro-etale twist.
- msearch loogle: `"Kummer"`. Eight field/ring-theoretic Kummer and
  Kummer-Dedekind hits; no match.
- msearch grep: `Kummer|Cartier.*class|Chern`. Twenty-five hits in arithmetic
  Kummer-Dedekind and p-adic valuation files; no match.
- msearch leansearch: `A Cartier divisor defines a supported Kummer first Chern
  class in degree two etale cohomology`. Eight hits about the étale locus,
  cohomology-class constructors and formal étaleness; no matching statement.
- `rg` of the node id in the upstream `WeilConjectures` source found no declaration.
  Keyword searches of upstream and `lean/Sheaf` found the existing ordinary
  supported Kummer system and theorem, which were read. They supply the étale
  part but do not state the projection-normalized pro-etale comparison, exponent
  independence, or the simultaneous finite coefficient reductions required here.
- A name search of the upstream and side sources checked the new public names.

Edge cases checked before and during writing:

- m=1 is n=0 and is retained even for ramification index e=2; no e|m occurs.
- The empty divisor has zero supported source and the trivial Cartier line with
  its canonical nowhere-vanishing section. The boundary specification gives zero.
- The empty scheme is retained by all scheme binders and local-generator formulas.
- Pullback by the identity and equal coefficient levels are included. Constant
  and pure-tensor normalizations give the ordinary identity comparisons.
- A non-flat h is allowed whenever the pullback divisor remains Cartier. Pullback
  by i itself generally fails that hypothesis, as it should.
- All r>=1 annihilating the coefficient ring are retained; no minimal exponent is
  selected. Any two can be compared through their maximum.
- No global principal equation, regular ambient scheme, finite type, separatedness,
  boundedness of complexes, or quotient-flatness hypothesis was added.

No statement correction and no STATEMENT-DISPUTED flag is needed.

## Saved second reading by Q121

The dispatcher explicitly prohibited starting another agent. This section records
my fresh second pass through the node and file; it does not claim that a separate
worker reviewed them. The maintainer's independent mathematical review remains
the independent reading specified in the dispatch brief.

I checked the original thirteen-step node and all the predicate bodies against
the main theorem. In particular, a bare existential supported arrow would admit
zero and would omit the relative class. The delivered statement instead retains
`SupportedKummerBoundary` and the actual Kummer Chern normalization. A bare
existential twist isomorphism would admit a scalar multiple; the delivered q is
fixed on root projections. The support isomorphism is fixed by the quotient unit.
The pro-etale pullback and reduction equations are stated separately, not left
only in the proof text. The same c for every r makes exponent independence an
actual equality. The actual quotient levels are n+1, so m=1 is present.

During this pass I corrected the natural-number cast of l^(r+1), made the units
coercions explicit in the root-projection equations, and replaced the provisional Tate-line transport definitions with the exact
published finite Tate site-descent declarations.
The target is the actual published inverse-limit twist; the étale tensor
is its witness. All new declaration docstrings name the item and source.

Final declaration interface: `CartierKummerFamily` stores the arrows in the
published `Ext` type, and `cartierKummerMap` exports its canonical `.hom` in the
ordinary unbounded derived category. In
`Sheaf.Paper.FiniteTateSiteDescent` I read every helper signature and docstring
and the complete `finite_tate_site_descent` theorem. This delivery reuses
`finiteTateCoefficient`, `finiteTateProSheaf`, `finiteTateProGenerator`,
`IsFiniteTateSiteComparison` at tensor exponent 1, and
`IsFiniteTateProPullback` at tensor exponent 1. No new Tate presentation,
pure-tensor construction or root-comparison predicate is defined here.

Supplemental searches for that transport interface: msearch leansearch
`The original finite pro etale Tate twist in constant scalar modules and its
root projection normalized comparison` returned eight formally-etale/root-pairing
hits; loogle `"Tate"` returned twelve Init.Prelude state-monad hits;
msearch grep `purTwistFiniteOne|proEtaleRootsOfUnityTower` returned no Mathlib hits.
The corresponding read-only source grep found `FiniteTateSiteDescent`, whose
recorded declarations were reused. Blueprint search `Tate twist projection`
returned no definition node. The existing Tate interface is reused; the distinct pro-etale coefficient-reduction predicate is the new definition node described below.

All compatibility equations are written in Ext. The existing canonical Ext/derived-Hom
bijection takes Ext products to the displayed degree-two derived compositions;
`cartierKummerMap` provides the actual derived arrow. The Chern equation directly
normalizes the supported composite, so no auxiliary arbitrary Chern class is selected.

`Sheaf.AlgebraicGeometry.ProEtaleConstantModuleUnit` supplies the already recorded
`Scheme.proEtaleFixedConstantModule`, used at the actual quotient ring. Its
signature and docstring, and the unique scalar-unit realization comparison in
that module, were read. This is the same fixed constant object used by the
recorded ordinary pro-etale module presentation.

The ordinary etale witness is specified by its actual relative boundary.
The requested scheme-pullback equation is stated on the pro-etale arrow in
`CartierKummerBaseChange`, with the published normalized Tate pullback and the
canonical supported quotient normalization. The Chern equation is in
`CartierKummerChern`, independently of the relative-boundary predicate. Scalar
compatibility is stated both for the ordinary etale witnesses and for the
pro-etale arrows. All these clauses retain their original sites and coefficients.

## New nodes
`def-amb-proetale-supported-coefficient-reduction` defines coefficient-reduction
compatibility for supported degree-two arrows into the ORIGINAL finite pro-etale
Tate line. Its module is `Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction`.
It contains the supported source and its constant generator/unit, the arrow-family
space, the actual quotient factor, the unbounded derived scalar-unit predicate,
and the normalized Ext reduction square. It asserts no existence of an arrow and
uses no chosen map. The item uses its `CartierKummerReduction` predicate directly.
The source is the final coefficient-extension/reduction clause of the current
Cartier-Kummer proof. The ordinary etale scalar definition cannot supply this
predicate because its site and coefficient objects are fixed to the etale site;
its signature and body were read. The existing original Tate presentation and
pure tensors from `FiniteTateSiteDescent` are reused without redefinition.

Before creating it, LeanSearch on supported pro-etale finite Tate coefficient
systems returned eight etale-algebra/scheme hits; Loogle `"restrictScalars"`
returned twelve ordinary linear-map hits; Mathlib grep on
`SupportedDerivedScalarUnit|SupportedKummerScalar` returned zero hits. Source and
DAG grep found the etale scalar definition and its callers, with no corresponding
pro-etale supported coefficient-reduction predicate. Blueprint search
`supported coefficient system` returned zero matches. The node records these
searches. Its edge cases include a=b, m=1, the empty divisor/scheme, and non-flat
coefficient reductions. The new module has real definitions and no postponed
proof. My second reading checked its constants, root tensors, universal property
on ALL unbounded objects, and Ext equation against its complete node statement.
The ownership node also cites `lem-amb-finite-tate-site-descent` in its statement dependency list solely to place the changed extraction module in the delivery prerequisite closure; its statement explicitly says this is the source module citation and does not use the descent theorem conclusion. The item and `def-amb-proetale-supported-coefficient-reduction` cite only the new ownership node for these definitions.

`def-amb-finite-tate-site-comparison-data` owns
`Sheaf.Paper.FiniteTateSiteComparisonData`. It contains all twelve existing definitions
extracted from `Sheaf.Paper.FiniteTateSiteDescent`: `finiteTateCoefficient`,
`finiteTateConstantRestriction`, `finiteTateProSheaf`, `finiteTateProGenerator`,
`finiteTateProPowerGenerator`, `finiteTateEtalePowerGenerator`,
`finiteTateEtaleRootValue`, `finiteTateLimitRootValue`, `IsFiniteTateSiteComparison`,
`IsFiniteTateEtalePullback`, `IsFiniteTateProPullback`, and
`IsFiniteTateEtaleTransition`, all in `AlgebraicGeometry.Scheme`.
Their names, binders and bodies are unchanged; the source/blueprint docstrings now name
the owning definition node. The new node introduces no chosen comparison or existence
assertion and has no `sorry`. The source is Stacks 03PK (section-kummer), 099R
(section-comparison), and the final paragraph of the current Cartier-Kummer proof,
which identifies the scalar-extended target with the original Tate twist.

Fresh searches on 2026-10-18: msearch LeanSearch with query
"Fixed scalar presentation of finite pro etale Tate twists with root projection normalized
comparison and pullback predicates" returned eight general formally-etale, pullback and
adjunction declarations, with no matching presentation. Loogle `"finiteTate"` returned
zero hits. Mathlib grep `finiteTateCoefficient|IsFiniteTateSiteComparison|finiteTateConstantRestriction`
returned zero hits. Read-only rg in upstream `WeilConjectures`, side `lean/Sheaf`, and
`dag/nodes` found the theorem module and its theorem record, with no definition node owning
these declarations. `blueprint_refs.py search 'finite Tate'` found five statements, none
defining this interface; `ancestor` confirms this item's own blueprint origin.
The new node records these actual queries and results.

Hypothesis/clause reading: prime, finite extension and positive coefficient level are
`l`, `E` and `n+1`; fixed scalars are `finiteTateCoefficient` and
`finiteTateConstantRestriction`. Original twists are `finiteTateProSheaf`.
The first tensor, higher tensors, and etale tensors are the three generator definitions.
The actual root units are the two root-value definitions. Root-projection normalization,
etale pullback, pro-etale pullback, and exponent transition are respectively the four
`IsFiniteTate*` predicates. These are definitions for arbitrary schemes; no invertibility
hypothesis is required until the separate existence theorem. Zero tensor power and the
empty scheme are included; `n=0` represents coefficient exponent one. The transition
predicate uses natural subtraction also when r'<r; existence is asserted by the theorem
only when r<=r'. No hypothesis has been added to any extracted declaration.

## Returned-delivery repair

The initial dry run of the saved packet reproduced return L: the coefficient
module compiled in each file-only phase (35.4--38.7 seconds), but the theorem
module timed out after 60 seconds. Server confirmation reproduced the timeout.
The mathematical statements and normalization predicates are retained.

The fresh self-check also found that the saved report's proof-import claim did
not match the saved module. The theorem module now explicitly imports all
recorded proof-dependency modules, retaining public imports for its statement
interfaces. The coefficient-twist dependency's current owning module is
`Sheaf.Paper.PbcCoefficientTwists`; it reexports the same finite coefficient
construction used here and is now imported. The sheafification and small-Ext instance
caches are public named aliases of existing instance proofs and are listed in
their owning nodes' declarations, so the delivered interfaces require no
file-local instance registration.

The baseline profile completed at 54.3 seconds, close to the hard limit. It
reported about 14.6 seconds in kernel checking of `CartierKummerChern`, with
additional generated instance proofs, and 46.7 seconds in the asynchronously
running private-module linter. These overlapping times are not additive.
The repair caches `HasSheafify` (including left exactness) and `HasExt.{u+1}`
for the actual pro-etale and etale module categories. These propositions are
proved by the existing instances; no new mathematical assumption, category,
coefficient, or universe identification is introduced. This replaces repeated
large synthesized instance expressions with references to named proof constants.

The repaired profile compiled both files separately through `scompile.py`:
the coefficient module took 29.9--32.0 seconds across its phases, and the theorem
module took 44.3 seconds in the sandbox and 46.3 seconds in the library check.
Kernel checking of the Chern predicate fell to 8.5--8.7 seconds. Only the scratch
profiling file emitted the expected development-option warnings; the delivered
files contain no profiling settings. The required final dry run checks those
actual delivery files again, with the unchanged 60-second limit.

The fresh second pass checked that the theorem signature and all seven
normalization/scalar/pullback clauses are unchanged, including the positive
coefficient level n+1, every annihilating exponent r+1, the empty divisor and
scheme, identity pullback, equal coefficient levels, and arbitrary non-flat
Cartier-preserving pullback. The coefficient predicate's signature and body are
unchanged. All cache universes are explicitly u+1, exactly the existing sheaf
and Ext universes; every variable is explicitly bound. No local instance or
notation remains, and each new cache is included in its owner's lean.declarations.

Final validation: `deliver2.py Q121 lem-amb-cartier-kummer-map --no-push`
printed OK: both actual delivery files compile cleanly and the packet passes
preflight. That earlier packet contained two Lean modules and their two node files.
The current ownership repair below supersedes that inventory.

## Dependency modules

`lem-amb-finite-tate-site-descent`: its recorded module owned both the existence theorem
and twelve definitions. The item and its scalar-reduction definition use the latter and
do not use the theorem's conclusion, which caused return L F1. The module now publicly
imports `Sheaf.Paper.FiniteTateSiteComparisonData` and contains only the unchanged
`finite_tate_site_descent` theorem, including its full existing proof-plan docstring.
The dependency node is copied with only `lean` changed: its declaration inventory now
contains only that theorem and `lean.note` explains the extraction. This module change
is explicitly required by the return to preserve one definition per notion. Its natural
statement, dependency fields and proof are untouched.

## Returned-delivery repair: L F1 at 239dc8cbaf91

The required first dry run of the saved packet passed at dry-run commit 525fcf33f0.
I retained its mathematical statements and definitions and repaired the returned semantic
ownership fault. Both the item and
`def-amb-proetale-supported-coefficient-reduction` replace their statement dependency
`lem-amb-finite-tate-site-descent` by `def-amb-finite-tate-site-comparison-data`.
The latter's natural statement citation is updated accordingly. Both consumer modules
now publicly import the owning definition module directly. The theorem module publicly
imports the new module, so all existing clients still see the same names and there is
one definition of each notion. The new module compiled cleanly through `scompile.py`
(5.7 seconds sandbox, 5.9 seconds library).

## Second reading by Q121

Fresh self-check of F1 (no sub-agents, as the dispatcher requires): I compared each
extracted declaration with the published server source read through `scompile.py --source`
and the local read-only source. Removing just the docstrings leaves identical definition
text. The descent theorem's signature and complete proof-plan docstring are unchanged.
Both consumers' definition/theorem text is unchanged; only their import changes.
The new node's predicate clauses were read against all four predicate bodies, including
arbitrary pro-etale tests over etale objects, root values at every projection for
pullback, positive predecessor exponents, zero tensor powers and natural subtraction.
There are four Lean modules, four node files and this report in the repaired packet.
The maintainer's independent review remains the independent reading.

Final full-packet `scompile.py` check passed cleanly for all four modules, each separately:
`FiniteTateSiteComparisonData` 5.7 seconds, `ProEtaleSupportedCoefficientReduction`
28.8 seconds, `FiniteTateSiteDescent` 4.1 seconds, and `CartierKummerMap` 42.1 seconds
(library phases). Sandbox and private-overlay phases also passed without warnings.

## Delivery tool failure after completing L F1

The repaired packet's `deliver2.py Q121 lem-amb-cartier-kummer-map --no-push`
compiled all four files cleanly, then refused the explicitly requested theorem-module
extraction with exactly these two preflight findings:

> (b) dag/nodes/sec-smooth-purity/lem-amb-finite-tate-site-descent.json: the node
> lem-amb-finite-tate-site-descent exists on the base and is not in the item's
> statement/proof prerequisite closure on the base or as delivered: a delivery changes
> only the item, new definition nodes and dependency nodes of the item
>
> (c) lean/Sheaf/Paper/FiniteTateSiteDescent.lean: no node of the delivery has it as
> lean.file (every module is the module of the item, of a new definition node or of a
> dependency node)

The second finding follows from the first: that theorem node IS included in the packet
and its lean.file is the rejected theorem module, but preflight refuses to classify it.
Return L explicitly requires that module to import the new owning definition module;
removing its change would leave duplicate definitions. Restoring the theorem as a
statement dependency would recreate the exact F1 fault. No mathematical statement needs
correction, so a fabricated statement_change or a new dependency on the theorem would
be an improper workaround. I inspected the delivery reader's prerequisite-closure rule;
it permits only forward statement/proof dependencies, with no supported exception for
this explicitly authorized extraction of definitions from their old owning theorem.
The theorem is outside that closure once F1 is repaired. The tools are read-only for
workers under AGENTS.md section 3, so I have not edited or bypassed them.

Nothing was pushed. All four repaired Lean modules, their four node records, exact
preservation checks, search records and report remain in this sandbox for the delivery
tool's authorized ownership-move exception. A maintainer/tool repair must permit this
specific lean-only theorem-node/module relocation; the packet itself is fully compiled.

## Saved-packet retry, 2026-10-18

The fresh repair session first inspected this report and ran the prescribed
`deliver2.py Q121 lem-amb-cartier-kummer-map --no-push` on the retained packet.
All four delivered modules again compiled without errors or unexpected warnings.
Server preflight then reproduced exactly the two findings quoted above: the
required lean-only extraction repair for `lem-amb-finite-tate-site-descent` is
outside its accepted prerequisite closure, and consequently its module is
reported as having no owning delivery node. Nothing was pushed.

The fresh self-check compared the twelve extracted definition bodies with the
current shared source after stripping docstrings and normalizing whitespace:
all twelve are unchanged. The descent theorem text is unchanged. Every recorded
Lean signature is verbatim, every delivered Lean line has at most 100 characters,
and only the two theorem proofs contain `sorry`. Both consumers import and cite
the new definition owner rather than the descent theorem. The current shared
descent node differs from its sandbox copy only in `lean`. Thus F1 remains
fully repaired, and the repeated rejection is the same delivery-tool scope
failure, not a remaining Lean or statement-ownership defect. The tool sources
are read-only and have not been changed or bypassed.

## Saved-packet retry: 2026-10-18 01:34 UTC

As instructed, this session first read the saved report and ran
`deliver2.py Q121 lem-amb-cartier-kummer-map --no-push` on the retained packet.
All four actual delivery modules compiled cleanly in the wrapper's individual
checks. The refreshed current-base server preflight again returned precisely
the two previously quoted findings (b) and (c): it refuses the required lean-only
repair of `lem-amb-finite-tate-site-descent` as outside the prerequisite closure,
then refuses its module as having no admitted owner. Nothing was pushed.

A fresh read-only self-check against the current shared sources confirmed all
twelve extracted definition bodies unchanged and the descent theorem unchanged.
Each of the four node records has its exact signature in its own module, all
Lean lines meet the 100-character limit, both consumers cite the new definition
owner instead of the theorem, and the descent dependency copy changes only
`lean`. The current delivery reader has no admission path for this required
ownership extraction outside the forward dependency closure. Removing the
extraction would violate return L F1; adding an unused statement dependency
would recreate it. Tool edits and bypasses remain prohibited by AGENTS.md §3.
The fully repaired, compiled packet is retained pending the maintainer's tool
repair authorizing this ownership move.

## Final saved-packet validation, 2026-10-18

The required first dry run in this session passed: `deliver2.py Q121
lem-amb-cartier-kummer-map --no-push` printed `OK (dry run): commit bd4d72a7ea
passes the preflight and compiles; nothing pushed`. All four actual modules
compiled separately with the prescribed wrapper and unchanged 60-second limit.
The earlier preflight-scope failures recorded above no longer occur.

As instructed, the saved repair is retained. The final self-check confirms that
`FiniteTateSiteComparisonData` contains exactly the twelve extracted definitions,
while the delivered `FiniteTateSiteDescent` publicly imports that module and
redeclares none of those names. Thus the effective delivered library has one
definition of each notion, and all existing clients reuse it through the descent
module. The twelve definition bodies match the current published originals
(after removing docstrings and normalizing whitespace); the descent theorem
text is unchanged. Both consumers directly import the definition owner.

All four recorded signatures are verbatim, every Lean line is within 100
characters, and the only two postponed proofs are the matching Cartier-Kummer
and finite-Tate-descent theorems. The descent dependency node differs from the
current shared node only in `lean`. No mathematical statement or normalization
was changed during this retry. This validation supersedes the older tool-failure
status paragraphs above; there is no outstanding preflight failure.

## Returned-head duplicate-name self-check, 2026-10-18

The required first dry run of the saved packet passed at commit `f34a99a847`:
`OK (dry run): commit f34a99a847 passes the preflight and compiles; nothing pushed`.
All four modules passed their individual wrapper checks with no errors or unexpected
warnings. As the dispatch brief explicitly directs after this result, the saved
mathematical work is retained; this session adds the completed self-check record.

For return L at immutable head `f37c292b2306`, I checked each of the twelve flagged
names against the effective delivered source tree: the current read-only shared
sources with this packet's replacement files applied. Every name has exactly one
source owner, `Sheaf.Paper.FiniteTateSiteComparisonData`. The delivered
`Sheaf.Paper.FiniteTateSiteDescent` publicly imports that owner and declares none
of those twelve names. Both consumer modules also publicly import that owner.
No name was renamed, and no duplicate definition is retained in the delivered tree.
The original current-server descent source was read with `scompile.py --source`;
its twelve definition bodies match the extracted bodies after documentation and
whitespace normalization. The descent theorem and its full proof docstring are
unchanged. This is a replacement of the original owning module in the same
packet, rather than addition of a second definition alongside it.

Fresh clause reading: the prime and finite-extension binders, level `n+1`,
Cartier ideal and invertibility hypotheses remain explicit. The family has the
actual supported direct-image source and original pro-etale Tate target. The
relative Kummer normalization, Chern composite, common arrow for every
annihilating exponent, Cartier-preserving pullback square, and scalar-normalized
reduction square remain the six predicates in `cartier_kummer_map`. The exported
`cartierKummerMap` is its degree-two derived arrow. The ordinary etale witness is
retained. I checked level one, empty divisor and scheme, identity pullback,
equal coefficient levels, and non-flat Cartier-preserving pullback. There is
no ramification-divisibility or coefficient-flatness hypothesis.

All four recorded signatures occur verbatim in their modules; all delivered Lean
lines are at most 100 characters. The only postponed proofs are the matching
Cartier-Kummer and finite-Tate-descent theorems. The descent node changes only
`lean`. No statement or definition body was changed during this retry. This is
the author's self-check, as required by the no-sub-agents dispatch instruction;
the maintainer supplies independent review.

## Saved-packet self-check for return adf52c077c3d, 2026-10-18

As instructed, this session first inspected the saved report and ran the unchanged
packet through `deliver2.py Q121 lem-amb-cartier-kummer-map --no-push`. It printed
`OK (dry run): commit a8faca39c0 passes the preflight and compiles; nothing pushed`.
The local Cartier-Kummer library check reached the 60-second limit; the wrapper's
prescribed confirmation against current server sources succeeded, and the final
preflight accepted all four modules. No limit or tool was changed.

I retained the saved repair and checked the exact twelve names in return L at
immutable head `adf52c077c3d`. In the effective delivered source tree (current shared
sources with the packet's replacement modules applied), each has exactly one
source owner: `Sheaf.Paper.FiniteTateSiteComparisonData`. The replacement
`Sheaf.Paper.FiniteTateSiteDescent` publicly imports this owner and declares only
the unchanged descent theorem. Both consumers directly import the definition
owner. No declaration was renamed. I read the current server descent source with
`scompile.py --source Sheaf.Paper.FiniteTateSiteDescent` and compared the twelve
extracted definition bodies after removing docstrings and normalizing whitespace;
all are unchanged. The full descent theorem text and proof-plan docstring are
unchanged. Its node copy differs from the current shared node only in `lean`.

Fresh self-reading of the item and both definition nodes against their modules
confirmed the prime/finite-extension binders, positive levels n+1, Cartier ideal
and invertibility hypotheses, actual supported direct-image source, and original
pro-etale Tate target. The relative Kummer normalization, Chern composite, common
arrow for every annihilating exponent, arbitrary Cartier-preserving pullback,
derived scalar-normalized coefficient reduction, and ordinary etale witness are
retained. I checked level one, empty schemes and divisors, identity pullback and
equal coefficient levels, and non-flat Cartier-preserving pullback. All four
recorded signatures occur verbatim in their modules; every delivered Lean line
is at most 100 characters. Only the two matching named theorems have postponed
proofs. This is the author's self-check under the dispatcher's no-sub-agent rule;
the maintainer's independent review remains separate. No further mathematical
or source changes were needed after the successful saved-packet dry run.

## Saved-packet validation after return adf52c077c3d, 2026-10-18

The prescribed saved-packet dry run passed at `4dbb80f7f2`: preflight and
compilation accepted all four modules. The local final library check reached
its 60-second limit; the wrapper's prescribed server confirmation succeeded.
No compiler limit, launcher script or shared source was changed.

My fresh self-check read all four delivered modules and their node statements,
the current blueprint statement and proof, and the published descent source
through `scompile.py --source Sheaf.Paper.FiniteTateSiteDescent`. A read-only
comparison confirmed that all twelve names flagged by return L have exactly
one declaration in the effective delivered source tree, owned by
`Sheaf.Paper.FiniteTateSiteComparisonData`. Their bodies are unchanged after
removing docstrings and normalizing whitespace. The replacement descent module
publicly imports that owner, and its theorem and complete proof-plan docstring
are unchanged. Neither consumer duplicates or renames these declarations.

All four recorded signatures occur verbatim; all Lean lines meet the
100-character limit. The descent node changes only `lean`. Only the two
matching named theorems have postponed proofs. The prime and finite-extension
hypotheses, positive coefficient levels, Cartier condition, original pro-etale
Tate target, supported quotient, relative boundary and Chern normalization,
every annihilating exponent, Cartier-preserving arbitrary pullback, and
scalar-normalized coefficient reductions are retained. Level one, empty
schemes and divisors, identity pullback, equal levels, and non-flat
Cartier-preserving pullback remain included. This is the author's self-check
under the dispatcher's no-sub-agent instruction. As instructed after a passing
saved-packet dry run, the existing mathematical repair is retained.

## Compile-cost repair after the passing saved-packet dry run

The subsequent push attempt did not publish: current server confirmation timed
out on `CartierKummerMap`, after the coefficient module passed in 42.3 seconds.
The saved profiling log identifies `CartierKummerChern` as an expensive kernel
check. Its Chern-class expression previously formed `ordinaryFiniteClass ...
k.hom`, converting an Ext class to a derived arrow and immediately applying
the inverse equivalence inside `ordinaryFiniteClass`.

I replaced only that subexpression by its existing defining Ext expression:
`(Ext.mk₀ (ordinaryFiniteIntegralGenerator A T)).comp
(k.mapExactFunctor (RawModuleScalarComparison.forget A T)) (zero_add 2)`.
Unfolding `ordinaryFiniteClass` and `Ext.hom` and using
`Equiv.symm_apply_apply` proves equality with the former expression; the saved
`ClassConversionCheck.lean` contains precisely this check. This is the same
integral-generator coefficient-forgetting Chern class, with the intermediate
inverse pair cancelled. Its docstring now explains the equivalent expression.
No predicate clause, hypothesis, theorem signature, canonical map, twist
construction, or extracted declaration has changed. All four files are being
revalidated with the unchanged per-file compiler limit.

The full-packet `scompile.py` check passed on the current server after this
repair, with no errors or unexpected warnings: extraction 12.4 seconds,
coefficient reduction 57.6 seconds, descent 6.2 seconds, and Cartier-Kummer
50.1 seconds. Every file retained nice 19, two threads and the 60-second limit.
The earlier line saying that revalidation is running is superseded by this
successful result. Fresh self-reading confirms that cancelling the inverse
Ext realization pair preserves exactly the Chern normalization.

## Current saved-packet repair self-check, 2026-10-18

This retry first inspected the saved report and ran the prescribed unchanged-packet
`deliver2.py Q121 lem-amb-cartier-kummer-map --no-push`. The saved mathematical
repair is retained. A fresh source ownership scan over the current shared Lean
sources with the four delivery replacements applied confirms exactly one owner
for every one of the twelve names in return L at `adf52c077c3d`:
`Sheaf.Paper.FiniteTateSiteComparisonData`. The replacement descent module publicly
imports that owner and declares none of those names. Both consumers directly
import the owner. No name was renamed.

The current published descent source was read through `scompile.py --source`.
A fresh comparison of all twelve declaration bodies, normalized only for whitespace
and excluding their docstrings, confirms that each matches its published original.
The complete descent theorem and its proof-plan docstring are unchanged. The
four node signatures are verbatim; all delivered Lean lines are within 100 characters;
all files explicitly disable auto-implicit variables. The descent node differs
from its current shared version only in `lean`.

The second reading rechecked both new definition-node statements and the item
against their Lean bodies, including the original finite Tate target, positive
levels, every annihilating exponent, relative boundary, supported quotient and
Chern composite, arbitrary Cartier-preserving pullback, and the scalar-unit
universal property on every unbounded object. The direct Ext expression in the
Chern predicate is the existing `ordinaryFiniteClass` expression after cancelling
`Ext.homEquiv.symm (Ext.homEquiv k)`; it preserves the Chern normalization. Level one,
empty schemes and divisors, identity pullback, equal coefficient levels, and
non-flat Cartier-preserving pullbacks remain included. This is the author's
self-check, with no sub-agents as instructed; independent review is the maintainer's.

The required saved-packet dry run passed at `347a4b0ca2`:
`OK (dry run): commit 347a4b0ca2 passes the preflight and compiles; nothing pushed`.
The local coefficient-module sandbox check timed out at 60 seconds; the wrapper's
prescribed confirmation against current server sources succeeded. No compiler
limit, launcher script, shared source, mathematical statement, or declaration
body was changed during this retry. The retained ownership extraction fixes
return L, as confirmed by the source comparison above.


## Repair of returned delivery

The returned preflight identified duplicate declarations in `Sheaf.Paper.FiniteTateSiteComparisonData`: all twelve finite-Tate names already exist in the published `Sheaf.Paper.FiniteTateSiteDescent`. I removed both duplicate source modules from this packet, changed the two delivered modules to import and reuse `Sheaf.Paper.FiniteTateSiteDescent`, and marked the extraction and descent dependency Lean records `existing: true` with the published module and declarations. The non-existent extracted helper `finiteTateCoefficientCommRing` was removed from the declaration list. The item and new coefficient-reduction module therefore compile against the single published ownership source.

## Saved-packet self-check for return f08de612c173, 2026-10-18

This retry first read the saved report and invoked the prescribed unchanged-packet
`deliver2.py Q121 lem-amb-cartier-kummer-map --no-push`. The saved repair is
retained: the packet has two Lean modules, both using the published
`Sheaf.Paper.FiniteTateSiteDescent`, and no extracted duplicate module. Reading
that published source with `scompile.py --source` confirmed all twelve recorded
finite-Tate definitions and the descent theorem in that one module.

I reread both delivered modules, their node statements, and the current
main-20261015 Cartier-Kummer statement and proof. The explicit prime and finite
extension, all positive levels, Cartier and invertibility hypotheses, supported
direct image, original pro-etale Tate target, relative Kummer boundary, Chern
composite, every annihilating exponent, arbitrary Cartier-preserving pullback,
and derived scalar-normalized reductions remain present. Level one, the empty
scheme and divisor, identity pullback, equal coefficient levels, and non-flat
Cartier-preserving pullback remain included. No mathematical statement or
construction was changed in this retry.

A fresh mechanical self-check confirmed both signatures verbatim, all module
declarations recorded, explicit `autoImplicit false`, and maximum line width 97.
Only `cartier_kummer_map` has a postponed proof in these two modules; the
coefficient module contains no `sorry`. The descent node changes only `lean`;
the item's other change is the already recorded addition of statement dependencies.
This is the author's self-check under the dispatcher's no-sub-agent instruction;
the maintainer's independent review remains separate.

## Saved-packet self-check for return 6458eaf48b61, 2026-10-18

This retry first inspected the saved report and ran the unchanged packet through
`deliver2.py Q121 lem-amb-cartier-kummer-map --no-push`. It passed at
`955b711aaa`: preflight and compilation succeeded. The initial overlay reported
an unavailable cached `PbcCoefficientTwists.olean`; the wrapper's prescribed
confirmation against current server sources succeeded. The returned timeout in
`Sheaf.Paper.DerivedPullbackTensorHom` did not prevent this validation. Following
the dispatch instruction for a passing saved packet, the mathematical work is
retained without source or signature changes.

I reread both delivered modules, all four node statements and Lean records, and
the current main-20261015 Cartier-Kummer statement and proof. The clauses retain
the prime and finite extension, every positive quotient level, Cartier and
invertibility hypotheses, supported direct image and original pro-etale Tate
line, relative Kummer boundary, Chern composite, every annihilating exponent,
arbitrary Cartier-preserving pullback, and derived scalar-normalized coefficient
reductions. The ordinary etale witness remains explicit. Level one, empty schemes
and divisors, identity pullback, equal coefficient levels and non-flat
Cartier-preserving pullback remain included.

A fresh source read through `scompile.py --source Sheaf.Paper.FiniteTateSiteDescent`
confirmed the twelve finite-Tate declarations and descent theorem, each with one
owner in that published module. Both delivered modules import it, and neither
contains extracted duplicates. All four recorded signatures are verbatim; both
Lean modules disable auto-implicit variables, have maximum line width 97, and
record every declaration. Only `cartier_kummer_map` has a postponed proof; the
coefficient-reduction module contains no `sorry`. Comparison with the current
shared node files confirms that the descent dependency changes only `lean`, and
the item changes only `lean` and its permitted added `stmt_deps`. This is the
author's self-check under the dispatcher's no-sub-agent instruction; independent
review remains the maintainer's responsibility.

## Saved-packet self-check for return 17783e030a08, 2026-10-18

This retry first inspected the saved report and ran the retained packet through
`deliver2.py Q121 lem-amb-cartier-kummer-map --no-push`. It passed at
`7ff7c25dc5`: preflight and compilation succeeded. The initial overlay lacked
a cached `SfIntegralConstructibleTriangulated.olean`; the wrapper's prescribed
confirmation against current server sources succeeded. The returned missing
`OrdinaryFiniteP1Arrows.olean` did not recur in the successful confirmation.
As explicitly instructed after a passing saved-packet dry run, both Lean modules
and all four node records are retained without mathematical or signature changes.

I reread both delivered modules, all four node statements and records, and the
current main-20261015 Cartier-Kummer statement and proof. The prime, finite
extension, every positive quotient level, Cartier and invertibility hypotheses,
actual supported direct image and original pro-etale Tate target remain explicit.
The relative boundary normalization, Chern composite, common arrow for every
annihilating exponent, arbitrary Cartier-preserving pullback, scalar-normalized
coefficient reductions and ordinary etale witness remain present. Level one,
empty schemes and divisors, identity pullback, equal coefficient levels and
non-flat Cartier-preserving pullback are included. No ramification-divisibility
or coefficient-flatness hypothesis is imposed.

A fresh published-source read with `scompile.py --source
Sheaf.Paper.FiniteTateSiteDescent` confirmed the twelve finite-Tate definitions
and descent theorem in that module. Both delivered modules reuse that owner;
there is no duplicate extraction or replacement descent module in this packet.
All four recorded signatures occur verbatim in their sources. Both delivered
modules explicitly disable auto-implicit variables and have maximum line width
97. Only `cartier_kummer_map` has a postponed proof; the coefficient-reduction
module contains no `sorry`. Against the current shared nodes, the descent record
changes only `lean`, and the item changes only `lean` and the authorized added
`stmt_deps`. This is the author's self-check under the dispatcher's no-sub-agent
instruction; independent review remains the maintainer's responsibility.
