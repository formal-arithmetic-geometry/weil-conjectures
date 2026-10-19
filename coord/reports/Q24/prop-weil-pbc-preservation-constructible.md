## Worker report

Resumed worker audit (2026-10-16): re-read the current item, its recorded dependency
interfaces, all five sandbox modules, and the source blueprint paragraph. The existing
Lean statements need no revision. Confirmed again through `scompile.py --source` that
the complete-category and completed-pullback modules are not published. Repeated the
worker's LeanFinder, Loogle and Mathlib grep queries below with the same results.
Checked that the four dependency node copies differ from the shared base only in
`lean`, and the item only in `lean` and the two documented added `stmt_deps`.
All five recorded signatures match their source slices and every Lean line is at
most 100 characters. The earlier independent second reading below is retained;
this resumed worker has not supplied a replacement second reading or pushed a delivery.

The module `Sheaf.Paper.PreservationConstructible` states
`WeilConjectures.pbc_preservation_constructible`, with a sorry proof. The item statement
is unchanged. Every definition has actual data. Ordinary Rf_* is constructed from
sectionwise module pushforward through the adjoint of `completedCoefficientMap`, then
Mathlib's unbounded K-injective right derivation. No arbitrary coefficient map or
coefficient isomorphism is assumed. The only additional theorem in this module is the
named sectionwise additivity assertion needed by that construction; its proof is sorry.
`pbcReductionsCohomologyIn` records support containment on the canonical positive quotient
reductions, transported through the fixed equivalent small site.

Hypotheses and clauses, individually:

- The prime ell is `(l : ℕ) [Fact l.Prime]`. The finite extension E/Q_l is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  `pbcOECoefficients l E` has the existing valuation ring
  `Padic.coefficientExtensionIntegers l E`, the ideal spanned by the chosen existing
  `Padic.coefficientExtensionUniformizer l E`, and the finite perfect quotients.
- The four schemes and four arrows are the explicit X', X, Y', Y and g', f', f, g
  binders. `_square : ChosenCartesianSquare g' f' f g` retains the chosen fibre-product
  isomorphism, its two projection equations, and square commutativity.
- Each of the four Noetherian hypotheses is its separate `IsNoetherian` instance.
  Each finite-dimension hypothesis `_hDimX`, `_hDimY`, `_hDimX'`, `_hDimY'` asserts
  a natural upper bound on topological Krull dimension. WithBot includes the empty scheme.
- Both properness assumptions appear separately as `[IsProper f] [IsProper f']`.
- `(N : ℕ) (_hN : 0 < N)` is the common positive annihilator.
  `_hAnn : (N : Padic.coefficientExtensionRing l E 1) = 0` is exactly annihilation
  of A/I; killing 1 kills its whole additive group. The four `_hInvert...` binders
  assert `IsUnit (N : Γ(T, ⊤))` for the respective schemes. No separate ell-invertibility
  hypothesis is added: it follows from these assumptions as the node's proof explains.
- `(e : ℕ)` represents the nonnegative integer e. `_hFib` bounds the topological
  dimension of `pullback f` along the algebraic closure of each actual residue field.
  This is the geometric fibre at every point y, using the dependency's recorded formula.
- `(a b : ℤ)` supplies the common interval, without adding an ordering assumption.
  K is in the ambient derived category over the completed coefficient sheaf, with
  `_hK : IsPbcBoundedConstructibleComplete l E X K`, exactly the object predicate of
  the full subcategory. Its three conditions are intrinsic completeness, uniformly
  bounded constructible canonical reductions, and compatible retained etale origins.
- `_hInterval : pbcReductionsCohomologyIn ... a b K` is the stated common reduction
  support bound. Index n denotes exponent n+1, so every positive reduction is covered.
- Conclusion conjunct 1 is membership of `pbcCompletedDerivedDirectImage f ... K` on Y.
- Conjunct 2 is membership of `completedPullback g ...` of that same direct image on Y'.
- Conjunct 3 is membership of `completedPullback g' ... K` on X'.
- Conjunct 4 is membership of the ordinary direct image along f' of that third output.
- Conjunct 5 bounds the third output's canonical reductions by [a,b].
- Conjuncts 6, 7 and 8 bound the first, second and fourth outputs by [a,b+2e].
  `b + 2 * (e : ℤ)` substitutes c=2e without a new free parameter. The support
  predicate is vanishing in all q<a or b<q. It does not assert equal support or Tor
  amplitude, and does not incorrectly put the second output in [a,b].

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`, with its full inherited square data.
- `Sheaf.Paper.AdicCoefficientDatum`, the generalized continuous-function sheaves in
  `AlgebraicGeometry.Scheme.AdicCoefficients`, which reexport
  `Sheaf.Paper.CompletedAdicCoefficientDatum`: `AdicCoefficientDatum`,
  `CompletedAdicModules`, `CompletedAdicTowers`, `completedAdicRing`,
  `completedAdicReduction`, `completedAdicQuotientReduction`, and canonical balancing.
- `Sheaf.Paper.WeilPbcBoundedConstructibleTower`, the already delivered Q03 small-site
  interface: `pbcCompletedDerivedCategory`, `pbcReduction`, `pbcNormalization`,
  `PbcAdicTower`, `IsPbcBoundedConstructibleTower`, `PbcUniformlyBoundedConstructible`.
  This transports the completed coefficients and quotient actions rather than imposing
  equality of the full site's object and morphism universes.
- `Sheaf.Paper.EtaleOriginReduction`, `PbcEtaleOriginDataWithCoefficients` and
  `PbcEtaleOriginWitnessData`, retain the pair (L,alpha) with the actual comparison.
- `Sheaf.Paper.WeilPbcBoundedConstructibleComplete`, `pbcOECoefficients`,
  `PbcCompatibleEtaleWitness`, `IsPbcBoundedConstructibleComplete`, and
  `pbcBoundedConstructibleComplete`. The predicate is the object class of the full
  subcategory, so stating preservation with this predicate has the same objects and
  morphisms as membership in that category.
- `Sheaf.Paper.CompletedPullback`, `completedCoefficientMap`, `completedTowerPullback`,
  `completedPullback`, and its comparison unit, including the strict quotient-tower
  representative normalization. This is the delivered Q03 construction, reused whole.
- The existing arbitrary-ring module operations supply
  `proEtaleRingModules_hasKInjectiveResolutions` for the completed ring. Mathlib's
  `SheafOfModules.pushforward` and `Functor.rightDerivedFunctor` supply ordinary Rf_*.
- The scheme-conventions node explicitly defines nothing of its own. Its recorded
  Mathlib notions `IsProper`, `IsNoetherian`, `topologicalKrullDim` and `pullback` are used.
- Existing, stated proof dependencies are imported without `public`:
  `Sheaf.AlgebraicGeometry.FiniteLevelAmplification`,
  `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`,
  `Sheaf.Paper.ProEtaleCanonicalTensorPullback`,
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`,
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`,
  `Sheaf.Paper.RestrictionDirectImage`, and `Sheaf.Paper.ConstantCompletionEquivalence`.
  The tower, coefficient and complete-category proof dependencies are already public
  statement imports. The other five proof prerequisites have no published declaration:
  thm-weil-pbc-amplification-proper, lem-weil-pbc-normalized-constructible-local-effectivity,
  prop-weil-pbc-direct-image-limits, lemma-weil-pbc-perfect-projection-formula, and
  lemma-weil-pbc-completed-pullback-reduction. Their proof plans are retained in the
  theorem docstring; stage 2 supplies no proofs. No proof import closes an import cycle.

Edge cases checked mathematically before writing: zero K has empty support and satisfies
any interval; empty schemes have dimension bottom and are not excluded by the natural
upper bound; identity squares and e=0 retain both pullback bounds and direct-image bounds;
a=b is an inclusive single-degree interval; a>b permits only zero cohomology and is
not excluded; n=0 indexes the first positive quotient,
not the exponent-zero zero ring; arbitrary g and g' have no extra finite-type or
smoothness assumptions. The same actual objects recur in memberships and interval bounds.
All universes and variables are explicit, with `set_option autoImplicit false`.

Searches for an exact existing statement:

- `msearch.py ... leanfinder`, query "Proper direct image and completed pullback preserve
  bounded constructible adically complete complexes and uniform reduction cohomological
  bounds": 8 hits, including AdicCompletion.map_exact and affine transition limit results;
  none states the four-output theorem.
- `msearch.py ... loogle`, query `DerivedCategory, SheafOfModules`: 0 hits.
- `msearch.py ... grep`, query `constructible.*proper|proper.*constructible` in
  Mathlib/AlgebraicGeometry: 0 hits. Direct rg repeats that Mathlib search with 0 hits.
- `msearch.py ... leansearch`, query "Proper direct image and completed pullback preserve
  constructible complete complexes with uniformly bounded reductions": unavailable,
  Internal Server Error. This is recorded as unavailable, not as evidence of absence.
- rg of the upstream WeilConjectures sources for the node id and preservation names:
  no exact match; the broader phrase search found only the separate stability matrix
  and exceptional-adjoint context. rg in lean/Sheaf and dag/lean_names_upstream.json
  found no existing theorem or collision with any of this module's new names.
- Read the current published sources via `scompile.py --source` for
  Sheaf.Paper.BoundedConstructibleComplete, Sheaf.Paper.CompletedPullback,
  Sheaf.Paper.WeilPbcBoundedConstructibleComplete, Sheaf.Paper.WeilPbcBoundedConstructibleTower
  and Sheaf.Paper.EtaleOriginReduction: unavailable. Read the already delivered
  deliver/Q03/def-weil-pbc-bounded-constructible-complete and
  deliver/Q03/def-weil-pbc-completed-pullback node records and source files instead,
  including the prior return entries; their corrected imports are reused.
- Read the source blueprint proposition on the server. The reviewed DAG's corrected
  statement and canonical-reduction proof are authoritative here; the older source
  paragraph's erroneous claim that both pullbacks retain [a,b] is not reintroduced.

No statement correction, new independent definition node, or STATEMENT-DISPUTED issue.
The two added stmt_deps are existing recorded notions for retained origin witnesses and
ordinary module operations, as allowed by brief-stage2 section 5.

## Dependency modules

`def-weil-pbc-bounded-constructible-complete`: no Lean record or published module exists.
Reuse Q03's already delivered `Sheaf.Paper.WeilPbcBoundedConstructibleComplete`, whose
real coefficient datum uses the existing O_E and uniformizer. The predicate is the
conjunction of intrinsic completeness, common local models with normalization-compatible
reductions, and the existence of compatible retained etale witnesses. Each beta is
quotient-linear, each alpha comparison uses the canonical inverse-image/reduction
comparison, and every ordered triple satisfies the quotient cocycle. The full
subcategory retains all ambient morphisms. Its finite-dimensional/noetherian/ell-unit
domain is explicit; the preservation theorem derives ell-invertibility from N.

`def-weil-pbc-bounded-constructible-tower`: the recorded full-site interface has a datum
in Type (u+1), whereas the recorded completed-ring and intrinsic-completion interfaces
use A in Type u and a lifted quotient ring. Reuse Q03's already delivered equivalent
small-site interface `Sheaf.Paper.WeilPbcBoundedConstructibleTower`, without changing the
node's statement. `PbcAdicTower` retains the strict tower, actual quotient objects,
evaluation isomorphisms, transition equations and quotient cocycle. The uniform property
has one finite locally closed stratification, covers, bounded complexes with adic-lisse
terms, finite-lisse reduction cohomology, and compatible quotient-linear e_n. Canonical
reductions specialize this construction. No independent arbitrary normalization or
arbitrary local comparison map is substituted for the canonical ones.

`def-weil-pbc-etale-origin-witness`: its recorded `EtaleOriginWitness` is for a full-site
finite coefficient derived Plus category. This does not directly type the normalized
quotient reductions on the equivalent small site. Reuse Q03's already delivered
`Sheaf.Paper.EtaleOriginReduction` transport, retaining the bounded-below L and the
specified alpha isomorphism through the actual comparison functor. It publicly retains
the recorded old witness rather than replacing its mathematical notion.

`def-weil-pbc-completed-pullback`: no published record is available. Reuse Q03's delivered
`Sheaf.Paper.CompletedPullback` with the corrected AdicCoefficientDatum imports. The
coefficient map is uniquely fixed by its finite projection equations, module pullback is
inverse image followed by canonical scalar extension, tower pullback has its universal
left-derived counit and objectwise K-flat computation, and completed pullback is actual
right-derived inverse limit of that pulled-back canonical reduction tower. The comparison
uses the strict quotient unit and the derived constant/limit adjunction unit. The file
also retains the finite-evaluation, transition-compatible tower, completion-unit and
constant/completed coefficient comparisons from the delivered interface. These are
named postponed theorems with source and proof docstrings; definitions have real data.

The four dependency node copies change only lean, with a note describing the interface
repair. The Q03 modules have been reused rather than replaced by independent new copies
of their constructions. Each delivered file is compiled separately through scompile.py.


## Earlier second reading (a previous round; superseded)

I independently read the current DAG item and its five proof steps, the original
blueprint paragraph on the server, and the cited Stacks TeX, with the delivered Lean
open. The blueprint's old sentence assigning [a,b] to both pullbacks is already
corrected in the reviewed DAG: applying the identity g to Rf_*K must retain its
[a,b+2e] bound. This delivery correctly follows the reviewed statement, and makes no
new statement correction. Stacks 09C1/09C2/09C7 are contextual results about constant
coefficients, not an identification with this blueprint's completed coefficient
category. I read proetale.tex labels definition-Dbc,
lemma-describe-constructible-complexes, proposition-Noetherian-adic-constructible,
definition-adic and lemma-pushforward-Noetherian-case; etale-cohomology.tex
lemma-cohomological-dimension-proper (095U); and more-etale.tex
theorem-constructible-shriek (0GL0). The latter's qcqs and finite-presentation
hypotheses follow here from Noetherian schemes and properness; its torsion requirement
holds for the finite quotient coefficients. No additional base field, separation
of the schemes, or Tor-amplitude assumption is implicit in the item.

Object/hypothesis/conclusion checklist, made before matching the Lean:

1. A prime ell and finite extension E/Q_ell; A=O_E, I=(varpi), every positive
   quotient P_n. Lean: `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra ℚ_[l] E]`,
   `[FiniteDimensional ℚ_[l] E]`, and `pbcOECoefficients l E`. I opened
   `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
   `coefficientExtensionIdeal` and `coefficientExtensionRing`: the annihilator
   hypothesis at exponent 1 uses exactly the same quotient ideal. Verdict: exact.
2. X', X, Y', Y and g', f', f, g forming the chosen cartesian square. Lean: the
   four Scheme binders, four arrows and `_square : ChosenCartesianSquare ...`.
   Its recorded structure extends CommSq and retains `isoPullback`, `hom_fst`
   and `hom_snd`, not merely a commuting diagram. Verdict: exact.
3. All four schemes Noetherian and finite dimensional. Lean: all four
   `IsNoetherian` instances and separate `_hDimX`, `_hDimY`, `_hDimX'`, `_hDimY'`
   natural upper bounds on `topologicalKrullDim`. No finite-type-over-a-field
   assumption occurs. Verdict: exact, including the empty schemes.
4. Both f and f' proper. Lean: `[IsProper f] [IsProper f']`; g and g' remain
   arbitrary. Verdict: exact (the second properness is allowed even though it also
   follows by base change).
5. One positive integer N annihilating A/I, invertible on every scheme. Lean:
   `(N : ℕ)`, `_hN`, `_hAnn`, and the four `_hInvert...` unit conditions on global
   sections. In a unital quotient ring, N*1=0 is equivalent to annihilation of
   every element. Being a unit on global sections is equivalent to local
   invertibility of this integer; local inverses glue uniquely. No extra ell-unit
   assumption is added: ell divides N. Verdict: exact.
6. Geometric fibres of f of dimension at most nonnegative e; c=2e. Lean:
   `(e : ℕ)` and `_hFib` for every actual point `y : Y`, with pullback along
   `Spec.map (algebraMap (Y.residueField y) (AlgebraicClosure ...))` followed by
   `Y.fromSpecResidueField y`. I checked the scheme-conventions dependency's
   geometric-fibre formula; it is the same object. Verdict: exact, not only closed
   points and not fibres over an unrelated field.
7. Any integers a,b and K in the completed bounded constructible category on X,
   with all canonical reductions supported in [a,b]. Lean: `(a b : ℤ)`, ambient
   `K : pbcCompletedDerivedCategory X ...`, `_hK` using the object predicate of
   `pbcBoundedConstructibleComplete`, and `_hInterval`. The predicate is precisely
   the full subcategory's object class; no morphisms are restricted. Verdict: exact.
8. Rf_*K belongs to the category on Y. Lean: conclusion conjunct 1, with
   `pbcCompletedDerivedDirectImage f`. Its ring map is the adjunct of the canonical
   `completedCoefficientMap`; pushforward is actual module pushforward and
   `rightDerivedFunctor` uses K-injectives in all completed modules. It is ordinary
   uncompleted Rf_*, not an additional completed functor. Verdict: exact.
9. Completed g-pullback of that same Rf_*K belongs to the category on Y'. Lean:
   conjunct 2, `completedPullback g ...` on precisely conjunct 1's object. Verdict:
   exact.
10. Completed g'-pullback of the original K belongs to the category on X'. Lean:
    conjunct 3, `completedPullback g' ... K`. Verdict: exact.
11. Ordinary Rf'_* of the object in item 10 belongs to the category on Y'. Lean:
    conjunct 4, the direct-image functor for f' applied to exactly that object.
    Verdict: exact.
12. Reductions of item 10 have support contained in [a,b]. Lean: conjunct 5.
    Verdict: exact.
13. Reductions of items 8, 9 and 11 have support contained in [a,b+2e]. Lean:
    conjuncts 6, 7 and 8 with `b + 2 * (e : ℤ)`. Verdict: exact. The same objects
    recur verbatim; in particular conjunct 7 does not incorrectly use b.

`pbcReductionsCohomologyIn` quantifies over all n:Nat and q:Int and asserts
`IsZero` of the actual quotient-module homology whenever q<a or b<q. I traced
`pbcReduction` to scalar extension along `pbcProjectionModel`, preceded by the
exact equivalence of sites `pbcToModel`; it preserves the quotient action. This is
support containment, not equality or Tor amplitude.

Dependency-module reading (H13):

- `def-weil-pbc-bounded-constructible-tower`: I read the whole delivered
  `WeilPbcBoundedConstructibleTower` against the node, including its small-site
  scalar extension and normalized composition, `PbcAdicTowerCore` evaluation
  isomorphisms, `PbcAdicTransitionCondition`, `PbcQuotientCocycle`, common finite
  stratification and covering sieves, fixed bounded adic-lisse local complexes,
  finite-lisse reduction cohomology, and `PbcLocalTowerComparison.compatibility`.
  Every b>=a comparison extends the successive-level condition using the same
  quotient cocycle. No independent normalization replaces the canonical one.
  The old recorded module has A in the coefficient universe; the completed datum
  used here has A:Type u and quotient coefficients in u+1. The replacement is an
  equivalent small-site interface, not a restriction identifying site universes.
- `def-weil-pbc-etale-origin-witness`: I opened the old `EtaleOriginWitness` and
  the entire delivered `EtaleOriginReduction`. The latter keeps the old interface
  publicly available, and transports the actual etale comparison site and
  constant-section coefficient map. `PbcEtaleOriginWitnessData` retains bounded
  below L and alpha, rather than only existence; its general coefficient form
  supports the canonical reductions needed here. Ring coefficients are not
  silently restricted to fields or commutative rings.
- `def-weil-pbc-bounded-constructible-complete`: I read every declaration.
  `pbcOE_properties` supplies only properties of the existing O_E/uniformizer;
  `pbcOECoefficients` has real data. The membership predicate has exactly intrinsic
  completeness, common canonical local models, and compatible etale witnesses.
  `PbcOriginReductionCompatibility` inserts the actual normalized inverse-image /
  coefficient-reduction comparison; `PbcCompatibleEtaleWitness` retains all beta
  maps and the quotient cocycle. The full subcategory carries the node's
  Noetherian, finite-dimension and ell-invertibility domain conditions. Using its
  underlying object predicate in this theorem neither drops a mathematical
  hypothesis nor adds one.
- `def-weil-pbc-completed-pullback`: I read the entire module against the node's
  coefficient map, K-flat strict-tower pullback, finite evaluations, derived limit,
  strict quotient-unit comparison, and constant-coefficient completion formula.
  The existence choices retain universal derived counits and representative
  normalizations, which determine them up to the required canonical equality;
  no map is chosen from bare Nonempty. The coefficient map is uniquely fixed by
  every finite projection. Both completion-unit formulas retain their arbitrary
  supplied K-flat representative and identity cases. Definitions contain real
  constructions. Every postponed property is a named theorem with a source and
  proof docstring under the owning node.

I also read the current server `CompletedAdicCoefficientDatum` via
`scompile.py --source`, including its actual finite ring limit, module categories,
strict derived reduction functor and independent-universe scalar extension. The
server still reports the complete-category and completed-pullback modules unavailable,
so including those already delivered Q03 prerequisite interfaces is necessary.
The four dependency node copies differ from the shared base only in lean records;
there are no new definition nodes requiring a stage-1 audit.

Independent searches (different query from the first reader): `msearch.py leanfinder`
with "Adic sheaf complexes with finite constructible quotient cohomology preserved by
derived proper direct image and derived completed inverse image" returned eight
condensed-module, sheafification and affine-limit hits, none this statement;
`msearch.py loogle` with `"constructible"` returned twelve constructible-set facts;
`msearch.py grep` with
`constructib.*(directImage|pushforward|complete)|(directImage|pushforward|complete).*constructib`
in Mathlib/AlgebraicGeometry returned zero hits. Direct rg in the upstream
WeilConjectures tree and shared lean/Sheaf located the separate integral and condensed
constructibility results. I opened `sfIntegralDirectImage_constructible`: it assumes
schemes of finite type over a field, uses a different tower-defined object and lacks
this four-output assertion. I read coord/pefw-upstream-framework.md and opened the
exact shared `ModuleObject/Derived/BoundedConstructible` upper/lower-star declarations:
they use condensed module objects and separated finite-type schemes over a field,
not this completed O_E tower category on general Noetherian schemes. Neither is an
exact existing match. The old origin and tower declarations were also opened rather
than identified by similar names.

Edge cases: n=0 means exponent 1, so no positive quotient is lost; zero K works for
any a,b, including a>b; the bounds are inclusive when a=b; empty schemes and empty
geometric fibres have bottom Krull dimension; the finite-stratification record permits
zero strata; e=0 and identity squares keep their stated bounds. Prime ell=2 is allowed,
and positive-characteristic schemes are restricted exactly by N's invertibility.
The actual small pro-etale site retains object universe u+1 and morphism universe u;
AsSmall enlarges Hom universes equivalently and coefficients/modules use u+1. No
universe-equality assumption or hidden implicit binder is introduced.

No mathematical mismatch was found, so I did not rewrite the Lean or the node's
statement. The second reading adds this independent audit and fresh search evidence.
The source/blueprint docstrings, five-step proof plan, sorry-only theorem bodies,
real definition data, public names and 100-column convention were checked. Compilation
and the required delivery preflight are recorded below after execution.


Validation: the second reader ran scompile.py on all five delivered modules together
(as separately compiled sibling modules). It exited 0 after server confirmation.
The local shared ConstantCompletionEquivalence overlay timed out at 60 seconds;
the prescribed wrapper automatically confirmed against current server sources, where
that dependency compiled in 36.1 seconds. Every delivered module compiled cleanly:
WeilPbcBoundedConstructibleTower 15.3s, EtaleOriginReduction 3.6s,
WeilPbcBoundedConstructibleComplete 5.2s, CompletedPullback 21.3s, and
PreservationConstructible 3.4s. There were no warnings. All five lean.statement
records were also compared with the literal source slices and match verbatim.


Delivery dry run: deliver2.py Q24 prop-weil-pbc-preservation-constructible
--no-push exited 0 and printed `OK (dry run): commit 19714433ce passes the preflight
and compiles; nothing pushed`. The dry run independently recompiled all sibling
modules through the prescribed wrapper; its local final probe lacked the shared
ConstantCompletionEquivalence object, and current-server confirmation passed.

## Second reading by Q24

Fresh independent reading, 2026-10-16. This section supersedes the earlier reading
and the worker's dependency inventory where publication has since changed. I opened
the item and its dependencies, the delivered modules, and the current server source
of `Sheaf.Paper.BoundedConstructibleComplete` through `scompile.py --source`.
I also read the original blueprint proposition (order 1355) and Stacks TeX:
proetale.tex `definition-Dbc` (09C1), `lemma-describe-constructible-complexes`
(09C2), `proposition-Noetherian-adic-constructible` (09C7),
`lemma-pushforward-Noetherian-case` (099N); etale-cohomology.tex
`lemma-cohomological-dimension-proper` (095U); more-etale.tex
`theorem-constructible-shriek` (0GL0).

The original blueprint's sentence giving both pullbacks [a,b] is already repaired
in the reviewed DAG. For identity g the second output is Rf_*K, so its bound is
[a,b+2e]. I preserve the current node exactly. Stacks 09C1 is a contextual
constant-coefficient definition with a Tor condition, and is not substituted for
the node's specified completed-coefficient, uniform-tower category. Stacks 095U
requires properness and a fibre-dimension bound; 0GL0 requires separated finite
presentation and qcqs, which follow from properness and the Noetherian schemes.
Its coefficient hypotheses hold for the positive finite quotients. There is no
hidden finite-type-over-a-field or smoothness hypothesis in this delivery.

The object/hypothesis/conclusion list, matched individually:

1. Prime ell, finite E/Q_ell, A=O_E, I=(varpi), all positive quotients.
   Lean: `l`, `Fact l.Prime`, `E`, `Field E`, `Algebra ℚ_[l] E`,
   `FiniteDimensional ℚ_[l] E`, `pbcIntegralDatum l E`. I checked the recorded
   `Padic.coefficientExtensionIntegers`, uniformizer, ideal and quotient formulas.
   The coefficient data is the actual ring and ideal. Verdict: exact.
2. Four schemes and four arrows in a chosen cartesian square.
   Lean: `X' X Y' Y`, `g' f' f g`, `_square : ChosenCartesianSquare ...`.
   I opened that structure: it extends CommSq and has `isoPullback`, `hom_fst`
   and `hom_snd`. Verdict: cartesian data, not just commutativity.
3. All four schemes Noetherian and finite dimensional.
   Lean: four `IsNoetherian` instances and four independent `_hDim...` bounds
   by a natural number in `WithBot ℕ∞`. Verdict: exact, including empty schemes.
4. f and f' proper; no property on g or g'.
   Lean: `[IsProper f] [IsProper f']`. Verdict: exact.
5. One positive N annihilates A/I and is invertible on all four schemes.
   Lean: `N`, `_hN`, `_hAnn` in `coefficientExtensionRing l E 1`, and the four
   `IsUnit (N : Γ(T, ⊤))` hypotheses. Killing the ring's unit kills every element;
   local inverse sections glue uniquely to the global inverse. No extra
   ell-invertibility binder is imposed; ell divides N. Verdict: exact.
6. Every geometric fibre of f has dimension at most e>=0; c=2e.
   Lean: `e : ℕ`, `_hFib` at every `y : Y`, with the algebraic closure of the
   actual residue field, `Spec.map` and `Y.fromSpecResidueField y`. I checked
   this against the scheme-conventions fibre formula. Verdict: exact.
7. Arbitrary a,b and K in the specified category, all reductions in [a,b].
   Lean: `a b : ℤ`, `K : PbcCompletedDerived ...`, `_hK`, `_hInterval`.
   `PbcIsBoundedConstructibleComplete` is the recorded category predicate itself.
   It retains intrinsic completeness, common normalized local models, and compatible
   etale origins, without restricting ambient morphisms.
   `pbcReductionsCohomologyIn` is vanishing of quotient-module homology of
   `pbcCompletedReduction` for q<a or b<q. Verdict: exact.
8. Ordinary Rf_*K belongs to the category on Y.
   Lean: conjunct 1, `completedDerivedDirectImage f ...`. I traced its
   sectionwise `SheafOfModules.pushforward`, the ring map adjoint to
   `completedCoefficientMap`, and unbounded K-injective `rightDerivedFunctor`.
   It is the ordinary derived direct image. Verdict: exact.
9. Completed g-pullback of that same Rf_*K belongs to the category on Y'.
   Lean: conjunct 2, `completedPullbackObject g ...` applied to conjunct 1's object.
   Verdict: exact.
10. Completed g'-pullback of the original K belongs to the category on X'.
    Lean: conjunct 3, `completedPullbackObject g' ... K`. Verdict: exact.
11. Ordinary Rf'_* of item 10 belongs to the category on Y'.
    Lean: conjunct 4, direct image for f' applied to precisely that object.
    Verdict: exact.
12. Reductions of item 10 are supported in [a,b].
    Lean: conjunct 5, `pbcReductionsCohomologyIn ... a b`. Verdict: exact.
13. Reductions of items 8, 9, 11 are supported in [a,b+2e].
    Lean: conjuncts 6-8 with `b + 2 * (e : ℤ)`. Verdict: exact. There is no
    equality-of-support or Tor-amplitude assertion and no ordering assumption a<=b.

Mismatch found and repaired (H4/H13): the worker's publication check had become
stale. The current DAG records Q06's `Sheaf.Paper.BoundedConstructibleComplete`,
and the current server supplies its source. I opened its full category definition,
including intrinsic completion, the tower/local-model criterion, and the
normalization-compatible etale-origin criterion. It already supplies the needed
notion, so this delivery must not replace it with a second definition. I removed
`WeilPbcBoundedConstructibleComplete.lean`, `WeilPbcBoundedConstructibleTower.lean`,
`EtaleOriginReduction.lean` and their three dependency-node overrides.

Before the final push, the publication check found that Q31 had also landed
`Sheaf.Paper.CompletedTowerPullback`, recorded for
`def-weil-pbc-completed-pullback`. I read its full current source using
`scompile.py --source` and read its derived-limit dependency. Its coefficient datum
has the same Type (u+1) size and original small site as the recorded category.
Accordingly I removed the old `CompletedPullback.lean` dependency module and node
override as well, and use `completedPullbackObject` directly with `pbcIntegralDatum`.
No coefficient transport helper is needed or delivered. The final packet has only
`PreservationConstructible.lean` and the item's node record, besides this report.

Reading of the now-recorded completed-pullback dependency (H3/H4/H13):
`completedFiniteCoefficientMap` is the fixed constant-section comparison conjugated
by `pbcLevelConstantComparison`. `completedCoefficientComponent` composes that map
with the actual pulled-back completion projection, and `completedCoefficientMap`
is an actual `limit.lift` from these components. It assumes no coefficient-map
invertibility. Module pullback is inverse image then scalar extension. The
`IsCompletedTowerPullbackPair` universal property retains the objectwise K-flat
computation and triangulatedness; its resolution uses the original site with
independent coefficient size. `completedPullbackObject` is `completedTowerRlim`
after that functor on `completedReductionTower`. The latter is the canonical
strict reduction tower, not arbitrary quotient data. The comparison uses the
normalized strict quotient unit, the constant-tower comparison, and the derived
constant/limit unit. The finite-evaluation comparison is only for reduction towers.
The completion comparison fixes its unit and retains arbitrary complex
representatives. These agree with the node and Stacks 099N(2),(5).
The derived limit is the K-injective right derived functor of actual strict-tower
limit. Neither a coefficient map nor a cone map is an unconstrained choice.

I also searched the now-published module inventory for ordinary completed-coefficient
direct image. `Sheaf.Paper.CompletedTowerDirectImage` already provides exactly this
construction, recorded under `prop-weil-pbc-direct-image-limits`. I opened its
`completedCoefficientDirectImageMap`, `completedModuleDirectImage` and
`completedDerivedDirectImage`: they use the adjoint of the same canonical coefficient
map, sectionwise module pushforward and the unbounded K-injective right derived
functor. Therefore I removed the four item-local direct-image helper declarations
as well. The item gains that existing node in `stmt_deps` and imports its module
publicly. Its proof dependencies have no return path to this item.

The final main statement uses exactly the recorded `pbcIntegralDatum`,
`PbcCompletedDerived`, `PbcIsBoundedConstructibleComplete`,
`completedDerivedDirectImage` and `completedPullbackObject`. The lifted valuation
ring and lifted uniformizer give the identical O_E-adic coefficients; `_hAnn`
still describes the unlifted residue ring, canonically the same finite ring under
ULift and quotient. There is no new coefficient assumption. The only helper,
`pbcReductionsCohomologyIn`, uses the actual canonical quotient objects of
`pbcCompletedReduction` in the full small-site module category.

Independent searches in this reading:

- LeanFinder: "Uniform cohomological bounds on adic constructible complexes under
  proper pushforward and completion of inverse image": eight hits (adic completion,
  local cohomology, affine limits), none the statement.
- Loogle: `"constructible"`: twelve topological constructible-set results, none
  the sheaf-complex preservation statement.
- Mathlib grep: `constructib.*(pushforward|adic)|(pushforward|adic).*constructib`:
  zero results.
- LeanSearch: "Derived completed inverse image and proper pushforward preserve
  uniform bounded constructible finite reductions": Internal Server Error,
  recorded unavailable, not as absence evidence.
- Direct rg in Mathlib, upstream WeilConjectures, and shared lean/Sheaf by the
  node ID, new declaration names and constructible/pushforward/preservation words.
  I opened `sfIntegralDirectImage_constructible`: it requires finite-type schemes
  over a field and states a different tower-valued result. I read
  `coord/pefw-upstream-framework.md` and the exact shared
  `ModuleObject/Derived/BoundedConstructible.lean`: its condensed module objects and
  finite-type-over-a-field hypotheses are different. Neither replaces this theorem.
  The category interface found in the current shared DAG is reused as explained above.

Edge cases: n=0 denotes exponent 1; there is no missing positive quotient. Zero K
has empty cohomological support and is allowed for every a,b, including a>b.
When a=b the support interval is inclusive. Empty schemes and empty geometric
fibres have bottom Krull dimension, so all natural dimension bounds allow them.
The recorded tower definition permits the empty stratification where applicable.
Identity squares and e=0 keep the stated bounds; in particular identity g does not
shrink the Rf_* bound. Prime 2 is allowed; positive characteristic is restricted
exactly by N's invertibility. The site retains object universe u+1 and morphism
universe u. The coefficient size lift changes presentation only, without equating
site universes or adding any universe hypothesis. Every variable is bound and
`autoImplicit false` remains enabled.

No node statement is corrected in this delivery. For context I also opened the
citers `cor-weil-pbc-constructible-complete` and `thm-cbc-finite-extension`; their
uses of the four memberships remain valid with these recorded coefficient
interfaces. No target unit statement changes. The source/proof docstrings,
sorry-only theorem bodies and actual definition data have been checked.

Final dependency inventory: no dependency module or dependency-node override,
no new definition node, and no transport helper is delivered. The earlier worker
and prior-reading dependency inventories describe superseded packets. The current
recorded category, completed pullback and ordinary direct image are used directly.

The first two-module dry run passed (`acf7b54d79`), but it preceded the discovery
of the landed Q31 interface. Its compilation and preflight therefore validate only
the superseded packet. The final one-module compilation, dry run and push are
recorded below after execution.

Final inventory: one Lean module, two declarations (the support predicate and the
sorry theorem), one item node record, and this report. All four original dependency
modules are removed; there are no coefficient transport or direct-image copies.

The final proof-import audit also follows the newly recorded
`Sheaf.Paper.FiniteLevelAmplification` wrapper. The four still-unstated proof
prerequisites are amplification-proper, normalized local effectivity, perfect
projection formula and completed-pullback reduction; their plans remain in the
theorem docstring. All currently stated proof prerequisites are imported, directly
or through public statement dependencies.

Final exact-source validation: `scompile.py Q24 prop-weil-pbc-preservation-constructible`
compiled the sole delivered file after all interface and proof-import changes, exited
0, and emitted no error or warning (`scratchpad/final-current-compile.log`).
Both source checks passed. The node's `lean.statement` equals the literal signature
slice, and its `lean.declarations` lists exactly the support predicate and theorem.

Final dry run: `deliver2.py Q24 prop-weil-pbc-preservation-constructible --no-push`
exited 0 and printed `OK (dry run): commit 2ebfa824c9 passes the preflight and
compiles; nothing pushed`. Its staged inventory is exactly the item module, item
node and report; no dependency-node override remains.
