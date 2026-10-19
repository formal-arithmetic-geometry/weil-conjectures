## Worker report

The item is stated by
`AlgebraicGeometry.Scheme.normalizedConstructibleTower_local_effectivity` in
`Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity`. Its sole postponed proof is
this named theorem, whose docstring reproduces all eight DAG proof steps and their
named dependencies. Definitions have actual data. Nothing is proved in this delivery.

Hypotheses and conclusions, clause by clause:

- The Noetherian scheme T is `(X : Scheme.{u}) [IsNoetherian X]`.
- The adic datum is `(d : AdicCoefficientDatum A)`, for a commutative ring
  `A : Type (u+1)`. The existing datum includes Noetherianity, the finitely generated
  ideal, additive torsion of A/I, and finite perfect positive quotients. No assumption
  of completeness of A, a valuation ring, a characteristic, or finite Tor amplitude
  is added. Positive exponent n+1 is indexed by `n : ℕ`.
- The coefficient sheaves and their completed inverse limit are precisely
  `pbcAdicRings X d` and `pbcAdicCompletion X d`, used by `AdicTower`.
- The supplied object of D(Tow), its quotient-linear levels, and identifications of
  scalar restrictions with evaluation are `M.tower`, `M.level`, and `M.evaluation` in
  `(M : AdicTower X d)`.
- The normalized derived reductions are `M.normalization`. Their scalar-extension
  maps induce the strict derived tower transitions by `M.transition`; the quotient
  cocycle is `M.cocycle`. The stored comparable-pair form includes the consecutive
  normalizations and the reductions obtained by their quotient cocycle, including
  equal indices. No arbitrary transition or arbitrary comparison is supplied.
- Intrinsic constructibility of every H^q(M_n) is `hconstructible`, for every `n` and
  every integer `q`. Its scalar action is transported by `pbcRestrict` along
  `(pbcLevelConstantComparison X d n).hom`, the canonical constant-to-functions
  comparison. The coefficient-universe interface is the dependency repair below.
  It requires a positive finite locally closed constructible stratification and
  finite-lisse restrictions, without any etale-origin hypothesis.
- The integers and their order are `(a b : ℤ) (hab : a ≤ b)`; the one common
  cohomological interval is `hbounded`, with `IsZero (H^q(M.level n))` for
  `q < a ∨ b < q`, for every level. These are bounds on quotient-linear levels,
  rather than solely bounds on completed-coefficient evaluations.
- The first conclusion is `∀ n, IsAdicTowerLevelOfBoundedConstructibleEtaleOrigin
  X d M n`. This helper applies the existing
  `ProEtale.isBoundedConstructibleFiniteCoefficient` to a representative `C` in the
  recorded finite-coefficient category, then identifies its localization after
  coefficient transport with `M.level n`. The transport is termwise
  `SheafOfModules.restrictScalars` along the canonical
  `AdicCoefficients.finiteRingComparison` hom, not a freely chosen equivalence.
  A representative is existentially quantified; every derived object has one, and
  transport along this ring-sheaf isomorphism is exact. Thus this says exactly
  bounded constructible etale origin in the dependency's coefficient presentation.
- The second conclusion is the existing
  `IsUniformlyBoundedConstructibleAdicTower d M`. Its definition supplies common
  termwise integer bounds, a single finite locally closed stratification, covering
  sieves of the final object on each stratum, and on each covering member an
  `AdicTowerLocalModel` over the actual inverse image of the completed ring.
  The local model's fields are the bounded complex, adic-lisse finite-type terms,
  finite-lisse cohomology at every reduction, quotient-linear reduction
  identifications and normalization compatibility. The last equation is expressed
  by semilinear adjuncts under the canonical scalar adjunction, as in the recorded
  definition. There is no projectivity field and none is imposed here.

Dependency declarations used:

- `Sheaf.Paper.AdicCoefficientDatum` (re-exporting
  `Sheaf.Paper.CompletedAdicCoefficientDatum`): `Scheme.AdicCoefficientDatum`,
  `Scheme.AdicCoefficients.ringSystem`, `completedRing`, `finiteRingComparison`.
- `Sheaf.Paper.BoundedConstructibleTower`: `Scheme.AdicTower`, `pbcModules`,
  `pbcRestrict`, `pbcLevelConstantComparison`, `IsRelativelyFiniteLisseModule`,
  `IsUniformlyBoundedConstructibleAdicTower`, and `AdicTowerLocalModel`.
- `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`: the generalized recorded
  intrinsic constructibility predicate described below; it re-exports the original
  `Sheaf.Paper.ProEtaleConstructibleSheaf` interface.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`, re-exporting
  `ProEtaleFiniteModules`: `ProEtale.FiniteCoefficientModules` and
  `ProEtale.isBoundedConstructibleFiniteCoefficient`. The latter is the strict
  essential image of the specified inverse image on bounded constructible etale
  objects, including the finite-stratification finite-module criterion.
- Mathlib `DerivedCategory` and `HasDerivedCategory`, and
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `DerivedCategory.Q`.

Recorded modules of stated proof dependencies are imported non-publicly, except
those already used publicly as statement dependencies and the incompatible published
`Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence` module. A separate import probe
confirmed that this module brings the legacy upstream pro-etale pullback API into the
new finite-coefficient API and produces an environment-already-contains error for
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»`. Following the explicit duplicate-import
repair instruction, this proof-only import is omitted; its role and proof dependency
remain in the theorem docstring and DAG unchanged. CompatibleFiniteDerivedTrivializations
was independently probed and is retained. The geometric-stalk exactness node has no
recorded module and supplies no additional import. No theorem about this item's own
canonical maps is assumed to define them.

Edge cases checked: empty scheme (the constructibility predicate permits one empty
stratum; the uniform local-model predicate also permits an empty partition), zero
ring, zero complex, a=b, negative cohomological endpoints, I=0, and the zero quotient
case I=A. Finite rather than projective local terms are retained. The coefficient
ring is permitted in the small site's object universe u+1 while the site's morphisms
remain in universe u; no universe equality has been imposed. The existing final-object
covering-sieve convention handles disconnected and empty covering members.

Searches made before writing:

- `msearch.py`, LeanFinder: "A uniformly bounded normalized constructible tower of
  complexes on the pro etale site admits compatible common bounded adic lisse local
  models". Eight hits, all etale morphism/site and affine-limit declarations;
  none is the assertion.
- `msearch.py`, Loogle: `DerivedCategory, AdicCompletion`. Zero hits.
- `msearch.py`, Mathlib grep: `constructible.*tower|adic.*lisse`. Zero hits.
- `rg` in WeilConjectures and lean/Sheaf: `IsUniformlyBoundedConstructibleAdicTower`,
  `AdicTower`, `normalized`, `ConstructibleLocal`, and `effectivity`. Found the owning
  adic tower definitions and a DVR realization theorem, which does not assert common
  constructible local complexes. No exact theorem exists.
- The upstream source contains no occurrence of this item's blueprint identifier;
  neither source tree nor Mathlib contains either newly introduced declaration name.
- Read every statement dependency's statement, recorded interface, signatures and
  docstrings, and the cohomology/derived-category Mathlib matches. Read the current
  server BoundedConstructibleTower source through `scompile.py --source`; it agrees
  with the interface used here.

The local literature checkout does not contain the Stacks TeX. The official source
pages were read directly: https://stacks.math.columbia.edu/tag/09AL (finite-level
bounded-below constructible comparison), https://stacks.math.columbia.edu/tag/09BT
(adic-lisse interpretation), https://stacks.math.columbia.edu/tag/09BV (compatible
adic local models), and https://stacks.math.columbia.edu/tag/09AV (normalized
pseudo-coherent reconstruction). The stronger bounded nonprojective local-complex
assertion is the DAG's explicit agent assembly, not represented as a verbatim Stacks
lemma. The complete assembly is retained in the theorem docstring.

There is no statement correction and no STATEMENT-DISPUTED finding.

## Dependency modules

`def-weil-proetale-constructible-sheaf`:
`Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf` re-exports the recorded interface
and supplies `Scheme.IsConstructibleProEtaleCoefficientModuleSheaf`. The recorded
predicate only accepts a scalar ring in Type u (with its canonical lift), whereas the
adic tower accepts A in Type (u+1). Its quotients therefore cannot be passed to the
recorded predicate without either a genuine coefficient transport or a universe
restriction. This §1(B) interface states the same intrinsic notion for the existing
site-universe constant ring: a positive finite locally closed constructible partition,
with finite-lisse restrictions along its immersions. It reuses
`IsRelativelyFiniteLisseModule` for the actual inverse-image coefficient sheaf. A locally
constant sheaf with finite geometric stalks admits, by refining its trivializing cover,
constant finite-module models; conversely these models have finite geometric stalks.
This is the same notion, with no uniform rank condition, no etale-origin condition and
no assumption about projectivity. The original small-coefficient predicate remains
available by public import. Only this dependency node's lean record changes.

## Validation

Both modules are compiled separately in dependency order using the prescribed
`scompile.py` wrapper. The worker dry run is performed with `deliver2.py --no-push`;
the independent second reader will write the second-reading section and deliver.

## Earlier second reading (a previous round; superseded)

I independently read the item node, both delivered modules, all six statement-dependency
nodes, and the declarations used from their modules. There are no new definition nodes
and no statement_change. The only dependency module is the coefficient-universe repair
of def-weil-proetale-constructible-sheaf. No mathematical mismatch was found; the Lean
and both lean records are retained unchanged. This reading adds this report section.

Object/hypothesis/conclusion inventory, matched to the Lean:

1. Noetherian scheme T: `(X : Scheme.{u}) [IsNoetherian X]`. Matches. No separatedness,
   dimension, nonemptiness, base field or proper morphism is assumed.
2. Commutative adic coefficient datum (A,I): `{A : Type (u + 1)} [CommRing A]` and
   `d : AdicCoefficientDatum A`. I opened CompletedAdicCoefficientDatum and its parent
   CompleteCoefficientDatum: the fields are the ideal, Noetherianity, finite generation,
   additive torsion of A/I, perfect positive quotients, and `quotientFinite`. Matches the
   cited datum; completeness of A is not required.
3. R_n and completed A_T: `pbcAdicRings X d` and `pbcAdicCompletion X d`, as used in
   `AdicTower`. I opened the actual coefficientRing, ringSystem and completedRing
   definitions and the canonical finiteRingComparison. These are sheafified continuous
   component functions, their quotient diagram and its limit, not discrete constant
   integral coefficients. Lean index n denotes source exponent n+1 throughout. Matches.
4. Object in D(Tow), quotient-linear levels and evaluation identifications:
   `M : AdicTower X d`, with `M.tower`, `M.level`, `M.evaluation`. The underlying tower
   category is explicitly `ℕᵒᵖ ⥤ pbcModules X (pbcAdicCompletion X d)` and evaluation is
   termwise derived evaluation. Matches; it is not an arbitrary collection of levels.
5. Normalized derived reductions: `M.normalization` is scalar extension along the actual
   quotient map. `M.transition` equates its semilinear adjunct, after scalar restriction
   and the evaluation identifications, with the transition of M.tower. `M.cocycle` equates
   direct and successive reductions. Matches. All comparable pairs merely package the
   iterates of the consecutive isomorphisms and the specified quotient cocycle; they add
   no mathematical restriction. The equal-index cocycle forces the identity normalization.
6. Intrinsically constructible H^q(M_n), every n and integer q: `hconstructible` applies
   IsConstructibleProEtaleCoefficientModuleSheaf to the homology object after
   `pbcRestrict (pbcLevelConstantComparison X d n).hom`. This comparison is characterized
   on constant sections, and hence is the canonical finite-coefficient identification.
   The predicate requires a positive finite immersed locally closed partition,
   constructible images and finite constant local modules on every stratum. Matches;
   no etale-origin hypothesis has been substituted.
7. Common cohomological interval: `(a b : ℤ) (hab : a ≤ b)` and `hbounded`, quantifying
   over every n and q and using `IsZero` when `q < a ∨ b < q`. The homology objects are
   computed from M.level with its quotient action. Matches. Bounds do not depend on n.
8. Bounded constructible etale origin of every level: the first conjunct quantifies
   over all n and uses IsAdicTowerLevelOfBoundedConstructibleEtaleOrigin. I unfolded
   this helper and isBoundedConstructibleFiniteCoefficient: the latter is the strict
   essential image of the recorded finite-coefficient comparison, with finite locally
   constant etale restrictions on finite constructible strata and bounded cohomology.
   The helper localizes an actual complex C in that category and restricts its scalars
   along finiteRingComparison.hom to identify it with M.level n. Restriction along this
   specified ring-sheaf isomorphism is an exact equivalence; every derived object has a
   cochain representative. Thus the extra representative witness changes no object or
   condition. Matches, without a private definition of etale constructibility.
9. One common stratification, covers, bounded adic-lisse finite-type complexes and
   compatible reductions: the second conjunct is exactly the recorded
   IsUniformlyBoundedConstructibleAdicTower d M. I opened its definition and every field
   of AdicTowerLocalModel: common ordered integer bounds, finite immersed strata,
   covering sieves of each final object, one bounded complex over the inverse image
   of the original completed ring per covering member, adic-lisse terms, finite-lisse
   cohomology of all derived reductions, quotient-linear identification, and the
   semilinear-adjunct compatibility equation. The scalar adjunction converts that
   equation to the node's normalization equation. Matches. Neither projective terms
   nor finite Tor amplitude is required; completing coefficients anew on the covering
   member is not substituted for inverse image.
10. Derived categories and cohomology: I opened Mathlib DerivedCategory, its Q, and
    homologyFunctor signatures. These are localization of integer cochain complexes
    and their factored homology, as the two dependency nodes specify. Matches.

Dependency repair checked independently: the original
IsConstructibleProEtaleModuleSheaf takes A : Type u and modules over the lifted
constant ring. The delivered interface takes A : Type (u+1), which the recorded
AdicTower already permits; imposing equality of site object and morphism universes
would lose the given site. Its finite-lisse clause reuses IsRelativelyFiniteLisseModule:
a covering sieve trivializes the actual inverse-image module as the inverse image of
a constant finite ModuleCat A object. The canonical inverse image of a constant ring
and module is constant, so this is precisely the node's pullback-linear local constancy.
Conversely a locally constant sheaf with finite geometric stalks has finite constant
models after refinement: each nonempty trivializing member has a geometric point whose
stalk is that model; empty members use the zero module. No uniform rank or fixed module
across members is imposed. The positive-strata and constructibility clauses are retained.
Only this dependency's lean changes. There are no hollow data or new postponed theorems
in the repair. Re-exporting the original interface preserves its existing uses.

Sources: the shared literature checkout lacks the cited TeX, so I fetched the official
Stacks repository's proetale.tex and more-algebra.tex into this item's scratchpad and
read the cited labels, including the surrounding section assumptions. Tags 09AJ/09AL
use a Noetherian coefficient ring; the finite quotients satisfy that. Tag 09AJ uses an
affine-local partition, whereas the dependency node explicitly uses a global partition;
the delivered definition follows the node. Tags 09BT and 09BU--09BX concern adic sheaves
and local completed finite-module models, not a verbatim derived nonprojective tower
theorem. Tag 09AV concerns normalized derived reductions over a complete ring with
pseudo-coherent first level. The node explicitly assembles these ingredients, applies
completion first, and records the additional derived argument in eight proof steps.
The theorem docstring preserves all eight steps and their dependencies. I found no
unrecorded standing source hypothesis missing from this node or its Lean rendering.

Edge cases: X empty is allowed. Stratification has no nonempty-stratum condition, so
the constructibility hypothesis permits a single empty stratum; the uniform conclusion
also permits the empty partition. Covering sieves and constant zero modules handle empty
members. The zero ring, zero levels, I=A, and I=0 are allowed whenever they satisfy the
recorded datum. There is no n=0 quotient A/I^0: n=0 is exactly the first positive quotient
A/I. Equal indices of normalization are included. Negative endpoints and a=b are
included, with no global bound on their values. No characteristic or invertibility
condition is introduced. The site is still Scheme.{u}.ProEt with object universe u+1
and morphism universe u; coefficients and local module models use u+1, as in the
recorded size convention. All variables and universes in both modules are explicit;
autoImplicit is false. The theorem is the sole sorry and every definition has real data.

Independent searches (different queries from the worker):

- LeanFinder via msearch.py: "Bounded compatible derived quotient systems have effective
  constructible adic local complexes on a common stratification". Eight results, ordinary
  localCohomology/AdicCompletion/Hausdorffification; no sheaf tower effectivity theorem.
- LeanFinder: "Sheaf of modules over a finite commutative ring locally constant on
  finitely many immersed constructible strata". Eight results, including
  CompHausLike.LocallyConstantModule.functor and SheafOfModules.IsFiniteType. The former
  has a different site; the latter has no constructible stratification or local-constant
  condition. Neither replaces the dependency interface.
- Loogle: `"IsLocallyConstant", "Finite"`. Only IsLocallyConstant.range_finite,
  concerning functions on a compact space, not module sheaves.
- LeanSearch: "A constructible sheaf of modules on the pro etale site admits a finite
  locally closed stratification with finite locally constant restrictions". Service
  unavailable (Internal Server Error), recorded as unavailable rather than a negative.
- rg over Mathlib, WeilConjectures and lean/Sheaf for effectivity, both orders of
  constructible/tower, and the two delivered definition names. No exact existing
  theorem or generalized constructibility declaration. NormalizedDVREffectivity was
  opened: it assumes a DVR coefficient datum and asserts integral realization and
  derived completeness, not this common constructible local-model conclusion.
  ElladicCohomology defines cohomology, not either delivered notion. The upstream name
  map has no matching new declaration names. Existing adic definitions are reused.

The current server BoundedConstructibleTower source was also obtained through
scompile.py --source; it agrees with the shared source apart from a trailing newline.
The reported omitted proof-only ComparisonPullbackCoherence import indeed imports the
legacy FiniteCoefficient.UpperLowerStar.Defs; its mathematical role remains in the DAG
and docstring. The worker's documented duplicate-environment import failure does not
alter this theorem's statement. Both node lean.statement strings are verbatim signatures
of their files, and both files satisfy the 100-character line limit. No statement or
unit correction, new definition node, or mathematical change was necessary.

Second-reader validation: the prescribed scompile.py invocation compiled both delivered
files separately and exited 0 with no warnings. Server confirmation took 2.4 seconds
for ProEtaleConstructibleCoefficientSheaf and 3.2 seconds for
NormalizedConstructibleTowerLocalEffectivity, with nice 19, two threads and the unchanged
60-second limit. The local run had passed the dependency and the main sandbox check,
then encountered a missing shared overlay artifact for
CompletedConstantFiniteComplexRealization during the main library-path check; the
wrapper's normal server fallback compiled that import and both delivery files cleanly.
This cache issue required no source or tool edits.


## Returned-delivery repair (2026-10-16)

The immutable-head compile reported inaccessible `AdicCoefficientDatum`, `AdicTower`,
`AdicCoefficients.finiteRingComparison`, and the constructibility predicates, followed
by an elaboration timeout. The main module now explicitly publicly imports
`Sheaf.Paper.AdicCoefficientDatum` and `Sheaf.Paper.BoundedConstructibleTower`, which
own the coefficient comparison and tower interfaces used in its public signatures.
The existing direct public import of the delivered intrinsic constructibility module
is retained. `autoImplicit` remains false. No declaration signature, definition body,
mathematical hypothesis, conclusion, or postponed proof is changed by this repair.

The current base's constructibility record names
`Sheaf.Paper.ProEtaleFixedModuleConstructible.IsConstructibleProEtaleFixedModuleSheaf`
(the declaration namespace is `AlgebraicGeometry.Scheme`). I read that definition:
it takes a fixed ModuleCat-valued sheaf, whereas the theorem uses ringed module sheaves.
The delivered dependency module is still required to state this intrinsic notion on
those objects; its lean.note now explains this current interface as well as the older
small-coefficient interface. The dependency's natural-language statement is unchanged.

A fresh LeanFinder query, “normalized constructible derived towers admit bounded adic
lisse local complexes”, returned eight scheme-normalization hits and no matching
theorem. A fresh rg search of WeilConjectures and lean/Sheaf for both declarations and
the item identifier returned no hits. The original clause-by-clause correspondence,
edge-case checks, and proof plan above still apply. No statement correction is needed.

The validation recorded above describes the earlier delivery; the fresh repair
validation below supersedes it for this returned delivery.

Fresh repair validation: `scompile.py NC
lem-weil-pbc-normalized-constructible-local-effectivity` with both delivered files
exited 0. Both files passed the sandbox and library-path checks with no compiler
warnings or errors. The main library-path check reported 49.8 seconds; the dependency
library-path check reported 6.3 seconds. All invocations used the wrapper's unchanged
limits and explicit-variable settings. The earlier missing identifiers and elaboration
timeout did not recur.

## Second reading by NC

Fresh independent reading of the returned-delivery repair, 2026-10-16. I opened the
item's node, both delivered modules, all six statement-dependency node records and the
actual definitions used from their modules. This section is the reading of the final
packet and supersedes earlier validation and second-reading history above.

Object, hypothesis and conclusion inventory (node order):

1. Noetherian scheme T: `(X : Scheme.{u}) [IsNoetherian X]`. Matches. No base field,
   separatedness, dimension, properness or nonemptiness is assumed.
2. Adic coefficient datum (A,I): `{A : Type (u + 1)} [CommRing A]`,
   `d : AdicCoefficientDatum A`. Matches. I read its inherited
   `CompleteCoefficientDatum`: the ideal, Noetherianity, finite generation, additive
   torsion of A/I, and perfectness of positive quotients are retained, together with
   `quotientFinite`. Completeness of A is not assumed.
3. Quotient coefficient sheaves R_n and their completed inverse limit: the
   `AdicTower X d` uses `pbcAdicRings X d` and `pbcAdicCompletion X d`. I read
   `AdicCoefficients.functionPresheaf`, `coefficientRing`, `ringSystem` and
   `completedRing`: they are the sheafified continuous-component functions and their
   actual inverse limit. Matches. Index n denotes exponent n+1, so n=0 is A/I.
4. Derived strict tower, quotient-linear levels and evaluation identifications:
   `M : AdicTower X d`, with fields `tower`, `level`, `evaluation`. Matches.
   `tower` is in D of the functor category of strict completed-coefficient towers,
   rather than merely a diagram in the derived category.
5. Normalization, transition and quotient cocycle: the fields `normalization`,
   `transition`, `cocycle` of this same structure. Matches. I read the scalar-unit
   adjuncts and their normalized composition comparisons; the stored all-pairs form
   includes the consecutive reductions and their forced composites. Its local-model
   equation is the adjunct of the node's scalar-extension equation.
6. Intrinsic constructibility of every cohomology sheaf at every level:
   `hconstructible : ∀ (n : ℕ) (q : ℤ), ...`. It applies
   `IsConstructibleProEtaleCoefficientModuleSheaf` to the homology of `M.level n`
   restricted along `(pbcLevelConstantComparison X d n).hom`. Matches. I read that
   comparison's constant-section characterization. The delivered predicate has a
   positive finite locally closed constructible stratification and finite constant
   module models on a covering of each stratum. It assumes no etale origin.
7. One cohomological interval: `(a b : ℤ) (hab : a ≤ b)` and `hbounded`, for all n,q,
   asserting `IsZero` of level homology when `q < a ∨ b < q`. Matches, including the
   quantifier order. The bounds are independent of n and concern quotient-linear levels.
8. Bounded constructible etale origin of every level: first conclusion
   `∀ n, IsAdicTowerLevelOfBoundedConstructibleEtaleOrigin X d M n`. Matches.
   I opened `FiniteCoefficientModules`, `finiteCoefficientDerivedComparison` and
   `isBoundedConstructibleFiniteCoefficient`. The latter is exactly the strictly full
   essential image of bounded etale complexes with finite constructible stratified
   local-module cohomology. The helper witnesses a cochain representative C and its
   localization after scalar restriction along the specified `finiteRingComparison`.
   This map is an isomorphism characterized by the sheafification units, so its exact
   scalar restriction is an equivalence. Every derived object has a representative;
   the witness imposes no additional condition. No arbitrary comparison is chosen.
9. Common finite stratification, covers, bounded finite-type adic-lisse local complexes,
   finite-lisse reduction cohomology, and compatible quotient-linear identifications:
   the second conclusion is the recorded `IsUniformlyBoundedConstructibleAdicTower d M`.
   Matches. I opened its definition and every field of `AdicTowerLocalModel`. The ring
   on a covering member is the inverse image of the original completed ring, and the
   local reductions use the actual restricted projection. One termwise window and one
   stratification serve all n. Terms are finite-type adic lisse, with no projectivity
   or finite Tor amplitude requirement.
10. Derived category and cohomology notions: Mathlib `DerivedCategory`, `Q`, and
    `homologyFunctor` have the signatures recorded by the dependency nodes. Their
    localization of integer cochain complexes and factored homology are exactly the
    categories and cohomology sheaves above. Matches.

Dependency repair H13: the current recorded constructibility predicate is
`IsConstructibleProEtaleFixedModuleSheaf`, on fixed ModuleCat-valued sheaves, whereas
this item uses ringed module sheaves. I read it and the older
`IsConstructibleProEtaleModuleSheaf`, which additionally puts the scalar ring in Type u
and lifts it. Neither directly types the present objects. The supplied ringed interface
uses the existing `IsRelativelyFiniteLisseModule` on the actual inverse-image constant
ring. This is the same intrinsic notion: local constant modules with finite stalks can
be refined to finite constant models, and these models have finite geometric stalks.
Empty covering members permit the zero model. This repair has real data, no postponed
theorem, no etale-origin clause and no extra Noetherian or uniform-rank assumption.
There are no new definition nodes and no statement correction to audit.

Sources read: the sandbox's complete Stacks `proetale.tex`, section
`section-constructible` and `definition-constructible`,
`lemma-compare-constructible-derived` (09AL), `definition-adic` (09BT),
`lemma-Noetherian-constructible`, `lemma-weird`, `lemma-connected-lisse`, and
`lemma-Noetherian-adic-constructible` (09BU--09BX); and `more-algebra.tex`,
`lemma-Rlim-pseudo-coherent-gives-complete-pseudo-coherent` (09AV), including its
hypotheses and surrounding reconstruction proof. The section assumes Noetherian
coefficients, supplied here by finite quotients and by the adic datum. Stacks'
affine-local constructibility convention differs from the dependency's explicit global
finite-partition convention; the delivered definition follows the dependency. The
common derived nonprojective local-model theorem is explicitly the node's eight-step
assembly, not a claimed verbatim Stacks lemma. All eight steps and their dependencies
appear in its theorem docstring. The current server BoundedConstructibleTower source
was read through `scompile.py --source` and has the same interface used above.

Edge cases checked: the empty scheme admits empty strata, so the positive-strata
hypothesis is witnessed by one empty stratum; the output permits an empty partition.
Zero coefficient rings and zero levels are not excluded. I=0 and I=A are covered when
they satisfy the recorded datum. The positive-level reindexing avoids an accidental
A/I^0 level. Equal indices, a=b, negative endpoints and the zero complex are covered.
No characteristic or invertibility restriction is introduced. Site objects remain in
u+1 and morphisms in u; coefficients and local module models are in u+1. There is no
extra universe equality. Every variable and universe is explicit, and both files set
`autoImplicit false`. No file-local notation, private data or new axiom is introduced.
The sole sorry is the named theorem with its source and full proof plan.

Independent searches during this reading:

- LeanFinder via msearch.py: "A derived compatible system of finite quotient sheaves
  with a uniform cohomological bound admits one bounded adic local model on each
  stratum". Eight ordinary localCohomology, completion and Hausdorffification hits;
  none states the theorem.
- Loogle via msearch.py: `"Sheaf", "constructible"`. No hits.
- LeanSearch via msearch.py: "A finite coefficient sheaf of modules is constructible
  if its restrictions to a finite locally closed partition are locally constant and
  have finite stalks". Eight finite-type/finite-presentation module-sheaf hits. Those
  notions do not impose local constancy on a finite stratification and are not matches.
- Mathlib grep via msearch.py: `locally.*finite.*strat|strat.*locally.*finite`. Only an
  unrelated Vitali-covering comment.
- Direct rg on Mathlib, WeilConjectures, lean/Sheaf and the upstream name map for
  normalized tower, tower effectivity, both orders of constructible/tower, and the
  delivered declaration names. No exact theorem or usable ringed constructibility
  interface. I opened the upstream DVR NormalizedTower and its effectivity theorem:
  those concern DVR reductions and derived completeness, without this common
  constructible-local-complex conclusion. The existing tower definitions are reused.

Mismatches and repairs: no mathematical mismatch was found. The public import of
`ProEtaleFiniteModuleIntrinsicComparison` was stale relative to the dependency node's
current `RefinementCoefficientRealization` record. I replaced it with that recorded
module, which reexports the same finite coefficient definitions and their canonical
realization. This also removes an unused specialized intrinsic interface. The returned
repair's direct public imports of AdicCoefficientDatum and BoundedConstructibleTower
are retained. The dependency node copy carried older `reviewed_lean` metadata; I
refreshed its non-lean fields from the read-only base, retaining only this delivery's
lean repair. Both node signatures remain verbatim substrings of their files. The
100-character line bound is satisfied in both files. All statement and proof fields
remain identical to the current base. The documented incompatible proof-only
ComparisonPullbackCoherence import remains omitted, with its role still recorded in
the unchanged DAG and proof docstring.

Validation of this final reading: the explicit two-file `scompile.py NC
lem-weil-pbc-normalized-constructible-local-effectivity ...` run exited 0 with no
warnings or errors. After the public-import repair, `deliver2.py NC
lem-weil-pbc-normalized-constructible-local-effectivity --no-push` compiled both final
files separately through the same prescribed wrapper and printed
`OK (dry run): commit 47215af1b9 passes the preflight and compiles; nothing pushed`.
The wrapper's compiler limits were not changed. No direct compilation or git mutation
was performed in either read-only source checkout.
