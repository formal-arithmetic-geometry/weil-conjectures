## Worker report

The delivery states `WeilConjectures.integral_ctf_isTriangulated` in
`Sheaf.Paper.IntegralCtfTriangulated`. Its accompanying real definition
`WeilConjectures.integralCtfProperty` is the property P introduced in this very node;
it introduces no independent notion and has no postponed data. Every theorem proof
is `by sorry`. The module docstrings contain the node's complete six-step proof plan.
No statement correction, disputed statement, or new DAG node is needed.

Hypothesis and clause correspondence for lem-weil-integral-ctf-triangulated:

- The global finite-field datum is `(D : FiniteFieldDatum.{d})`; its characteristic
  prime is `D.p`. The chosen coefficient prime is `(l : ℕ) [Fact l.Prime]`, and
  `(hl : l ≠ D.p)` is precisely the distinct-characteristic condition.
- `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]` is the finite extension of Q_l. Its valuation ring,
  chosen uniformizer and quotient rings are the dependency's canonical
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer` and
  `Padic.coefficientExtensionRing`, without a second coefficient construction.
- `(Y : AlgebraicGeometry.Scheme.{u})` is any scheme, and
  `[∀ y : Y, Invertible (l : Y.residueField y)]` says l is invertible at every point,
  equivalently invertible on Y. There is no finite-type, Noetherian, separatedness,
  dimension or nonemptiness assumption on Y. The independent datum universe d is
  unrestricted. The shared scheme/coefficient universe follows the recorded
  bounded-constructibility and Tor-amplitude interfaces; any smaller coefficient
  ring can be lifted to it.
- The ambient category is exactly `completedIntegralDerivedCategory l E Y D hl`,
  the derived category of modules over the completed integral coefficient sheaf,
  rather than the discrete constant valuation-ring sheaf.
- In `integralCtfProperty`, the intersection's first property is exactly
  `boundedConstructibleDerivedCompleteIntegral D l hl E Y`. This retains derived
  completeness, constructibility of every reduction, and the dependency's uniform
  cohomological support condition.
- The second property is `∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ... a b`.
  Thus a single ordered interval is chosen before all reduction levels. The stored
  index n denotes j=n+1, so every positive exponent is covered exactly once,
  including j=1. In particular this is not `∀ n, ∃ a b, ...`.
- The reduced object is `(integralDerivedReduction l E Y D hl n).obj K`.
  Its target is definitionally the recorded pro-etale derived category with
  coefficient ring `Padic.coefficientExtensionRing l E (n + 1)`. No forgetting of
  scalars, arbitrary comparison map, or change of coefficient category is used.
- `HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1)) ... a b`
  is the recorded notion, testing all module sheaves in degree zero and vanishing
  of tensor cohomology outside [a,b]. Its own order condition is retained; the
  explicit a≤b also mirrors the statement's ordered witness.
- `ObjectProperty.IsClosedUnderIsomorphisms (integralCtfProperty D l hl E Y)` is
  exactly the required isomorphism closure. `ObjectProperty.IsTriangulated` supplies
  zero, all integer shifts, and middle-vertex extension closure up to isomorphism.
  Combined with the first conjunct it gives closure for the actual middle vertex.
  Specifically Mathlib's `ObjectProperty.prop_zero`,
  `ObjectProperty.prop_shift_iff_of_isStableUnderShift`, and
  `ObjectProperty.ext_of_isTriangulatedClosed₂` give the node's three explicit clauses.
  `ObjectProperty.FullSubcategory` is full by construction, and the instances in
  `Mathlib.CategoryTheory.Triangulated.Subcategory` give its inherited triangulation
  and the exact inclusion. These consequences impose no extra hypothesis.
- The explicit `@ObjectProperty.IsTriangulated` arguments are the ambient category's
  canonical Mathlib instances. `(fun (n : ℤ) ↦ inferInstance)` selects additivity
  separately at each integer shift. This avoids an unresolved universe metavariable
  from automatic synthesis of the entire dependent family; it does not choose an
  alternative shift or triangulation. All universes and variables are explicitly bound.

Dependency declarations read and reused:

- `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.DerivedCompleteIntegralDetailed`,
  `WeilConjectures.boundedConstructibleDerivedCompleteIntegral` and its full-subcategory
  abbreviation. Its definition and full signature were read.
- `Sheaf.Paper.IntegralConstructibleTriangulated`,
  `WeilConjectures.boundedConstructibleDerivedCompleteIntegral_isTriangulated` (stated in this delivery).
- `Sheaf.Paper.IntegralDerivedReduction`, `WeilConjectures.integralDerivedReduction`,
  its canonical change-of-rings construction and exactness witness.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`,
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`,
  `CategoryTheory.ObjectProperty.IsTriangulated`, including its three parent classes
  and the induced full-subcategory instances; also the recorded
  `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms`.
- Proof-only imports retain the finite-stage theorem in `Sheaf.Paper.FiniteCtfTriangulated`,
  derived tensor in `Sheaf.Algebra.Homology.DerivedTensor`, and change of rings in
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`. Their full
  signatures and docstrings were read. Other public statement dependencies are already
  exposed by the imported dependency modules.

Source and edge cases:

Read Stacks `sites-cohomology.tex`, label `lemma-cone-tor-amplitude`, Tag 08G2:
part (2) retains the common interval for the middle vertex. Read the integral paragraph
of the blueprint `def-weil-finite-tor-amplitude.md` and the definition in
`def-weil-derived-complete-integral-detailed.md`. Zero uses [0,0] uniformly, including
on the empty scheme. Positive reduction indexing starts at j=1 and never includes the
zero-exponent quotient. Every integer shift, including zero and negative shifts, is
covered; shifting an interval gives [a-m,b-m] with no ordering issue. For an extension,
minimum of the two lower bounds and maximum of the upper bounds work at every level.
A singleton interval is allowed. No common stratification or bound on ranks is added.
Empty cohomological support is allowed. Merely separate finite intervals at each level
would not satisfy the definition; the quantifier order excludes that erroneous case.

Searches for existing statements and definitions (including the inherited search log):

- `msearch.py ... leanfinder "Derived complete constructible integral complexes whose
  reductions have uniformly bounded Tor amplitude form a triangulated subcategory"`:
  eight hits on generic derived-category t-structure and IsGE/IsLE bounds; none states
  the integral uniform-reduction theorem.
- `msearch.py ... loogle "CategoryTheory.ObjectProperty.IsTriangulated,
  CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms"`: twelve generic subcategory,
  intersection and localization hits; no integral coefficient statement. The generic
  Mathlib class is reused.
- `msearch.py ... grep "TorAmplitude|integral_ctf|integral_constructible"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Uniform Tor amplitude reductions integral complexes
  triangulated subcategory"`: service unavailable, Internal Server Error; this is
  recorded as unavailable, not as evidence of absence.
- `rg -n "integral_ctf|integral_constructible|boundedConstructibleDerivedCompleteIntegral|
  lem-weil-integral-ctf-triangulated"` in upstream `WeilConjectures` and project
  `lean/Sheaf`: only the existing bounded integral definition and its full-subcategory
  abbreviation were found; no closure theorem. Additional upstream adic and project
  triangulation searches found only finite-stage and unrelated closure statements.
- Read the source of every direct statement dependency and its recorded declaration;
  the original packet supplied the integral-constructibility closure dependency;
  this repair rebuilds its now-recorded declaration against the repaired tower.
  Its proof dependencies with declarations are imported without `public`; unstated
  proof dependencies are not needed to type this stage-2 theorem.

Validation: all ten delivered files compile separately, in dependency order, through
`scompile.py`, with no errors or warnings, at nice 19, two threads and the 60-second
per-file limit. The wrapper also rebuilds the dependent integral tower, completeness
and bounded-constructibility sources in its private overlay. No live files were edited
and no global build was run. Delivery preflight is checked by `deliver2.py --no-push`.
The independent second reader supplies the second-reading section and performs delivery.

## Dependency modules

`lem-weil-integral-constructible-triangulated`: the original packet supplied this
prerequisite when it had no Lean record. Its now-recorded statement is retained and
rebuilt with the repaired completeness interface in this delivery. `Sheaf.Paper.IntegralConstructibleTriangulated` states exactly its
isomorphism-closure and triangulation assertion for the existing
`boundedConstructibleDerivedCompleteIntegral`; it adds no invertibility or geometric
hypothesis to that dependency. Its data binders D,l,hl,E,Y retain exactly the dependency
coefficient context. Isomorphism closure plus Mathlib's triangulated object-property
class supplies every zero, shift, actual middle-vertex, inherited triangulation and
exact-inclusion clause. Its docstring reproduces all eight stored proof steps and
names their dependencies, including the independent-of-level support bounds.

`def-pc-kflat-complex`: the local and server recorded source is general in three
independent universes, whereas the published imported artifact specialized
`IsKFlatResolution` to the site universe. This made the already recorded integral tower
fail before the new statements elaborated. The delivery repairs the owning
`Sheaf.Algebra.Homology.KFlat` module under §1(B), supplying the independent-coefficient
interface and compiling its paired consumers together. The K-flat definition still tensors every acyclic
complex with the given complex and requires the resulting total complex acyclic;
a resolution is still precisely `QuasiIso f ∧ IsKFlatIndependentCoefficients ...`.
The node now records `IsKFlatIndependentCoefficients` as its main declaration; the
legacy `IsKFlat` remains available for existing finite-level consumers. All canonical monoidal and
abelian interfaces and their existing blueprint-tagged postponed theorems are retained.
The new declarations retain the canonical sheaf tensor structure; their explicit
coefficient-universe interfaces prevent the implicit instance specialization.
`def-pc-kflat-complex` is added to the item's statement dependencies as an existing
landed definition used by the recorded Tor-amplitude and integral-completeness notions.
The paired dependency modules are also `lem-pc-kflat-resolution`,
`def-weil-derived-complete-integral-detailed`, `lem-pur-derived-change-of-rings`,
`lem-weil-integral-reduction-tower-well-defined`, `def-weil-derived-complete`,
`def-weil-integral-reduction-tower`, and `def-weil-integral-derived-reduction`.
Recompilation with this paired interface resolves the tower's source/artifact mismatch;
site object and morphism universes remain distinct, and no extra universe equality or
mathematical hypothesis is imposed.


## H10 return repair

Read the return entry for immutable head f2fc00acb494. Its referenced review.md
was not present in this sandbox; the return states the concrete H10 failures. The return accepts the target
statement and requires a coherent universe interface plus a defined tower map.
I reproduced its seven-file scompile invocation: IntegralDerivedReduction fails
when the imported IsKFlat artifact fixes the coefficient universe to t+1, although
the actual sheaf has coefficients in max u (t+1). Compiling a tower subset also
loses the ordinary functor's Additive instance and causes dependent declarations
to fail. These failures explain the missing integralReductionTowerMap name.

Repair 1 (full coefficient universe): IntegralDerivedReduction,
IntegralReductionTowerWellDefined, IntegralReductionTower and DerivedComplete use
`IsKFlatIndependentCoefficients` or `IsKFlatResolutionIndependentCoefficients` at
coefficient size `max u (t+1)`. The resolution and derived-change-of-rings theorems
use this same predicate at their independent coefficient size `r`. The legacy
`IsKFlat.{u,v,w}` syntax was insufficient: implicit tensor instances specialized
its elaborated coefficient universe to the site size. The explicit coefficient
sheafification, monoidal-localization and zero-morphism interfaces in the owning
KFlat module avoid this specialization. The real total-tensor acyclicity condition
and quasi-isomorphism conjunction are retained. No site universe equality or new
mathematical hypothesis is imposed. All ten files are compiled as one coherent
packet; every variable and universe is explicitly bound.

Repair 2 (canonical tower map): integralReductionTowerMap is retained as
`(integralTowerAugmentationIso ...).inv ≫ DerivedCategory.Q.map (integralTowerUnit ...)`.
Its resolution binder now accepts the full coefficient universe. The preceding
well-definedness module successfully defines the finite tensor complex, restricted
complex, canonical counit comparisons, unique pure-tensor unit and transitions, and
inverse augmentation. Consequently the map, its naturality theorem and cone elaborate
in sequence. No arbitrary map, alternative reduction functor, or arbitrary isomorphism
was substituted. The zero, positive level-one, empty-scheme and negative-shift cases
remain included. The generic dependency repair also retains arbitrary independent
site universe t and field universe u, beyond the target's specialization t=u.

Read the actual generalized K-flat, resolution and change-of-rings signatures, the
completed coefficient sheaf construction, both tower modules and completeness sources.
Rechecked Stacks Tags 06YN, 06YY and 08G2, and the integral paragraph of the blueprint
from the launcher's literature mirror. Tag 08G2(2) states the middle-vertex interval
closure used here. The target statement, property and six-step proof docstring are
unchanged; no statement_change is needed. Every delivered theorem still has only sorry.

Fresh searches: msearch LeanFinder for “Integral complexes with a uniform Tor amplitude
for all reductions form a triangulated subcategory” returned eight generic t-structure
and homological-kernel hits; Loogle for CategoryTheory.ObjectProperty.IsTriangulated
returned the reused generic class and its instances; Mathlib grep for
`integral_ctf|integralReductionTowerMap|IsKFlatResolution` returned no hits. Searches
in the upstream and side sources locate the already recorded definitions, which this
paired repair uses. No new notion or new DAG node is introduced.

Validation: the revised ten-file scompile packet passed separately for every module
in both sandbox and library contexts, with no errors or warnings. The slowest file
was IntegralDerivedReduction (15.8 s), within the unchanged 60-second limit.
The final deliver2.py --no-push check rebuilds the entire packet and checks its node
records and preflight before READY. The next reader must compile all ten repaired modules together so the dependent
interfaces are rebuilt consistently.


## H10 repair revalidation

The returned head is f2fc00acb494. A fresh ten-file `scompile.py` invocation on the
current repaired sandbox passed every sandbox and library compilation without
errors or warnings; the slowest invocation was IntegralDerivedReduction at 24.2 s.
Both tower-map uses in its naturality theorem and its cone elaborate successfully,
so the previously unknown map identifier is now available downstream.

This pass also disabled autoImplicit explicitly in IntegralDerivedReduction, added
the missing zero-morphism instance to its owning node's declaration list, completed
the three new tensor-infrastructure proof docstrings, and corrected stale repair
text and dependency notes that described the unsuccessful legacy-universe attempt.
The item statement, its property, coefficient projection, canonical reduction functor,
pure-tensor unit/transition maps and canonical inverse augmentation are retained.
No statement correction is needed. The earlier second readings are archived in the sandbox scratchpad; the next
independent reader must review this repaired packet and deliver it.

Fresh searches in this repair: LeanFinder for “Integral complexes whose positive
coefficient reductions have one uniform finite Tor interval form a triangulated
subcategory” returned eight generic t-structure bounds; Mathlib grep for
`integral_ctf|integralReductionTowerMap|IsKFlatIndependentCoefficients` returned no hits.
Loogle for `CategoryTheory.ObjectProperty.IsTriangulated` returned twelve generic
class and instance declarations, including the reused class. Source grep locates the recorded tower maps and an existing consumer of the
independent-coefficient predicate, with no integral CTF theorem to reuse.
The current server KFlat source was read through `scompile.py --source`; it still
has the legacy interface. Re-read the local literature mirror's Tag 08G2(2) and
the blueprint integral paragraph: both require exactly the common interval recorded
in the unchanged target. The final mechanical gate is `deliver2.py --no-push`.

The post-edit standalone compilation passed all ten files, with the slowest
invocation at 17.6 s. The first dry run caught truncated `lean.statement` metadata
from a signature extractor that mistook named-argument `:=` for a declaration body.
Re-extracted every signature through its final body delimiter and checked balanced
binders; no Lean declaration changed. The second-reading section is intentionally
left to the next independent reader.


## Earlier second reading (a previous round; superseded)

Independent second reading of the repaired ten-module packet, 2026-10-16. I read
brief-stage2, delivery-errors H, the worker report and H10 return history, each
sandbox module, its owning node, all direct statement-dependency declarations,
the finite-stage proof theorem, and the actual current KFlat server source via
`scompile.py --source`. I did not write the submitted mathematical statements.

The source list and its Lean correspondence, item by item:

1. Global finite-field datum and characteristic p: `(D : FiniteFieldDatum.{d})`,
   with characteristic `D.p`. Read the structure in FiniteFieldFiber: it specifies
   a prime p, positive exponent, finite base field of the stated cardinality, and
   an algebraic closure. Verdict: exactly the global datum; no assumption that Y
   itself is a finite-type scheme over that field is introduced.
2. Prime ell distinct from p: `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
   Verdict: both source hypotheses, with no missing characteristic case.
3. Finite extension E/Q_ell, its valuation ring and chosen uniformizer:
   `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`. Read CoefficientExtension: its integer ring
   is the spectral-absolute-value valuation subring, and its chosen uniformizer
   supplies `coefficientExtensionIdeal` and `coefficientExtensionRing`.
   Verdict: the existing coefficient datum is used throughout, with no new
   valuation, quotient, or field embedding assumed.
4. Scheme Y with ell invertible: `(Y : AlgebraicGeometry.Scheme.{u})`
   and `[∀ y : Y, Invertible (l : Y.residueField y)]`. A section is invertible
   precisely when its image is invertible in every residue field, so this is
   invertibility of ell on Y. Verdict: exact; no Noetherian, separated, finite
   type, dimension, connectedness or nonempty hypothesis.
5. Positive quotient levels A_{E,j}: `n : ℕ` denotes `j = n + 1`, and the
   coefficient is `Padic.coefficientExtensionRing l E (n + 1)`.
   Verdict: every and only positive exponent occurs, including j=1 at n=0.
6. Ambient D(Y_proet,O_E): `completedIntegralDerivedCategory l E Y D hl`.
   Read CompletedIntegralCoefficients: it is modules over the inverse limit of
   constant finite quotient sheaves, with standard derived localization.
   Verdict: completed coefficient sheaf, exactly as the node requires.
7. Integral bounded constructibility: the first factor of `integralCtfProperty`
   is `boundedConstructibleDerivedCompleteIntegral D l hl E Y`. Its actual
   definition requires `IsDerivedComplete`, finite-torsion constructibility
   of each positive reduction, and one ordered cohomological support interval
   independent of the level. Verdict: all clauses retained; it does not replace
   completeness by a predicate about unrelated chosen data.
8. Canonical reduction of K: `(integralDerivedReduction l E Y D hl n).obj K`.
   Its ordinary functor has the tensor objects AND maps fixed by the
   change-of-rings witness; its derived functor and counit satisfy the universal
   left-derived property. Its K-flat computation is the counit isomorphism,
   and resolution comparisons invert the augmentation then use that counit.
   Verdict: exactly derived change of rings along the completion projection;
   its target at t=u is definitionally the finite-coefficient category used
   by HasProEtaleTorAmplitude. It is not just a restricted integral object.
9. A common ordered Tor interval: `∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ... a b`.
   Verdict: the existential precedes all levels. A separate interval at each
   level would be weaker and is excluded. No endpoint depends on n.
10. Tor amplitude at each level: `HasProEtaleTorAmplitude Y
    (Padic.coefficientExtensionRing l E (n + 1)) ... a b`. Read its body:
    it tests every module sheaf in degree zero and every K-flat resolution of
    every representative isomorphic to K; the tensor cohomology is zero for
    `i < a ∨ b < i`. Verdict: exactly Stacks 08FZ, including ordered endpoints.
11. Isomorphism closure: the first theorem conjunct is
    `ObjectProperty.IsClosedUnderIsomorphisms (integralCtfProperty D l hl E Y)`.
    Verdict: closure of this actual property, not an unrelated full subcategory.
12. Zero, all shifts and middle vertices: the second conjunct is Mathlib's
    `ObjectProperty.IsTriangulated` on the same property. Read its parents:
    ContainsZero, IsStableUnderShift ℤ and IsTriangulatedClosed₂. Together with
    conjunct 1, `ext_of_isTriangulatedClosed₂` gives the actual middle vertex,
    rather than only an isomorphic replacement. Shift stability plus isomorphism
    closure gives the iff for every integer shift, including the reverse shift.
    Verdict: precisely the node's three closure clauses.
13. Fullness, inherited triangulation, and exact inclusion: ObjectProperty's
    FullSubcategory is full by construction. Read Mathlib Subcategory's inherited
    Pretriangulated instance, its triangulated-category instance when the ambient
    is triangulated, and the instance `P.ι.IsTriangulated`. Verdict: the stated
    classes entail these clauses without an extra mathematical assumption.
14. Universes and ambient structures: d is independent of u. The main predicate
    uses the recorded same-size Y/coefficient interface; finite extensions can
    be represented in the scheme universe. Its explicit `@IsTriangulated`
    arguments are canonical ambient instances, and `fun (n : ℤ) ↦ inferInstance`
    fixes the family of additive shift functors. The dependency packet remains
    general in independent scheme t and field u, at coefficient size
    `max u (t + 1)`, with site objects t+1 and morphisms t. Verdict: no extra
    equality of site universes, unresolved variable, or extra instance binder.

Source check: read the local literature mirror's blueprint integral paragraph of
`def-weil-finite-tor-amplitude` and full definition
`def-weil-derived-complete-integral-detailed`; read Stacks sites-cohomology.tex,
labels definition-tor-amplitude (08FZ), lemma-cone-tor-amplitude (08G2),
definition-K-flat (06YN), lemma-K-flat-resolution (06YS) and
lemma-derived-base-change (06YY), including their surrounding contexts. 08G2
assumes only a ringed site, a distinguished triangle and integer endpoints;
part (2) preserves a preassigned interval for the middle vertex. There is no
hidden geometric finiteness condition. The blueprint imposes ell invertible
on Y and explicitly one interval independent of j. Also read Bhatt--Scholze
PDF p.24, section 3.5, especially Definition 3.5.2: the coefficient sheaf is
an inverse limit and completeness uses the canonical reduction augmentation.
No statement_change is present or needed, so no correction citer audit applies.

Dependency modules reviewed under §1(B), with the corresponding node statements:

- def-pc-kflat-complex / KFlat: both the legacy and independent coefficient
  predicates say total tensor with every acyclic complex is acyclic; resolution
  means precisely quasi-isomorphism and this K-flatness. The server still has
  only the legacy interface; the added independent interface explicitly binds
  coefficient sheafification, tensor localization and zero-map structures.
  These are the canonical structures, with real tensor data, not new tensor
  products. Relative essential smallness and the sheafification hypotheses are
  infrastructure for the coefficient universe and are supplied for this site.
  The retained legacy names support the already recorded finite-level tensor
  and Tor-amplitude modules. Verdict: owning-module interface repair, no private
  replacement of the mathematical notion. Corrected the resolution helper's
  blueprint attribution to this owning definition node.
- lem-pc-kflat-resolution / KFlatResolutionIndependentCoefficients: for every G,
  existence of K,f with independent K-flatness, flat terms, QuasiIso f and
  degreewise Epi. In sheaves Epi is local surjectivity, exactly termwise
  surjectivity in the source's sheaf category. Verdict: every source clause.
- lem-pur-derived-change-of-rings / DerivedChangeOfRingsIndependentCoefficients:
  arbitrary same-site commutative ring-sheaf map; ordinary tensor functor with
  fixed object/map formulas; preservation of quasi-isomorphisms between K-flat
  complexes; everywhere-defined pointwise left derived functor with universal
  counit, exactness and invertibility on K-flat representatives. Verdict: both
  node clauses and canonical, composable comparisons, with independent sizes.
- def-weil-integral-derived-reduction / IntegralDerivedReduction: standard
  localizations, actual completion projection, ordinary tensor functor and
  universal derived pair, exactness, local surjectivity and canonical K-flat
  computation. Verdict: full node, no arbitrary derived functor choice.
- lem-weil-integral-reduction-tower-well-defined /
  IntegralReductionTowerWellDefined: explicit sheafified pure tensors;
  uniquely characterized unit and transition maps; finite comparison through
  the common derived object, then exact restriction of scalars; both augmented
  and transition compatibility identities. Verdict: exactly both node clauses.
  The existence theorem specifies a UNIQUE pair before its maps are chosen;
  this is permitted postponed proof data and not a hollow existential choice.
- def-weil-integral-reduction-tower / IntegralReductionTower: ofOpSequence of
  the canonical transitions; map `[q]⁻¹ ≫ Q.map γ_n`; naturality for every
  arrow of ℕᵒᵖ and the resulting cone. Verdict: the source's augmented tower.
  In particular the map identifier is really defined before naturality/cone.
- def-weil-derived-complete / DerivedComplete: quantified representative G,
  K-flat resolution q:P→G and iso QG≅K; the cone is transported by that iso
  and the Roos triangle uses its specified first arrow. Verdict: exact node
  predicate, retaining the actual augmentation, not any map to a derived limit.
- def-weil-derived-complete-integral-detailed / DerivedCompleteIntegralDetailed:
  derived completeness, each constructible reduction, common cohomological
  support interval, and the full subcategory abbreviation. Verdict: exact node.
- lem-weil-integral-constructible-triangulated / IntegralConstructibleTriangulated:
  isomorphism closure and IsTriangulated for the preceding predicate, no extra
  invertibility or geometric condition. The two sheafification instances merely
  specialize the already constructed coefficient-size transport. Verdict: all
  node closure, inherited-triangulation and exact-inclusion assertions.

The dependency records describe why the published interfaces cannot be used
unmodified. There are no new DAG nodes. I checked all declarations listed in
each owning lean.declarations record. Every postponed theorem is named, tagged
and has its proof plan; the main statement reproduces its node's six proof steps
and the constructibility prerequisite its eight steps. Every theorem proof is
sorry; definitions contain real constructions, proof projections or choices
fixed by a universal property/uniqueness. No proof was filled during this reading.

Edge cases: the empty scheme is allowed and the residue-field condition is then
vacuous for the correct reason. Zero has common interval [0,0] and empty support.
The reduction family is nonempty: n=0 is exponent one; exponent zero is excluded
as in the source. A singleton interval a=b is allowed. All positive/zero/negative
shifts are quantified. No rank, common stratification or finiteness of Y is
assumed. Empty covers/strata are controlled by the recorded constructibility
predicate. For extensions min of lower endpoints and max of upper endpoints
remain independent of n. No independent empty index type can trivialize the
uniform-level condition.

Independent searches in this reading:

- LeanFinder: "Triangulated closure of derived complete complexes with a common
  Tor interval for all coefficient quotients" returned eight generic derived
  t-structure/boundedness declarations; none is the integral theorem.
- Loogle: `CategoryTheory.ObjectProperty.IsTriangulated` returned twelve generic
  class/instance declarations. Opened and reused the class, its parents and
  inherited subcategory/exact-inclusion instances.
- Mathlib grep through msearch: `adic.*triangulated|uniform.*Tor|integralCtf`
  returned no hit. Direct rg with other words (uniform Tor bounds, adic and
  integral constructibility, independent coefficient K-flatness) was run on
  Mathlib, upstream WeilConjectures and the project's lean/Sheaf.
- LeanSearch: "Integral pro-etale complexes whose reductions have one common
  finite Tor amplitude form a triangulated subcategory" was unavailable with
  Internal Server Error; this is not treated as absence evidence.
- Opened the upstream Etale Derived IntegralCoefficients normalized-tower
  membership theorem and ProEtale Derived TorAmplitude declarations. They use
  sheaves valued in ModuleCat, discrete integral/etale coefficients or generic
  finite-stage Tor predicates; they do not state this completed-ring-sheaf
  integral uniform-reduction theorem. Read pefw-upstream-framework: its module
  object/condensed framework likewise supplies no matching integral-to-completed
  coefficient statement. The exact recorded Sheaf dependency notions are reused.

Mismatches and repairs: no mathematical mismatch in the repaired main statement
or dependency statements was found. Fixed the K-flat resolution helper's
blueprint tag (it wrongly named the existence theorem's node); restored stale
maintainer-owned reviewed_lean metadata in dependency sandbox copies, leaving
only the authorized lean fields changed. The item's signature and mathematical
node statement are unchanged. No target unit statement was changed.

Validation is recorded below after the required clean packet compile and
preflight/delivery gates.


Additional source-scope check: Bhatt--Scholze section 6.5 is stated for qcqs X
and its own residue-stage definition of D_cons. The owning DAG node explicitly
uses the blueprint uniform-reduction variant, rather than asserting that those
two definitions are textually identical for arbitrary X. Its closure argument
uses the general ringed-site completeness and finite-stage closure interfaces;
no qcqs assumption from the paper's different D_cons definition is silently
added to this node. The local framework files also explicitly distinguish
module-object constructibility without derived completeness.

The first required ten-file scompile invocation reached the server fallback:
KFlat, KFlatResolutionIndependentCoefficients and DerivedChangeOfRingsIndependentCoefficients
compiled there, then nt_compile.py raised OSError 28 while creating its temporary
symlink overlay (No space left on device). This is a compiler-wrapper storage
failure, not a Lean error. The required delivery dry run is being retried on the
same corrected packet; no timeout/resource limit or live source was changed.


The retry's ten-file compile passed: deliver2 progressed beyond its scompile
error/warning gate and entered its prescribed shared-repository delivery lock.
All sibling files were supplied together and each compiled separately at the
unchanged 60-second per-file limit. The wrapper now awaits the shared fetch lock
before building its preflight commit. By-eye checks and a direct textual check
also confirm all ten lean.statement signatures occur verbatim in their files;
no line exceeds 100 characters, and autoImplicit is disabled in every module.


Final dry run: `deliver2.py NZ lem-weil-integral-ctf-triangulated --no-push`
printed OK: commit 748ccc7e26 passes the server preflight and compiles, with
nothing pushed. The transient overlay-storage failure cleared on the retry.
The independent second reader now performs the prescribed delivery.


## Immutable-head compiler return 68d378e92749

The return has one point: the independent file-only compiler raised
`FileNotFoundError(2, 'No such file or directory')`. It names no missing path or
Lean diagnostic. I checked that every `lean.file` in the ten delivered node
records exists in this sandbox and reran the full dependency packet through the
prescribed `scompile.py` wrapper. The successful run elaborated every delivered
module separately, both as a fresh sandbox module and at its library module name.
Its complete output is retained in `scratchpad/l-return-compile.log`: exit 0,
no errors or warnings, and a maximum Lean invocation of 18.8 seconds. The
FileNotFoundError did not recur. No source-path substitute or weakened declaration
was needed. The packet remains self-contained with all ten repaired sources;
compiling just the target against the older published tower reproduces its legacy
K-flat universe mismatch and is not a check of this packet.

One earlier wrapper attempt fell back to the server and reported an unrelated
`OSError: [Errno 28] No space left on device` while creating its private artifact
links. Local disk space was healthy. I made no tool, cache, live-source or global
build changes. A subsequent complete local-wrapper run succeeded, including the
canonical tower map, naturality and cone, and then the integral CTF statement.
Thus the available evidence resolves the returned compilation check; it does not
identify the missing path in the maintainer's original invocation.

For the next independent reader, the compilation input is exactly the ten
`lean.file` paths in this delivery's ten node records. Pass all ten to one
`scompile.py NZ lem-weil-integral-ctf-triangulated ...` invocation; the wrapper
compiles them separately in dependency order. Each path is relative to this
sandbox, or may be supplied as its existing absolute path. The required
`deliver2.py NZ lem-weil-integral-ctf-triangulated --no-push` check discovers and
checks the same ten modules. This report is the repair's new evidence and explicit
reproduction procedure; the independent second reading remains the next reader's.

Fresh Mathlib search through `msearch.py` for
`integralCtfProperty|integral_ctf_isTriangulated|IsKFlatIndependentCoefficients`
returned zero hits. Rechecked the finite-field datum, pro-etale Tor predicate,
canonical reduction/tower/completeness interfaces and Mathlib's triangulated
object-property class. The hypothesis and clause correspondence and edge-case
checks in the worker report still apply. No mathematical statement change is
indicated by this tool-level return.

LeanFinder query “A uniform Tor amplitude interval for every integral coefficient
reduction is preserved by shifts and distinguished triangles” returned eight
generic t-structure shift/bound hits, with no matching integral theorem. Loogle
query `CategoryTheory.ObjectProperty.IsTriangulated` returned twelve generic
class/instance hits, including the exact class reused here. The path audit checked
all ten unique module owners and that each recorded main signature appears
verbatim in its existing source file.

## Second reading by NZ

Independent reading of the current repaired packet, 2026-10-16. I read the node,
all ten delivered modules and their owning nodes, the direct statement dependencies,
and the source passages below. This reading follows the compiler-only return for
68d378e92749; I did not write the submitted statements. The main statement requires
no mathematical repair. I leave the Lean and node records unchanged and add this
current review and fresh validation evidence.

The node's objects, hypotheses and conclusions, matched individually:

1. Global finite-field datum with characteristic p: `D : FiniteFieldDatum.{d}`,
   `D.p`. I opened `Sheaf.Paper.FiniteFieldFiber`: its fields give a prime p,
   positive exponent, finite base field of the specified cardinality, and algebraic
   closure. Verdict: the node's datum; it does not silently make Y a scheme over D.k.
2. Prime ell different from p: `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`.
   Verdict: both hypotheses retained, including arbitrary residue characteristic
   different from ell; there is no characteristic-zero restriction.
3. Finite extension E/Q_ell with valuation ring, uniformizer and finite quotients:
   `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
   `[FiniteDimensional (Padic l) E]`. I read `CoefficientExtension`: its ring is
   the spectral-absolute-value integer subring; its chosen uniformizer generates
   the quotient ideal used in `Padic.coefficientExtensionRing l E (n + 1)`.
   Verdict: the dependency's coefficient data, without a new ring or uniformizer.
4. Scheme Y with ell invertible: `Y : AlgebraicGeometry.Scheme.{u}` and
   `[∀ y : Y, Invertible (l : Y.residueField y)]`. Invertibility in every residue
   field expresses invertibility on Y. Verdict: no Noetherian, finite-type,
   separated, qcqs, dimension or nonemptiness hypothesis is added.
5. Ambient completed integral derived category:
   `completedIntegralDerivedCategory l E Y D hl`. I read
   `CompletedIntegralCoefficients`: the ring sheaf is the limit of the positive
   constant quotient sheaves; module sheaves and their standard derived
   localization are then formed. Verdict: completed sheaf coefficients, exactly
   the ambient category in the node, with the recorded pro-etale topology.
6. Membership in D^b_c(Y,O_E): the first factor of `integralCtfProperty` is
   `boundedConstructibleDerivedCompleteIntegral D l hl E Y`. Its delivered
   definition explicitly conjoins `IsDerivedComplete` with constructibility
   at every positive reduction and a single cohomological support interval.
   Verdict: all parts of the owning definition are retained.
7. A single ordered Tor interval before all positive reductions:
   `∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, HasProEtaleTorAmplitude ... a b`.
   The reduced object is `(integralDerivedReduction l E Y D hl n).obj K`;
   n denotes exponent n+1. Verdict: the quantifier order is exact, rather than
   allowing the endpoints to depend on n. All positive exponents occur.
8. The finite coefficient object and its Tor condition are the recorded
   `Padic.coefficientExtensionRing` and `HasProEtaleTorAmplitude`. I opened
   `ProEtaleDerivedCategory`, `ProEtaleTorAmplitude`, and `DerivedTensor`:
   they use the constant commutative-ring sheaf, its module category, every
   degree-zero module sheaf, and vanishing outside [a,b] of the tensor computed
   by K-flat representatives. The reduction's target is definitionally that
   category at t=u. Verdict: no forgetting of scalars or substitute tensor.
9. Isomorphism closure: the first conclusion is
   `ObjectProperty.IsClosedUnderIsomorphisms (integralCtfProperty ...)`.
   Verdict: exactly the separate closure assertion.
10. Zero: `ObjectProperty.IsTriangulated` extends `ContainsZero`; with the
    preceding isomorphism closure this gives the actual zero object via
    `ObjectProperty.prop_zero`. Verdict: the node's zero clause.
11. Every integer shift, in both directions: the same Mathlib class extends
    `IsStableUnderShift ℤ`; isomorphism closure gives
    `prop_shift_iff_of_isStableUnderShift`. Verdict: includes all m in Z and
    the reverse implication, with no positivity restriction.
12. Middle vertices of distinguished triangles: its third parent is
    `IsTriangulatedClosed₂`. I read `ext_of_isTriangulatedClosed₂`: with
    isomorphism closure, its conclusion is the property of the actual middle
    vertex. Verdict: precisely K and M satisfying P implies L satisfies P.
13. Full subcategory and inherited triangulation: `ObjectProperty.FullSubcategory`
    is full; Mathlib's `Triangulated.Subcategory` constructs its pretriangulation,
    exact inclusion and triangulation when the ambient category is triangulated.
    Verdict: all the final categorical clauses follow from the stated class,
    without an additional unmentioned assumption. The explicit class arguments
    and `(fun (n : ℤ) ↦ inferInstance)` select the ambient canonical instances.

Sources read: the launcher's local Stacks mirror, `sites-cohomology.tex`,
`definition-tor-amplitude` (08FZ), `lemma-cone-tor-amplitude` (08G2),
`definition-K-flat` (06YN), `lemma-K-flat-resolution` (06YS),
`lemma-derived-tor-quasi-isomorphism-other-side` (06YT), and
`lemma-derived-base-change` (06YY); `derived.tex`,
`definition-triangulated-subcategory` (05QM); both blueprint files
`def-weil-finite-tor-amplitude.md` and
`def-weil-derived-complete-integral-detailed.md`; Bhatt--Scholze Definitions
3.5.2 and 6.5.1 and the setup of section 6.5. Stacks 08G2(2) is for any
ringed site and preserves a specified common interval. Bhatt--Scholze section
6.5 has qcqs X and a different residue-stage constructibility definition;
the node explicitly follows the blueprint's uniform-reduction definition.
Its arbitrary-scheme closure is therefore not an assertion that these two
definitions agree without the paper's hypotheses.

Dependency-module reading (no new nodes in this packet):

- `def-pc-kflat-complex`: I checked both legacy and independent-coefficient
  predicates in KFlat. The latter tensors every acyclic complex with K and
  asks that the total complex be acyclic; its resolution is exactly
  `QuasiIso f ∧ IsKFlatIndependentCoefficients ...`. The tensor is the
  canonical sheafified tensor. The extra sheafification/localization interfaces
  retain independent site object, site morphism and coefficient universes.
  Verdict: the node's definitions, with the documented interface repair.
- `lem-pc-kflat-resolution`: arbitrary G has K, an augmentation, K-flatness,
  flatness of every term, quasi-isomorphism and degreewise epi. Verdict: all
  clauses of 06YS, without boundedness of G or enough-projectives assumptions.
- `lem-pur-derived-change-of-rings`: E's objects AND maps are constrained to
  the recorded scalar extension; quasi-isomorphisms between K-flat objects
  are preserved. The pointwise universal derived functor has its counit,
  triangulated structure and invertible K-flat computation. Verdict: both
  node clauses and canonical composable resolution comparisons are retained.
- `def-weil-integral-derived-reduction`: uses the actual completed-ring
  projection and that universal derived pair. The named functor and counit
  are its projections; resolution comparisons invert the augmentation's
  image and then use the counit. Verdict: exactly derived reduction, with
  coefficient size max u (t+1), not an arbitrary functor.
- `lem-weil-integral-reduction-tower-well-defined`: units and transitions
  are characterized on sheafified pure tensors, with a unique pair of
  chain maps. Finite comparisons pass through the common derived reduction;
  restriction of scalars and localization comparisons fix their endpoints.
  The theorem states both augmentation and transition identities. Verdict:
  both node clauses, with canonical rather than arbitrary isomorphisms.
- `def-weil-integral-reduction-tower`: `Functor.ofOpSequence` uses those
  transitions; its map is `[q]⁻¹ ≫ Q.map γ_n`. Naturality is stated before
  the cone is constructed. Verdict: the augmented tower of the source.
- `def-weil-derived-complete`: quantifies a representative and K-flat
  resolution and transports the canonical cone through its representative
  isomorphism. The Roos triangle uses precisely that cone's first arrow.
  Verdict: completeness through the specified reduction maps, without an
  unconstrained map to a homotopy limit.
- `def-weil-derived-complete-integral-detailed`: completeness, every
  constructible reduction, and the uniform cohomological support interval
  are all explicit; its category abbreviation is the full subcategory.
  Verdict: the complete owning definition, not only finite-stage membership.
- `lem-weil-integral-constructible-triangulated`: isomorphism closure and
  the same triangulated object-property class give all owning-node clauses.
  It has no ell-invertibility assumption on Y, as required for this dependency.
  The two coefficient-size instances specialize the recorded transport.
  Verdict: unchanged general closure statement and full eight-step proof plan.

I checked the named theorem docstrings, including the three tensor-infrastructure
helpers and unique tower-map existence. They name the owning source/blueprint
and explain the postponed proofs. The main docstring contains all six node
steps, including enlargement to min/max endpoints independent of the reduction
level. Every postponed theorem body remains sorry. Definitions have actual
data, proof projections or choices determined by uniqueness/universal properties;
there is no choice of an arbitrary map or uncharacterized isomorphism.

Edge cases: empty Y is included (the invertibility hypothesis is vacuous there),
zero admits [0,0], and empty cohomological support is permitted. At n=0 the
reduction is exponent one; the zero-exponent quotient is correctly excluded.
Intervals may have equal endpoints or negative endpoints. Shifts may be positive,
zero or negative; extension bounds use min/max independently of n. There is no
empty reduction-index type that could make the uniform condition vacuous.
The datum universe d is independent. Y and E use the recorded common ambient u;
the actual site still has object universe u+1 and morphism universe u, with
coefficient sheaves in u+1. The repaired dependencies also cover independent
field universe u and scheme universe t via max u (t+1); none equates the site
universes or leaves a variable/universe auto-implicit.

Fresh searches in this reading:

- LeanFinder through msearch: "Complexes over a completed coefficient sheaf with
  uniformly bounded tensor cohomology at every quotient form a triangulated
  subcategory" returned eight generic derived t-structure bounds, no match.
- Loogle through msearch: `CategoryTheory.ObjectProperty.IsTriangulated` returned
  twelve generic class/instance declarations, including the exact class reused.
- Mathlib grep through msearch:
  `completed.*triangulated|integralCtf|uniform.*TorAmplitude` returned zero hits.
- Direct rg on upstream WeilConjectures and project lean/Sheaf used integral
  constructibility, uniform Tor, and integral CTF terms. I opened the upstream
  etale normalized-tower membership theorem and pro-etale TorAmplitude file;
  their discrete coefficients/sheaves valued in ModuleCat and finite-stage
  definitions do not state this completed-ring-sheaf theorem. The copied
  module-object framework and its documented scope likewise give no match.

Mismatches found in the current packet: none in the mathematical statements,
canonical constructions or dependency-node correspondence. The earlier
compiler return supplies no missing path to repair. Every delivered lean.file
exists, all ten main signatures appear verbatim in their files, and comparison
with the shared node copies shows only authorized lean changes on dependencies.
No statement correction or target-unit change is needed. The required fresh
packet compile and dry-run/delivery results are recorded below.

Fresh validation: the full ten-file `scompile.py NZ
lem-weil-integral-ctf-triangulated ...` invocation exited 0. Each module compiled
separately in sandbox and library contexts, with no errors or warnings. The
slowest invocation was IntegralDerivedReduction at 49.0 seconds, below the
unchanged 60-second limit. All ten files disable autoImplicit; none has a line
over 100 characters. No missing-file error recurred, and the defined tower map,
its naturality, cone, completeness predicate and final statement all elaborated.

Fresh LeanSearch query through msearch, "A completed integral coefficient complex
with one common Tor amplitude bound on all positive quotients defines a
triangulated subcategory", returned service unavailable (Internal Server Error).
This is recorded as unavailable, not as evidence of absence.

The required dry run printed `OK (dry run): commit 41467d4670 passes the preflight
and compiles; nothing pushed`. The wrapper preserved current maintainer-owned
reviewed_lean metadata on four dependency records instead of delivering stale
sandbox copies of those fields. Its staged packet contains exactly the ten
owning node records, ten modules, and this report. I now run the prescribed
delivery wrapper on the same statements and this completed review.
