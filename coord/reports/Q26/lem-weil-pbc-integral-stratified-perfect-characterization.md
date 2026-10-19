## Worker report

Historical worker report: the second reading below supersedes its dependency and
coefficient-interface inventory. The final packet contains only the item module
and item node; the proposed dependency modules were removed in the second reading.

The item is stated without changing its mathematical statement. The main module gives
the three equivalent conditions, the closure assertion, and the comparison with the
existing detailed integral category as three theorem declarations of this one DAG node.
All theorem proofs are sorry; all definitions contain actual constructions.

Source checked: Bhatt–Scholze, arXiv:1309.1198, Proposition 6.6.11,
Definition 6.8.10, Proposition 6.8.11(1),(3), and
Definition 6.5.1. The main source explicitly describes locally constant perfect values
by completed constant realization, and distinguishes bounded constructible cohomology
from that local perfect-complex condition.

Hypotheses and clauses:

- The prime is l : ℕ with [Fact l.Prime].
- E is a field with [Algebra ℚ_[l] E] and [FiniteDimensional ℚ_[l] E].
  The existing Padic.coefficientExtensionIntegers and coefficientExtensionUniformizer
  provide A and its uniformizer. pbcPadicCoefficientDatum uses exactly their principal ideal.
- T : Scheme and [IsNoetherian T] encode a quasi-compact locally Noetherian scheme,
  equivalently a finite affine Noetherian cover.
- _hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n is the finite chain-length bound.
  The empty scheme has dimension bottom and is included.
- _hl : IsUnit (l : Γ(T, ⊤)) is equivalent to stalkwise invertibility: a sheaf
  section whose germs are units is invertible locally and those inverses glue.
- The ambient ring is pbcAdicCompletion T (pbcPadicCoefficientDatum l E), the actual
  inverse limit of the positive finite quotient sheaves in the dependency record.
  Module sheaves are pbcModules and the ambient localization is DerivedCategory.
- Condition (i) is the dependency's IsPbcBoundedConstructibleComplete. It retains a
  K-flat representative, intrinsic completion, the uniform normalized strict reduction
  tower, and Nonempty PbcCompatibleEtaleOrigins. The latter stores all origin objects,
  comparison isomorphisms, universally specified coefficient-reduction isomorphisms,
  compatibility, and the quotient cocycle. It is not merely a list of unrelated origins.
- Condition (ii) is IsIntegralStratifiedPerfect. It quantifies over a recorded finite
  LocallyClosedStratification, a covering sieve on the terminal pro-etale object of
  each stratum, and a perfect A-complex on every cover member.
  DerivedCategory.IsPerfectRingComplex is exactly the recorded bounded finite-projective
  model predicate. integralConstantDerived realizes A_T ⊗^L_A P using the exact constant
  module realization and normalized completed-ring comparison. integralLocalDerived
  restricts along the immersion and then to the actual slice site. Both objects in
  each local isomorphism have exactly the same restricted coefficient ring.
- Condition (iii) is IsIntegralBoundedConstructibleCohomology. Its first conjunct gives
  a finite interval with K.IsGE and K.IsLE. Every degree is then tested by
  DerivedCategory.homologyFunctor and IsIntegralStratifiedFinitelyPresented.
  This sheaf predicate uses finite strata, covering sieves, and Module.FinitePresentation
  on a module N. Its comparison object is the ordinary integralConstantModule applied
  to N and restricted by the same module inverse image and slice restriction.
  The degree-wise stratifications may differ, as the English statement allows.
- integralStratifiedPerfectCharacterization asserts (i) iff (ii), and (ii) iff (iii).
- integralStratifiedPerfectClosure asserts closure under every integer shift,
  the third vertex of every ambient distinguished triangle whose first two vertices
  satisfy (i), both standard truncation functors at every integer, and every
  cohomology sheaf embedded by DerivedCategory.singleFunctor in degree zero.
- integralStratifiedPerfectDetailed compares the existing
  boundedConstructibleDerivedCompleteIntegral predicate, under its own FiniteFieldDatum
  and l ≠ D.p hypotheses, with (i). No new finite-field hypothesis is added to the
  main characterization or closure theorem.
  The recorded detailed notation uses E : Type u, T : Scheme u; the small-site
  completed-tower interface uses coefficients in Type (u+1). Thus this comparison
  uses the canonical field ULift E. integralCoefficientULift is uniquely fixed on
  residue representatives, and integralDetailedCoefficientComparison is uniquely
  fixed by EVERY positive quotient projection. integralDetailedTransport is exact
  restriction along this canonical ring isomorphism. Consequently the same completed
  ring and actual reduction functors are compared; no arbitrary equivalence or
  equality of different ambient module categories is assumed.

The helper predicates and coefficient comparisons in the main module are constituent
notions of the characterization itself. They do not replace a recorded definition.
The ordinary completed-constant realization reuses completedKoszulConstant, scalar
restriction, and pbcCompletedComparison. General slice restriction reuses
ringedSiteDerivedRestrictionOfUniverses and the published residue-lifting slice instances.

Edge cases checked: zero modules and complexes; the empty scheme and empty covering
sieve; zero strata on an empty scheme; varying local perfect models; unbounded K in
the ambient category (boundedness is a conclusion/condition, not a hypothesis);
positive quotient exponents indexed by n+1, never the exponent-zero quotient;
all integer shifts and truncations, including degrees outside the support; arbitrary
choices of uniformizer (the quotient lift preserves maximal-ideal powers);
no extra equality between site-object, site-Hom and coefficient universes.

Searches: msearch.py LeanFinder, query “A bounded constructible derived complete pro
etale complex is stratified locally perfect over a complete discrete valuation ring”,
returned eight generic etale declarations and no match. Loogle query
"IsPerfectRingComplex", "Module.FinitePresentation" returned zero matches. LeanSearch
for “A constructible complete adic complex is locally a perfect complex after finite
stratification” was unavailable (Internal Server Error), recorded by the search wrapper.
msearch grep for pro.?etale.*perfect|constructible.*complete|
adicLisseConstantModules.*(Additive|additive) returned zero Mathlib hits.
Direct rg of WeilConjectures and lean/Sheaf found the published perfectness, coefficient,
restriction, constant-realization and residue-lifting ingredients, but no theorem
stating this node. Direct rg of Mathlib homology and algebraic geometry found no
stratified-perfect complete characterization. blueprint_refs search found no separate
already-formalized copy. The published CompletedConstantSheafReduction and
ResidueLissePerfectLift declarations were inspected and reused.

## Dependency modules

`def-weil-pbc-bounded-constructible-complete`: this prerequisite has no recorded Lean declaration and
scompile.py --source reports its module unavailable. This delivery therefore supplies
BoundedConstructibleComplete.lean and a lean-only record for that existing node,
as required by the human's “nothing waits” instruction. A search of all server delivery refs found the same prerequisite on
deliver/Q01/lem-cbc-integral-compact-support-uniform-restriction and an alternate
interface on deliver/Q06/sbc-def-admissible-lattices. This delivery reuses the Q01
BoundedConstructibleComplete and GeneralAdicReductionDatum sources verbatim; it
adds no second definition of their notions.

`def-weil-pbc-adic-coefficient-datum`: GeneralAdicReductionDatum.lean supplies the
strict derived reduction-tower interface of this already existing node in the
small-site coefficient universe.
The published AdicCoefficientDatum, BoundedConstructibleTower and all their canonical
ring constructions are imported rather than copied. The unique tensor-generator formula
fixes each tower transition; the derived universal property fixes the derived functor.
This is a lean-only dependency repair with an explanatory lean.note.

## New nodes

None. Both additional modules belong to existing prerequisite nodes. The main module's
local-model and canonical coefficient-comparison helpers belong to the item's notion.

## Validation

`scompile.py Q26 lem-weil-pbc-integral-stratified-perfect-characterization` with
all three delivered modules exited 0 after the import repair. Each file passed
both the wrapper's sandbox and library-name checks in dependency order, with no
compiler errors or unexpected warnings. No global build was run.

`deliver2.py Q26 lem-weil-pbc-integral-stratified-perfect-characterization --no-push`
is the final preflight and repeats the per-file checks. The independent second
reading and actual delivery are reserved for the second reader; nothing is pushed
by this worker.

## Dependency declarations used

| Node | Module / source file | Declaration |
|---|---|---|
| def-weil-pbc-adic-coefficient-datum | Sheaf.Paper.AdicCoefficientDatum | AlgebraicGeometry.Scheme.AdicCoefficients.coefficientRing |
| def-weil-abstract-derived-category | Mathlib.Algebra.Homology.DerivedCategory.Basic | DerivedCategory |
| def-weil-pbc-bounded-constructible-complete | Sheaf.Paper.BoundedConstructibleComplete | AlgebraicGeometry.Scheme.IsPbcBoundedConstructibleComplete; AlgebraicGeometry.Scheme.pbcBoundedConstructibleComplete |
| def-constructible-stratification | Sheaf.AlgebraicGeometry.LocallyClosedStratification | AlgebraicGeometry.Scheme.LocallyClosedStratification |
| def-weil-derived-complete-integral-detailed | Sheaf.Paper.DerivedCompleteIntegralDetailed | WeilConjectures.boundedConstructibleDerivedCompleteIntegral |
| def-sbc-standard-tstructure-derived-category | Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean | DerivedCategory.TStructure.t |
| def-weil-l-adic-coefficient-extension | Sheaf.NumberTheory.Padics.CoefficientExtensionFinite | Padic.finite_coefficientExtensionRing |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian | AlgebraicGeometry.IsLocallyNoetherian |
| def-weil-pbc-quasi-compact-scheme | Mathlib.Topology.Defs.Filter | CompactSpace |
| def-kun-topological-krull-dimension | Mathlib.Topology.KrullDimension | topologicalKrullDim |
| def-weil-sheaf-of-modules-category | Sheaf.CategoryTheory.RingedSiteModules | CategoryTheory.ringedSiteModules |
| def-weil-pbc-proetale-site | Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory | AlgebraicGeometry.Scheme.proEtaleDerivedCategory |
| def-pc-perfect-ring-complex | Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral | DerivedCategory.IsPerfectRingComplex |
| def-weil-pbc-projective-module | Mathlib.Algebra.Module.Projective | Module.Projective |
| def-sc-finitely-presented-module | Mathlib/Algebra/Module/FinitePresentation.lean | Module.FinitePresentation |
| def-weil-derived-tensor | Sheaf.Algebra.Homology.DerivedTensor | AlgebraicGeometry.Scheme.derivedTensor |
| def-pur-sheaf-tensor-product | Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses | SheafOfModules.siteSheafTensorRight |
| def-weil-pbc-bounded-derived-subcategories | Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean | DerivedCategory.Plus |

Additional exact interfaces used are completedKoszulConstant and completedKoszulConstant_additive
(Sheaf.Paper.IntrinsicCompletionCompleted), pbcCompletedComparison, adicTowerPullback,
proEtaleModuleInverseImage, residueLisseSliceAbSheafify, residueLisseSliceAbLocallyBijective,
residueLisseSliceHasDerivedCategory, and ringedSiteDerivedRestrictionOfUniverses.
The recorded proof-dependency modules are imported as ordinary imports, except
ResidueLissePerfectLift which also supplies the slice instances used by the statement,
and the unused ComparisonPullbackCoherence import omitted in the import repair below.

Server source check found no published BoundedConstructibleComplete module. A read-only
inspection of all delivery refs found Q01 and Q06 versions. The Q01 sources are reused
verbatim in this delivery, retaining their canonical reduction and etale-origin API.

## Continuation checks

Reopened the full three modules and the current DAG statements. The server source query
again reports `Module source unavailable: Sheaf.Paper.BoundedConstructibleComplete`.
The copies of all three existing nodes differ from the shared DAG only in `lean`.
All delivered Lean lines have at most 100 characters. Re-read the exact dependency
signatures, including the general perfect-ring-complex predicate, the finite locally
closed stratification, the detailed integral predicate, and the independent-universe
slice restriction. No mathematical statement correction was needed.

Downloaded and read the cited arXiv v2 paper directly. Proposition 6.6.11 defines the
local model as the completed realization of a perfect coefficient complex; Definition
6.8.10 uses finitely presented integral coefficient modules; Proposition 6.8.11(3)
gives precisely boundedness plus constructibility of every cohomology sheaf.

Repeated searches with msearch.py: LeanFinder query “Derived complete integral
constructible complexes are stratified locally perfect over the ring of integers of
a finite padic extension” returned eight generic p-adic completion/valuation-ring
results (BDeRhamPlus, BDeRham and related declarations), with no characterization.
Loogle query `"Constructible", "perfect"` returned no hits. Mathlib grep query
`stratified.*perfect|constructible.*complete|adic.*constructible` returned no hits.
Direct rg for `integralStratified|IsIntegralStratified|integralConstantModule` in
WeilConjectures and the published Sheaf sources found no existing declarations;
the blueprint-id search in WeilConjectures likewise found none.
`blueprint_refs.py search 'stratified perfect'` found no duplicate blueprint node.

The continuation found three coefficient-action helpers missing from the prerequisite
record’s declaration inventory. Added `pbcCompletedScalars_exists`, `pbcCompletedScalars`
and `pbcCompletedLinear` to that record; the Lean definitions were already present.

## Import repair

The first full compile exposed a duplicate notation declaration between the newer
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` and
its older `UpperLowerStar.Defs` counterpart. The new version entered through the
proof-only `ComparisonPullbackCoherence` import; the published finite-level site
comparison and residue-lifting prerequisites still bring the older version through
their compiled imports. Removed the unused direct `ComparisonPullbackCoherence`
proof import. No declaration from it occurs in the statement or definitions; the
canonical inverse-image coefficient action remains the existing `adicTowerPullback`
and `proEtaleModuleInverseImage`. This is the narrower-import repair prescribed for
an environment-already-contains error. The comparison-pullback proof dependency
remains in the DAG and its proof explanation remains in the theorem docstring.

The first repaired dry run compiled every module successfully. Preflight requested
that the dependency report name both exact node ids; those ids are now explicit in
`## Dependency modules`. The independent second-reading section is intentionally
left for the second reader, as required by the delivery wrapper.


## Second reading by Q26

I independently opened the node, its dependency nodes and their exact signatures,
the three original sandbox modules, the current published dependency sources, and
the Bhatt--Scholze paper supplied in scratch/bhatt-scholze.txt. The mathematical
statement and its statement/proof dependencies are unchanged. The final Lean says
the node's statement. No statement_change or citer correction is required.

Objects, hypotheses and conclusion clauses, matched independently:

1. Prime ell: `(l : ℕ) [Fact l.Prime]`; exact, including ell = 2.
2. Finite E/Q_ell: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
   [FiniteDimensional ℚ_[l] E]`; exact recorded coefficient convention. The
   current prerequisite's `PbcIntegralRing l E` is ULift of the actual recorded
   valuation ring, and `pbcUniformizer l E` is its lifted recorded uniformizer.
   `pbcIntegralDatum l E` uses its principal ideal. This is the canonical ring
   size transport, with no extra field hypothesis or changed valuation.
3. Scheme T: `(T : Scheme.{u})`; exact. `[IsNoetherian T]` is precisely
   IsLocallyNoetherian plus CompactSpace, as read in Mathlib Noetherian.lean:280.
   The affine-cover criteria there identify it with the node's finite affine
   Noetherian cover. No separatedness, base field, or nonemptiness is assumed.
4. Finite dimension: `_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n`; exact.
   KrullDimension.lean uses strict chains of irreducible closed subsets and
   WithBot ℕ∞. This includes dimension zero and dimension bottom for empty T.
5. Invertibility in all local rings: `_hl : IsUnit (l : Γ(T, ⊤))` (and `_hinv`
   in the detailed comparison); equivalent, not stronger. Global units map to
   units in every stalk. Conversely, local inverses of a section with unit germs
   agree on overlaps and glue to a global inverse. This also holds on empty T.
6. Completed ring and ambient K: `pbcAdicCompletion T (pbcIntegralDatum l E)`
   is the actual inverse limit of positive finite quotient coefficient sheaves,
   not the discrete constant valuation ring; K ranges over all of
   `DerivedCategory (pbcModules T ...)`. I opened AdicCoefficientDatum,
   BoundedConstructibleTower, RingedSiteModules and DerivedCategory.Basic.
   No boundedness or completeness is assumed in the ambient object binder.
7. Condition (i): `PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K`.
   I read its three conjuncts in the newly landed BoundedConstructibleComplete:
   `PbcIsIntrinsicallyComplete`, `PbcHasUniformConstructibleReductions`, and
   `PbcHasCompatibleEtaleOrigins`. The first transports the named intrinsic
   completion unit along the canonical completed-ring comparison. The second
   identifies a uniformly constructible normalized tower with the actual derived
   reductions, including every semilinear transition. The third existentially
   retains `PbcWitnessedTower`, its bounded-below origins, comparison isomorphisms,
   theta, beta and compatibility, identified with the canonical reductions.
   WitnessCompatibility defines longer quotient normalizations by their iterated
   composites; identities and quotient cocycles are part of that encoding.
   Thus these are compatible origins, not independent origins at each level.
8. Condition (ii): `IsIntegralStratifiedPerfect`. Its quantifier order is one
   finite `LocallyClosedStratification`, then each stratum, then a covering sieve
   of its terminal pro-etale object, then each cover member and its perfect
   complex P. P may vary locally, exactly as the node permits. The recorded
   `DerivedCategory.IsPerfectRingComplex` means an isomorphism to a bounded
   complex with Module.Finite and Module.Projective in every degree. The model
   is `integralConstantDerived`: actual constant-module sheafification followed
   by completed scalar extension, transported by `pbcCompletedComparison`.
   `integralLocalDerived` applies the actual immersion inverse image and slice
   restriction to both objects, so both sides have the same coefficient sheaf.
   It does not substitute scalar extension along an arbitrary scheme map for
   the immersion's completed-ring identification. Exact match.
9. Condition (iii): `IsIntegralBoundedConstructibleCohomology`. The first conjunct
   is one finite integer interval, expressed by K.IsGE and K.IsLE. Every integer
   cohomology object is obtained by the actual homologyFunctor and tested by
   `IsIntegralStratifiedFinitelyPresented`. That predicate again has finite
   strata and covering sieves, but its model is an actual ModuleCat object N
   with Module.FinitePresentation, realized by ordinary `integralConstantModule`.
   Its stratification may depend on the degree. Exact match; no common
   degree-wise stratification or projectivity of N was added.
10. Equivalence: `integralStratifiedPerfectCharacterization` asserts (i iff ii)
    and (ii iff iii). This is all three equivalences with the same ambient K.
11. Detailed integral category: `integralStratifiedPerfectDetailed` now uses the
    dependency's current recorded `WeilConjectures.sfIntegralConstructible`,
    opened in SfIntegralConstructible. It says completeness plus all actual
    finite reductions constructible in one common interval. Its source is the
    same completed ring without an auxiliary finite-field datum. The comparison
    `integralCoefficientULift_exists` is uniquely determined on every residue
    representative of the lifted valuation ring. The completed comparison is
    uniquely fixed by EVERY positive quotient projection. Restriction along this
    ring isomorphism defines `integralDetailedTransport`. Therefore it compares
    exactly the same ring and canonical derived reduction functors, and covers
    the full generality of the current dependency. Exact match after repair.
12. Closure: `integralStratifiedPerfectClosure` quantifies over all integer shifts,
    all ambient distinguished triangles with the first two vertices in (i),
    both standard truncation functors at every integer, and every homology
    object embedded by singleFunctor in degree zero. Distinguished triangles
    give exactly closure under cones of all ambient maps. Exact match.

Source reading: Section 6.5 fixes a qcqs scheme and a Noetherian adically complete
coefficient ring and defines the completed ring as a limit. Proposition 6.6.11
assumes topological Noetherianity, gives a finite stratification, and explicitly
specifies locally constant perfect values as completed realization of a perfect
coefficient complex. Definition 6.8.10 uses finitely presented valuation-ring
modules. Proposition 6.8.11(3) gives boundedness plus constructibility of all
cohomology sheaves for finite E. The node retains stronger, explicitly stated
scheme hypotheses and its own compatible-origin/uniform-bound convention;
the proof docstrings must verify those extra clauses, not identify them by name.

Edge cases: the empty scheme permits zero strata, and no nonempty cover is
required on an empty stratum. Zero modules and zero complexes are included by
finite presentation and the bounded finite-projective predicate; boundedness of
zero can use any ordered interval. Finite coefficient indices are n+1, including
n=0 as exponent one. All cohomological degrees and shifts are integers. No
nonempty, characteristic-p, separated, or finite-field instance is present.
Schemes and finite extensions use the dependency's Type u convention; modules
and the canonically lifted valuation ring use u+1. The site's object universe
remains u+1 and its morphism universe u; ringedSiteDerivedRestrictionOfUniverses
is used without equating them. Every variable is explicitly bound.

Independent searches: msearch LeanFinder, “Complete constructible integral sheaf
complex has perfect constant local models on finitely many locally closed pieces”,
returned eight generic constructible-topological-set/manifold/integrability hits,
no match. Loogle `"IsPerfectRingComplex"` returned zero hits. msearch grep
`stratification.*complete|complete.*constructible|constructible.*perfect` returned
zero Mathlib hits. LeanSearch “Bounded complete adic complexes are constructible
if and only if their cohomology sheaves are locally finitely presented on finite
stratifications” was unavailable (Internal Server Error), recorded without a
negative verdict. Direct rg in Mathlib homology/algebraic geometry, upstream
WeilConjectures and published Sheaf sources used stratified/perfect, complete/
constructible and the blueprint id. No existing characterization or copies of
the three new local-model predicates exist. The search did find the now-landed
Q06 BoundedConstructibleComplete module and the updated detailed predicate;
these exact declarations are now reused.

Mismatches and repairs:

- The worker's dependency module competed with a subsequently landed definition.
  I used scompile --source to read the current server source, then opened its
  now-synced node record. Removed BOTH proposed dependency modules and their
  dependency-node copies from the delivery. No current dependency record is
  overwritten, and no extra prerequisite module remains in the final packet.
- Replaced IsPbcBoundedConstructibleComplete and the private pbcPadic coefficient
  datum by the landed PbcIsBoundedConstructibleComplete and pbcIntegralDatum.
  The coefficient convention now lifts the valuation ring, retaining E : Type u,
  rather than lifting E as a field and introducing another coefficient datum.
- The detailed dependency record now points to SfIntegralConstructible. Replaced
  the superseded detailed predicate and removed its auxiliary FiniteFieldDatum
  and l ≠ D.p binders. The canonical comparison is now normalized directly on
  the lifted ring's quotient representatives and all completed projections.
- Expanded the main theorem docstring to all seven proof steps and their named
  dependencies; the detailed comparison carries step 8 and closure carries step 9.
- Derive the additive instance from the named exactness theorem's existing
  finite-limit structure, avoiding a fragile opaque instance search. All theorem
  bodies remain sorry and every definition has real construction data.
- Updated lean.statement verbatim to the final signature. The mathematical node
  statement, proof, stmt_deps and proof_deps were not changed.

Final inventory: one new item module, one item node record, this report. No new
nodes and no dependency modules. The historical worker dependency proposal above
is superseded, including its claim that BoundedConstructibleComplete was absent.


The canonical source interfaces used in the final statement are
AlgebraicGeometry.Scheme.PbcIsBoundedConstructibleComplete from
Sheaf.Paper.BoundedConstructibleComplete and WeilConjectures.sfIntegralConstructible
from Sheaf.Paper.SfIntegralConstructible. The historical DerivedComplete module
is retained as a non-public proof-dependency import; the current detailed
statement uses IsSfDerivedComplete through its recorded parent predicate.
The earlier unused ComparisonPullbackCoherence proof-only import remains omitted
for the documented old/new UpperLowerStar notation collision. Its mathematical
proof dependency is unchanged and explicitly named in the proof docstring.


Second-reading validation: the repaired item passed scompile.py under both sandbox
and library module names with no errors or warnings. There are exactly seven
postponed theorem bodies and seven sorry terms. The node's lean.statement matches
the signature, its declaration inventory is complete, and every Lean line is at
most 100 characters. deliver2.py --no-push reported OK at dry-run commit 6375d76c77,
with only the item module, item node and report staged. No global build was run.
