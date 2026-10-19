## Worker report

The module `Sheaf.Paper.BoundedConstructibleTower` states the definition node
`def-weil-pbc-bounded-constructible-tower` as
`AlgebraicGeometry.Scheme.IsUniformlyBoundedConstructibleAdicTower`. It also supplies the
fully specified supporting data used by that definition: `AdicTower`,
`AdicTowerLocalModel`, coefficient-system comparisons, local derived reductions and
transitions, and the finite-lisse predicate. Every postponed mathematical fact is a named
 theorem with `sorry` and a source/proof docstring; all definition data is constructed.

The definition renders the statement clause by clause as follows.

* `X : Scheme.{u}` supplies the scheme and its small pro-etale site. The coefficient datum
  is `d : ProEtale.PbcAdicCoefficientDatum X A`, with `A : Type (u + 1)`, `[CommRing A]`,
  `d.noetherian`, `d.ideal`, `d.finitelyGenerated`, `d.quotientFinite`,
  `d.quotientPerfect`, and `d.quotientTorsion`.
* `pbcAdicRings X d` and `pbcAdicCompletion X d` are the finite quotient coefficient
  system and its actual inverse-limit sheaf. `pbcModules` and `DerivedCategory` give the
  derived module categories. `pbcDerivedExtend`, `pbcDerivedRestrict`, and the named
  adjunction/counit declarations use the recorded K-flat scalar-extension interfaces.
* `AdicTower.tower` is an object of the derived category of strict towers. `level n` is
  quotient-linear, `evaluation n` identifies its completed-coefficient restriction with
  tower evaluation, and `normalization b a hab` is the derived quotient-reduction
  isomorphism. `transition` gives the actual tower transition after restriction, and
  `cocycle` states direct reduction equals successive reduction for every
  `a ≤ b ≤ c`. Thus the quotient cocycle and the coefficient datum's canonical
  scalar-restriction comparisons are explicit.
* `IsUniformlyBoundedConstructibleAdicTower` begins with integers `d₀ ≤ d₁`, then one
  `LocallyClosedStratification X`. On each stratum it chooses a covering sieve in the
  stratum's pro-etale site and, on each covering object, an
  `AdicTowerLocalModel` for the composite cover map followed by the stratum immersion.
  The model has one common complex over the inverse image of the completed ring,
  `bounded : ∀ q, q < d₀ ∨ d₁ < q → IsZero (complex.X q)`, and
  `adicLisse` termwise finite-type adic-lisse modules.
* For every level `n` and degree `q`, `finiteLisse n q` applies the finite-lisse
  predicate to the derived homology of the local reduction. That predicate chooses its
  own covering sieve and finite `ModuleCat A` on each member, so these trivializing covers
  may vary with `(n,q)`. `identification n` is the required derived linear isomorphism,
  and `compatible` is the displayed normalization equation via the canonical semilinear
  transitions. The bounds, stratum and common complex are bound outside all level and
  degree quantifiers.

The auxiliary `pbcQuotientConstant` definition makes the discrete codomain topology an
explicit argument to `ContinuousMap.const`; this is definitionally the constant section
used by `pbcLevelConstantComparison_exists` and introduces no extra mathematical datum.

Dependencies used (all imported from their recorded declarations) are:

* `Sheaf.Paper.AdicCoefficientDatum`: `PbcAdicCoefficientDatum`, coefficient sheaves and
  systems, `pbcCompletedRing`, `pbcRingModules`, quotient projections, scalar extension,
  derived scalar extension, adjunctions, balancing normalizations and tower transitions.
* `Sheaf.Paper.AdicLisseModule`: `IsRelativelyAdicLisseModule`, adic-lisse constant rings,
  systems and completed rings.
* `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`: the fixed constant-module and local
  inverse-image constructions; `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `LocallyClosedStratification`.
* `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction` and
  `ProEtaleRingSheafChangeAdjunction`: canonical inverse-image coefficients, derived
  pullback and restriction/pullback comparison.
* `Sheaf.Algebra.Homology.KFlat`,
  `KFlatResolutionIndependentCoefficients`, and
  `DerivedChangeOfRingsIndependentCoefficients`: K-flat and independent-universe
  change-of-rings interfaces. Mathlib supplies `DerivedCategory`,
  `CochainComplex`, `DerivedCategory.homologyFunctor`, and exact-functor localization.

## Dependency modules

The delivery includes `Sheaf.Paper.AdicCoefficientDatum` for
`def-weil-pbc-adic-coefficient-datum`. Its recorded `CompletedAdicCoefficientDatum`
interface coupled the coefficient type universe to the scheme universe, while the
relative lisse-module interfaces used here require coefficients in `Type (u + 1)` on
the same small pro-etale site. The delivered module is the broader coefficient datum
interface with that universe, including real finite coefficient sheaves, the completed
limit, strict and derived tower constructions, scalar-extension interfaces and the
recorded quotient normalizations. This is the authorized §1(B) repair; the dependency's
natural-language statement and node fields other than `lean` are unchanged.

## Earlier second reading (a previous round; superseded)

I reread the complete definition against the blueprint order 1250 and the Stacks Tags
09AI and 09BT cited by the node. The outer bounds, one finite locally closed
stratification, stratum covers, common bounded complex, termwise adic-lisse condition,
per-level/per-degree finite-lisse condition, derived level identifications and the
normalization compatibility are all present with their original quantifier order. The
coefficient datum retains `n = 0`, all quotient cocycles and the distinct pro-etale
object/morphism universes. The explicit topology parameter in `pbcQuotientConstant` is
only an elaboration device for the prescribed discrete topology. No hypothesis or
conclusion was added or dropped.

Edge cases checked before writing: level `n = 0` is `A/I`; all positive quotients occur;
equal indices and every intermediate index are included in the cocycle; empty schemes,
empty stratifications, zero complexes and zero rings remain admissible; `I = 0` and the
unit ideal are not excluded; equal bounds and negative cochain degrees are allowed;
term modules need not be finite as integral sets; finite-lisse trivializing covers need
not be uniform; and the pro-etale object/morphism universes remain distinct.

Searches for an existing notion were made with `msearch.py` LeanFinder (uniformly bounded
constructible adic tower; only unrelated local-cohomology and completion hits), Loogle
(`SheafOfModules, DerivedCategory`; no result), Mathlib grep (`adic.*tower`,
`boundedConstructible`, `lisse`; no match), and `rg` over upstream `WeilConjectures` and
project `lean/Sheaf` (`AdicTower`, `UniformlyBoundedConstructible`, `adicTower`; no exact
declaration). The dependency node and recorded declarations were read in full. No
`STATEMENT-DISPUTED` flag or statement correction is needed.

The required compilation command passed on 2026-10-16:
`scompile.py Q03 def-weil-pbc-bounded-constructible-tower` with both
`AdicCoefficientDatum.lean` and `BoundedConstructibleTower.lean` (50.6s and 6.3s,
respectively, within the 60s limit). The final dry run is required below.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the complete Lean module independently. The coefficient
datum introduces `X : Scheme.{u}`, `A : Type (u + 1)`, the commutative-ring structure,
Noetherianity, finitely generated ideal, finite/perfect quotients and torsion quotient;
these render as `d : ProEtale.PbcAdicCoefficientDatum X A` and its named fields. The
finite quotient sheaves and completed inverse-limit sheaf render as `pbcAdicRings X d`
and `pbcAdicCompletion X d`, with the stated quotient projections and cocycle.
`AdicTower` then supplies the derived tower object, every quotient-linear level, derived
evaluation isomorphisms, all comparable-pair normalization isomorphisms, transition
compatibility, and the direct-versus-successive reduction cocycle. This is the explicit
Lean elaboration of the node's displayed consecutive normalizations; the all-pair form
is needed to state the cocycle and includes equal indices.

The local-model clauses match item by item. `IsUniformlyBoundedConstructibleAdicTower`
binds `d₀ ≤ d₁`, one `LocallyClosedStratification X`, and for every finite stratum index
a covering sieve in that stratum's pro-etale site. Each covering object receives one
`AdicTowerLocalModel` for the composite cover map and stratum immersion. Its `complex`
is over the inverse-image completed coefficient sheaf; `bounded` gives termwise zero
outside `[d₀,d₁]`; `adicLisse` gives the completed finite-type adic-lisse condition;
`finiteLisse n q` gives a possibly `(n,q)`-dependent trivializing sieve and finite
`ModuleCat` value for every derived reduction homology sheaf; `identification n` gives
the required quotient-linear derived isomorphism; and `compatible` is the normalization
equation. The bounds, stratum, covering object, and common complex occur outside the
level and degree quantifiers, preserving the node's order.

Verdict: the Lean definition says exactly the node's definition, including the node's
explicit quotient-linear coefficient actions. It adds no Noetherian-scheme, flatness,
finite-etale, dimension, characteristic, or universe-equality hypothesis. The relative
inverse-image coefficient maps are the canonical recorded operations, so no arbitrary
transport or chosen equivalence is introduced. All supporting declarations have source
and `(blueprint: def-weil-pbc-bounded-constructible-tower)` docstrings; postponed facts
are named `sorry` theorems and definition data is concrete.

Edge cases checked: `n = 0` is the quotient `A/I`; equal and nonconsecutive indices are
covered by the all-pair normalization and cocycle; `d₀ = d₁`, negative degrees, zero
complexes, zero rings, `I = 0`, and the unit ideal remain admissible; an empty scheme may
use an empty stratification; finite-lisse covers may vary with `(n,q)`; and the site
object universe remains distinct from its morphism/coefficient universes. These are the
same cases covered by the node and its coefficient datum.

My fresh `msearch.py` LeanFinder query was 'A compatible inverse sequence in the derived
category of quotient module sheaves locally realized by one bounded complex'. Its eight
hits concern general complex factorizations and bounded derived representatives, not
this tower definition. Loogle query `"AdicTower"` returned zero hits. Independent `rg`
searches used `constructible.*tower`, `tower.*constructible`, `normalized.*system`, and
`IsRelativelyFiniteLisseModule` over Mathlib, upstream WeilConjectures and project Lean.
The upstream trace-formula adic API uses specialized coefficients and homotopy-limit
towers without this common local model. Project `NormalizedDVRTower` is also specialized
to DVR coefficients and has no bounded constructible local-model predicate. Neither
replaces this general definition. The earlier worker's LeanSearch failure remains
recorded in the node; I do not count it as a fresh search. I also read the dependency
declarations, including the delivered commutative-coefficient
`PbcAdicCoefficientDatum` interface and `IsRelativelyAdicLisseModule`; both
match the dependency nodes they serve.

The tower statement needs no correction. I found one H4/H13 mismatch in the dependency
repair: its justification named an older recorded interface, but the current server
record is `ProEtaleAdicCoefficientDatum` in `AdicCoefficientDatumCompleted`, already at
the required universe. I imported that owning module, replaced the duplicate coefficient
structure with the transparent `PbcAdicCoefficientDatum` alias, and replaced duplicate
perfectness data with the existing `adicQuotientPerfect` predicate at positive index.
The `lean.statement` and `lean.note` now record those exact facts. This retains every
coefficient hypothesis and uses the canonical datum already published. The supporting
module still supplies the actual CommRingCat continuous-function quotient sheaves and
limit and their universal scalar-extension/tower APIs, while publicly reexporting the
existing constant-diagram/RingCat presentation. The older dependency justification in
the worker report is superseded by this second-reading correction.

The local checkout does not contain the literature source paths. I read the blueprint
source at its recorded path on the server over read-only SSH; its displayed uniform
local-model formula, single termwise window and final Stacks interpretation match the
expanded DAG statement. I obtained the Stacks
`proetale.tex` source from the official stacks-project repository and read
`section-constructible`, `section-adic`, and `definition-adic` (09AI, 09BS, 09BT). They
assume a Noetherian coefficient ring, an ideal, and an arbitrary scheme; they do not
assert this blueprint's uniform tower data. The finite quotient coefficients are
Noetherian, and finite underlying module values coincide with finite type over these
finite rings. The supplied DAG statement and its recorded source text specify the
additional common complex and normalization clauses reviewed above.

The pre-repair two-file scompile run passed cleanly (46.1s and 5.9s); the alias repair
is recompiled below before delivery. No new node or source statement correction is needed.

Final second-reader validation: the fresh two-module `deliver2.py --no-push` run exited
0 and printed `OK (dry run): commit 210b10c0bb passes the preflight and compiles; nothing
pushed`. This validates the coefficient aliases as well as the unchanged tower module.
The wrapper retained newer maintainer review metadata on the dependency node rather than
delivering stale sandbox metadata. The signature record is verbatim equal to the alias
signature in its file.

## Return repair: duplicate derived evaluation

The return for immutable head `44159fea025b` names the collision
`AlgebraicGeometry.ProEtale.pbcDerivedEvaluation`. I read both definitions in full,
including the current server source through `scompile.py --source`.
`Sheaf.Paper.PbcDerivedProductRepresentation` owns the full evaluated-diagram functor
for `Scheme.AdicCoefficientDatum A` with `A : Type u` and `T : Scheme.{u}`. The delivered
helper was the single-level exact evaluation with `A : Type (u + 1)` and the actual
commutative-function completed ring. Substituting the first interface directly would
change the coefficient universe and ring presentation of the node.

I removed the delivered helper entirely, and removed its name from the dependency
node's `lean.declarations`. Both comparison declarations now use the already imported
Mathlib `CategoryTheory.Functor.mapDerivedCategory` applied directly to
`(evaluation ℕᵒᵖ (pbcModules T d)).obj (op n)`. This is the exact body of the removed
transparent definition. The existing `pbcDerivedEvaluation` remains owned solely by
`PbcDerivedProductRepresentation`; no renamed evaluation definition or theorem is added.
The implementation reuses Mathlib's evaluation, derived extension and
`mapDerivedCategoryFactors`, including the same representative comparison in the
uniqueness theorem. Its type and comparison equation are definitionally unchanged.
The bounded-constructible tower module and all of its mathematical clauses are unchanged.

Search in this repair: `rg -n pbcDerivedEvaluation` across the project Lean library,
upstream source and delivery located the two declarations and all consumers. The fresh
`msearch.py` Loogle query `CategoryTheory.Functor.mapDerivedCategory` returned 12 hits,
including the exact functor in `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
I read its signature, docstring and `mapDerivedCategoryFactors` from pinned Mathlib.
The ordinary evaluation remains exact by the existing functor-category instances, and
Mathlib's derived functor applies without a new coefficient or universe hypothesis.
The main signature and coefficient alias signature are unchanged; the records use the
UTC date from `date -u +%F` (2026-10-15). This repair introduces no new node, source
statement change, postponed theorem, or proof.

Fresh repair validation: the prescribed two-file `scompile.py` command exited 0.
The current server compiled `AdicCoefficientDatum.lean` in 46.6 seconds and
`BoundedConstructibleTower.lean` in 6.0 seconds, with no errors or warnings. The wrapper's
local overlay first reported missing declarations in a prerequisite's mirrored source;
its automatic confirmation compiled that prerequisite and both delivered files cleanly
against the current server library. The per-file 60-second limit was unchanged.
The exact output is in `scratchpad/return-collision-compile.log`.

The additional collision regression check also exited 0: a scratch module imports
`Sheaf.Paper.BoundedConstructibleTower` and
`Sheaf.Paper.PbcDerivedProductRepresentation` together. The server compiled both
owning coefficient interfaces, the existing product-representation module, both
delivered modules and this combined-import module cleanly. The combined import took
1.4 seconds and produced no duplicate-name error. The scratch probe is not delivered;
its complete output is `scratchpad/return-collision-coexistence.log`.

## Second reading by Q03

This is the current second reading. The earlier second-reading and dependency-repair
sections describe superseded sandbox versions. I opened the current node, its dependency
records and declarations, both sandbox modules, the saved blueprint source at order 1250,
and Stacks `proetale.tex`, `section-constructible` (09AI) and `definition-adic` (09BT,
in section 09BS). The source assumes an arbitrary scheme and a Noetherian coefficient
ring with an ideal; the uniform tower model is the blueprint's additional definition.
No source statement correction or new node is needed.

The object/hypothesis/clause checklist, in the source's order, is:

1. Scheme T and its small pro-etale site: `X : Scheme.{u}` and `ProEt.topology X`.
   The site has object universe u+1 and morphism universe u. Verdict: exact; no
   Noetherian, quasi-compact, separated, finite-dimensional or characteristic condition
   on X is added.
2. Commutative Noetherian A, finitely generated I, torsion A/I, finite and perfect
   positive quotients: `A : Type (u + 1)`, `[CommRing A]`, and
   `d : AdicCoefficientDatum A`. I read `AdicCoefficientDatum` in the landed
   `CompletedAdicCoefficientDatum` and its parent `CompleteCoefficientDatum`.
   Its fields are exactly `ideal`, `noetherian`, `finitelyGenerated`,
   `quotientTorsion`, `quotientPerfect`, `quotientFinite`. The datum structure itself
   has no scheme parameter, so instantiating its ring universe at u+1 adds no equality
   between the scheme and coefficient universes. Verdict: exact.
3. R_n and the completed coefficient sheaf: `pbcAdicRings` transparently uses the
   landed `AdicCoefficients.ringSystem X d.ideal d.quotientFinite`;
   `pbcAdicCompletion` uses its actual inverse limit `AdicCoefficients.completedRing`.
   I read `functionPresheaf`, `coefficientRing`, `coefficientMap`, `ringSystem` and
   `completedRing` in the current owning module, also obtained via
   `scompile.py --source Sheaf.Paper.AdicCoefficientDatum`. They sheafify continuous
   functions on connected components with the discrete finite quotient topology;
   maps are postcomposition by the quotient maps. Verdict: exact, not a constant
   sheaf substituted for the completion.
4. Module categories, complexes, cohomology and derived tensors: `pbcModules` is the
   recorded `ringedSiteModules`/Mathlib `SheafOfModules`; `CochainComplex ... ℤ`,
   `DerivedCategory` and `DerivedCategory.homologyFunctor` are Mathlib's recorded
   notions. `pbcExtend`, `pbcDerivedExtend` and their universal counit reuse
   `completedAdicChange`/`completedAdicDerivedChange` and the normalized witness
   `completedAdicChangeData`. I read their signatures and the independent-coefficient
   change-of-rings theorem, including its fixed objects/maps, universal property and
   K-flat computation. The explicit independent-coefficient K-flat import follows
   the current dependency record. Verdict: the prescribed sheafified scalar extension,
   with no flatness assumption and no arbitrary comparison.
5. Derived strict tower and quotient-linear levels: `AdicTower.tower` is in the
   derived category of `ℕᵒᵖ ⥤ pbcModules X (pbcAdicCompletion X d)`;
   `level n` lives over R_n, and `evaluation n` identifies its scalar restriction
   with actual derived evaluation of that strict tower. Verdict: exact.
6. Normalizations, actual transitions and quotient cocycle:
   `AdicTower.normalization b a hab`, `transition`, and `cocycle c b a hab hbc`.
   These retain all quotient actions. `adicTowerSemilinearTransition` is precisely
   the scalar-extension unit followed by restricted normalization. The ordinary unit
   is fixed by 1 tensor x, and the derived unit is fixed on K-flat representatives.
   Thus the semilinear cocycle is the adjoint of the tensor-normalization cocycle.
   All comparable pairs render the source's consecutive maps and their composites;
   equal-index cocycles and invertibility enforce the identity normalization.
   Verdict: exact, including direct versus successive reduction.
7. One window and one finite stratification, then stratum covers:
   `IsUniformlyBoundedConstructibleAdicTower` quantifies `d₀ d₁ : ℤ`, `d₀ ≤ d₁`,
   one `LocallyClosedStratification X`, then a covering sieve on each stratum.
   I read this dependency's scheme domains, immersion morphisms and range equalities,
   together with its finite topological partition. The composite
   `U.hom ≫ S.immersion α` is the required restriction map. Verdict: exact order;
   no constructibility or closure-incidence condition is added to the stratification.
8. One complex per covering object, independent of level: `AdicTowerLocalModel.complex`
   is over the inverse image of the completed coefficient sheaf; `bounded` is
   termwise `IsZero` outside the same [d₀,d₁], including negative degrees.
   `adicLisse` uses the recorded `IsRelativelyAdicLisseModule` after restriction along
   the canonical `pbcCompletedComparison`. I read that relative predicate's complete
   module, finite-type N/IN, local completed constant model and scalar-linearity test.
   It does not commute inverse image with an infinite limit. Verdict: exact.
9. Every finite reduction and every degree has finite-lisse cohomology:
   `finiteLisse n q` applies `IsRelativelyFiniteLisseModule` to the homology of
   `adicTowerLocalReduction`. Its own covering sieve and finite `ModuleCat` value
   occur inside n and q; the isomorphism is linear over the actual inverse-image
   coefficient ring, using the fixed constant-section comparison. The constant
   modules use the imported dependency's `adicLisseConstantModules` and canonical
   `proEtaleModuleInverseImage`, whose signatures I read. Verdict: exact; covers may
   vary with n,q, and integral terms are not required to be finite sets.
10. Linear level isomorphisms and normalization compatibility:
    `identification n` is in the derived category over the restricted R_n.
    `compatible b a hab` says the restricted semilinear transition followed by
    restricted e_a equals e_b followed by the common model's transition.
    `adicTowerLocalTransition` is the adjunct of the balancing map determined by the
    normalized scalar adjunction, not a chosen arrow. The scalar-extension Hom
    bijection converts this equation to e_a rho = sigma (e_b tensor R_a).
    `adicTowerRestrictedTransition` uses the recorded canonical restriction/pullback
    comparison, whose full signature and identity-on-inverse-image characterization
    I read. Verdict: exact, including restrictions along immersions and covers.

Edge cases: the positive exponent is n+1, so n=0 is A/I, not I^0. Equal and
nonconsecutive levels and every intermediate index occur in the cocycle. Zero rings,
zero complexes, I=0 and I=1 are not excluded. Empty schemes can have zero strata;
there is no nonempty-cover or nonempty-index requirement. Equal bounds and negative
cochain degrees are included. No characteristic restriction is introduced. Coefficients
and module values stay in u+1 while site morphisms stay in u; smaller coefficients can
be lifted to the site universe. The module introduces no additional universe equality.

Fresh searches: `msearch.py` LeanFinder with "An inverse system in the derived category
of coefficient sheaves locally represented by one bounded complex with lisse reductions"
returned eight unrelated local-cohomology/condensed/sheaf-cohomology hits. Loogle
`"AdicTower"` returned zero hits. Independent `rg` searches over pinned Mathlib,
upstream WeilConjectures and project Sheaf used `constructible.{0,50}tower`,
`tower.{0,50}constructible`, `normalized.{0,30}(system|tower)` and
`IsRelativelyFiniteLisseModule`. I opened upstream TraceFormula/Adic and project
NormalizedDVRTower: the former lacks this uniform bounded common local model and the
latter is a specialized DVR notion explicitly without constructibility/local models.
Neither is a match. The earlier LeanSearch service failure remains documented and is
not counted as a fresh successful query.

Mismatch found and repaired (H4/H13): the sandbox's dependency module would replace the
current landed `Sheaf.Paper.AdicCoefficientDatum` with a stale, 839-line implementation,
duplicating coefficient, scalar-extension and tower constructions. The current owning
module (Q32) publicly imports `CompletedAdicCoefficientDatum` and supplies the exact
finite-function commutative ring presentation at the needed coefficient universe.
I removed the stale dependency module and its stale node copy from the delivery, and
retargeted the tower's transparent wrappers to these landed definitions. The existing
`AdicCoefficientDatum` supplies the coefficient hypotheses, so the old duplicate datum
alias is unnecessary. The quotient maps now use the existing diagram's arrows, and
projection/cocycle helper statements express its limit/functor laws. Their named sorry
proofs have source and complete proof docstrings. The independent K-flat predicate is
imported explicitly. No mathematical clause of the tower definition changed.

All retained supporting declarations have source/blueprint docstrings, real definition
data, and named sorry theorems for postponed facts. Tensor functors are fixed on objects
and maps, derived pairs by their universal property, and the new comparison/adjunction
choices by uniqueness with section or K-flat normalization. No bare Nonempty choice of
a canonical map is used. No new definition node, dependency module, statement correction
or target change is delivered. The main `lean.statement` is verbatim the file signature.

Current validation: the prescribed `deliver2.py Q03
 def-weil-pbc-bounded-constructible-tower --no-push` finished with exit 0 and
`OK (dry run): commit bf1592e925 passes the preflight and compiles; nothing pushed`.
The final packet has only the main module, its node record and this report; no stale
coefficient dependency record or replacement module is staged. The standalone preceding
`scompile.py` check also passed its current-server confirmation without warnings.
