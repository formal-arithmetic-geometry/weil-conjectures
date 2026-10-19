## Worker report

Repair of return L on immutable head 45b4f1be429b. The saved packet's initial
dry run passed at 0ff836fcfc, compiling both delivered modules. I retained its
explicit-binder repair and checked each of the five reported overlaps against
the existing declaration and its surrounding variable declarations.

All five signatures explicitly bind `(l : ℕ) [Fact l.Prime] (E : Type v)
[Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
(X : Scheme.{u})`. The existing declarations instead have section variables
`E : Type u` and `X : Scheme.{u}`. They use `DerivedNakayama.integerRing l E`
and its quotient objects, constructed directly on E via
`continuousCoefficientRingSheaf`. The saved module uses
`SmallAdicCompletion.Coefficients.integerRing.{u} l E`, constructed on
`Shrink.{0} E` via `continuousMapRingObj`, independently of u and v.
Thus identical-looking local names previously hid different coefficient objects
and different universe binders. The return explicitly permits retaining such
statements when those binders are made explicit; that is the retained repair.

- `Coefficients.pullback_regular` explicitly binds both universes through E and X;
  both sides use the small coefficient integerRing. The existing
  `DerivedNakayama.pullback_regular` uses its unsized integerRing on E.
- `augmentation_comm` explicitly binds P over
  `SmallAdicCompletion.Modules l E X`; its unitProduct and roos refer to the
  small-coefficient tower. The existing AdicCompletion theorem binds P over
  `AdicCompletion.Modules l E X`, the original coefficient tower.
- `derivedReduction_isNormalized` explicitly binds K over the small module
  category; its normalization and reductions use that same category. The
  existing AdicCompletion theorem uses the original module category.
- `quotient_transition` explicitly binds E and X, so quotient and transition
  resolve to the small coefficient quotient objects in this namespace, whereas
  the existing theorem concerns the original coefficient quotient objects.
- `roosD_sq` explicitly binds P over `SmallAdicCompletion.Modules l E X`;
  roosD is the differential on the small-coefficient product. The existing
  theorem takes a complex over `AdicCompletion.Modules l E X` instead.

No theorem proof was filled, no upstream module or record was changed, and no
new universe equality was imposed. The five saved explicit signatures compile
together with their existing counterparts through the public DerivedCompletion
import. The initial dry run passed the current server preflight as well.

Repair of returned immutable head 321b8f029332, points R1 and R2. The retained
packet was inspected first. Its required initial dry run passed at d555b822a8;
nothing was pushed because that packet still had the two returned defects.
The repair retains the substantive F1--F5 corrections accepted by that review.

`Sheaf.Paper.IntegralHeartLocalModel` states clauses (1)--(3) over
`constantModelBoundedConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X`.
The ring abbreviation now belongs to the new definition node. Its body is identical
to `integralHeartCoefficientRingObj` in the downstream integral-heart sibling.
It uses `Module.Finite.small`, `Shrink.algEquiv`, the spectral norm and the existing
`Profinite.continuousMapRingObj`; there is no changed coefficient convention.

R1: removed the sandbox replacement of `sk-def-pe-derived-completion.json`.
The delivery neither edits Q16's node nor its `DerivedCompletion.lean`; its recorded
46 declarations and all consumers remain intact. The small-presentation interface
is owned by the new node `def-sfb-small-coefficient-derived-completion`, which the
item cites. Its module publicly imports `Sheaf.SixFunctors.ProEtale.DerivedCompletion`
and preserves that API. No replacement record is delivered.

R2: removed the public import of `Sheaf.Paper.IntegralConstantModelHeart` from the
small-coefficient definition module. Defined `SmallAdicCompletion.Coefficients.integerRing`
there using the identical body of the sibling abbreviation, as the return requests.
The item uses this definition and directly imports
`Sheaf.Paper.CondensedConstantConstructibility`. Neither delivered module imports
the downstream theorem. A separate temporary consumer imports the item and sibling
together and checks equality of their coefficient rings with `rfl`; this check is
removed before delivery. The sibling can consequently import this item without
an inversion through its own theorem module.

Hypothesis-by-hypothesis correspondence:

- `(ℓ : ℕ) [Fact ℓ.Prime]` fixes the prime.
- `(E : Type v) [Field E] [Algebra (Padic ℓ) E]
  [FiniteDimensional (Padic ℓ) E]` is an arbitrary finite extension. Universe v
  is independent of the scheme/base-field universe u. Canonical smallness is
  constructed by finite-dimensionality, not assumed.
- `(k₀ : Type u) [Field k₀] (p : ℕ) [CharP k₀ p] (_hp : 0 < p)` supplies
  the field of positive characteristic. `_hℓ : p ≠ ℓ` is its prime inequality.
- `(X : Scheme.{u}) [X.Over (Spec (.of k₀))]` is the scheme over k₀.
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` are instances on its
  actual structure map, and together express separated finite type.
- `integralHeartScalars ℓ E` is the universe lift of the valuation ring of the
  canonical small field. Its uniformizer and ideals come from the existing
  finite coefficient-extension construction.
- `K : integralHeartDerivedCategory ℓ E X` is in the ordinary unbounded derived
  category of internal modules over the pulled-back continuous condensed ring.
  `hK` is precisely constant-model bounded constructibility over that ring.

Clause-by-clause correspondence:

1. `integralHeartFiniteFreeLocalModel` quantifies over one
   `Scheme.FiniteLocallyClosedStratification X`. Its fields give finiteness,
   locally closed strata, disjointness, covering, scheme domains and immersion
   realizations; its displayed conjunct requires every stratum to be constructible.
   Each stratum receives one pro-etale `Scheme.Cover`. On each chart there is a
   scalar `CochainComplex P`, integers b and c, `P.IsStrictlyGE b`,
   `P.IsStrictlyLE c`, and both `Module.Free` and `Module.Finite` for every term.
   Choosing finite bases writes its scalar-linear differentials as matrices over
   the same DVR. The isomorphism restricts K along the actual composite
   `𝒰.f i ≫ s.immersion a`; its other side is Q of the termwise realization of P.
   Realization is constructed: constant scalar presheaves, the map sending a to
   its constant continuous function, constant sheafification, the existing change
   of rings followed by sheafification, the inverse section-module equivalence,
   and the published inverse image from the point. No realization functor or
   arbitrary comparison is assumed.
2. For every q the theorem separately asserts
   `SmallAdicCompletion.IsDerivedComplete ℓ E X (integralHeartCohomology ℓ E X K q)`
   and constant-model bounded constructibility of that same object.
   `integralHeartCohomology` is H^q(K) placed in degree zero by `singleFunctor`.
   The local cohomology clause remains INSIDE the same existential s, cover,
   chart and P of (1): every q has `Module.Finite ... (P.homology q)` and an
   isomorphism of the restriction of H^q(K) with the realization of that exact
   `P.homology q`. There is no new stratification, cover, complex or module.
3. For every q both standard good truncations
   `(DerivedCategory.TStructure.t.truncLE q).obj K` and
   `(DerivedCategory.TStructure.t.truncGE q).obj K` satisfy the identical
   constant-model bounded-constructible predicate as hK.

All helpers have source/blueprint docstrings. Construction data are explicit.
Postponed construction laws are public named theorems with `sorry` and natural-language
proof plans, listed in the owning node's lean.declarations. No proof was filled.

Dependency declarations used (their signatures and docstrings were read):

- `Sheaf.Paper.CondensedConstantConstructibility`:
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`;
  `UpperLowerStar.Defs`: `CondensedRing.upperStar` and exactness.
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`:
  Q16's preserved `IsDerivedComplete`, augmented Roos reduction construction,
  derived reductions and normalized towers. The small-presentation module
  constructs its independent-universe version without altering that record.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public imports:
  valuation ring, uniformizer, ideals, finite quotient rings and transitions.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`:
  `Profinite.continuousMapRingObj`, continuous quotient maps and commutativity.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionRingSheaf`, `sectionModuleEquivalence`; its already landed owning
  node remains an added statement dependency.
- Mathlib: `DerivedCategory.homologyFunctor`, `singleFunctor`, standard
  `truncLE`/`truncGE`, `CochainComplex`, `HomologicalComplex.homology`,
  `Module.Free`, `Module.Finite`, `PresheafOfModules.sheafification`.
  The sheaf-tensor interface supplies `SheafOfModules.changeOfRingsOfUniverses`.
  The cohomology node's general Mathlib match is used, not its unrelated
  sfModelCohomology specialization. The composite truncation node supplies the
  standard good truncations; its homotopy-colimit declaration is not used.
  Non-public imports AdicStratifiedPerfect, CompletedConstantSheafReduction,
  ConstantModuleSectionProperties, CartesianCoefficients and
  TruncationsAndHomotopyColimits remain the stated proof-dependency plan.

Edge cases: empty X permits zero strata; the covering conditions handle empty
strata/charts. P and each finite free rank can be zero. All integers b,c,q are
allowed, including q outside the bounded support. H^q(P) can be torsion or zero:
only finite generation, not freeness, is required. There is no nonempty support,
Tor-amplitude, completeness or universe-equality hypothesis. The same chart and
complex witnesses give both P and H^q(P) comparisons. Positive reduction level
n+1 avoids a hidden level-zero convention; the completion allows unbounded K.

Searches retained from the earlier repair: leanfinder for integral constructible
finite free local models/cohomology/completeness/truncations gave eight generic
truncation hits; loogle for IsDerivedComplete, constantModelBoundedConstructible,
integralHeartLocalModel gave no hit; Mathlib grep for these in AlgebraicGeometry
gave no hit. Upstream and side-source rg found no existing item declaration.
The existing strictPerfectConstantPresheaf fixes equal site object/Hom universes;
the explicit local construction respects the actual Profinite universe split.

New-node searches (2026-10-18), made through msearch.py and recorded in
mathlib_searches exactly with their queries:

- leanfinder: `derived completion internal modules continuous condensed coefficients
  finite extension independent universe Shrink`: eight hits about CondensedMod,
  light/solid modules and finite/profinite free functors; no completion interface.
- loogle: `SmallAdicCompletion, IsDerivedComplete`: zero hits, unknown identifier
  SmallAdicCompletion.
- leansearch: `derived complete complex continuous condensed p adic coefficient ring
  small presentation`: eight ordinary IsAdicComplete/adic-topology hits; no
  derived internal-sheaf completion.
- Mathlib grep in CategoryTheory: `SmallAdicCompletion|small.*[Cc]oefficient.*[Cc]ompletion`:
  zero hits. rg in DAG, upstream WeilConjectures and side Sheaf for the small
  presentation/completion names found no matching node/interface (only unrelated
  CompletedPullbackAdjunction text). `blueprint_refs.py search 'small coefficient'`
  returned no blueprint node. The canonical continuous ring itself is reused.

No natural-language statement correction or STATEMENT-DISPUTED is needed.

## New nodes

`def-sfb-small-coefficient-derived-completion` owns
`Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion` and all its 55
recorded declarations. It defines the canonical small coefficient field,
continuous integral ring and positive quotient rings, the pulled-back module
category, actual quotient/transition/unit maps, tensor reductions, explicit
Roos differential and specified (unit,0) augmentation, derived completeness,
derived reduction functors and normalized towers. Source: main-20261015
sk-def-pe-derived-completion, applied to the small presentation required by the
integral-heart coefficient setting. The searches above find no usable interface
with independent coefficient and scheme universes. This node is a presentation
interface for the existing completion notion; it leaves Q16's general record
intact. The identical coefficient abbreviation is now housed here as expressly
requested in R2, not imported from the sibling theorem. Its module publicly
retains DerivedCompletion and the existing continuous-ring and Shrink APIs.
All construction-law theorems are attached to this definition node and listed.

## Second reading by NW

Author self-reading, with no additional agent because the dispatcher forbids one.
Opened the current item node and blueprint clauses, both repaired full modules,
the unchanged Q16 record and source, the sibling's coefficient abbreviation,
and the directly imported constant-model constructibility definitions.

R1 was a real ownership defect: public import of Q16's API did not excuse dropping
its declaration list from its node record. The replacement node file has been
removed from the delivery. The new definition node owns only the small-presentation
module and is added to the item. Q16's existing 46-declaration record is unchanged.

R2 was a real import inversion: the downstream theorem was imported to obtain a
plain abbreviation. That import is gone. I compared the new integerRing body
line by line with the sibling abbreviation: same Small proof, transported finite
dimension, spectral norm and continuousMapRingObj on the same valuation ring.
The direct CondensedConstantConstructibility import now provides the item predicate.
The temporary consumer checks both imports together and their ring equality by rfl.

F1 remains repaired: input, cohomology membership and both truncation conclusions
use the same bounded-constructible predicate on that exact ring. F2 remains
repaired: a separate derived-completeness conjunct uses the canonical K-flat
reduction tower and augmentation, rather than an unrelated isomorphism to a limit.
F3: E : Type v is still independent of Scheme.{u}. F4: every local cohomology model
is the homology of the same scalar P within the same strata and cover witnesses;
both restrictions use `𝒰.f i ≫ s.immersion a`. F5: the displayed hypotheses match
the field, characteristic, prime inequality, finite extension, and separated
finite-type setting. No new mathematical restriction accompanies R1 or R2.

The two delivered files compiled through scompile.py with no errors or warnings:
SmallCoefficientDerivedCompletion 50.7 s (sandbox pass 56.1 s),
IntegralHeartLocalModel 7.3 s, each within the unchanged 60-second limit.

The temporary joint-import consumer also compiled cleanly (3.6 s). Its ring-equality
example closed by `rfl`, and the check file was removed before packaging.

Repaired the dry-run metadata diagnostic: because this item is itself its blueprint
ancestor, preflight requires `blueprint.from.via = []` on the owned definition.
The node now carries that exact ancestry convention; no Lean or statement changed.
