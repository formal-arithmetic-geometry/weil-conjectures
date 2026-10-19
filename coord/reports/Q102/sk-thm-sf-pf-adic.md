## Worker report

`Sheaf.Paper.IntegralOpenImageProperFormulas` states the three assertions of
`sk-thm-sf-pf-adic`: `integralOpenDirectImage`, `integralProperBaseChange`, and
`integralProperProjection`, in `AlgebraicGeometry.ProEtale.CondensedRing`.
Each theorem has a whole-theorem `sorry` proof and the source proof in its docstring.
The source is the current main-20261015 blueprint unit `_section.md`; its statement,
standing setting and four DAG assembly steps were read again during this repair.

The mathematical node statement, proof and proof dependencies are unchanged.
The item's statement dependencies additionally name the three already-landed
owners of the canonical projection map, ambient exchange and chosen square:
`def-sfb-module-object-projection-map`, `def-weil-pbc-ambient-ringed-exchange`,
and `def-weil-pbc-cartesian-square`. Neither canonical map is constructed again.

Hypothesis and clause correspondence:

- `(ℓ : ℕ) [Fact ℓ.Prime]` fixes the prime; the embedded finite extension is
  `E : PadicAlgCl.FiniteIntermediateField ℓ`. The condensed coefficient
  `Profinite.padicIntegersRingObj ℓ E.val` is continuous functions into O_E,
  with the topology induced by the ell-adic absolute value, including ramification.
  `condensedRingObj ... T` is its canonical pullback to each scheme T.
- `(k : Type u) [Field k] [Fact (ringChar k).Prime]` supplies the field of positive
  characteristic; `[Fact (ringChar k ≠ ℓ)]` excludes ell. Each scheme has
  `.Over (Spec (.of k))` and its structure map has `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated`, exactly the separated finite-type setting.
  Every arrow has `.IsOver (Spec (.of k))`. No perfectness, algebraic closedness,
  dimension bound or further geometry hypothesis is imposed.
- In `integralOpenDirectImage`, `[IsOpenImmersion j] [QuasiCompact j]` is precisely
  a quasi-compact open immersion. `K : ConstantModelConstructibleFiniteTor ... U`
  is a Dctf input. The first conclusion,
  `constantModelBoundedConstructible ... X ((moduleObjectDerivedPushforward ... j).obj K.obj)`,
  is bounded constructibility of Rj_*K. The second is
  `DerivedCategory.finiteTorAmplitude _` of that same object. Together they say
  Rj_*K belongs to Dctf(X,O_E).
- In `integralProperBaseChange`, `[IsProper f]` is properness and
  `sq : ChosenCartesianSquare g' f' f g` is the cartesian square with its chosen
  identification with the fibre product. Its commutativity is `g' ≫ f = f' ≫ g`.
  The horizontal map g is arbitrary. The hypothesis
  `hK : localizingClosureProEtale ... X K` puts K in Loc(Dctf(X)). The first two
  conjuncts put Lg*Rf_*K and Rf'_*Lg'*K in Loc(Dctf(Y')). The last is exactly
  `IsIso ((condensedAmbientExchange (Profinite.padicIntegersRingObj ℓ E.val) sq).app K)`.
- In `integralProperProjection`, f is again proper. `hK` and `hL` put the inputs
  in Loc(Dctf(X)) and Loc(Dctf(Y)). The first conclusion puts Rf_*K tensor^L L
  in Loc(Dctf(Y)); the second puts Rf_*(K tensor^L Lf*L) there. The tensors are
  applications of the existing `derivedTensor ... Y` and `derivedTensor ... X`.
  The third conclusion is exactly
  `IsIso (moduleObjectProjectionMap (Profinite.padicIntegersRingObj ℓ E.val) f K L)`.
  This is the ordinary relative K-flat tensor; no completion or tensor over Z
  replaces it.
- Both proper conclusions include both endpoint memberships and ambient
  invertibility. Because Loc is a full subcategory, the ambient inverse is a
  morphism there, exactly expressing invertibility inside Loc as the node asks.

Dependency declarations read and used, with signatures and docstrings:

- `Sheaf.Paper.CondensedConstantConstructibility`: `HasFiniteConstantLocalModel`,
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`, and
  `ConstantModelConstructibleFiniteTor`. This is the recorded constant-scalar-model
  constructibility, not upstream constructibility with arbitrary local matrices.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`, publicly importing
  `Sheaf.Paper.LocalizingClosure`: `localizingClosureProEtale` is the intersection
  of all full replete triangulated subcategories containing precisely that Dctf
  predicate and closed under ambient small coproducts. No completeness condition
  is imposed. O_E is one of the recorded admissible coefficients.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the recorded `compactificationOverField` setting was read, including the current
  Over-object interface via `scompile.py --source` in the saved investigation.
  The item needs only the explicit setting binders, with no compactification input.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, and its commutative-ring instance give pulled-back coefficients.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `derivedUpperStarLowerStarAdjunction` derives the full underived upper/lower-star
  composites; `leftDerivedUpperStarComp` is the composition comparison in the
  exchange definition. The general `Functor.leftDerivedFunctor` and
  `rightDerivedFunctor` are used directly by the two named specializations in
  `Sheaf.Paper.CondensedModuleDerivedPushpull`, described below.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and its Tensor
  import: `derivedTensor`, `derivedHom`, and `Mod.derivedMonoidalCategory` supply
  the recorded relative K-flat convention. Writing the tensor functor explicitly
  rather than using the generic tensor notation changes no operation.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare` has
  its specified fibre-product isomorphism and both projection equations.
- `Sheaf.Paper.CondensedAmbientExchange`: `condensedAmbientPullbackComparison`
  is the inverse of `leftDerivedUpperStarComp Λ f' g`, commutativity, then
  `leftDerivedUpperStarComp Λ g' f`. `condensedAmbientExchange` is its mate under
  the specified derived adjunctions, exactly the canonical unit/square/counit arrow.
- `Sheaf.Paper.ModuleObjectProjectionMap`: `moduleObjectProjectionMap` is
  `rightAdjointProjectionMap` applied to the published `leftDerivedUpperStarTensor`,
  exactly the adjoint transpose of the K-flat tensor comparison followed by counit
  tensor identity.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicIntegersRingObj` supplies the condensed ring and instances.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` is the recorded
  definition. Properness is Mathlib's `IsProper`.

The item privately imports its landed proof inputs
`Sheaf.Paper.IntegralLocalizingProperBaseChange` and
`Sheaf.Paper.IntegralProperProjectionFormula`. Their declarations are
`integralLocalizing_properBaseChange` and `integralProperProjectionFormula`.
The qcqs-over-affine leaf is already imported through Mathlib.
`det-def-localizing-closure-ctf-equals-bc` and `det-thm-sf-pf-adic-open` have no
recorded module in the inspected base; their assembly steps remain explicit in
proof docstrings. No nonexistent module is imported and no proof is supplied here.

Edge cases checked: empty schemes and the empty open; zero objects; identity
proper maps and identity cartesian squares; every compatible chosen pullback
identification; g neither flat nor proper; ramified E; and unbounded objects in
Loc that need not be derived complete. The existing scheme universe u,
`ProEt.topology T` and `Ab.{u+1}` convention is retained. No site-universe equality
or independent test universe is added. The new derived-functor names work for every
commutative condensed ring and arbitrary morphisms, without extra hypotheses.

Searches retained from the saved packet and checked against the repair:

- `msearch.py ... leanfinder`: "Integral l-adic pro-etale open direct image
  preserves bounded constructible finite Tor complexes and proper base change
  and projection formula hold on their localizing closure". Eight hits on etale
  morphisms/sites; none states the three-clause pro-etale module-object theorem.
- `msearch.py ... loogle '\"projectionFormula\"'`: zero hits.
- `msearch.py ... grep` for
  `projectionFormula|projection_formula|hasProjectionFormula_of_derivedCompleteIntegral`:
  zero Mathlib hits.
- `rg` in the named project's `lean/Sheaf` and upstream `WeilConjectures` trees
  for the item id and canonical map names locates the landed map owners and
  separate detail theorems. Their definitions and docstrings were opened.
- The entire upstream small-etale theorem
  `AlgebraicGeometry.Etale.hasProjectionFormula_of_derivedCompleteIntegral` was
  read: it assumes bounded constructibility, finite Tor amplitude and derived
  completeness of both inputs in another coefficient category, so is not this unit.
- The prior packet's LeanSearch query "Proper base change and projection formula
  for integral adic module sheaves on the pro-etale topology" returned eight
  generic sheaf/pullback/properness hits and no exact combined statement.
- During this repair, `rg` for `moduleObjectDerivedPushforward`,
  `moduleObjectDerivedPullback`, and definitions named `derivedLowerStar` or
  `derivedUpperStar` in `lean/Sheaf`, the side pro-etale framework and upstream
  pro-etale source found no named specialization of these two composites.
  The existing general derived functors are used, not reconstructed.

No statement fault or STATEMENT-DISPUTED claim was found. There is no statement
correction and no new DAG node.

## Dependency modules

`sk-def-sfb-module-derived-pushpull`: its recorded general interface states the
correct mathematics, but repeated concrete specialization of its many monoidal
and K-flat structural arguments prevented the consumer's library-artifact compile
from finishing within 60 seconds. Both the preliminary compile and independent
server confirmation reproduced that failure. The authorized §1(B) repair is
`Sheaf.Paper.CondensedModuleDerivedPushpull`, naming
`moduleObjectDerivedPushforward` and `moduleObjectDerivedPullback` for arbitrary
commutative condensed coefficients and arbitrary scheme morphisms. Their bodies
are exactly `(lowerStar Λ f).rightDerivedFunctor` and
`(upperStar Λ f).leftDerivedFunctor`. Thus the composite is derived, not its
factors; all K-injective/K-flat choices are precisely the existing ones. These
are names for the existing specializations, with real data and no new theorem,
axiom, construction or choice. The original adjunction, bounded-below version,
resolution and factorization interfaces remain publicly imported and recorded.
Only this dependency node's `lean` field changes. Its statement, dependency edges,
proof and Mathlib record are untouched.

## Second reading by Q102

This is the author's self-check: the dispatcher forbids starting other agents;
the maintainer provides the independent review. Opened the item, its source unit,
all three signatures and the canonical map definitions again. The prime, embedded
finite extension, positive-characteristic base field, excluded characteristic,
separated finite-type schemes and k-morphisms match the standing setting exactly.
The open assertion retains precisely a quasi-compact open immersion and Dctf input,
with both bounded constructibility and finite Tor amplitude at the output. Both
proper assertions retain every Loc membership and the exact existing canonical map.

Read the repaired dependency module beside its DAG statement. Its generic Lambda,
X, Y and f binders add no restriction; the two definition bodies are direct
applications of the already specified general derived functors to the full
underived composites. Its public upstream import preserves every recorded
adjunction and comparison interface. The consumer's replacement expressions are
therefore definitionally the same derived operations. Explicit `derivedTensor`
applications likewise unfold to the same monoidal tensor as before.

The mismatch repaired in this retry is computational: repeated large structural
arguments in the consumer, not a mathematical hypothesis or conclusion. There are
no copied canonical maps, new notions, hollow data, new postponed lemmas, private
notations or local instances. All variables and universes are explicitly bound
with `autoImplicit false`; all lines are within 100 columns. The two new definitions
contain real data; the item still has exactly three whole-theorem `sorry` proofs.
Both node `lean.statement` fields are checked verbatim against their source signatures.

## Repair of immutable head c3c7068b5ef0

As instructed, first inspected the saved report and ran the saved packet's dry
run before editing. It passed as `5ffdcf9d38`. The self-check then retained that
source, but the final delivery compile timed out at its library path and server
confirmation timed out too; nothing was pushed. This concrete failure caused the
following source repair rather than an unchanged re-push.

Profiling showed substantial instance synthesis inside the left-derived pullback
and generic tensor expressions. The theorem commands elaborated, but producing
the library artifact exceeded 60 seconds. Keeping underived functors locally
opaque and spelling out the tensor reduced the sandbox compile to 23.5 seconds
but did not resolve the library timeout. Those extra underived irreducibility
settings were removed. The retained coefficient-inverse-image opacity setting is
unchanged. Temporary profiling options were removed.

The final repair names the general derived composites once in their dependency
module and uses those names in every consumer endpoint; tensors use the existing
`derivedTensor`. This changes the saved packet substantively while preserving
all mathematical statements and canonical maps. The first dependency compile
identified the required scoped `CategoryTheory.Obj` instances; that scope was added.
The prescribed timeout, launcher tools and read-only libraries were never changed.


## Validation

The final two-module packet passed the prescribed `scompile.py` in dependency
order with exit 0 and no errors or warnings. The dependency's private overlay
compile took 19.9 seconds, preliminary compile 6.5 seconds, sandbox compile
44.1 seconds and library compile 8.8 seconds. The consumer's sandbox compile
took 6.4 seconds and library compile 42.5 seconds, under the unchanged 60-second
limit. Every delivered Lean file was checked separately. Verbatim signatures,
100-column lines, explicit binding, the three expected sorry proofs, and allowed
node field deltas were checked mechanically afterward.
