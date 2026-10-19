## Worker report

`Sheaf.Paper.EtaleGeometricBiduality` states
`WeilConjectures.finite_stage_etale_geometric_biduality`, with proof `sorry`.
`FiniteEtaleGeometricBiduality` spells out its conclusion as a proposition, with
real data. The theorem docstring reproduces all sixteen steps of the current
DAG proof, including the variable-field induction and the independent
constructible/Tor preservation argument. No natural statement or proof changes.

Hypothesis and clause correspondence:

- The global field k is `D.k` for `D : FiniteFieldDatum.{u}`. The recorded field,
  finite base, algebra and algebraic-closure instances give exactly the global
  finite-field convention; k is not an arbitrary nonclosed field.
- The coefficient prime is `(l : ℕ) [Fact l.Prime]`, with `_hl : l ≠ D.p`.
  The finite coefficient extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Positive level is `(n : ℕ) (hn : 1 ≤ n)`.
  The ring used everywhere is the recorded `Padic.coefficientExtensionRing l E n`.
  `ULift.{u+1,u}` is its canonical ring lift for the ModuleCat-valued small-etale
  sheaf convention. It is the same finite quotient, not an arbitrary finite ring
  or a field coefficient stage. Finiteness is supplied inside the conclusion
  definition by the existing named `Padic.finite_coefficientExtensionRing` theorem;
  it is not an extra assumption on the theorem.
- Every separated finite-type X/k is `(X : Scheme.{u})`
  `(aX : X ⟶ Spec (.of D.k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [QuasiCompact aX]`. The last two classes together mean finite type. There is
  no extra properness, smoothness, dimension, nonemptiness or Noetherian hypothesis.
  Nagata's existing instance supplies compactification.
- The ambient category is `Etale.DerivedCategoryModule (ULift (...) ) X`, i.e.
  the derived category of `ModuleCat`-valued sheaves on X.smallEtaleTopology.
  The subcategory is `finiteTorConstructibleEtale l E n hn X`, the conjunction
  of the recorded `Etale.DerivedCategory.isBoundedConstructible` and an ordered
  finite interval of the recorded `Etale.DerivedCategory.hasTorAmplitudeIn`.
  In particular upstream `constructibleFiniteTor` with its alternative stalk
  constructibility notion is not silently substituted.
- Omega is the recorded ambient `Etale.dualizingComplex (ModuleCat ...) aX`.
  `Etale.verdierDual (ModuleCat ...) aX` is the existing contravariant derived
  internal Hom into that object, including its action on morphisms.
- The natural delta map is `Etale.AmbientDualityPairing.bidualityMap ... X h K`.
  Its pairing witness fixes the symmetry to descended Koszul symmetry,
  evaluation to the adjunct of the identity, and delta to its transpose.
  The witness `h` is existentially asserted in the conclusion; it is not a
  hypothesis, an arbitrary arrow, or a choice of a double-dual isomorphism.
  These normalization equations determine the projected arrow uniquely.
- For each K in the displayed subcategory, the first conjunct is `IsIso` of
  that precise delta_K. The following conjunct states that D_X preserves the
  same subcategory, as required for an endo-anti-equivalence.
- The anti-equivalence clause binds `e : P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory`
  and a natural isomorphism `e.functor ⋙ P.ι ≅ P.ι.op ⋙ Etale.verdierDual ...`.
  This fixes the restriction on objects and morphisms, rather than merely
  asserting the existence of an unrelated self-equivalence.
- Exactness binds one coherent `s : D_X.CommShift ℤ`, and for every distinguished
  triangle in the opposite ambient category with all three vertices in P,
  asserts that its explicitly displayed D_X-image triangle is distinguished.
  Its connecting map uses the same `s.commShiftIso 1`. Opening Mathlib's
  `Pretriangulated.Opposite` gives the correct reversed integer shift; exactness
  is tested in the inherited full-subcategory triangles, avoiding an arbitrary
  separately chosen triangulation on that subcategory.

Recorded dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, its instance
  fields and coefficient conventions. This imports the recorded coefficient
  quotient constructions in `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, together
  with `QuasiCompact`. `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsSeparated`.
  Full signatures and docstrings of these recorded interfaces were read.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`, using the recorded finite-value
  `Scheme.IsConstructibleEtaleModuleSheaf`; source and full signatures read.
- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`:
  `Etale.hasTorAmplitudeIn_iff_exists_flatModel`, together with its existing
  `hasTorAmplitudeIn` notion from Derived.Coefficients. Its full theorem and
  docstring were read; its upstream bounded-constructibility predicate is not
  used to replace the project's bounded-constructibility predicate.
- `Sheaf.Paper.DualityPairing`: `Etale.ambient_duality_pairing`,
  `Etale.AmbientDualityPairing` and its canonical `bidualityMap` projection.
  An initial server --source check found no published module. Q29 landed while
  this worker was drafting; a repeat check read the newly published module, which
  has no callable bidualityMap. Its statement and the Q11 projections were read
  in full and reused, not replaced by another tensor, Hom or pairing.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale`, the
  etale specialization of the recorded finite-Tor constructible category.
  The Q11 dependency module is reused. Its unchanged original pro-etale,
  integral and field definitions remain publicly imported.
- `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`: `dualizingComplex`,
  `verdierDual`; `...Derived.Hom`: `derivedHom`, `derivedTensorHomAdjunction`.
  These were read in full. `...Compactification.NagataCompactification`
  supplies the compactification instance, with no extra theorem hypothesis.
- Every recorded, stated proof-dependency module, including Mathlib leaves
  resolved through their mathlib_match files, is directly imported without
  `public`; missing proof-only declarations are deferred to their own nodes.
  There are no proof-dependency import omissions intended in this draft.

Edge cases checked: n=1 is included; n=0 is excluded exactly by the source's
positive-level hypothesis. The zero complex, empty scheme and zero-dimensional
schemes impose no extra binders. Negative as well as positive Tor bounds are
allowed. The scheme need not be smooth or proper. Nonreduced schemes are allowed.
All integer shifts, including zero and negative shifts, use the coherent shift
structure. Both the canonical map and the equivalence refer to the ordinary
etale category, with no pro-etale/integral substitution. Non-finite-Tor bounded
constructible objects are not silently admitted. The field may be any fixed
algebraic closure in the global datum. No statement dispute or unit correction.

Searches actually run:

- msearch LeanFinder: “Verdier duality biduality isomorphism bounded constructible
  finite tor amplitude etale sheaves”: eight generic derived-category and
  triangulated-functor hits, no canonical geometric biduality theorem.
- msearch Loogle: `IsIso, biduality, duality`: no hits; unknown identifier IsIso
  in the remote search index. This was not counted as proof of absence.
- msearch grep: `bidual|verdier|Verdier`: 25 generic Verdier quotient/reference
  hits in Mathlib, no etale geometric theorem.
- Direct rg over upstream SixFunctors and the project's lean/Sheaf for
  `bidual|verdier|Verdier|dualityPairing|doubleDual`: upstream Derived.Dualizing
  gives preservation and a bare `Nonempty (K ≅ D D K)`. Its full signatures and
  docstrings were read. It neither fixes the canonical delta nor states the
  exact restricted anti-equivalence, and uses another constructibility record.
  ProEtale.TraceFormula.GeometricOperations.bidualityMap requires package data
  already assuming biduality and belongs to another site, so it cannot be used.
- grep for the item id in upstream WeilConjectures: no occurrence. Direct rg
  for both new declaration names over Mathlib, upstream and lean/Sheaf: no
  collision. The exact natural-language source and its unit were read from
  the launcher's restored blueprint literature tree.
- Server-source checks for `Sheaf.Paper.DualityPairing` and
  `Sheaf.Paper.FiniteTorAmplitudeSites`: initially both unavailable. Q29 subsequently landed; its current source was
  rechecked and lacks the callable canonical-map projection. Existing delivered
  sources were checked and reused for the dependency repairs, avoiding a
  dependency on downstream thm-fix-general-biduality.

- msearch LeanSearch for the canonical double-dual/anti-equivalence statement:
  unavailable (Internal Server Error), recorded as unavailable, not as a negative
  result. Loogle `CategoryTheory.Functor.CommShift`: twelve generic coherence
  structure hits, including CommShift itself, with no geometric biduality result.

Validation: all three final modules compiled without errors or warnings through
the prescribed per-file wrapper. `deliver2.py Q22 thm-weil-etale-geometric-biduality
--no-push` printed `OK (dry run)` for commit 56aa255b90; preflight passed except
for the independent second reading, which the tool explicitly leaves to the
next worker. Nothing was pushed. Each module was compiled separately in
dependency order. No global build, live-library edit, direct git
mutation, target change, or second-reading claim was made by this worker.

## Dependency modules

`lem-weil-duality-pairing`: the first shared snapshot had no Lean record and the
first server source check returned unavailable. Q29 landed during this worker's
draft, and the repeated source check shows the normalized existential family
interface, without a callable canonical-map projection. This delivery retains
that entire module and adds Q11's two canonical bidualityMap projections. The added
projection definitions only extract uniquely normalized data, with no sorry in
definition data. Its record changes only in lean, with lean.note explaining the
unusable callable interface. Both site theorem clauses are preserved.

`def-weil-finite-tor-amplitude`: the recorded interface exposes the intrinsic
ringed-site pro-etale category and integral/field stages, whereas this item needs
the ordinary etale finite-level category with the recorded constructibility.
The Q11 dependency module imports that entire original interface and adds its
etale presentation, plus the canonical fixed-scalar pro-etale presentation.
Its record changes only in lean; the item adds the existing node to stmt_deps.
No independent new definition node or statement correction is introduced. A
read-only dependency-graph traversal confirmed that this added definition
dependency has no path back to the item, so it introduces no dependency cycle.


## Earlier second reading (a previous round; superseded)

Independent second reader, 2026-10-16. I opened the delivered node, its restored
blueprint source at order 2128, the containing unit and chapter, every statement
dependency node, and the Lean declarations used below. The source is a blueprint
statement, not a Stacks theorem with that title. Its global conventions come from
`def-weil-finite-field-fiber`; the unit includes other coefficient stages, while
this node is precisely its ordinary-etale positive finite-stage assertion.

The statement checklist and its Lean correspondence are:

1. Fixed geometric base `k`, the algebraic closure of the fixed finite field:
   `(D : FiniteFieldDatum.{u})` and `Spec (.of D.k)`. I read the structure fields
   `prime`, `exponent_pos`, `cardinality_eq`, `card_base`, `algebra_closure`, and
   `isAlgClosure`. These specify the global base, without requiring that X descend
   to the finite field. Verdict: exact.
2. Coefficient prime different from the base characteristic: `(l : ℕ)
   [Fact l.Prime] (_hl : l ≠ D.p)`. The cardinality and prime fields of D identify
   its characteristic; no extra `HasInvertibleExponent` instance is assumed in
   the main theorem. Verdict: exact global hypothesis.
3. Every finite extension E of Q_l and positive level n: `(E : Type u) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)`.
   I opened `CoefficientExtension.lean`: the coefficient is the actual quotient
   of its valuation subring by the nth power of the chosen uniformizer ideal.
   `ULift.{u+1,u}` changes its universe, not its ring. Finiteness is supplied
   internally by the named `Padic.finite_coefficientExtensionRing`, not an extra
   theorem hypothesis. Verdict: exact coefficient stage.
4. Every separated finite-type scheme X/k: `(X : Scheme.{u})
   (aX : X ⟶ Spec (.of D.k)) [IsSeparated aX] [LocallyOfFiniteType aX]
   [QuasiCompact aX]`. I read the Mathlib classes: closed diagonal, locally finite
   type on affine pairs, and compact inverse images of compact opens. The latter
   two are the recorded finite-type conjunction. Nagata supplies the compactification
   used by `dualizingComplex`; there is no extra compactification, properness,
   smoothness, dimension or Noetherian binder. Verdict: exact.
5. Ambient category D(X_et,A): every K is in `Etale.DerivedCategoryModule` of the
   lifted quotient ring, whose abbreviation is the unbounded derived category of
   `ModuleCat`-valued sheaves on `X.smallEtaleTopology`. Verdict: ordinary etale,
   with the recorded coefficient convention.
6. K in D^b_ctf: `finiteTorConstructibleEtale l E n hn X K`. I unfolded the
   delivered predicate and read `isBoundedConstructible`,
   `IsConstructibleEtaleModuleSheaf`, and `hasTorAmplitudeIn`. It requires finite
   locally closed constructible strata with finite constant module values, bounded
   cohomology, and one ordered integer Tor interval tested against every module
   sheaf in degree zero. It does not silently use the upstream geometric-stalk
   constructibility predicate. Verdict: exact.
7. Omega and D_X: `Etale.dualizingComplex (ModuleCat ...) aX` and
   `Etale.verdierDual (ModuleCat ...) aX`. I opened Derived.Dualizing,
   Derived.UpperShriek and Derived.Hom: omega is the ambient right adjoint of
   ordinary compact support applied to the unit, and D is the full contravariant
   internal-Hom functor into omega. Verdict: correct objects and morphisms.
8. Natural canonical delta_K: the conclusion asserts a normalized
   `Etale.AmbientDualityPairing ...` witness h, then uses its `bidualityMap ... h K`.
   I checked the existential equations: Koszul symmetry is fixed by HEq to the
   descended braiding, evaluation after symmetry is the adjunct of the identity,
   and delta is its transpose. The projection extracts this determined arrow;
   it does not choose an unconstrained map. Naturality and shift/triangle
   compatibility remain in the same witness. Verdict: exact canonical map.
9. Delta_K is an isomorphism for every such K: the first universally quantified
   conjunct is precisely `IsIso` of that arrow under the membership implication.
   Verdict: exact, including the order of quantifiers.
10. D_X restricts to D^b_ctf: the second conjunct is preservation of exactly the
    same predicate. This spells out what the endo-anti-equivalence entails.
    Verdict: no stronger subcategory or weaker preservation conclusion.
11. Anti-equivalence: an equivalence from `P.FullSubcategoryᵒᵖ` to
    `P.FullSubcategory`, together with a natural isomorphism between its composite
    with inclusion and `P.ι.op ⋙ Etale.verdierDual ...`. This identifies the
    restriction on morphisms as well as objects. The first conjunct, with the
    pairing's naturality, fixes the canonical natural double-dual isomorphism.
    Verdict: exact, not a bare unrelated equivalence.
12. Exactness: one coherent `D_X.CommShift ℤ` and distinguishedness of the displayed
    image of every ambient opposite distinguished triangle whose three vertices
    satisfy P. I read Mathlib's Opposite.Pretriangulated: its shift reverses the
    integer degree. The third arrow uses that same s at 1. These are the triangles
    inherited by the full triangulated subcategory. Verdict: exact contravariant
    exactness, with no independently chosen triangulation.

Edge cases: n=1 is admitted and n=0 is excluded by the source's positive-stage
convention, rather than by an accidental instance. The zero complex, empty X,
nonreduced X and zero-dimensional X are all admitted. There is no finite index or
nonempty hypothesis; trivial covers/stratifications on the empty scheme introduce
no new theorem binder. Both positive and negative cohomology/Tor endpoints and
integer shifts occur. The characteristic restriction is exactly l ≠ p; all
separated finite-type X are allowed. Universe u is arbitrary, the coefficient
ring has its explicit lift to u+1, and the derived category lives at u+2.
Different sizes can be placed in a common universe; no equality between the
small site's object and morphism universes has been imposed.

Independent searches: I ran msearch LeanFinder with “canonical evaluation double
dual isomorphism exact anti-equivalence constructible etale finite Tor”; its eight
hits concerned finite-dimensional vector-space duality and affine schemes, not
this theorem. Loogle `CategoryTheory.Functor.CommShift` gave twelve generic shift
coherence declarations. LeanSearch “Verdier duality canonical biduality
constructible etale complexes” returned Internal Server Error; this is unavailable,
not a negative result. Direct rg for `bidual`, `double.?[Dd]ual`, and
`anti.?equivalence` searched upstream SixFunctors, project Paper modules and Mathlib
CategoryTheory; a second search checked `boundedConstructibleFiniteTor` and
`constructibleFiniteTor` and all newly declared names. The upstream geometric
biduality theorem gives only Nonempty of an object isomorphism, with its other
constructibility convention; perfect-object duality and ProEtale.GeometricOperations
are respectively a special case and an interface already assuming biduality.
None states this normalized ordinary-etale theorem and exact restricted functor.
No new independent definition node is required.

Dependency-module reading:

- `lem-weil-duality-pairing`: I read its source at order 2122 and Stacks
  sites-cohomology.tex Tags 08J9, 08JA and 08JC (tensor-Hom and triangulatedness),
  including their ambient ringed-site hypotheses. The generic coefficient-category
  structures specialize to ModuleCat, not to an added hypothesis on this item.
  The module's theorem retains both sites, arbitrary ambient K and arbitrary
  specified pro-etale W, the canonical normalization and all compatibility clauses.
  The added projections only extract the uniquely normalized arrows; there is no
  sorry in definition data and no new theorem without a DAG statement.
- `def-weil-finite-tor-amplitude`: I read its full current node, source at order
  1464, original FiniteTorAmplitude module, intrinsic constructibility and Tor
  definitions, canonical finiteCoefficientIntrinsicRealization and the current
  Q11 upstream ProEtale.Derived.TorAmplitude record. The latter serves the finite
  stage in the fixed-scalar pro-etale presentation; it does not supply the ordinary
  etale predicate with the project's finite-value constructibility. The final site
  module publicly retains that current recorded upstream interface and defines
  only the needed ordinary-etale presentation. The original integral/field
  declarations remain unchanged in Sheaf.Paper.FiniteTorAmplitude and are not
  consumed by this finite-stage item. No unneeded second pro-etale presentation
  is delivered. This follows the already-reviewed Q11 finite-stage specialization
  convention; the dependency's natural statement is unchanged.

Mismatches repaired in this reading:

- The draft imports the older intrinsic FiniteTorAmplitude and its realization
  solely for its unneeded pro-etale helper and higher stages. These import retired
  FiniteCoefficient.UpperLowerStar declarations that collide with the current
  published ProEtale.Derived.Hom and derived-direct-image APIs. I checked the Hom
  wrappers, Q11's documented compiler collision and its reviewed current finite-Tor
  record. Keeping the published pairing unchanged is possible by replacing the
  unused old import closure with the current recorded upstream finite-Tor module,
  importing coefficient-ring finiteness explicitly, and dropping the unneeded
  pro-etale helper. The etale definition and its exact conditions are unchanged.
  All removed higher-stage definitions remain untouched in their original module.
- I refreshed DualityPairing from the current published source (also checked with
  scompile.py --source), kept its complete normalization and proof plan, and added
  only the two needed canonical-map projections. The pro-etale projection's target
  uses the published derivedHom wrapper. No import adaptation or duplicate notion
  is required in this final module. The dependency lean.note explains both the
  missing callable interface and the finite-Tor import-closure repair.
- Three proof-dependency modules had become available after drafting:
  `EtaleDirectImageVanishing`, `DimensionExtension`, and
  `FiniteDirectImageComposition`. I opened them and added their non-public proof
  imports. No hypotheses, conclusion clauses or proof-plan steps changed.
- The shared finite-Tor node gained a reviewed Q11 record during parallel work.
  I retained its current non-lean fields, and updated this delivery's lean.note
  and declaration inventory to describe the actual recorded interface and final
  ordinary-etale-only addition rather than the earlier snapshot.

The principal theorem signature and all sixteen natural-language proof steps
are unchanged; the sole whitespace difference in step 2 splits its long displayed
Hom calculation across lines. Every theorem still has whole proof `sorry`, every
new definition has real data, and source/blueprint docstrings and 100-character
lines were checked. No local notation, private notion, file-local instance or
unbound implicit variable was introduced. There is no statement correction,
statement dispute, new node, or target-unit change.


The first compile of the earlier snapshot confirmed the import collision explicitly:
`FiniteCoefficient.UpperLowerStar.Defs` failed because the environment already
contained the legacy `ProEtale.UpperLowerStar.Defs` notation declaration. That
snapshot was superseded by the finite-Tor import repair above. The wrapper's
server-confirmation pass reread the final files and compiled all three delivered
modules cleanly, including the newly imported proof dependencies (main theorem
4.1 s, pairing 5.7 s, finite-Tor definition 1.8 s). The final dependency
descriptions in this second reading supersede the initial draft's import/export
inventory. No timeout limit was raised.

Final validation: deliver2.py --no-push printed OK for commit 721c29c3b2;
all three final modules compiled cleanly in sandbox and library views, and
server preflight accepted the complete second-reading package.

## Repair of return L (immutable head 572f02362bd5)

The returned errors were in the main biduality module: the coefficient finiteness
theorem was visible only through private imports, and the finite-Tor predicate was
not exported by the dependency interface loaded in that immutable compile. Those
missing declarations also prevented synthesis of the ambient exceptional adjoint
and left the universe metavariables of the existential pairing unresolved.

The main module now publicly imports
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` directly. Its finiteness
instance has the explicit type `Finite (Padic.coefficientExtensionRing l E n)`,
and the same explicit type is used in the finite-Tor definition. The canonical
`ULift` ring obtains its finite instance from that quotient; the existing
`Etale.isLeftAdjoint_rightDerivedLowerShriek` instance therefore applies. No
extra adjunction or finiteness hypothesis is added to either declaration.

`FiniteTorAmplitudeSites.lean` and its dependency node are included in this
delivery and expose `WeilConjectures.finiteTorConstructibleEtale` publicly.
The current server source of `Sheaf.Paper.FiniteTorAmplitude` was read through
`scompile.py --source`: its recorded interface is now the intrinsic pro-etale
definition, integral uniform Tor condition, and field aliases. A trial public
import of that entire module compiled in isolation but failed when combined with
the published pairing: the legacy and `FiniteCoefficient.UpperLowerStar.Defs`
modules both declare `AlgebraicGeometry.ProEtale.«term(_)_*[_]»`. The unused import
was removed from this ordinary-etale module. The original pro-etale, integral and
field definitions remain unchanged in their original owning module; this module
only supplies the missing ordinary-etale presentation and does not introduce an
alternative pro-etale notion. Its `lean.note` describes the current interface and
the exact collision. The dependency's non-lean fields were refreshed verbatim
from the shared node. This paragraph supersedes the earlier report's account
of which finite-Tor module is publicly reexported. The pairing module still
retains the published Q29 definitions and adds only the two normalized biduality-map projections.

The source statement at blueprint order 2128, all seven current statement
dependencies and their recorded signatures, the positive-level finite coefficient
ring, and the ambient dualizing and Verdier-dual signatures were rechecked.
The repairs affect import visibility and the explicit types of proof instances;
no hypotheses, conclusion clauses, canonical maps, coefficient universes,
edge cases, or sixteen-step proof plan are changed. No new node or statement
correction is introduced. Compilation and the required dry run are recorded below.

Repair validation: the final `scompile.py Q22 thm-weil-etale-geometric-biduality`
invocation compiled all three delivered modules separately in dependency order,
in both sandbox and library views, with exit status 0 and no warnings or errors.
The final log is `repair-final-compile.log`. All three recorded signatures remain
verbatim, every Lean line is at most 100 characters, and the only node-field
changes are the item's `lean`/added `stmt_deps` and the dependencies' `lean`.

The required `deliver2.py Q22 thm-weil-etale-geometric-biduality --no-push`
printed `OK (dry run)` for commit `b52b51c2d0`: preflight and all per-file compiles
passed, with all three Lean modules and their node records staged. Nothing was
pushed. Full output is retained in `repair-dry-run.log`. The tool ignored a
concurrent change to maintainer-owned `reviewed_lean`; that metadata was not
delivered. The sandbox copy was refreshed to the current shared metadata afterward.

## Second reading by Q22

Fresh independent reading of the repaired return, 2026-10-16. I opened the
current node, all seven statement dependencies, the three delivered modules,
the restored blueprint theorem at order 2128 and its unit, and the sources at
orders 411, 2122, and 1464. The item is a blueprint theorem, not a Stacks theorem
with this title. For its pairing dependency I also read sites-cohomology.tex,
Tags 08J9, 08JA, and 08JC: their ambient hypotheses are a ringed site and
unbounded derived objects, with no constructibility restriction.

My object/hypothesis/conclusion checklist and Lean correspondence are:

1. The fixed geometric field is the algebraic closure of the fixed finite field:
   `(D : FiniteFieldDatum.{u})`, `D.k`, and `Spec (.of D.k)`. I read the datum's
   prime, positive exponent, cardinality, finite field, algebra, and algebraic
   closure fields. There is no descent assumption on X. Verdict: exact.
2. The coefficient prime differs from the characteristic:
   `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`. The finite-field cardinality in D
   determines its characteristic. No extra invertibility hypothesis is imposed
   on the main theorem. Verdict: exact global convention.
3. Every finite extension E/Q_l and positive level n is covered by `(E : Type u)
   [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
   (n : ℕ) (hn : 1 ≤ n)`. I read CoefficientExtension: its coefficient ring is
   the actual valuation-ring quotient by the nth power of the uniformizer ideal.
   `ULift.{u+1,u}` changes only its size. Finiteness comes internally from the
   named `finite_coefficientExtensionRing`, not an extra assumption. Verdict: exact.
4. Every separated finite-type X/k is `(X : Scheme.{u})
   (aX : X ⟶ Spec (.of D.k)) [IsSeparated aX] [LocallyOfFiniteType aX]
   [QuasiCompact aX]`. I opened the three Mathlib class signatures: closed
   diagonal, locally finite-type affine ring maps, and quasi-compact inverse
   images. The last two together are the recorded finite-type condition.
   No properness, smoothness, dimension, Noetherian, nonempty, or extra
   compactification binder occurs. Verdict: exact.
5. The ambient category is `Etale.DerivedCategoryModule (ULift (...) ) X`.
   Its abbreviation in Derived.Coefficients is the unbounded derived category
   of ModuleCat-valued sheaves on `X.smallEtaleTopology`. Verdict: ordinary
   etale category and correct coefficient stage, without a site substitution.
6. K in D^b_ctf is `finiteTorConstructibleEtale l E n hn X K`. I unfolded it,
   `isBoundedConstructible`, `IsConstructibleEtaleModuleSheaf`, and
   `hasTorAmplitudeIn`: finite locally closed constructible strata with finite
   constant module values, bounded cohomology, and some ordered integer Tor
   interval tested against every module sheaf in degree zero. Verdict: exact;
   upstream geometric-stalk constructibility is not silently substituted.
7. Omega and D_X are `Etale.dualizingComplex (ModuleCat ...) aX` and
   `Etale.verdierDual (ModuleCat ...) aX`. I read Derived.Dualizing and Hom:
   omega is the ambient compact-support right adjoint applied to the unit;
   D_X is the contravariant internal-Hom functor into omega, including its
   morphism action. Nagata and the finite-coefficient exceptional-adjoint
   instances supply the structures without new theorem assumptions. Verdict: exact.
8. The natural arrow is `Etale.AmbientDualityPairing.bidualityMap ... h K`.
   The pairing witness h is existentially asserted in the conclusion. I checked
   its nested normalizations: HEq fixes the descended Koszul braiding,
   adjunction fixes evaluation by the identity, and delta is its transpose.
   These uniquely determine the extracted arrow, retaining naturality and
   shift/triangle compatibility. It is not arbitrary output data. Verdict: exact.
9. For every K satisfying that same membership predicate, the first conjunct
   is `IsIso` of precisely this arrow. The pairing is uniform before the
   universal quantifier on K. Verdict: exact canonical-map assertion.
10. D_X preserves the same D^b_ctf: the second conjunct applies
    `finiteTorConstructibleEtale` to `(Etale.verdierDual ...).obj (op K)`.
    This is the preservation needed for the anti-equivalence. Verdict: exact.
11. The anti-equivalence is `e : P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory`, with
    natural isomorphism `e.functor ⋙ P.ι ≅ P.ι.op ⋙ Etale.verdierDual ...`.
    This fixes the restriction on morphisms as well as objects, rather than
    permitting an unrelated equivalence. Verdict: exact.
12. Exactness uses one coherent `(Etale.verdierDual ...).CommShift ℤ` and
    preservation of the displayed image triangle for every opposite ambient
    distinguished triangle whose three vertices lie in P. The third arrow
    uses that same shift comparison at 1. I read Opposite.Pretriangulated:
    the opposite shift by n is the original shift by -n. These are the inherited
    full-subcategory triangles. Verdict: exact contravariant exactness.

Edge cases: n=1 is included, n=0 excluded exactly by the source's positive-stage
convention. The empty scheme, zero complex, nonreduced schemes, and dimension
zero remain admitted. There is no index-set or cover nonemptiness hypothesis.
Tor endpoints and shifts range over all integers. The characteristic condition
is exactly l != p. Universe u is arbitrary; the coefficient ring is lifted to
u+1 for ModuleCat sheaves and the derived category lives in u+2. Data can be
placed in a common universe, and no equality of site object and morphism
universes is imposed. All variables are explicitly bound with autoImplicit=false.

Independent searches actually run in this reading:

- LeanFinder `canonical bidual morphism Verdier dual constructible derived
  sheaves equivalence`: eight sheaf-adjunction, dense-subsite, and condensed
  category hits; none the geometric theorem.
- Loogle `CategoryTheory.Functor.CommShift`: twelve generic coherence and
  transport hits; no geometric biduality result.
- LeanSearch `Verdier duality evaluation transpose isomorphism finite Tor
  constructible sheaves`: eight module-dual/transpose and gluing hits; none
  this theorem. The service succeeded in this round.
- msearch grep `bidual|double.?dual|anti.?equivalence`: module, group, and
  topological duality and opposite-triangle references; none this theorem.
- Direct rg over Mathlib, upstream WeilConjectures, and project Lean for
  biduality, anti-equivalence, and all delivered names. I opened upstream
  `constructibleFiniteTor_verdierDual` and `nonempty_iso_verdierDual_verdierDual`.
  They use the other geometric-stalk constructibility convention, and the latter
  gives only an object isomorphism, without fixing the canonical arrow or
  restricted exact functor. Neither replaces this node. The project's
  coefficient biduality is a coefficient result, not this geometric assertion.

Dependency modules: there are no new nodes. For `lem-weil-duality-pairing`,
I compared the sandbox with the published module, also read via
`scompile.py --source`. Its original definitions, both site clauses,
normalizations, compatibility, and theorem are retained. The two added callable
projections extract uniquely determined arrows with real terms and source/blueprint
docstrings. I read the side framework's exact ProEtale.Derived.Hom signature and
coord/pefw-upstream-framework.md; the older source tree is not substituted.

For `def-weil-finite-tor-amplitude`, I opened the current node and its owning
FiniteTorAmplitude module: intrinsic pro-etale finite Tor, the uniform integral
reduction condition, and the field aliases. That interface does not expose the
ordinary-etale predicate needed here. FiniteTorAmplitudeSites supplies precisely
that presentation using the actual quotient, the recorded constructibility,
and the existing Tor test. The owning pro-etale/integral/field declarations are
untouched. Its lean.note explicitly explains the unused original import closure's
legacy/FiniteCoefficient notation collision with the pairing. No alternative
pro-etale notion or extra assumption is introduced. The dependency nodes'
non-lean fields match the base.

I retained the preceding return repairs: public coefficient-finiteness import,
explicitly typed Finite instances, and publicly visible ordinary-etale predicate.
All three lean.statement records occur verbatim as the actual signatures. I
compared the main docstring with all sixteen current DAG proof steps: each step
and citation occurs in order, with only line-wrapping spaces in the displayed
Hom calculation. Every theorem remains wholly sorry and every definition has
real data. There is no local notation, private definition, local instance,
statement correction, statement dispute, or target-unit change.

Mismatch repaired in this reading: proof-import coverage was stale after parallel
landings. I added non-public imports of DeltaRestriction, SfHomTriangulated,
FiniteConstantProjectionFormula, CoefficientFrobenius, and DeltaProperPushforward
to the main module, and ModuleDerivedCategory to the pairing module. I checked
the import graph: none creates an import cycle. Their declarations serve the
unchanged proof plan; no hypothesis, conclusion, mathematical definition, or
proof-plan step changed.

Proof-import integration issue reported to the maintainer: the newly recorded
SmoothStratificationFiniteTor and StratumAmbientHom modules also belong to this
proof plan, but their published import closures cannot currently coexist with
the published pairing. I checked their signatures and traversed the import graph.
Both reach FiniteCoefficient.UpperLowerStar.Defs; the pairing reaches the legacy
UpperLowerStar.Defs through the published ProEtale.Derived.Hom/Tensor modules.
A separate import-only scratch file compiled through scompile.py reproduced:
`environment already contains 'AlgebraicGeometry.ProEtale.lowerStarComp'`.
The two modules duplicate that upstream declaration. Their proof-only imports
are consequently omitted here; they are not replaced by assumptions, private
copies, or changes to the item's statement. The node's proof dependencies and
the complete natural-language proof remain intact for the framework integration
repair. The five compatible main imports and one pairing import are included.

Validation of the final files: scompile.py compiled all three sibling modules
separately in dependency order, in both sandbox and library views, with exit
status 0 and no diagnostics. The complete log is second-reading-compile.log.
The separate import-only collision was also confirmed against current server
sources. All delivered Lean lines are at most 100 characters. Only the item's
lean/added stmt_deps and the dependencies' lean records differ from the base;
no maintainer metadata or natural-language statement was changed.

The required deliver2.py --no-push printed OK (dry run) for commit 231ec72194:
preflight and all per-file compiles passed. Its log is second-reading-dry-run.log.
