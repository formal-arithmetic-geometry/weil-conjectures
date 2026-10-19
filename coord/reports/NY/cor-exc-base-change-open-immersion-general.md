## Worker report

The delivery states both clauses of `cor-exc-base-change-open-immersion-general` in
`Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange`. No statement correction is made.
The two main declarations are `sfAmbientExceptionalOpenBaseChange` and
`sfFiniteExceptionalOpenBaseChange`; the record lists both. All theorem proofs are
`sorry`, with their natural-language proofs in their docstrings. Definitions have real
data. The additional modules repair or supply existing dependency interfaces.

### Hypotheses and conclusions

* The prime and finite extension are `(l : ℕ) [Fact l.Prime]`, `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Positive levels are
  written `n + 1`, with `n : ℕ`; these are exactly the integers at least one. The
  coefficient is the recorded `Padic.coefficientExtensionRing l E (n + 1)`, lifted
  by `ULift` only to fit the existing module-sheaf universe convention. Its finiteness
  instance invokes the recorded coefficient-finiteness theorem, without a new assumption.
* In the ambient clause, `S X Y`, their `Over S` instances, and `f.IsOver S` give the
  scheme base and the S-morphism. `_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))`
  states invertibility on S. Each finite-type condition is the pair
  `LocallyOfFiniteType` and `QuasiCompact`; `IsSeparated f` is separatedness.
* `c : Compactification f` and
  `D : SfAmbientExceptionalRightAdjointDatum A f c` are precisely the supplied
  compactification and actual ambient datum, rather than a replacement assumption
  of a relative or constructible adjunction. The recorded datum and its actual
  `D.adjunction d` are used.
* `g : Y' ⟶ Y` has only `[IsOpenImmersion g]`. There is no quasi-compactness,
  Noetherianity, affine-base, or finite-type-over-S condition on g or Y'.
* The cartesian square is the canonical fibre product, `pullback f g`, with projections
  `pullback.fst f g`, `pullback.snd f g` and proof
  `IsPullback.of_hasPullback f g`. The recorded `ChosenCartesianSquare` module is
  imported; its chosen projection-respecting identification with this pullback
  transports this formulation to any square in that dependency. This is not a
  restriction on Cartesian squares.
* The result returns an integer `c_cd` satisfying the original FullCD bound and
  the same bound for `(c.ofIsPullback ...).g`, and a datum `D'` at this base-changed
  compactification. In particular the base change does not ask for a fresh
  compactification or a stronger bound.
* The ordinary unbounded compact-support functor is the recorded
  `sfAmbientCompactSupportCandidate`. The specified realization equivalence
  `sfIntrinsicDerivedEquivalence` identifies its category with fixed-scalar module
  sheaves. `sfIntrinsicCompactSupportComparison` is built from the recorded
  extension by zero and the uniquely normalized direct-image comparison.
  `sfFixedAmbientAdjunction` transports the *supplied* adjunction through this
  comparison, so both its unit and its counit are fixed.
* `sfFixedCompactSupportExchange` is the direct-image mate for the proper part,
  followed by the inverse canonical extension-by-zero comparison. It is defined
  before any invertibility assertion. `sfAmbientExceptionalOpenComparison` is
  exactly `mateEquiv` applied to its inverse. The proof `hEx` certifies the
  invertibility of this specified map and is not an arbitrary chosen comparison.
  The ambient conclusion is `IsIso` of that mate on the full ordinary derived
  categories. Every displayed fixed-scalar object is carried to the intrinsic
  object by the recorded, specified equivalence, not by an unspecified identification.
* An affine-open immersion is included by the same `g` binder; no additional
  hypothesis is needed for the “in particular” sentence.
* Independently, `Dk : WeilConjectures.FiniteFieldDatum` supplies
  `k = algebraic closure of F_q`. The second theorem has `l ≠ Dk.p`, finite-type
  structure morphisms of X and Y to `Spec Dk.k`, and the separated finite-type
  k-morphism f. It has **no ambient datum**. It is stated for any compactification c;
  such a c exists by Nagata under the stated finite-type-over-field hypotheses,
  and the definition itself needs the chosen compactification to specify its formula.
* The independent functor `sfFiniteExceptionalFixed A c` is literally
  `Rν_* ⋙ f_et^× ⋙ Dν^*`, using the existing etale right adjoint. Its conjugate
  `sfFiniteExceptional A c` lives in the recorded intrinsic categories.
* The left disjunct of `_hK` is `∃ F, (comparisonUpperStar ... Y).essImage F ∧
  Nonempty ((DerivedCategory.singleFunctor _ 0).obj F ≅ K)`. This is every
  etale-origin sheaf placed in degree zero; it does not require finiteness or
  constructibility of F. The right disjunct applies the recorded
  `intrinsicFiniteTorsionConstructible` to K's canonical intrinsic realization;
  it is the bounded constructible class, with exactly its recorded cohomological
  predicate. The conclusion is `IsIso (sfFiniteExceptionalOpenComparison ... c K)`.
* That last comparison is an actual composite: comparison pullback square,
  etale exceptional mate, and the derived comparison-direct-image open-restriction
  square. The restriction square is derived from the literal site restriction
  identity; preservation of K-injectives is supplied by the relevant actual
  adjunctions. This fixes the canonical map on whole complexes. The accompanying
  relative-adjunction module describes only the bounded-below etale-origin test
  class and bounded-below targets, with no unrestricted adjoint assertion.

### Dependency declarations read and used

* `Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint`:
  `AlgebraicGeometry.Scheme.SfAmbientExceptionalRightAdjointDatum`,
  `sfAmbientCompactSupportCandidate`, and the full signature of
  `HasAmbientExceptionalRightAdjointDatum`.
* `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, the ordinary intrinsic category.
* `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including `isoPullback`, `hom_fst`, `hom_snd`.
* Mathlib `AlgebraicGeometry.IsOpenImmersion`, `IsPullback`, and
  `CategoryTheory.Functor.essImage` (the Mathlib match of `def-sf-fullcd-used-class`).
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleBaseChange`, `proEtaleConstantRing`,
  `proEtaleConstantModuleDirectImage`, and the object-valued
  `proEtaleConstantModulePullback` (the reason a functor interface was needed).
* `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero` and its exactness module:
  `sfIntrinsicModuleEquivalence`, `sfIntrinsicExtensionByZero` and their existing
  exact/additive structures. The realization is the existing
  `finiteCoefficientIntrinsicRealization`, not a second construction.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`:
  `proEtaleConstantDerivedDirectImage`; and
  `Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension`:
  `sfFullCohomologicalDimension`, with both full-sheaf quantifiers read.
* `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `intrinsicFiniteTorsionConstructible`, and the underlying
  `finiteTorsionConstructible` definition in `Sheaf.Paper.FiniteTorsionConstructibility`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; `Sheaf.Paper.FiniteFieldFiber`:
  `WeilConjectures.FiniteFieldDatum`.
* The finite-coefficient `UpperLowerStar` and open `LowerShriek` modules:
  `ProEtale.upperStar`, `lowerStar`, `upperStarCompIso`,
  `upperStarLowerStarAdjunction`, `openImmersionLowerShriek`,
  `openImmersionLowerShriekUpperStarAdjunction`, and the restriction isomorphisms.
* `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`:
  `comparisonUpperStar`, `comparisonLowerStar`, `comparisonAdjunction`.
* `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps`:
  `Etale.rightDerivedUpperShriek`, `rightDerivedUpperShriekBaseChangeMap`,
  and `leftDerivedUpperStarIsoMapDerivedCategory`.
* `WeilConjectures.Compactification.BaseChange`: `Compactification.ofIsPullback`
  and its two cartesian-square declarations. Generic Mathlib/upstream derived
  comparison, composition, K-injective, mate and adjunction-transport APIs are used.

### Edge cases

Checked the empty scheme and zero sheaf/complex: neither input class requires
nonemptiness or nonzero cohomology, and no arbitrary section or point is chosen.
The identity open is admitted; every square and mate has its canonical identity
normalization from the existing composition/adjunction APIs. Non-quasi-compact opens
are admitted in the ambient clause. In the independent finite-type-over-field clause
Noetherianity implies quasi-compactness of opens, but no such assumption was inserted.
The infinite etale-origin sheaf case is retained explicitly in the first disjunct.
No boundedness hypothesis is imposed in the ambient clause, and no unrestricted
ambient datum is asserted in the independent one. Level zero is excluded exactly by
indexing positive levels as n+1. Primes equal to the characteristic are excluded by
`l ≠ Dk.p`, as in the source. A bounded constructible complex with arbitrary shifts is
covered by the recorded cohomology predicate, without a degree-zero restriction.

### Searches and validation

The mandatory `msearch.py` searches were made with the sandbox search-log root.
LeanSearch “Exceptional inverse image base change by an open immersion for sheaves”
was unavailable (Internal Server Error). LeanFinder on the same query returned
underived restriction/open-immersion/module lemmas, no exceptional-derived match.
Loogle `CategoryTheory.Adjunction, CategoryTheory.IsIso` returned general adjunction
and equivalence APIs. Mathlib grep `exceptional.*base.change|upperShriek.*baseChange`
had no matching exceptional comparison. `rg` searches of Mathlib, WeilConjectures and
`lean/Sheaf`, including the item id, found the generic mate APIs and upstream etale
exceptional comparison, but no theorem with these two pro-etale clauses. Read the
legacy pro-etale derived, comparison, extension-by-zero/base-change and exceptional
source signatures; the legacy imports duplicate declarations in the finite-coefficient
intrinsic import closure, confirmed by the prescribed compiler. Read the exact
finite-coefficient framework and its compatibility manifest instead. Search details
are also preserved in the sandbox `searches.jsonl`.

The theorem proof docstrings follow all seven proof steps of the node. The local
record/text checker passes for every module. Every file is submitted through the
prescribed scompile.py wrapper, separately in dependency order; the final dry run
will be recorded below when it completes.

## Dependency modules

`def-weil-proetale-inverse-image`: `SfIntrinsicRealizationTransport` supplies a genuine
finite-coefficient inverse-image functor where the recorded declaration only supplied
an object map, together with its adjunction to the existing intrinsic direct image.
The specified existing realization equivalence is extended to derived categories.
Two unique comparisons are normalized on the actual constant-unit sections and on
K-injective representatives. Their uniqueness determines their data; neither is
chosen from a bare existence or `Nonempty` statement.

`def-weil-exceptional-inverse-image`: `SfFiniteExceptionalInverseImage` supplies the
finite-level formula in the compatible intrinsic coefficient import closure. The
current published field-base formula is read and its incompatible import closure
is documented in the updated node note. Its functor
is the literal source formula, with the existing etale adjoint. The actual canonical
open comparison and comparison-coordinate transports are data. This finite-coefficient
delivery consumes none of the integral/rational/common-stage extensions of the same
node; those coefficient stages are not replaced by a finite approximation.

`lem-cbc-proetale-extension-zero-base-change`: the old recorded legacy module cannot
be imported with the existing intrinsic finite-coefficient category. The replacement
`SfFiniteOpenExtensionBaseChange` gives the same conjugate-of-mate construction and
its degreewise derived isomorphism using compatible smaller modules. It does not
assume or choose an arbitrary base-change transformation.

`def-sf-fullcd-class`: `SfClassFullCohomologicalDimension` supplies the compatible
finite-coefficient interface to the now-published definition, including both
absolute and all pro-etale-base-change
vanishing clauses, with the original sheaf ranging over the full etale-origin class.
The inverse image to a base-changed source is the recorded exact sheaf functor.

`cor-sf-ambient-adjoint-discharge`: `SfConstructibleExceptionalAdjointDischarge`
supplies the node proof's relative interpretation on all bounded-below etale-origin
tests; the current published interface restricts to bounded constructible tests. It asserts FullCD_cls(2d)
and natural Hom bijections with the defined functor, expressed by a relative counit,
its induced bijectivity on all bounded-below etale-origin test objects, and its
naturality on all bounded-below targets. There is no ambient-data assumption or
unrestricted vanishing conclusion. The explicit dimension parameter is the one
used in the node's proof.

Source check: read the complete imported unit record `dag/units/sk-prop-sf-existence.json`,
including its explicit separation of the conditional ambient clause and the
unconditional transported-etale relative adjunction. The untracked literature tree
is absent in this clone; the unit record carries the source statement and proof.
A current-server source lookup for `Sheaf.AlgebraicGeometry.ExceptionalInverseImage`
reported that no such module was available. The exact existing etale and finite
framework declarations were read locally.

The earlier NL delivery at `dde2fa25c670681080ed094fb3d6392c34a04c7e` was
returned because its compactification comparisons admitted scalar twists. A new
published discharge and exceptional interface have since landed and were read in
this recovery. This delivery's canonical map continues to use the explicit
comparison-site paste of the existing canonical etale exceptional mate. The
relative-counit existence in the discharge theorem only expresses the relative
adjunction property; no canonical map is selected from that existential statement.

Earlier attempt's file verification, before this recovery: the prescribed
scompile.py invocation with all six delivery
modules completed successfully after current-server confirmation. Every delivered
file compiled cleanly, with no compiler errors or non-sorry warnings. The server
confirmation compiled the current files, including all final proof-plan imports;
the final main module took 4.5 seconds under the required 60-second per-file limit.

Recovery check against the current published library (2026-10-16): the earlier
preflight closure cap has been raised to 50000 by the maintainer; no project tool
was edited in this sandbox. The current dry run is being rerun with the repaired
tool. The current sources of `AmbientAdjointDischarge`,
`FiniteTypeExceptionalInverseImage`, upstream `FullCohomologicalDimension`, and
upstream `UpperShriekCanonicalMaps` were read through `scompile.py --source`.

The first three of these prerequisites now have published records. Their sandbox
records are retained as §1(B) interface repairs, with notes updated against those
actual records. The published discharge theorem restricts its test objects to
bounded constructible objects, while this item's degree-zero etale-origin input
can be infinite and nonconstructible. The replacement's relative Hom bijections
retain all bounded-below etale-origin tests, as the dependency node's proof says.
The published finite-type exceptional definition uses the identical etale
transport formula but imports the legacy pro-etale derived closure. The
published FullCD class likewise imports legacy `Derived.Comparison` and
`ExceptionalAdjoint`. The compatible smaller finite-coefficient modules remain
necessary with the recorded intrinsic ambient categories. The FullCD replacement
retains both original-source-sheaf quantifiers and every small pro-etale base
change. There is a source-node explanatory fault: etale origin does not imply
constructibility (an infinite constant module is a counterexample). Both the
published and replacement definitions correctly use etale origin; this delivery
makes no such identification and does not edit that dependency's statement.

The additional search during recovery used LeanFinder with the query
“Exceptional inverse image base change along open immersion on pro etale derived
categories”; its eight hits were underived restriction and general scheme lemmas,
with no matching exceptional comparison. Direct `rg` of the upstream and side sources found no declaration
with this item's identifier or either proposed main declaration name. The
existing `Functor.essImage` signature was checked directly: it is precisely an
existential witness and an isomorphism, and imposes no finiteness condition.

Proof-plan imports were refreshed against the current DAG. The main module also
imports `EtaleOriginDerivedCategory`, `ComparisonPullbackExact`, and
`ProEtaleComparisonPullbackSections` as non-public proof dependencies. The legacy
umbrella imports `EtaleOriginAdjointClass`, `ComparisonDirectImage`,
`ProEtaleExtensionZeroComparison`, and
`WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek` cannot be
combined with the intrinsic finite-coefficient closure: they import the legacy
`UpperLowerStar`/derived hierarchy that redeclares the finite-coefficient names.
The actual compatible pullback, open adjunction, comparison-site square and
transported finite-level functor interfaces are imported by the delivered
modules instead. Unstated proof-only lemmas are described in the theorem's proof
plan and have no module to import.

The extension-base-change module explicitly imports the recorded
`OpenImmersionSquare` and `ProEtaleExtensionZero` modules as well as the compatible
inverse-image interface. Its cartesian binders express the same chosen pullback
square, with both open-immersion instances. All final source and record edits
were completed before the final dry-run snapshot.


## Earlier second reading (a previous round; superseded)

I independently read the current node, both theorem signatures and every definition
on which their canonical maps depend, all five dependency modules in this delivery,
and the recorded dependency declarations. This is a stage-2 statement review; theorem
proofs remain `sorry`. No statement correction is needed or made.

### Source and object-by-object statement check

The original blueprint source is available read-only at
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-existence/cor-exc-base-change-open-immersion-general.md`.
I read it and its enclosing `_section.md`, especially the distinction between the
conditional ordinary-category assertion (b) and the unconditional relative assertion
(c). The current DAG expands that distinction explicitly and repairs the source's
suggestion to use Nagata over an arbitrary base; the existing compactification in the
ambient datum is used instead. This delivery does not alter that already-recorded
statement or its proof. I also read `more-etale.tex`, in the same literature tree,
`lemma-shriek-proper-and-open` (Tag 0F7B), its composition/base-change lemmas, and
`lemma-cartesian-square-Rf-upper-shriek`. The proper/open interchange admits arbitrary
schemes with the stated proper and locally quasi-finite maps and is invertible for
torsion coefficients; its bounded-below alternative is also stated explicitly. Those
hypotheses are satisfied in the independent finite-coefficient clause. The ambient
clause uses its separate FullCD-based inputs, rather than assuming the etale assertion
applies to arbitrary pro-etale sheaves.

The list below is the node's objects, hypotheses and conclusions, matched to Lean.

| Node item | Lean rendering and verdict |
| --- | --- |
| Prime, finite extension and positive finite coefficient | `(l : ℕ) [Fact l.Prime]`, `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, and `Padic.coefficientExtensionRing l E (n + 1)`. This is the recorded valuation-ring quotient; positive integers are exactly successor indices. Match. |
| Scheme base S with l invertible | `(S X Y : Scheme.{u})`, `[X.Over S]`, `[Y.Over S]`, and `_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x)`. These are the geometric data of `HasAmbientExceptionalRightAdjointDatum`, whose full signature and datum structure I opened. Match. |
| X and Y finite type over S | `LocallyOfFiniteType` and `QuasiCompact` on both structure maps. Match; no Noetherian, qcqs-base or field assumption is inserted. |
| Separated finite-type S-morphism f | `(f : X ⟶ Y) [f.IsOver S] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`. Match. |
| Supplied compactification and actual ambient adjunction | `(c : Compactification f)` and `(D : SfAmbientExceptionalRightAdjointDatum A f c)`. I read `fullCD`, `rightAdjoint`, `adjunction`, `theta`, `rho`, and their unit/counit and cocycle fields. The transported adjunction is built from `D.adjunction d`, so it retains the supplied adjunction. Match. |
| Arbitrary open immersion g | `{Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g]`. No `QuasiCompact g`, finite-type Y'/S, affine, nonempty or Noetherian assumption. Match. |
| Cartesian X', g', f' | `pullback f g`, `pullback.fst f g`, `pullback.snd f g`, `IsPullback.of_hasPullback f g`. I read `ChosenCartesianSquare.isoPullback` and its two projection equations: the canonical representative covers every stated square up to the specified square isomorphism. Match. |
| Ordinary derived categories of pro-etale A-modules | `proEtaleDerivedCategory` is the uncompleted ordinary derived category of modules over the constant ring sheaf on `ProEt.topology`. `sfIntrinsicDerivedEquivalence` is the derived equivalence of the recorded, specified `sfIntrinsicModuleEquivalence`. The fixed-scalar category uses `ULift A` in `ModuleCat.{u+1}` only for that established presentation. Match. |
| Same FullCD bound after base change | The ambient conclusion exhibits `c_cd` and both `sfFullCohomologicalDimension c.g A c_cd` and its base-changed counterpart. I opened the definition: both absolute vanishing and every small-pro-etale-base-change vanishing range over all original-source sheaves. Match. |
| New adjoint from the base-changed compactification | The conclusion gives `D' : SfAmbientExceptionalRightAdjointDatum A (pullback.snd f g) (c.ofIsPullback ...)`. The original c is used, with the same restricted bound in the preceding conjunct. Match. |
| Canonical exceptional comparison, isomorphism | `sfFixedCompactSupportExchange` pastes the proper ordinary direct-image mate with the canonical extension-by-zero exchange. `sfAmbientExceptionalOpenComparison` applies `mateEquiv` to its inverse under the transported actual adjunctions. The existential `hEx` is a proof of invertibility of that already defined exchange; it supplies no freely chosen map. `IsIso` is asserted for the resulting natural transformation on the full ordinary categories. Match. |
| Affine-open specialization | Every affine-open inclusion satisfies the sole `IsOpenImmersion g` condition. The same theorem applies without another hypothesis. Match. |
| Independent finite-field geometric datum | `Dk : WeilConjectures.FiniteFieldDatum.{u}` and `_hl : l ≠ Dk.p`. I opened the structure: it includes a prime p, a positive exponent, a finite base field of cardinality q=p^a, and a fixed algebraic closure k. Match. |
| Finite-type k-schemes and separated finite-type k-map | The two `Over (Spec (CommRingCat.of Dk.k))` instances, finite-type structure-map pairs and `f.IsOver` render precisely those assumptions. This theorem has no D or unrestricted ambient-datum hypothesis. Match. |
| Constructible exceptional functor | `sfFiniteExceptionalFixed A c` is literally `Rν_* ⋙ Etale.rightDerivedUpperShriek ⋙ Dν^*`; `sfFiniteExceptional` is its conjugate in the recorded intrinsic categories. Its map uses the existing canonical etale exceptional mate, with the comparison pullback and open-restriction squares. I opened the current etale canonical-map source and verified its mate orientation. Match. |
| Arbitrary etale-origin sheaf in degree zero | The left disjunct of `_hK` witnesses a sheaf F in `(comparisonUpperStar ... Y).essImage` and an isomorphism from `(DerivedCategory.singleFunctor _ 0).obj F` to K. Mathlib `Functor.essImage` is exactly an existential witness with an isomorphism. No finiteness or constructibility assumption is imposed on F. Match. |
| Every bounded constructible complex | The right disjunct applies `intrinsicFiniteTorsionConstructible` to the canonical intrinsic realization of K. I read its definition: finite support of nonzero cohomology and constructibility of every cohomology sheaf, with arbitrary integral degrees. Match. |
| Independent canonical comparison is invertible | `IsIso (sfFiniteExceptionalOpenComparison A (IsPullback.of_hasPullback f g) c K)` has source `g'^* (Rf! K)` and target `Rf'! (g^* K)`. The restriction square is derived from the actual site localization identity using the actual K-injective-preserving adjunctions. The comparison is fixed before its isomorphism theorem. Match. |
| Quantifiers and compactification | All geometric data and c precede arbitrary g and K. The independent theorem works for every compactification c; existence under the finite-type field hypotheses is the recorded Nagata input, not a restriction of the class of f. Match. |

### Dependency-module reading and repairs

No new definition node is present. All five additional node records are existing
statement dependencies or, for `def-sf-fullcd-class` and the extension-base-change
lemma, the additional explicitly cited statement dependencies of the sandbox item.
Their mathematical fields are unchanged; their Lean records are interface repairs.

* `def-weil-proetale-inverse-image`: I opened `ProEtaleInverseImage` through
  `proEtaleConstantModulePullbackMap`, not merely its primary set-valued declaration.
  I also searched independently and found that `ProEtaleIntrinsicFiniteOperations`
  already supplies `sfIntrinsicPullback` and `sfIntrinsicDerivedPullback`, with the
  same canonical equivalence transport. The worker had duplicated this notion as
  `sfIntrinsicConstantModuleInverseImage` and `sfIntrinsicConstantDerivedInverseImage`,
  and duplicated the realization-additivity instance. I removed those three
  declarations, imported the owning module, and made the new adjunction use the
  existing `sfIntrinsicPullback A f`. The dependency record now primarily records
  `sfIntrinsicConstantModuleAdjunction` and explains the reuse. The genuinely missing
  direct-image comparisons remain uniquely specified on scalar-unit sections and
  K-injective representatives. Their unique characterization fixes the chosen data;
  neither comparison is selected from a bare existence assertion.
* `def-weil-exceptional-inverse-image`: I read the current published field-base
  interface and the delivered finite formula and canonical map. The former's legacy
  import closure is incompatible with the finite-coefficient intrinsic closure.
  The replacement keeps the same finite-level transported-etale formula and its
  canonical mate. It supplies only the finite-level interface consumed here; it
  does not claim to replace integral/rational coefficient transitions. Match.
* `lem-cbc-proetale-extension-zero-base-change`: I read the node, its open-square
  definition, the upstream map and the delivered smaller import closure. The reverse
  underived exchange is the conjugate of the specified direct-image mate; its
  inverse is the node's direction, and exact functors descend it termwise. No
  constructibility or boundedness premise is inserted. Match.
* `def-sf-fullcd-class`: the replacement has both displayed vanishing clauses,
  including every V in the small pro-etale site and every etale-origin sheaf F on
  the original source, followed by actual pullback of F. The published definition
  has this same mathematical content but an incompatible legacy closure. The
  node's explanatory identification of all etale-origin sheaves with constructible
  sheaves is false for an infinite constant module; the formal definition retains
  etale origin exactly, and this delivery changes no dependency statement. Match
  to the two defining clauses, with that source fault explicitly recorded.
* `cor-sf-ambient-adjoint-discharge`: I read the node proof and enclosing unit clause
  (c). They specify all bounded-below etale-origin tests, not merely constructible
  tests, against all bounded-below targets. The delivered relative-counit formulation
  makes the natural Hom maps bijective on exactly that class and adds the explicit
  FullCD_cls(2d) bound. It asserts no unrestricted ambient adjunction. The actual
  exceptional comparison is constructed separately and is not chosen from this
  relative-counit existence assertion. Match.

I also found omitted, already stated proof-plan modules. I added non-public imports
of `FullCdAmbientAdjoint`, `ExceptionalBaseChangeReducesToProper`, and
`IntrinsicDerivedOpenAdjunction`. Their signatures and constructions were read,
including the current server source of `FullCdAmbientAdjoint`. The legacy incompatible
proof imports listed by the worker remain excluded for the documented import-name
collision; their compatible constructions are already in the delivered closure.

### Edge cases, universes and conventions

The empty scheme, zero sheaf and zero complex are admitted: no point, section,
nonzero cohomology or nonempty index is assumed. The identity open and non-quasi-compact
opens remain in the ambient theorem. An arbitrary open of a finite-type k-scheme is
quasi-compact by Noetherianity in the independent clause; this is a consequence used
in the proof, not an added binder. Infinite etale-origin degree-zero sheaves remain
in `_hK`, while bounded constructible complexes may have any shifts. The minimum
level is n+1=1 when the Lean index n=0; coefficient level zero is excluded exactly as
in the source. Both prime 2 and other primes are admitted, with l≠p only in the
finite-field clause and l invertible on S in the ambient clause.

The site remains `Scheme.{u}.ProEt`, with objects in u+1 and morphisms in u. The module
value universe is u+1, including `ULift.{u+1,u} A`; no equality between the site object
and morphism universes is imposed. The ordinary intrinsic derived-category signature
is unchanged. All variables are explicit under `autoImplicit false`. No local notation,
private notion, hollow definition, arbitrary-map parameter, or proof inside a definition
was introduced. Every postponed theorem has its source/blueprint docstring and a
natural-language proof; the two main docstrings follow respectively Steps 1–4 and
5–7 of the node. All lines are at most 100 characters and every recorded primary
`lean.statement` is literally the file's declaration signature.

### Independent searches and verification

I ran fresh prescribed searches with different wording:

* LeanFinder: “Exceptional pullback commutes with restriction to arbitrary open
  subschemes” returned eight Mathlib restriction/fibre-product lemmas, no match.
* Loogle: `CategoryTheory.mateEquiv` returned its exact mates API and its unit,
  counit and pasting equations; these supply the categorical construction, not this
  exceptional base-change theorem.
* LeanSearch: “The mate defining exceptional inverse image base change is invertible
  for open immersions of schemes” succeeded and returned eight ordinary open-immersion
  lemmas, no match.
* Direct `rg` searches of Mathlib, upstream `WeilConjectures`, the exact side framework,
  and `lean/Sheaf` used `rightDerivedUpperShriekBaseChangeMap`, exceptional/open patterns,
  and intrinsic pullback/derived/realization comparisons. They found the etale
  canonical map, the already published intrinsic pullback interface reused above,
  and the reduction-to-proper theorem, but no existing declaration stating both
  pro-etale clauses of this node. I opened the relevant hits rather than accepting
  a name match. The search wrapper records these queries in `searches.jsonl`.

The repairs change reuse and proof-plan imports only. Neither main theorem signature,
coefficient class nor canonical-map construction was weakened or otherwise changed.

Source-label check: the realization/direct-image helper docstrings cited Tag 03DA
(the abelian module category), where the direct-image construction is Tag 03D1.
I corrected those labels and cited Tag 03D3 for its module adjunction. I also read
Stacks 099R and 09AF directly in `proetale.tex`: comparison is site inclusion,
and its extension-by-zero comparison is the unique left-adjoint comparison of
the literal localization identity. These confirm the construction used here.

The inverse-image repair reexports the original arbitrary-ring site and module
constructions through the published operations imports. Its finite-coefficient
realization helpers do not remove or redefine those general constructions.

Final second-reader validation: the prescribed direct six-file `scompile.py`
check passed with no errors or non-sorry warnings. After the reuse and proof-import
repairs, `deliver2.py NY cor-exc-base-change-open-immersion-general --no-push`
printed `OK (dry run): commit 31fd3e7a5d passes the preflight and compiles;
nothing pushed`. That dry run compiled all six repaired modules separately.
The signature/declaration-list and 100-character Lean line-width checks also pass.
The final delivery wrapper recompiles the final sources, including the corrected
documentation labels, before pushing.

## Returned compilation repair (2026-10-16)

The immutable-head check reported unknown `sfFixedDerivedPullback` and
`upperStarCompIso` in `SfFiniteOpenExtensionBaseChange`. The exact termwise
derived-pullback abbreviation now belongs to `SfIntrinsicRealizationTransport`,
the module of `def-weil-proetale-inverse-image`; it is removed from the exceptional
module and its declaration ownership records are updated. The extension-by-zero
module imports that inverse-image module and the finite-coefficient
`UpperLowerStar.Iso` module directly. The latter defines the canonical
`upperStarCompIso` used in both square constructions. Thus this module no longer
relies on the exceptional-functor module for its pullback or coherence prerequisites.
No theorem statement, hypothesis, canonical-map formula or proof was changed.

The current published `Sheaf.Paper.FiniteExceptionalInverseImage` was also read
through `scompile.py --source`. It now gives the intrinsic transported formula
directly, using Nagata compactifiability over a field. The retained dependency
module exposes this same construction on a specified compactification, the
base-changed compactification, and their canonical exceptional comparison; these
are the additional interfaces needed by this item. Its node note now describes
that current interface rather than the earlier legacy-category record.

Returned-repair verification: the prescribed six-file `scompile.py` run completed
with exit code 0. Every delivered module compiled separately, both in its sandbox
check and at its library module name. There were no compiler errors or non-sorry
warnings. In particular `SfFiniteOpenExtensionBaseChange` compiled against the
directly imported inverse-image and square-comparison interfaces.

## Second reading by NY

This reading is independent of the worker and of the superseded earlier reading above.
I opened the current DAG node, all six delivered modules, every statement-dependency
record and its actual declaration, the source blueprint node and enclosing unit (b)/(c),
and the source places used by the dependency repairs. There is no new node and no
`statement_change` in this delivery. The already-reviewed natural statement is unchanged.

### Objects, hypotheses, conclusions, and verdicts

| Node item | Lean rendering and verdict |
| --- | --- |
| Prime, finite extension, positive coefficient level | `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`, and `Padic.coefficientExtensionRing l E (n + 1)`. I read the coefficient-finiteness signature; its conclusion supplies the instance, rather than an extra hypothesis. Every positive level occurs. Match. |
| Ambient geometric base, with l invertible | `S X Y : Scheme.{u}`, the two `Over S` instances, and `_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x)`. These are exactly the geometric data in `def-weil-ambient-exceptional-adjoint`. Match. |
| Finite-type structure maps and separated finite-type S-map | Each `LocallyOfFiniteType`/`QuasiCompact` pair is finite type; `[f.IsOver S]` supplies the S-map condition and `[IsSeparated f]` separatedness. No Noetherian or qcqs assumption on S. Match. |
| Supplied compactification and ambient adjunction | `c : Compactification f` and `D : SfAmbientExceptionalRightAdjointDatum A f c`. I read all fields of the datum: FullCD for c, actual adjunctions for every compactification, and refinement comparisons with unit/counit, identity, and composition equations. The theorem uses this datum, rather than mere existence of an unrelated right adjoint. Match. |
| Arbitrary open base change | `{Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g]`. Neither `QuasiCompact g` nor finite type of Y'/S is assumed. In particular affine opens and the identity are included. Match. |
| Cartesian X', g', f' | The theorem uses `pullback f g`, its `fst` and `snd`, and `IsPullback.of_hasPullback f g`. I opened `ChosenCartesianSquare.isoPullback`, `hom_fst`, and `hom_snd`; these identify any node square with this representative preserving both projections. The map definitions themselves accept arbitrary `IsPullback` squares. Match. |
| Ordinary pro-etale module derived categories | The recorded `proEtaleDerivedCategory` is the ordinary unbounded localization of intrinsic constant-ring module sheaves. `sfIntrinsicDerivedEquivalence` is induced by the specified published realization, not a freely chosen equivalence. The fixed-scalar `ModuleCat.{u+1} (ULift A)` coordinates used in the comparisons describe those same categories. Match. |
| Restricted FullCD and base-changed adjoint | The existential conclusion supplies the same `c_cd` in both `sfFullCohomologicalDimension` predicates and `D'` at `c.ofIsPullback ...`. I read the FullCD definition: both vanishing clauses quantify over all original-source sheaves, including their pullbacks to every small-pro-etale base change. Match. |
| Canonical ambient exceptional comparison is invertible | `sfFixedCompactSupportExchange` pastes the actual ordinary direct-image mate and the canonical open-extension exchange. `sfAmbientExceptionalOpenComparison` is `mateEquiv` of its inverse, under `sfFixedAmbientAdjunction A D c` and the corresponding D' adjunction. These adjunctions transport the supplied units and counits through the uniquely normalized realization comparison. `hEx` is a proof for this already defined map, not data specifying a replacement map. The concluding `IsIso` is on the entire natural transformation. Match. |
| Independent algebraic closure of a finite field | `Dk : WeilConjectures.FiniteFieldDatum.{u}` gives a finite field of cardinality p^a and its specified algebraic closure. `_hl : l ≠ Dk.p` is exactly the characteristic restriction. Match. |
| Independent finite-type k-schemes and k-map | Both `Over (Spec (CommRingCat.of Dk.k))` structures, their finite-type pairs, `f.IsOver`, and separated finite type of f are present. There is no ambient datum hypothesis. The arbitrary compactification c specifies the formula; its existence is Nagata under these hypotheses. Match. |
| Constructible exceptional inverse image | `sfFiniteExceptionalFixed A c` is literally `Rν_* ⋙ Etale.rightDerivedUpperShriek ⋙ Dν^*`; `sfFiniteExceptional` conjugates it by the specified realization. I read the newly published `Scheme.finiteExceptionalInverseImage`: it uses the same composite with compactifiability supplied over a field. The repair exposes the specified c and its base change needed by the map. Match. |
| Every etale-origin sheaf in degree zero | The first `_hK` disjunct gives F in `(comparisonUpperStar ... Y).essImage` and an isomorphism from `(DerivedCategory.singleFunctor _ 0).obj F` to K. I read Mathlib `Functor.essImage`, whose data are precisely an etale object and an isomorphism. There is no finiteness or constructibility restriction on F. Match. |
| Every bounded constructible complex | The second disjunct applies the recorded `intrinsicFiniteTorsionConstructible` to K's canonical realization. Its body requires finite support of nonzero cohomology and constructibility in every integral degree. Thus arbitrary shifts are included, and neither a finite-Tor condition nor concentration in degree zero is added. Match. |
| Canonical independent comparison is invertible | `IsIso (sfFiniteExceptionalOpenComparison A (IsPullback.of_hasPullback f g) c K)`. Its definition pastes the actual site-square pullback comparison, the published etale exceptional mate, and the derived open-restriction/direct-image comparison, with source g'^*Rf!K and target Rf'!g^*K. I read `Etale.rightDerivedUpperShriekBaseChangeMap`: it is the mate of the inverse compact-support exchange, in this orientation. Match. |
| Quantifiers and affine specialization | The ambient datum precedes arbitrary g; the independent clause quantifies over all c, g, K in its two classes. Choosing a compactification imposes no additional geometric restriction in the field clause. Every affine-open inclusion is already an allowed g. Match. |

### Dependency modules and source reading

No new definition node needs a stage-1 audit. The five dependency modules were checked
against their own nodes and current recorded interfaces, not only against this consumer.

* `SfIntrinsicRealizationTransport`: the general site/ring/module constructions of
  `ProEtaleInverseImage` remain reexported. I read its actual sectionwise direct image,
  coefficient structure map, and tensor inverse image. The delivered module reuses
  the existing `sfIntrinsicPullback`; it adds its adjunction and uniquely normalized
  direct-image comparisons. The scalar-unit equation determines the underived map,
  and the K-injective representative equation determines the derived map. The choices
  use `∃!`, and no object is chosen from unconstrained existence. Match.
* `SfFiniteExceptionalInverseImage`: the fixed-scalar and intrinsic formulas are the
  source's finite-level formula. The recorded field-based interface does not expose
  a specified compactification/base-change comparison. The repair adds those actual
  maps; it does not introduce a new notion of exceptional inverse image or assert
  unrestricted pro-etale adjointness. Higher coefficient transitions are not consumed
  or replaced. Match to the finite-level dependency used here.
* `SfFiniteOpenExtensionBaseChange`: I read the upstream construction and its smaller
  replacement. The underived map is the conjugate of the direct-image mate, in the
  reverse direction to the node; the delivered derived isomorphism takes its inverse.
  Both open immersions and the cartesian condition are present. Exact termwise
  descent covers every complex, without boundedness. The original import closure
  uses legacy names that collide with the finite-coefficient framework; the repair
  uses that framework directly. Match.
* `SfClassFullCohomologicalDimension`: I read both the published definition and the
  replacement. Both absolute and every small-pro-etale-base-change clauses retain
  the same original-source etale-origin sheaf quantifier, followed by its pullback.
  Canonical pullbacks replace arbitrary representatives without changing the predicate.
  The source's explanatory identification with all constructible sheaves is false
  for infinite constant modules; the defining etale-origin clauses are retained and
  the existing report explicitly records that source fault. No dependency statement
  is changed here. Match to the defining clauses.
* `SfConstructibleExceptionalAdjointDischarge`: I read the source proof and enclosing
  unit (c), which expressly quantify over every bounded-below etale-origin test and
  every bounded-below target. Its relative counit gives precisely the Hom map whose
  bijectivity is asserted, with target naturality and the FullCD_cls(2d) input. The
  published interface only exposes bounded constructible tests; the repaired one
  retains the larger source-specified class needed for infinite degree-zero sheaves.
  The canonical comparison is defined independently of this existential counit.
  Match.

I read Stacks `proetale.tex` section-morphism (09A5), section-comparison (099R),
lemma-jshriek-comparison (09AF), and `more-etale.tex` lemma-shriek-proper-and-open
(0F7B). The latter permits bounded-below torsion cohomology, or a torsion ring on
all complexes; the finite coefficients here satisfy this source condition. The site
comparison square and the literal restriction identity give the comparison factors
used in the finite formula. The blueprint node and unit supply the two distinct
ambient and relative scopes; no unrestricted conclusion is inferred from unit (c).

### Edge cases and conventions

The empty scheme and the zero sheaf/complex remain allowed; no point or nonzero
section is chosen. The identity open is included and the ambient clause admits
non-quasi-compact opens. In the field clause quasi-compactness of opens follows
from Noetherianity, without an added binder. The Lean index n=0 means coefficient
level 1, and all positive levels are covered. Prime 2 is included; l=p is excluded
only where the source excludes it. Infinite etale-origin sheaves and bounded
constructible complexes in arbitrary degrees are included separately.

The scheme/site universe is u, site objects are in u+1 and morphisms in u, and module
values are in u+1 with the canonical ULift of the coefficient ring. No equality
between object and morphism universes is imposed. All variables are bound under
`autoImplicit false`. All theorem bodies remain `sorry`; definitions have real data,
with proof prerequisites named separately and listed in their owning node records.
The main proof docstrings cover respectively Steps 1–4 and 5–7 of the node. The
primary `lean.statement` strings are verbatim signatures, and all declaration names
are listed in their records. No local notation, private definition, or local instance
is introduced. The earlier dependency declaration ownership repair is retained.

### Searches, mismatches, and changes in this reading

Fresh prescribed searches with wording different from the worker's:

* LeanFinder: `Open localization Beck Chevalley for right adjoints to compact support
  on proetale sheaves` returned eight ordinary sheaf-adjunction/restriction results,
  with no theorem matching these exceptional clauses.
* Loogle: `CategoryTheory.mateEquiv` returned the generic mate API, including unit,
  counit, and composition identities. I opened the actual etale canonical-map use.
* LeanSearch: `Right adjoint of compactly supported derived pushforward commutes with
  restriction to an open subset` returned eight underived adjunction/restriction
  declarations, with no matching theorem.
* Independent `rg` searches over Mathlib, slopmaster2, shared `lean/Sheaf`, and the
  exact side `lean/WeilConjectures` used upper-shriek/base-change, exceptional/open,
  and intrinsic-realization/direct-image patterns. The relevant hits were the etale
  mate, the existing intrinsic operations, and the proper-case reduction; none states
  both clauses of this node. These existing constructions are used. Wrapper query
  evidence is appended in `searches.jsonl`.

I found no signature or canonical-map mismatch needing a mathematical change.
I corrected stale module-docstring blueprint orders 1475 → 1489 in
`SfFiniteExceptionalInverseImage` and 1558 → 1583 in
`SfFiniteOpenExtensionBaseChange`, verified against their source front matter.
I added the prescribed main-declaration summaries to the four modules with multiple
constructions/statements. No Lean term, theorem signature, node mathematical field,
or declaration ownership changed during this reading. The worker report stays intact.

The final tag-table cross-check also found that `03S9` is an obsolete tag for an
unrelated etale-cohomology remark, not this extension-by-zero construction. I replaced
its citations in `SfFiniteOpenExtensionBaseChange` by the actual source places of
its constructions: 09A5 (inverse-image square), 0B65 (adjunction conjugation), 04J0
(ringed-site localization), 09AE (pro-etale extension by zero), and 015F (exact
termwise derived descent). These are documentation repairs; all terms and signatures
are unchanged. The final compile and dry run include these corrected sources.

Final validation for this second reading: the prescribed six-file `scompile.py` run
returned exit code 0. Local validation encountered a missing shared-overlay
`ProEtaleConstantDerivedDirectImage.olean`; the wrapper's authorized current-server
confirmation compiled all six delivered files and the required side dependencies
cleanly, with nice 19, two threads, and the unchanged 60-second per-file limit.
No compiler error or non-sorry warning remained. The longest delivered file in
that confirmation took 15.7 seconds; the main module took 7.6 seconds.
The prescribed `deliver2.py NY cor-exc-base-change-open-immersion-general --no-push`
returned `OK (dry run): commit 11b46aac35 passes the preflight and compiles; nothing
pushed`. This includes the corrected source citations. The final delivery wrapper
will recheck the complete source/report snapshot before pushing.
