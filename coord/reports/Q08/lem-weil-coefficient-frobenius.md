## Worker report

The delivery states `lem-weil-coefficient-frobenius` in
`Sheaf.Paper.CoefficientFrobenius`, namespace `WeilConjectures`. All five
statements have proof `sorry`; no mathematical theorem is proved. Their
source/proof docstrings together reproduce all ten DAG proof steps, with
finite-presentation biduality, the DVR obstruction, the length-one integral
resolution, signed derived evaluation, and the finite-Tor application.
The original statement is unchanged. No statement dispute was found.

Hypotheses and clauses are rendered as follows.

- A prime ell is `(l : ℕ) [Fact l.Prime]`. A finite extension E/Q_l is
  `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Positive quotient levels are
  `(n : ℕ) (hn : 1 ≤ n)`. Coefficients are exactly the recorded
  `Padic.coefficientExtensionRing l E n` and
  `Padic.coefficientExtensionIntegers l E`, not abstract substitute DVRs.
  The coefficient theorem is algebraic, so its statement has no scheme,
  residue-characteristic exclusion, or global finite-field parameter that
  does not occur in these algebraic assertions.
- Clause 1 is `coefficient_frobenius`: a conjunction of
  `coefficientFrobeniusProperties` for A_{E,n}, E, and
  `AlgebraicClosure (Padic l)`. The algebraic closure is the ordinary
  algebraic coefficient field, not a topological or continuous dual.
- Unfolding that predicate: `Module.Injective.{u,u} R R` is precisely
  injectivity as a module over itself in the common-universe convention
  of `lem-sf-baer-criterion`. `IsArtinianRing R` means the descending-chain
  condition on submodules of R, which are the ideals in this commutative
  setting. The two together are exactly the node's quasi-Frobenius
  convention. This condition does not occur in the general derived theorem.
- Ordinary exactness quantifies over ALL `M N P : ModuleCat.{u} R`, with
  linear maps `f`, `g` satisfying `Function.Injective f`,
  `Function.Exact f g`, `Function.Surjective g`. Its conclusion has the
  same three conditions on `g.dualMap`, `f.dualMap` in reverse order.
  This is exactness of `Hom_R(-,R)` on short exact sequences, including
  infinite modules, not merely preservation of injections or a finite case.
- Preservation of finite modules is
  `∀ M, Module.Finite R M → Module.Finite R (Module.Dual R M)`.
  The same clause requires `Function.Bijective (Module.Dual.eval R M)`.
  Evaluation is the actual linear evaluation map x |-> (f |-> f(x));
  bijectivity of this linear map is equivalently a module isomorphism.
- Derived anti-equivalence is an existential functor from the opposite of
  the FULL bounded finite-cohomology subcategory to that same subcategory,
  with `F.IsEquivalence` and a natural isomorphism identifying its inclusion
  into D(R) with the full inclusion followed by `coefficientDerivedDual R`.
  Thus this is an anti-equivalence by the specified derived dual, not an
  unrelated equivalence or just individual object isomorphisms.
- Clause 2's ordinary distinction is
  `integral_coefficient_ordinary_duality`. Its first conjunct negates
  `IsArtinianRing O_E ∧ Module.Injective O_E O_E`. Its second quantifies
  over `Module.Finite O_E M` AND `Module.Projective O_E M` and asserts
  bijectivity of the actual ordinary evaluation. Its third supplies a
  finite module whose ordinary evaluation is not bijective. The source
  witness O_E/(pi) is recorded in its proof docstring.
- Clause 2's derived assertion is `integral_coefficient_derived_duality`.
  `hK : boundedFiniteCoefficientComplex O_E K` imposes bounded cohomology
  and `Module.Finite O_E (H^i K)` in every degree. The conclusion is
  `DerivedCategory.IsPerfectRingComplex K ∧
  IsIso (coefficientDerivedEvaluation K)`, using the recorded perfectness
  predicate. There is no finite-Tor or self-injectivity hypothesis here.
- Clause 3 is `perfect_coefficient_derived_evaluation`, over an arbitrary
  `(R : Type u) [CommRing R]` with only the recorded perfectness predicate
  on K. This follows the node's explicit commutative-ring convention for
  the words "any ring"; no Noetherian, local, or injectivity condition is
  added. The conclusion is `IsIso` of the canonical derived evaluation.
- The final point consequence is additionally stated as
  `finiteTor_point_coefficient_evaluation` for positive finite coefficients,
  bounded finite cohomology and `DerivedCategory.finiteTorAmplitude`.
  This is the algebraic point condition: tensoring with any module in
  degree zero has cohomology in one finite interval. At field stages the
  anti-equivalence already covers every bounded finite-cohomology object;
  the integral derived theorem already covers every such integral object.

The new definition module's `boundedFiniteCoefficientComplex` uses
`DerivedCategory.TStructure.t.bounded` and `DerivedCategory.homologyFunctor`.
Its dual is the upstream monoidal closed `internalHom` specialized to the
unit R[0]. That closed structure right-derives Hom using K-injective
resolutions, the module/one-object case of the recorded derived-internal-Hom
notion. Evaluation is `MonoidalClosed.curry` of the composite of the canonical
`DerivedMonoidal.braiding Qh (HomotopyCategory.quasiIso ...)` and `ihom.ev`.
This is the formula of upstream `MonoidalClosed.toIhomIhomUnit`, specialized
to that constructed Koszul braiding, without a `Nonempty` choice.
The helper interface explicitly binds `HasDerivedCategory.{u} (ModuleCat.{u} R)`;
for module categories this is supplied without an added hypothesis by
`HasDerivedCategory.ofIsGrothendieckAbelian`. In particular the theorem
statements do not assume a derived-category existence axiom. They use this
natural small-Hom localization rather than the larger `standard` localization.

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, publicly importing the actual
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, and `coefficientExtensionRing` constructions.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`,
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`, and
  `Sheaf.Paper.SfIntegralConstructible`,
  `WeilConjectures.sfIntegralConstructible`, identify the coefficient stages
  mentioned in the node. Their recorded signatures were read; the purely
  coefficient assertions require no geometric object from them.
- `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`;
  `Mathlib.Algebra.Module.Projective`, `Module.Projective`;
  `Mathlib.Algebra.Module.Injective`, `Module.Baer.iff_injective` and the
  `Module.Injective` extension condition; `Mathlib.RingTheory.Artinian.Defs`,
  `IsArtinianRing`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`,
  `DerivedCategory.IsPerfectRingComplex`: exactly a bounded finite-projective
  model, with independent localization universe. The natural localization
  here specializes that general interface; no private perfectness predicate.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses`: the ringed-site Hom-complex
  localization and its comparison with K-injective representatives. Its
  signature was read without replacing the general-site interface; the
  module-category closed structure supplies the one-object case here.
- `Sheaf.Paper.FiniteTorAmplitude`,
  `WeilConjectures.finiteTorConstructible` and
  `WeilConjectures.finiteTorConstructibleIntegral`, identify the geometric
  finite-Tor categories mentioned in the final convention. On coefficient
  module complexes the actual tensor-test predicate is the upstream
  `DerivedCategory.finiteTorAmplitude` from
  `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`.
- `WeilConjectures.CategoryTheory.DerivedCategory.Perfect` and
  `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory` supply
  the canonical derived tensor--Hom structure; its underlying localization
  is Mathlib's `DerivedCategory` (`def-weil-abstract-derived-category`).

Edge cases checked: n=1; n=0 is outside the positive-stage assertion;
zero finite modules and zero perfect complexes; an empty cohomological
support (the zero complex); torsion modules O_E/(pi) in contrast with
finite projectives; infinite fields E and Qbar (finite means finitely
generated, never finite underlying set); and arbitrary commutative rings,
including the zero ring, in the perfect-complex assertion. No self-injectivity
or regularity hypothesis has slipped into the last assertion. Signed
Koszul evaluation is required; an unsigned degreewise map would generally
not be a chain map.

Searches made with the prescribed msearch wrapper:

- LeanFinder: "Ordinary duality for finitely generated modules over self
  injective Artinian rings and derived evaluation for perfect complexes".
  Eight hits: `FGModuleCat.exactPairing` and related field-only rigid
  results, plus `Module.dual_projective`/`Module.dual_finite`. None states
  the finite, integral and general derived assertions together.
- Loogle: `Module.Injective, Module.Dual`: zero hits.
- Mathlib grep: `bidual|quasi.?Frobenius|self.?injective`: unrelated normed
  double-dual results and function-injectivity lemmas, no full match.
- LeanSearch: "derived coefficient duality exact anti equivalence bounded
  finite cohomology Artinian self injective rings": unavailable (HTTP
  Internal Server Error), recorded as unavailable, not as negative evidence.
- LeanFinder: "Bounded derived category of modules with finitely generated
  cohomology and coefficient duality Hom into the coefficient ring": eight
  Ext/cohomology hits, no specialized category/duality definition package.
- Mathlib grep in CategoryTheory/Monoidal:
  `boundedFiniteCoefficient|coefficientDerived|coefficientFrobeniusProperties|toIhomIhomUnit|internalHom`:
  finds `MonoidalClosed.internalHom`, which is reused.
- Direct upstream grep for the item id: no declaration for this item.
  Concept/name searches in upstream WeilConjectures and project lean/Sheaf
  found the existing generic perfect-biduality API; it is reused to define
  the canonical map, not replaced by chosen data. No exact existing full
  statement was found. `blueprint_refs.py search` for "coefficient duality"
  and "bounded finite" found this item and geometric consumers, no matching
  definition package.
- Current server source checks for
  `Sheaf.Paper.PointFiniteCohomologyComplexes`,
  `Sheaf.Paper.PointFgCompleteComplexes`, and `Sheaf.Paper.PointFdComplexes`:
  the first requires finite underlying sets, the second additionally
  requires derived completeness, the third is field-specific. They do
  not define the arbitrary-ring bounded finitely generated-cohomology
  category needed here. In particular replacing finite generation by
  `Finite` would incorrectly exclude the E and Qbar cases.

## New nodes

`def-sf-coefficient-duality` defines the bounded finite-cohomology full
subcategory, the coefficient dual and its canonical derived evaluation,
and a predicate packaging exactly the first clause's Frobenius-duality
assertions. Its source is the assigned blueprint node, with Stacks 08J7,
07VI and 0AVF. The module reuses Mathlib/upstream module duals, localization,
closed structure, and Koszul evaluation. The definition package is absent
from the DAG/Mathlib/project searches above. No new assumption is introduced,
and no data is postponed with `sorry`. The main node gains only this
statement dependency and its `lean` record.


## Earlier second reading (a previous round; superseded)

I independently opened the assigned node, both delivered modules, the new
node, the recorded statement-dependency signatures, and the following source
places. The blueprint markdown is not materialized in this checkout; the
imported node and its unit remark retain its text and source attribution.
I read the Stacks TeX at Tags 0AVF (more-algebra,
lemma-characterize-injective-bis), 066Z (lemma-regular-perfect), 066U
(lemma-cohomology-perfect), 07VI (lemma-dual-perfect-complex), 0A66
(lemma-RHom-out-of-projective), and 08J7 (sites-cohomology,
section-internal-hom). These assume a ring, or a ringed site, without
Noetherianity for derived Hom or perfect biduality. Tag 066Z assumes
regularity; the node correctly supplies its DVR specialization through a
finite-free resolution rather than assuming regularity of an arbitrary ring.

Object/hypothesis/conclusion checklist, with the node and Lean side by side:

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. Finite extension E/Q_l:
   `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`. Verdict: exact coefficient datum;
   no finite underlying-set hypothesis on E. There is no geometric object
   in this algebraic node, so no scheme, separation, global characteristic,
   or invertibility instance is needed.
2. Positive quotient level n: `(n : ℕ) (hn : 1 ≤ n)`.
   A_{E,n} is `Padic.coefficientExtensionRing l E n`; O_E is
   `Padic.coefficientExtensionIntegers l E`. I read CoefficientExtension
   and CoefficientExtensionFinite: the former uses the spectral absolute
   value, its actual integer subring, the chosen uniformizer, and the
   quotient by its nth-power principal ideal. The latter publicly imports
   these definitions and states positive-level finiteness. Verdict: same
   rings as the dependency node, rather than substitute abstract rings.
3. The algebraic closure coefficient stage is
   `AlgebraicClosure (Padic l)`. Verdict: an algebraic closure of Q_l;
   no topology or continuous dual is introduced. All the field assertions
   are algebraic and invariant under choosing another algebraic closure.
4. Self-injectivity and quasi-Frobenius for all three stages:
   `coefficient_frobenius` asserts `coefficientFrobeniusProperties` for
   A_{E,n}, E, and that algebraic closure. Its first clauses are
   `Module.Injective.{u,u} R R ∧ IsArtinianRing R`. I read the extension
   condition in Module.Injective and the common-universe Baer dependency;
   IsArtinianRing is DCC on submodules of R, hence on ideals. Verdict:
   exactly the node's stated commutative quasi-Frobenius convention.
5. Exact ordinary duality on all modules: the predicate quantifies over
   `M N P : ModuleCat.{u} R`, arbitrary linear maps f and g, and
   `Function.Injective f → Function.Exact f g → Function.Surjective g`.
   It concludes the same three assertions for `g.dualMap`, `f.dualMap`
   in reverse order. Verdict: all short exact sequences, including
   infinite modules; the finite restriction appears only in the next clause.
6. Preservation of finite modules and canonical ordinary biduality:
   `∀ M, Module.Finite R M → Module.Finite R (Module.Dual R M) ∧
   Function.Bijective (Module.Dual.eval R M)`.
   The Finiteness.Defs definition is finite generation of the top submodule;
   Dual.eval really sends x to the functional f ↦ f x. A bijective linear
   evaluation is the required linear isomorphism. Verdict: exact, including
   finite-dimensional modules over infinite fields.
7. Derived anti-equivalence on bounded finite cohomology:
   `boundedFiniteCoefficientComplex R` is `TStructure.t.bounded K` and
   `∀ i : ℤ, Module.Finite R ((homologyFunctor _ i).obj K)`.
   The predicate's final existential F runs from the opposite FULL
   subcategory into itself, requires `F.IsEquivalence`, and identifies its
   inclusion naturally with inclusion followed by `coefficientDerivedDual R`.
   Verdict: the specified dual restricts to the anti-equivalence; this is
   stronger than an unrelated equivalence or individual chosen isomorphisms
   in exactly the way the node requires.
8. Integral ordinary distinction:
   `integral_coefficient_ordinary_duality` negates
   `IsArtinianRing O_E ∧ Module.Injective O_E O_E`, requires canonical
   ordinary evaluation to be bijective for every finitely generated
   projective module, and exhibits a finitely generated module where it is
   not bijective. Verdict: all three integral ordinary clauses, with no
   accidental assertion that every finite integral module is reflexive.
9. Integral derived distinction:
   `integral_coefficient_derived_duality` takes any K with the bounded
   finite-cohomology predicate, and concludes
   `DerivedCategory.IsPerfectRingComplex K ∧
   IsIso (coefficientDerivedEvaluation K)`. I opened
   PerfectRingComplexGeneral: its data are exactly a bounded finite
   projective model, with an independent localization universe. Verdict:
   no derived-completeness or finite-Tor hypothesis restricts the node's
   arbitrary bounded finite-cohomology integral K.
10. General perfect evaluation:
    `perfect_coefficient_derived_evaluation (R : Type u) [CommRing R]`
    takes only `DerivedCategory.IsPerfectRingComplex K` and concludes
    invertibility of the canonical derived evaluation. Verdict: arbitrary
    commutative coefficients as explicitly stipulated by the node, without
    Noetherianity, locality, nontriviality or self-injectivity.
11. Finite-Tor point consequence:
    `finiteTor_point_coefficient_evaluation` takes positive finite
    coefficients, bounded finite cohomology, and the upstream
    `DerivedCategory.finiteTorAmplitude` tensor-test predicate. I opened
    TorAmplitude: it tests against every module in degree zero over one
    interval. It concludes canonical evaluation is invertible. At O_E the
    preceding integral result applies even without finite Tor; the field
    stage is already covered by the bounded finite-cohomology duality.
    Verdict: the point consequence uses perfectness rather than a new
    injectivity hypothesis. An ordered interval can always be obtained by
    widening the upstream interval, including for the zero object.

Canonical-map and new-node audit: `def-sf-coefficient-duality` introduces
only the common-ring bounded finitely generated cohomology predicate, the
specialization of the existing internal-Hom functor to R[0], its evaluation,
and the conjunction of clause 1. Its cited dependency ids are exactly those
used in its self-contained statement; created, chapter/unit, blueprint
ancestor/via, search fields, and empty proof fields satisfy §5.
I checked the ancestor using blueprint_refs.py. I opened the recorded
derivedInternalHomOfUniverses interface and the upstream monoidal closed
derived-category interface. The latter gives the equivalent one-object
module internal Hom. `coefficientDerivedDual` specializes this existing
bifunctor, and `coefficientDerivedEvaluation` uses `MonoidalClosed.curry` of the actual
`DerivedMonoidal.braiding` for Qh followed by `ihom.ev`. This is the formula
of `MonoidalClosed.toIhomIhomUnit`: Koszul interchange followed by evaluation,
exactly the canonical signed map in 07VI. This construction was expanded in
the timeout repair described below; the fresh second reader must recheck it. There is no arbitrary map, unspecified isomorphism, or chosen
Nonempty datum. The HasDerivedCategory.{u} helper parameter is discharged
in the main signatures by the module-category Grothendieck localization
instance; it is not an extra mathematical assumption. All definitions
have actual data and none contains sorry. There are no dependency modules.

Edge cases: n=1 is included and n=0 is correctly excluded by the coefficient
definition. The prime 2 is not excluded. Zero modules, the zero complex,
and empty cohomological support are included; finite generation allows an
empty generating list. The general perfect theorem includes the zero ring.
Infinite modules are allowed in exactness, infinite fields in the field
stages, and arbitrary commutative rings in clause 3. There is no indexed
family or scheme binder, so no empty-index or empty-scheme case is silently
lost. All universes and variables are explicitly bound under autoImplicit
false. The common module/ring universe follows the recorded Baer interface;
no equality between distinct site universes is imposed.

Independent searches:

- LeanFinder: “Canonical double dual morphism on perfect derived module
  complexes and dual equivalence for modules over Frobenius local rings”.
  Eight hits, including FGModuleCat.exactPairing and ordinary perfect
  pairing APIs; these cover field/ordinary special cases, not this node.
- Loogle: `Module.Dual.eval`. Twelve hits, including the actual evaluation,
  its naturality and reflexivity criteria. These are reused via the
  existing ordinary dual, not redefined.
- LeanSearch: “Artinian principal ideal rings are self injective and finite
  modules are reflexive”. Service unavailable (Internal Server Error);
  recorded as unavailable, not evidence of absence.
- Grep via msearch and direct rg with `quasi.?Frobenius`, `self.?injective`,
  `bounded.*finite.*cohomology`, `coefficient.*dual`, and
  `toIhomIhomUnit`, across Mathlib, upstream and project Lean. Found the
  upstream generic perfect-complex biduality theorem
  `DerivedCategory.IsPerfect.isIso_toIhomIhomUnit`; the present clause 3
  specializes its arbitrary-braiding interface to the actual canonical
  coefficient evaluation and the recorded general perfect predicate.
  It is not a full match for the assigned multi-clause coefficient node.
  The underlying dual and evaluation constructions are reused directly.
- Opened the project PointFiniteCohomologyComplexes, PointFgCompleteComplexes,
  PointFdComplexes and CoefficientCohomologyModules modules. Respectively
  they require finite underlying sets, add derived completeness, or require
  a field. None defines the arbitrary-ring bounded finite-generation
  subcategory needed for both clauses 1 and 2. The cohomology-module module
  restricts the existing homologyFunctor to these same categories.
- blueprint_refs searches “bounded finite cohomology” (no matching node)
  and “coefficient duality” (assigned node and geometric consumers) found
  no existing general coefficient-duality package. Exact declaration-name
  searches found no collision in Mathlib, upstream, or the project.

Mismatches and repairs: no mathematical statement mismatch, node correction,
or missing definition/dependency was found. I removed the three unused
geometric category imports from CoefficientFrobenius and imported the actual
upstream algebraic TorAmplitude module directly. I also removed the unused
ringed-site derived-Hom import from CoefficientDuality: its actual module
derived-Hom construction is supplied by the upstream closed structure already
provided by the explicit derived-monoidal and closed-structure imports. I added ordinary imports
for the available finite-presentation, K-injective, K-projective, exact
homology/derived-functor, finite-projective dual, DVR-free-module and
finite-quotient proof dependencies, as required by the stage-2 import rule.
The mathematical signatures and node statement are unchanged. Every theorem
still has exactly a sorry proof. Module/declaration source and blueprint
docstrings, all ten natural-language proof steps, 100-character line width,
and both primary lean.statement strings were checked against the files.

Historical validation of the returned version, before this repair: the prescribed scompile.py invocation
listed both sibling modules. Its current-source server confirmation compiled
CoefficientDuality in 26.0 seconds and CoefficientFrobenius in 2.0 seconds,
with nice 19, two threads, the unchanged 60-second limit, and no warnings.
The local check had timed out under shared load; the authorized wrapper's
server confirmation returned exit 0 for the final sources.


## Repair of return L (2026-10-16)

The immutable head 50f560477dd0 was returned because preliminary compilation
of CoefficientDuality exceeded 60 seconds. This repair changes its actual
construction, rather than retrying unchanged source.

Profiling the returned implementation showed negligible elaboration cost but
about 52 seconds in kernel type checking locally (about 28 seconds on server
confirmation). Removing the unneeded Perfect import and spelling out only
the double-internal-Hom target did not remove the costly check. The final
construction directly curries the composite of
`DerivedMonoidal.braiding Qh (HomotopyCategory.quasiIso ...)` and `ihom.ev`.
It thereby avoids passing the entire concrete braided-category structure to
`MonoidalClosed.toIhomIhomUnit`. This is precisely that upstream definition's
formula, not a different or chosen biduality arrow. The target is written as
nested `ihom` into the tensor unit; unfolding `coefficientDerivedDual`,
`Functor.flip`, and `MonoidalClosed.internalHom` identifies it with the
previous double-dual target. No node statement, hypothesis, mathematical
conclusion, or theorem signature has changed.

CoefficientDuality now imports the t-structure, derived monoidal construction,
flat-resolution interface and closed-structure instances (including generic
currying) directly. The rigid-biduality import is no longer needed and is removed. The perfect-complex predicate and algebraic-closure imports
are in CoefficientFrobenius, where they are used. There are no new declarations,
postponed construction data, instance hypotheses, or extra axioms.

The diagnostic scratch copy with the final formula completed both local
checks in 14.1 and 23.4 seconds; kernel checking took 8.6 and 11.2 seconds.
Profiling options remain only in scratch files and are absent from delivery
modules. Both primary lean.statement fields still match their file signatures
verbatim; all Lean lines have at most 100 characters. CoefficientDuality
contains no sorry, and the five theorem bodies remain exactly sorry.
The prior second-reading section records the earlier version; a fresh reader
must review this repair and the final validation below before delivery.


Final verification: the prescribed two-file scompile.py invocation passed all
five local preliminary/sandbox/library checks without errors or warnings.
The first delivery dry run returned OK (commit f6064765a1), passing preflight
and per-file compilation without pushing. After removing the now-unused
rigid-biduality import, both final modules are checked again and the final
dry run is repeated. Every compiler invocation retains nice 19, two threads,
and the 60-second default; no limit was raised.


## Second reading by Q08

This is a fresh reading of the timeout-repaired files. I opened the main
node, the new definition node, both modules, all recorded statement-dependency
interfaces, and the available proof-dependency interfaces. The source text is
available in the read-only archive `/home/ubuntu/work-bp/sheaf/literature/`:
I read the original blueprint markdown and Stacks `more-algebra.tex`,
lemmas characterize-injective-bis (0AVF), regular-perfect (066Z),
cohomology-perfect (066U), dual-perfect-complex (07VI), and
RHom-out-of-projective (0A66), plus `sites-cohomology.tex`, section
internal-hom (08J7). The source assumes a ring for the general perfect
assertion and a ringed site for derived Hom; it does not assume arbitrary
rings Noetherian or self-injective. The node explicitly fixes commutative
coefficients. Its DVR specialization supplies regularity through the
length-one finite-free resolution in its proof, rather than adding a
regularity hypothesis to the general assertion.

Object, hypothesis, and conclusion checklist:

1. Prime ell, finite extension E/Q_ell, and positive quotient level:
   `(l : ℕ) [Fact l.Prime]`, `(E : Type u) [Field E]`,
   `[Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, and
   `(n : ℕ) (hn : 1 ≤ n)`. Verdict: exact. The dependency
   `CoefficientExtension` defines the spectral absolute value, its actual
   integer subring, a uniformizer, and its power-ideal quotient;
   `CoefficientExtensionFinite` retains these data. No abstract substitute
   DVR or extra valued-field structure is assumed.
2. The coefficient rings are `Padic.coefficientExtensionRing l E n`,
   `E`, `AlgebraicClosure (Padic l)`, and, integrally,
   `Padic.coefficientExtensionIntegers l E`. Verdict: exact algebraic
   coefficients. The geometric constructibility dependencies introduce
   these stages but no scheme occurs in this algebraic assertion. Their
   scheme and invertibility parameters are therefore not binders here.
3. Self-injectivity and quasi-Frobenius for the first three rings:
   `coefficient_frobenius` gives `coefficientFrobeniusProperties` for each;
   its first clauses are `Module.Injective.{u,u} R R ∧ IsArtinianRing R`.
   I opened Module.Injective, Module.Baer.iff_injective, and IsArtinianRing:
   these are precisely the all-inclusions extension property and DCC on
   ideals in the common universe. Verdict: exact, no assumed injectivity.
4. Ordinary exactness: the predicate quantifies over arbitrary
   `M N P : ModuleCat.{u} R`, linear maps f,g, and injective/exact/surjective
   hypotheses; it concludes injective/exact/surjective for `g.dualMap`,
   `f.dualMap`. Verdict: exact reversal of every short exact sequence,
   including infinite modules, with quantifiers in the right order.
5. Finite dual and ordinary evaluation: for every M with `Module.Finite`,
   the predicate asserts `Module.Finite R (Module.Dual R M)` and
   `Function.Bijective (Module.Dual.eval R M)`. I opened the actual eval
   definition/property: x maps to the functional f mapping to f(x).
   Verdict: finite generation, not finite cardinality; bijectivity of this
   linear map is exactly its being a module isomorphism.
6. Derived anti-equivalence: `boundedFiniteCoefficientComplex R K`
   means `TStructure.t.bounded K` and `Module.Finite` of every integer
   homology module. The existential functor F is an equivalence between
   the opposite of this full subcategory and itself, naturally identified
   after inclusion with `coefficientDerivedDual R`. Verdict: the actual
   RHom(-,R[0]) restricts to the asserted anti-equivalence, rather than an
   unrelated equivalence or only objectwise isomorphisms.
7. Integral ordinary distinction: `integral_coefficient_ordinary_duality`
   negates Artinian self-injectivity, asserts bijective ordinary evaluation
   for every finite projective module, and exhibits a finite module whose
   evaluation is not bijective. `Module.Projective` is the recorded
   split-free-module/lifting notion. Verdict: every clause is present;
   the residue-field counterexample in the docstring is the source's.
8. Integral derived distinction: `integral_coefficient_derived_duality`
   quantifies over every K with bounded finite cohomology and concludes
   `IsPerfectRingComplex K ∧ IsIso (coefficientDerivedEvaluation K)`.
   I read PerfectRingComplexGeneral: it is exactly a bounded
   finite-projective representative. Verdict: no added finite-Tor,
   completeness, or self-injectivity hypothesis.
9. General perfect evaluation: `perfect_coefficient_derived_evaluation`
   takes any `(R : Type u) [CommRing R]` and only perfectness of K,
   and concludes `IsIso` of the canonical evaluation. Verdict: exact
   under the node's explicit commutative-ring convention, including
   non-Noetherian and nonlocal rings.
10. Finite-Tor point consequence: `finiteTor_point_coefficient_evaluation`
    takes bounded finite cohomology and the upstream
    `DerivedCategory.finiteTorAmplitude` on the finite coefficient ring.
    I opened TorAmplitude: it tests tensoring with every ordinary module
    in degree zero over one finite interval. Verdict: exact point
    condition. Unordered bounds in this upstream predicate are equivalent
    to ordered bounds by widening, also for zero objects. Integral cases
    are already covered without finite Tor; field cases are covered by
    the anti-equivalence. No self-injectivity hypothesis is added.

Canonical construction and new-node audit:
`def-sf-coefficient-duality` is a definition node in the same chapter/unit,
with the required created/ancestor/search/lean fields and empty proof fields.
Its self-contained statement describes exactly the four implemented
notions, not an extra hypothesis or theorem. I read the recorded
`derivedInternalHomOfUniverses` source and the upstream
`DerivedCategory.Monoidal.Closed` construction: the latter derives the
Hom-complex functor using K-injectives and is the module/one-object version
of 08J7. Thus reusing this existing closed structure introduces no second
independent derived Hom. `coefficientDerivedDual` specializes
`MonoidalClosed.internalHom.flip.obj` to the unit. Its double application
unfolds to exactly the nested ihom target of `coefficientDerivedEvaluation`.
I opened upstream `MonoidalClosed.toIhomIhomUnit`: its body is
`curry ((β_ _ K).hom ≫ (ihom.ev K).app (𝟙_ _))`. The delivered map is this
same body specialized directly to `DerivedMonoidal.braiding Qh quasiIso`,
whose source characterizes it as the descended Koszul braiding. Currying
has the required source D(K) tensor K and hence yields K -> D(D(K)).
The expansion avoids expensive conversion through the full braiding
structure while using its canonical arrow. No arbitrary map, Nonempty
choice, postponed construction data, or hidden proof is introduced.
`HasDerivedCategory.{u}` is an explicit helper parameter; the main
signatures discharge it by the existing Grothendieck module-category
instance, which I read. Universe u is arbitrary and common to the ring
and modules as in the Baer dependency; no extra universe equation on a
site is imposed. There are no new dependency modules in this delivery.

Edge cases: n=1 and ell=2 are included; n=0 is outside the source's
positive stages (the construction itself then gives the zero ring).
Zero finite modules, zero complexes, and empty cohomological support are
included. Finite projective modules may have rank zero. Ordinary exactness
allows infinite modules; E and its algebraic closure need not be finite
sets. The arbitrary-ring perfect theorem includes the zero ring. No index
set, scheme, or empty-scheme restriction occurs in this algebraic node.

Independent searches in this reading (msearch records them in searches.jsonl):

- LeanFinder: "Canonical morphism from a perfect complex to its double
  derived dual over a commutative ring" returned eight K-projective,
  Ext, derived-category, and double-complex hits; no whole-node match.
- Loogle: `Module.Dual.eval` returned the existing eval/reflexivity API,
  which is already used, and no finite/integral/derived package.
- LeanSearch: "Duality on bounded derived categories of finitely generated
  modules over self injective Artinian rings" succeeded with eight hits,
  including field-only FGModuleCat duality and finite projective dual
  results; these cover only parts of this node. This successful query
  supersedes treating the earlier service failure as negative evidence.
- msearch grep `Artinian|Frobenius|IsReflexive`, and direct rg with
  `quasi.?frobenius`, `self.?injective`, `coefficient.*dual`,
  `double.*dual`, and `bidual` across Mathlib, upstream, and project Lean.
  I opened upstream IsPerfect.isIso_toIhomIhomUnit: it supplies the generic
  perfect-complex clause for a chosen braiding, but neither finite-stage
  Frobenius duality nor the integral assertions. Its canonical-map formula
  is reused by specialization. No exact existing whole statement was found.
- blueprint_refs searches "coefficient duality" and "bounded finite
  cohomology", and DAG/source searches found no general coefficient
  bounded-finitely-generated category. I opened PointFiniteCohomology,
  PointFgComplete, and PointFdComplexes: they respectively require finite
  underlying sets, derived completeness, and a field. None gives the
  arbitrary commutative-ring category here. The geometric double-dual
  modules concern different sheaf categories/dualizing objects.

Mismatches and repairs in this fresh reading: no mathematical mismatch,
statement correction, or missing definition was found. Two proof modules
are now recorded and available: PerfectCohomologyAssembly and
FiniteTorAmplitudePerfect. I opened their statements and added their
ordinary imports to CoefficientFrobenius, as required by the import-plan
rule. All mathematical definitions, theorem signatures, and node statements
are retained. The primary lean.statement strings agree verbatim with the
file signatures. Both modules have bound universes and autoImplicit false,
source/blueprint docstrings and lines of at most 100 characters; the five
named theorem proofs are still sorry, with all ten proof steps in their
docstrings. No statement_change or citer audit is needed.


Fresh-reader verification: the final prescribed two-file scompile.py command
passed, including both new proof-import overlays and all five checks of the
delivered modules, with no errors or warnings. The wrapper retained its
default 60-second per-file limit, nice 19, and two threads; no limit was
changed. The earlier failed invocation used the wrong working directory;
it read no files and was immediately rerun from this sandbox successfully.
