## Worker report

The item module `Sheaf.Paper.SmoothExceptionalPreservation` states
`WeilConjectures.PurityFiniteSetting.smooth_exceptional_preservation` with `sorry`.
Its three conjuncts are the two preservation clauses and the explicit “in particular”
conclusion. The module also states the fixed-setting consequence
`PurityFiniteSetting.prime_isUnit_stalk`, needed to pass the coefficient-prime
invertibility parameter of the recorded interval definition. Its proof is `sorry`,
and its source and complete proof are in its docstring (the node's proof step 1).
The item's mathematical statement and dependencies have not been changed.

The physical source read was
`sec-six-functors/sk-prop-sf-rf-shriek-preservation/cor-pur-smooth-admissibility.md`
in the launcher's read-only literature replica, together with the current DAG
statement, all its statement-dependency statements and records, and its eight proof
steps. The source's finite-type domain has already been made explicit by stage 1;
this delivery keeps that current statement.

Hypothesis and clause correspondence:

- The fixed finite field, algebraic closure, prime different from the characteristic,
  finite coefficient extension inside the fixed coefficient closure, uniformizer
  quotient, and positive level are exactly `P : PurityFiniteSetting.{u}`.
  In particular `P.Ring` reduces to
  `Padic.coefficientExtensionRing P.coefficients.l P.extension P.level`.
- `X Y : Scheme.{u}` and the two `Over (Spec (.of P.field.k))` instances are the
  two k-schemes. `LocallyOfFiniteType` and `QuasiCompact` on each structure map
  are precisely finite type, as recorded in `def-weil-finite-type-morphism`.
- `f : X ⟶ Y` and `[f.IsOver (Spec (.of P.field.k))]` are the k-morphism.
  `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and `[QuasiCompact f]` express
  separated finite type. No separatedness of either structure map is added.
- `d : ℕ` and `[SmoothOfRelativeDimension d f]` express smoothness of pure
  nonnegative relative dimension. The Mathlib class implies `Smooth f`.
- The first conjunct quantifies over **every** `a b : ℤ`, `hab : a ≤ b`, and
  `L : proEtaleDerivedCategory Y P.Ring`. Its hypothesis is exactly the recorded
  `finiteTorsionConstructibleIn ... Y ... a b hab L`. Its conclusion is the same
  recorded predicate on X and the value of the constructed exceptional functor,
  with endpoints `a - 2 * (d : ℤ)` and `b - 2 * (d : ℤ)`. The proof
  `sub_le_sub_right hab _` only supplies the required ordering of those endpoints.
  No Tor condition is imposed on L.
- The second conjunct quantifies over every integer interval and every K in the
  recorded `finiteTorConstructible ... Y` predicate. It assumes precisely
  `HasProEtaleTorAmplitude Y P.Ring K a b`, and concludes the same recorded Tor
  predicate for the exceptional image and the two shifted endpoints. The Tor
  predicate itself includes `a ≤ b` and tests every degree-zero module sheaf.
- The third conjunct is the explicit “in particular”: every object satisfying
  `finiteTorConstructible ... Y` has exceptional image satisfying
  `finiteTorConstructible ... X`. It includes bounded constructibility as well
  as existence of an ordered finite Tor interval.
- The signed constants are literally -2d at both endpoints. The node's closing
  description of these two clauses as the **constructible** preservation clauses
  is represented by these explicit conjuncts, rather than by asserting the false
  unrestricted ambient-admissibility predicate. No ambient adjoint datum,
  FullCD bound on all pro-etale sheaves, or coefficient-transport compatibility
  is a hypothesis. The ambient-definition module is imported for its contextual
  role. The discharge corollary and optional ambient-admissibility
  definition are contextual references; no new notion from them is needed
  to type these explicit preservation assertions.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  its fields and `PurityFiniteSetting.Ring`.
- `Sheaf.Paper.ConstructibleIntervals`:
  `AlgebraicGeometry.Scheme.finiteTorsionConstructibleIn` (the recorded
  interval category is its full subcategory).
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`:
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.SmoothOfRelativeDimension` and its smoothness implication.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `AlgebraicGeometry.IsSeparated`.
- `Sheaf.Paper.FiniteExceptionalInverseImage` (supplied below):
  `AlgebraicGeometry.Scheme.finiteExceptionalInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `ProEtale.finiteCoefficientIntrinsicRealization`,
  `ProEtale.finiteCoefficientIntrinsicRealization_exact`,
  `ProEtale.finiteCoefficientIntrinsicRealization_additive`, and
  `ProEtale.finiteCoefficientIntrinsicDerivedComparison`.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`:
  `AlgebraicGeometry.hasCompactification_of_finiteType_over_field`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the quotient construction.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`:
  `AlgebraicGeometry.Etale.rightDerivedUpperShriek` and its finite-coefficient
  adjoint-existence instance.
- `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`:
  `ProEtale.comparisonLowerStar`; its ordinary unbounded right derived functor
  is the Rnu_* in the defining formula.

The preservation proof imports include
`SmoothTensorDuality`, `ProEtaleConstructibleOrigin`, ordinary module inverse-image
exactness, constant-module pullback, derived tensor triangulatedness, constructible
pullback, the exact-functor cohomology formula, and the Nagata module. Unstated
proof dependencies are retained in the node for their future statements.

Edge cases checked before writing:

- d = 0 fixes both endpoints. For d = 1 and a = b = 0 the output is in degree
  -2, consistently with H^r(C[2]) = H^(r+2)(C).
- Arbitrary negative endpoints and a = b are allowed. Tor input ordering is
  carried by `HasProEtaleTorAmplitude`; an empty/reversed nonzero Tor interval
  is not silently admitted.
- Empty source and zero complexes are allowed. A morphism to the empty target
  forces empty source. No `Nonempty`, connectedness, or nonzero-object hypothesis
  is introduced, and smooth pure dimension on an empty source is harmless.
- n = 1 is included, and n = 0 is excluded by exactly the given conventions.
  All n > 1 are included. A constructible A/(ell) sheaf for A = Z/ell^2 can have
  infinite Tor dimension: the first conjunct still applies to it. The second
  and third conjuncts use the additional finite-Tor condition only where stated.
- The elliptic-curve counterexample concerns the unrestricted ambient adjunction;
  the theorem asks for none of that datum and uses the actual comparison composite.
- The site object universe remains u+1 and its morphism universe u. Coefficients
  in fixed-scalar sheaves use ULift to u+1; the intrinsic predicates retain their
  published categories. No equality of these universes is imposed.

Searches made for an existing statement/notion:

- `msearch.py`, LeanFinder, query “For a smooth separated morphism exceptional
  inverse image preserves constructibility and shifts the cohomological and Tor
  intervals by twice the relative dimension”: 8 hits. They were derived-category
  fraction/t-structure facts and constructible images of scheme morphisms, not
  exceptional preservation.
- `msearch.py`, Loogle, `AlgebraicGeometry.SmoothOfRelativeDimension`: 12 hits,
  including the class, its smoothness implication, and permanence results. This
  confirms use of the existing geometric notion; there is no exceptional-functor
  preservation theorem among the hits.
- `msearch.py`, grep, `UpperShriek|exceptional.*inverse` in Mathlib's
  AlgebraicGeometry directory: 0 hits.
- `msearch.py`, LeanSearch, “Smooth exceptional inverse image preserves
  constructible intervals and finite Tor amplitude”: service unavailable,
  Internal Server Error. This is recorded as unavailable, not absence evidence.
- `rg` in the upstream WeilConjectures source, with
  `constructible.*rightDerivedUpperShriek|rightDerivedUpperShriek.*smooth`:
  found the ordinary-etale Tor-preservation theorem at
  `SixFunctors/Etale/Derived/Stability/UpperShriek.lean:133` and ordinary-etale
  bounded constructibility at `UpperShriekConstructible.lean:63`. I read their
  full signatures and docstrings. The former imposes Tor amplitude on its input;
  the latter does not give the sharp interval. Neither is this two-clause
  pro-etale statement.
- `rg`/the requested blueprint-id grep over upstream found no exact
  `cor-pur-smooth-admissibility` declaration.
- `rg` in `lean/Sheaf` for exceptional inverse image, upper shriek, smooth
  preservation, and interval predicates found the existing ambient datum,
  ordinary-etale smooth tensor duality, constructible intervals, and canonical
  intrinsic realization. The exceptional inverse-image node had no recorded
  declaration and no module giving this intrinsic finite operation.
- Read the shared delivery-branch listing with `merge_delivery.py list` and
  opened the matching Q37 item/discharge and Q09 admissibility reports with
  `merge_delivery.py show`. These are stage-1 statement/proof splits, not a
  delivered stage-2 implementation. No delivered Lean was duplicated.
- Queried the prescribed current-source wrapper for the guessed missing
  exceptional/admissibility module names; no such source was available. The
  actual operation uses the published sources that were present and read.

No STATEMENT-DISPUTED finding for the item, and no statement correction.

## Dependency modules

The returned delivery originally supplied `def-weil-exceptional-inverse-image`
when it had no `lean` record. Its current record is now a fixed-scalar interface,
which does not type against the intrinsic interval predicate. Under §1(B),
`Sheaf.Paper.FiniteExceptionalInverseImage` supplies its finite-level displayed
construction, the only coefficient operation quantified over by this corollary.
It is a real composite of the canonical coefficient-realization inverse, Rnu_*,
the published ordinary-etale exceptional right adjoint, and the exact intrinsic
comparison inverse image. The latter is nu_X^* in the required presentation.
The inverse realization is the inverse of the specified fully faithful essentially
surjective realization, not an arbitrary equivalence. The ordinary right adjoint
is determined up to its unique adjunction-compatible isomorphism; Nagata chooses
a compactification via the published theorem. The definition contains no `sorry`,
no Nonempty choice of a free functor, and no assumption of ambient pro-etale
adjoint existence. It gives the actual value of Rf! on arbitrary ambient
representatives, interpreted on the bounded constructible inputs here. The
coefficient-transport and preservation assertions mentioned later in that
definition node are separate theorem obligations, not hypotheses of this
construction. The dependency copy changes only `lean`, with the required note.

`def-weil-finite-tor-amplitude` now records the existing fixed-scalar predicate,
which cannot be applied to an intrinsic constant-ring complex. Its §1(B) repair
reuses `WeilConjectures.finiteTorConstructible` and its full subcategory from
`Sheaf.Paper.FiniteTorAmplitude`. This is exactly the already published intrinsic
bounded-constructible and finite-Tor intersection, and no new module is needed.
Only the dependency's `lean` field changes, with an explanatory note.

## Return repair

Return L at immutable head e150490cc646 reports the collision between
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
The preceding reader added `Sheaf.AlgebraicGeometry.AmbientAdjointDischarge` to
this intrinsic statement module. Its transitive import
`Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass` loads the legacy pro-etale
framework, whereas the statement's intrinsic interval and Tor interfaces load
its finite-coefficient counterpart. Both export the same syntax declarations.

Removed that import. The statement continues to use the specified canonical
exceptional functor, built from the ordinary-etale right adjoint and comparison;
its existence needs no pro-etale ambient-adjunction theorem. The discharge
corollary explains the adjunction interpretation in the source; it is not used
to define the functor or to assert either preservation bound. Its reference
remains in the DAG and in the proof docstring, for the contextual interpretation
in steps 2 and 8. This import selection follows the repair instruction to import
only the compatible side needed by this module. All actual preservation-proof
imports remain, including `ComparisonPullbackExact` and
`ResidueTorAmplitudeTest`, which the preceding reader added.

No theorem signature, definition body, universe, mathematical hypothesis,
conclusion, or node statement changed in this repair. No live source was edited.
The two dependency repairs continue to use the intrinsic constant-ring
presentation matching the recorded interval interface. Node copies were refreshed
from the current read-only DAG, retaining only the delivery's `lean` records.
The old second-reading entry described the failed packet and is superseded;
a new independent reader must read this repair before delivery.

## Validation

`scompile.py Q09 cor-pur-smooth-admissibility` compiled both delivered modules
cleanly in dependency order, in preliminary, sandbox and library contexts.
`current-repair-compile.log` records all five successful checks, including the
main theorem in Sandbox1 and its final library module. There are no errors or
warnings. The default timeout was retained. The node signatures were checked
verbatim, no Lean line exceeds 100 characters, and the three node copies differ
from the current DAG only in `lean`.

The mandatory `deliver2.py Q09 cor-pur-smooth-admissibility --no-push` is run on
this finalized packet; `current-repair-dryrun.log` records the result. READY is
reported only after it prints OK. No delivery is pushed by this worker.

## Second reading by Q09

I independently read the current item node, both delivered Lean modules, every
statement-dependency node and its available recorded declarations, and the physical
blueprint sources for this corollary, purity conventions, exceptional inverse image,
and finite Tor amplitude in the launcher's read-only literature replica. The item's
source is the blueprint Markdown, not a Stacks tag. For the underlying notions I
also read Stacks `morphisms.tex`, definition-smooth-relative-dimension (02G2), including
its nonempty-fibre qualification, and `sites-cohomology.tex`,
definition-tor-amplitude (08FZ), including its arbitrary module-sheaf quantifier.
The stage-1 finite-type clarification in the current node is the domain of the
exceptional operation and unit; it is retained. There is no statement_change in this
packet and no new definition node to audit.

The following is my object/hypothesis/conclusion inventory and correspondence check.
Every entry passes against the current node and source.

1. The fixed tuple p,a,q,k0,k and k its algebraic closure, ell different from p,
   the fixed coefficient closure, finite subextension E, and positive integer n:
   `P : WeilConjectures.PurityFiniteSetting.{u}`. I opened `PurityFiniteSetting`
   and `FiniteFieldDatum`, rather than treating these names as evidence. The
   coefficient datum contains the distinct-prime condition and algebraic closure;
   `P.extension` is an actual intermediate field, with its finite-dimensional
   instance, and `P.level_pos : 1 ≤ P.level`. No ramification-divisibility or
   Kummer-level hypothesis is required. `P.Ring` is definitionally the existing
   quotient `Padic.coefficientExtensionRing P.coefficients.l P.extension P.level`.
2. The two finite-type k-schemes: `X Y : Scheme.{u}`, their `Over (Spec (.of
   P.field.k))` instances, and `LocallyOfFiniteType` plus `QuasiCompact` on
   each structure morphism. I read the recorded Mathlib finite-type interface:
   these two classes are exactly finite type. Neither structure map is assumed
   separated, smooth, or geometrically connected.
3. The k-morphism, separated and finite type: `f : X ⟶ Y`,
   `[f.IsOver (Spec (.of P.field.k))]`, `[IsSeparated f]`,
   `[LocallyOfFiniteType f]`, `[QuasiCompact f]`. All are in the node. Nagata
   compactifiability, Noetherianity, and prime invertibility are consequences,
   not additional theorem parameters.
4. Smoothness of pure relative dimension d ≥ 0: `d : ℕ` and
   `[SmoothOfRelativeDimension d f]`. I read Mathlib's standard-smooth chart
   definition and `SmoothOfRelativeDimension.smooth`. This is the constant
   relative dimension of 02G2, including empty fibres, not merely formal
   smoothness or an upper bound on dimension.
5. The specified constructible exceptional operation: every occurrence is
   `(finiteExceptionalInverseImage P.coefficients.l P.extension P.level
   P.level_pos P.field.k X Y f).obj`. I unfolded its four-factor construction:
   the inverse of the canonical intrinsic realization on Y, ordinary `Rnu_Y,*`,
   `Etale.rightDerivedUpperShriek`, and the canonical intrinsic derived comparison
   on X. Thus it is precisely `nu_X^* f^times Rnu_Y,*`, in the coefficient
   presentation of the interval predicate. No ambient pro-etale adjoint, arbitrary
   functor, or arbitrary comparison equivalence is supplied by the caller.
6. Clause (1) quantifies over every `a b : ℤ`, `hab : a ≤ b`, and every
   `L : proEtaleDerivedCategory Y P.Ring`. Its premise is
   `finiteTorsionConstructibleIn ... Y ... a b hab L`. I read that definition:
   intrinsic bounded constructibility and vanishing of every cohomology sheaf
   outside `Set.Icc a b`. The conclusion uses the identical predicate on X and
   the specified exceptional image, at `a - 2 * (d : ℤ)` and
   `b - 2 * (d : ℤ)`. `sub_le_sub_right hab _` supplies only endpoint ordering.
   There is no finite-Tor hypothesis in this conjunct.
7. Clause (2) quantifies over every integer interval and K, with precisely
   `finiteTorConstructible ... Y K` and `HasProEtaleTorAmplitude Y P.Ring K a b`.
   I read both definitions. The former intersects intrinsic bounded
   constructibility with existence of a finite Tor interval; the latter includes
   `a ≤ b` and tests all degree-zero module sheaves using K-flat resolutions.
   Its conclusion is that same Tor predicate on X at both shifted endpoints.
   No flatness or perfectness assumption is added.
8. The explicit “in particular” is the third conjunct, universally quantified
   over K, carrying `finiteTorConstructible ... Y` into
   `finiteTorConstructible ... X`. It includes bounded constructibility, not
   just finite Tor amplitude.
9. The signed constants are literally -2d at both endpoints. The source's
   closing “constructible sense” describes these clauses and the separately
   established bounded-class adjunction. It does not assert the optional ambient
   datum or the integral/rational/common-stage coefficient transports. The Lean
   correctly adds neither as a premise nor as a conclusion.

Dependency reading (H4/H13): `def-weil-exceptional-inverse-image` currently records
`Sheaf.Paper.FiniteTypeExceptionalInverseImage`, which I opened. Its operation uses
fixed-scalar `Sheaf ... (ModuleCat ...)`; it cannot be applied to an object of the
intrinsic constant-ring derived category in `ConstructibleIntervals`. The supplied
§1(B) module is the same finite-level displayed operation in that intrinsic
presentation. I also opened `finiteCoefficientIntrinsicRealization`, its exactness
and equivalence theorem, `finiteCoefficientIntrinsicDerivedComparison`, the ordinary
comparison definitions, and the current ordinary-etale UpperShriek source obtained
by `scompile.py --source`. The inverse is determined by the canonical realization,
and the ordinary adjoint by its adjunction, satisfying the non-hollow-data rule.
`hasCompactification_of_finiteType_over_field` supplies the required existence with
exactly the available geometric hypotheses. Its arbitrary-field definition is
harmlessly available beyond the fixed setting; the item only uses the stated
finite-type k-scheme case. The coefficient transport and preservation paragraphs
of the dependency node are separate theorem obligations, not data assumed by this
construction. The original fixed-scalar helpers remain in their existing module.

The finite-Tor dependency changed on the shared base during this reading: NW has
now landed the exact intrinsic record `WeilConjectures.finiteTorConstructible`,
including the integral and field declarations of `Sheaf.Paper.FiniteTorAmplitude`.
I removed our now-redundant dependency-node copy, rather than overwrite that landed
record. I opened the existing module: the integral predicate uses one interval for
all positive reductions, and the field notation is an alias; no duplicate notion
is needed. No new dependency module or definition is introduced by this cleanup.

I also opened the newly recorded `ExceptionalAdjointAdmissibility` module. Its
optional ambient predicate is stronger than the present corollary and is correctly
absent from the signature. I added that module as a proof/context import now that
it is available. The previously removed `AmbientAdjointDischarge` import stays
excluded for the documented incompatible legacy/finite-coefficient framework syntax
collision. I read its recorded declaration and the explanatory source paragraph:
it supplies the bounded-class adjunction interpretation, not data needed for this
canonical comparison composite or a further conclusion of the preservation theorem.
The reference remains in the DAG and the proof docstring.

Edge cases: d=0 leaves both intervals unchanged; d=1 and [0,0] give [-2,-2],
consistent with H^r(C[2])=H^(r+2)(C). Negative and singleton integer intervals
are included; input intervals are ordered exactly as in the source. Zero objects,
empty schemes and empty fibres are allowed, with no Nonempty or nonzero hypotheses.
An empty target forces the source empty for a morphism. No index set occurs in the
statement; the arbitrary trivializing cover in the proof need not be finite, since
the constructible stratification, rather than that cover, is finite. n=1 and all
larger n occur; n=0 is excluded by the given conventions. ell=p is excluded by those
same conventions, with no further restriction on either prime. Constructible
A/(ell) for A=Z/ell^2 need not have finite Tor dimension and is still admitted by
clause (1). The site remains object universe u+1, morphism universe u, and the
fixed-scalar realization uses ULift of the actual coefficient quotient. There is
no independent smaller test universe or equality forcing the site universes
coincident. All variables are explicitly bound under autoImplicit=false.

Independent searches used other wording than the worker:

- `msearch.py ... leanfinder` for “A smooth extraordinary inverse image shifts
  bounded constructible cohomology and finite Tor intervals by minus twice relative
  dimension”: eight generic derived support/shift results, no matching statement.
- `msearch.py ... leansearch` for “extraordinary pullback preserves constructible
  complexes for smooth morphisms”: eight module pullback/base-change results, no
  exceptional preservation theorem. This service worked on this reading.
- `msearch.py ... loogle` for `"SmoothOfRelativeDimension"`: twelve standard-smooth
  algebra results; the scheme class was checked directly in Mathlib source.
- `msearch.py ... grep` for `extraordinary|exceptional.*pullback|smooth.*shriek`:
  two irrelevant extraordinary-homology comments in bordism.
- Direct `rg` over Mathlib AlgebraicGeometry, upstream WeilConjectures and shared
  `lean/Sheaf`, including `upperShriek`, `rightDerivedUpperShriek`, sharp smooth
  constructibility, the blueprint id, and the delivered declaration names:
  no duplicate of this intrinsic two-clause pro-etale theorem or its canonical
  intrinsic exceptional composite. I read the nearest upstream statements:
  `constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension`
  is ordinary etale and assumes Tor amplitude on its input;
  `boundedConstructible_rightDerivedUpperShriek_of_smoothOfRelativeDimension`
  is ordinary etale and gives no sharp cohomological interval. Neither can replace
  this node with an existing:true record. The upstream-name index has no exact
  blueprint-id/declaration match.

No mathematical mismatch remains. I retained the theorem signature and definition
body. The changes in this reading are the newly available contextual proof import,
removal of the redundant finite-Tor dependency repair, and this independent audit.
Both sorry theorems are named, listed in lean.declarations, and documented with
source, blueprint id and proofs: prime_isUnit_stalk is precisely the coefficient
invertibility observation in node proof step 1; smooth_exceptional_preservation
carries all eight steps. The definition has real composite data, and no theorem
is proved in this stage. The node's lean.statement was checked verbatim against
its signature; declarations have the required docstrings, and Lean lines are at
most 100 characters. Final wrapper compilation and delivery preflight results
are recorded below.

Final validation: the prescribed `scompile.py` passed both delivered files in
preliminary/sandbox/library contexts. With the added proof import,
`deliver2.py Q09 cor-pur-smooth-admissibility --no-push` then compiled the two
required import dependencies and both delivered modules, with no diagnostics,
and printed `OK (dry run): commit d8e7868b3e passes the preflight and compiles`.
The log is `final-second-reading-dryrun.log` in the sandbox. The final packet has
five files: the two Lean modules, the item node, the exceptional-inverse-image
dependency record, and this report. The finite-Tor dependency is reused directly
from the landed base. The mandated limits were retained; no live file was edited.
