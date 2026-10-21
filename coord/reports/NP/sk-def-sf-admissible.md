## Worker report

This delivery states the current main-20261015 definition of exceptional-adjoint
admissibility, at one positive finite coefficient level and one specified
compactification. The module is `Sheaf.Paper.SfExceptionalAdjointAdmissibility`.
It defines `WeilConjectures.HasSfAmbientExceptionalDatum` for clause (1), and
`WeilConjectures.IsSfExceptionalAdjointAdmissible` for the conjunction of (1)--(3).
Both have complete definitional bodies. No theorem, proof, axiom, or `sorry` is added.
The item's statement, statement dependencies, and proof fields are unchanged.

Read the complete item, all thirteen statement-dependency nodes, their recorded
signatures/docstrings, and the current blueprint source:
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-def-sf-admissible/_section.md`, order 1702. The definition follows its three
numbered conditions. The Brown representability paragraph, Yoneda comparison, and
counterexample warning are explanations/consequences, not additional conjuncts.
The example Sheaf CompactObject module has been withdrawn; its node now records
`WeilConjectures.CategoryTheory.CompactObject`, whose header and definition were read.
The returned H13 repair is described below; no mathematical statement correction is needed.

Hypothesis and clause correspondence:

- The global finite-field setting is `D : FiniteFieldDatum.{u}`. Its fields specify
  the prime `D.p`, positive exponent, finite field of the corresponding cardinality,
  and fixed algebraic closure `D.k`. `l : ℕ`, `[Fact l.Prime]`, and `_hl : l ≠ D.p`
  give the distinct coefficient prime. No extra invertibility hypothesis is added;
  it follows for this prime in characteristic `D.p`.
- `(E : Type u) [Field E] [Algebra (Padic l) E]`
  `[FiniteDimensional (Padic l) E]` is precisely a finite extension of Q_l.
  `(n : ℕ) (hn : 1 ≤ n)` enforces the positive coefficient stage. Every coefficient
  occurrence is the recorded `Padic.coefficientExtensionRing l E n`, with the
  recorded chosen uniformizer; there is no arbitrary ring parameter in the main
  definition. `Padic.finite_coefficientExtensionRing` installs the existing proven
  finiteness of this ring inside the body, rather than adding a hypothesis.
- `(X Y : Scheme.{u})`, their `Over (Spec (CommRingCat.of D.k))` instances, and
  `LocallyOfFiniteType` plus `QuasiCompact` for both structure morphisms give the
  finite-type k-schemes. `(f : X ⟶ Y)` and its `IsOver` instance make it a k-morphism.
  `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` give exactly its stated
  separated finite-type hypotheses, using the recorded Mathlib classes.
- `(c : Compactification f)` supplies `c.Z = Xbar`, `c.i = j`, `c.g = p`, properness,
  open immersion, and the factorization equation. No refinement is supplied.
  The base structure on `c.Z` is induced by `c.g` and the structure of Y as in the
  node. Thus p is proper between finite-type schemes over Spec k.
- All categories are `proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n)`:
  the ordinary unbounded derived categories of modules over the constant ring
  sheaf on `T.ProEt`. The ring and module sheaves are lifted internally to universe
  `u+1`, following the existing site convention; no equality of object and
  morphism universes is imposed. The same universe `u` for the schemes, fields,
  and coefficient carrier follows the recorded dependencies; it is arbitrary.
- The functor in every adjunction is the dependency's actual
  `sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n)`, whose body is
  `(sfIntrinsicExtensionByZero c.i A).mapDerivedCategory ⋙`
  `proEtaleConstantDerivedDirectImage c.g A`. This is exactly Rp_* j_! for this c.
  There is no replacement by an arbitrary functor or an etale-origin restriction.
- Clause (1) is `HasSfAmbientExceptionalDatum l E n hn c`, namely
  `∃ cCD : ℕ, sfFullCohomologicalDimension c.g A cCD`. Nonnegative integers are
  represented by natural numbers and coerced to integers in the recorded FullCD.
  This directly uses both clauses of the dependency: all source sheaves and their
  restrictions to every pro-etale object of Y. No constructibility hypothesis or
  finite-type condition on that site object is introduced. The helper is also
  defined on other compactified schemes, just as FullCD is; its use in the main
  definition has all of the node's finite-field and finite-type hypotheses.
- Clause (2), first sentence, is the second conjunct: for every functor G between
  the entire indicated derived categories and every adjunction `F ⊣ G`,
  `intrinsicFiniteTorsionConstructible ... Y L` implies the same predicate at X
  for `G.obj L`. `Adjunction.homEquiv` supplies the stipulated natural Hom bijections.
  Quantifying over adjunction structures adds no condition to the preservation
  property, which does not depend on the choice of that structure.
- Clause (2), displayed bound, is the third conjunct. Its order is
  `∃ cMinus cPlus : ℤ, ∀ G, (F ⊣ G) → ∀ a b : ℤ, a ≤ b → ∀ L, ...`.
  Thus one signed pair works for all right adjoints and all input intervals.
  Input membership is `constructibleInterval ... Y a b L`; output membership is
  `constructibleInterval ... X (a + cMinus) (b + cPlus) (G.obj L)`.
  The predicate is the one whose full subcategory is the dependency's recorded
  `intrinsicConstructibleIntervalCategory`; it includes bounded constructibility
  as well as all the cohomological vanishing, with inclusive endpoints.
- Clause (3) is the fourth conjunct with the same universal right-adjoint
  quantifier and the existing `finiteTorConstructible` predicates at Y and X.
  These mean bounded constructibility AND finite Tor amplitude against every
  degree-zero module sheaf. They are not bare constructibility and do not
  replace finite coefficients by the field-stage convention.
- The four conjuncts are exactly (1), the two sentences of (2), and (3).
  No right-adjoint existence clause, refinement coherence, integral coefficient
  condition, or rational coefficient condition is added. Ambient names (1) alone;
  neither predicate is installed as a typeclass or assumed of every morphism.

Dependency declarations used (all source bodies and docstrings read):

| Node | Module and declaration(s) |
| --- | --- |
| def-weil-finite-field-fiber | `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`; reexports `Padic.coefficientExtensionRing`, integers and chosen uniformizer |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact` |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, reexported `IsSeparated` and `UniversallyClosed` |
| def-weil-compactifications-refinements | `WeilConjectures.Compactification.Refinement`, with the actual factorization structure `AlgebraicGeometry.Compactification` reexported from `.Defs`; no refinement is used |
| def-weil-pbc-proetale-site | recorded `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`; its already published constant-ring derived realization `Scheme.proEtaleDerivedCategory` from `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` |
| def-weil-derived-cohomology-sheaves | the node's usable `mathlib_match`, `DerivedCategory.homologyFunctor` in `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, as used in FullCD, support and constructibility |
| def-weil-derived-direct-image | `Sheaf.Paper.SfDerivedDirectImage`, reexporting `Scheme.proEtaleConstantDerivedDirectImage` from `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage` |
| def-compact-support-direct-image-detailed | `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `Scheme.sfIntrinsicCompactSupport` |
| def-weil-full-cohomological-dimension | `Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension`: `Scheme.sfFullCohomologicalDimension` |
| def-weil-finite-torsion-constructibility | `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`: `Scheme.intrinsicFiniteTorsionConstructible` |
| def-weil-constructible-intervals | `Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals`: `WeilConjectures.intrinsicConstructibleIntervalCategory`, transparent alias of the full subcategory of the reexported `constructibleInterval` from `Sheaf.Paper.ConstructibleIntervalsUnordered` |
| def-weil-finite-tor-amplitude | superset record: `Sheaf.Paper.FiniteTorAmplitudeSites` publicly imports `Sheaf.Paper.FiniteTorAmplitude`; the item uses `WeilConjectures.finiteTorConstructible`, while `WeilConjectures.finiteTorConstructibleEtale` remains the primary recorded declaration |

The cohomology node's latest primary record concerns common-stage Weil cohomology,
which cannot take objects of the present finite coefficient derived category. Its
existing Mathlib match already states exactly the general cohomology-sheaf functor
needed here, so that match is used, without creating a replacement definition.

Edge cases checked before writing the definition: `n=0` is excluded exactly by
`hn`, and `n=1` is allowed. The characteristic prime is excluded exactly by `_hl`.
The empty scheme and zero derived objects are allowed; no nonemptiness or
nonzero-object hypothesis occurs. `cCD=0` is included. Both shift constants may
be negative and are not assumed ordered. Inputs include `a=b`. Outputs with
`b+cPlus < a+cMinus` are allowed: `constructibleInterval` uses `Set.Icc`, which
then is empty, so its support condition requires all cohomology sheaves to vanish.
FullCD has no finite-type restriction on `V : Y.ProEt` and tests all module sheaves.
The preservation clauses quantify over every right adjoint, including arbitrary
isomorphic choices. No right-adjoint choice, representability theorem, or
compactification-independence result is used to define the predicates.

Searches actually run using `msearch.py`:

- LeanFinder: "Exceptional adjoint admissibility at finite coefficients: FullCD of
  chosen compactification, every right adjoint preserves bounded constructible
  complexes with uniform signed cohomology shifts and finite Tor amplitude".
  Eight results: DerivedCategory.IsGE, IsLE, a Serre-class right-adjoint lemma,
  two fraction representation lemmas, existence of bounded representatives,
  isGE_Q_obj_iff, and its instance. None defines this datum.
- Loogle: `"ExceptionalAdjoint"`. Zero hits.
- Mathlib grep: `ExceptionalAdjoint|FullCohomologicalDimension|finiteTorConstructible`.
  Zero hits.
- LeanSearch: "Exceptional inverse image on pro etale sheaves preserves bounded
  constructible intervals and finite Tor amplitude". Eight results on finite
  limits for sheaf pullback and sheaf-to-presheaf, ordinary module inverse maps,
  and sheaf-equivalence components. None defines this datum.

Direct rg searches of Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json` checked the proposed names and the existing
exceptional-adjoint/FullCD names. The new full names have no matches. The
required node-id grep in `WeilConjectures` found `ExceptionalAdjoint.lean` and
its consumers; the complete candidate definitions at lines 106--203 were read.
Its `HasAmbientExceptionalRightAdjoint` includes right-adjoint existence and uses
the fixed-scalar sheaf category. Its `IsExceptionalAdjointAdmissible` extends that
structure, whereas the current unit explicitly defines (1) as FullCD alone in the
intrinsic constant-ring presentation supplied by its dependencies. The old
`Sheaf.Paper.ExceptionalAdjointAdmissibility.IsExceptionalAdjointAdmissibleAtFiniteStage`
was also read: it existentially supplies a coherent family of adjunctions and
comparison maps for ALL compactifications through
`SfAmbientExceptionalRightAdjointDatum`, not merely the current unit's chosen-c
predicate. Reusing either old datum would insert defining clauses absent from this
node. All actual underlying notions (FullCD, compact support, intervals,
constructibility and finite Tor amplitude) are reused without private copies.

No disputed mathematical assertion or statement correction is needed.
The first server-only scompile passed both sandbox and library checks with no
warnings (9.9 s and 13.5 s). The final packet is verified again by deliver2's
server compilation and preflight after the explicit dependency imports and node
records are installed.

## Dependency modules

`def-weil-finite-tor-amplitude`: section 1(B), repair of returned H13 at
immutable head `c9664d838c32`. The saved packet's initial dry run passed at
`734de304444`, but its dependency record dropped the landed NW etale declaration.
This repair retains the current landed record's primary module
`Sheaf.Paper.FiniteTorAmplitudeSites`, primary declaration
`WeilConjectures.finiteTorConstructibleEtale`, and verbatim signature, and lists
both declaration families. The Sites module gains exactly one public import of
`Sheaf.Paper.FiniteTorAmplitude`; all existing imports, docstrings and definitions
are unchanged. Thus the recorded module exposes the etale predicate and all five
original pro-etale, integral and field declarations. Existing etale consumers retain
their declaration and domain, and this item retains the original pro-etale predicate.
No definition is copied or replaced. Only the dependency node's `lean` field changes.

The etale predicate has domain `Etale.DerivedCategoryModule (ULift A) Y`, so it
cannot accept this item's ordinary pro-etale constant-ring derived objects.
`finiteTorConstructible` has exactly that pro-etale domain and is the intersection
of `intrinsicFiniteTorsionConstructible` and `HasFiniteProEtaleTorAmplitude`.
The same original module supplies the integral uniform-reduction condition and
field-stage aliases. Publicly reexporting this unchanged family makes the record
a superset and preserves both site presentations.

## Second reading by NP

No independent worker reading is claimed. The dispatcher explicitly prohibits
starting other agents and directs the worker to deliver; the maintainer's
independent review reads this packet. The worker re-read the source, item, both
new definitions, and the dependency-record repair: (1) is exactly the FullCD
existential, (2) has separate bounded-constructible preservation and one global
signed pair of interval shifts, and (3) is finite-Tor preservation. The output
interval has no order hypothesis. The finite-field and morphism hypotheses all
occur explicitly in the main signature. The H13 repair was checked against the landed NW record and current server source: its primary etale declaration and signature remain unchanged, its declaration list only grows, and Sites gains just one public import. The original pro-etale predicate is reused. No source-statement change was made.

The first final-packet dry run compiled successfully but rejected both recorded
signatures because its signature reader starts at `def`, excluding the
`noncomputable` modifier. Both records were corrected to start at `def`; the Lean
source and its mathematical meaning are unchanged.

## Repair validation and tool failure

The returned H13 repair is implemented in the sandbox. Server scompile compiled
both delivered files cleanly: FiniteTorAmplitudeSites 7.2 s and
SfExceptionalAdjointAdmissibility 8.8 s (sandbox checks also clean, 5.4/8.6 s).
The local structural check confirms both node files differ from current main
only in `lean`; the dependency retains its landed primary module, declaration
and verbatim signature, and its declaration list is a superset. The Sites source
diff is exactly the added public import; both Lean files satisfy the line limit
and contain no `sorry`.

The repaired deliver2.py --no-push failed preflight with five identical-shape
errors, one for each publicly imported original declaration. For example:
`lean.declarations names WeilConjectures.finiteTorConstructible, which the file
does not declare and which neither Mathlib nor the source has`.
The other rejected declarations are finiteTorConstructibleCategory,
finiteTorConstructibleIntegral, finiteTorConstructibleIntegralCategory, and
finiteTorFieldCoefficientCategory, all in namespace WeilConjectures.

Read-only inspection of tools/stage2_delivery.py, check_lean_text, confirms
that this check accepts only declarations directly parsed from the recorded
file or found in the Mathlib/upstream name index. It does not follow public
imports of project modules. Reversing the import direction would instead reject
the etale declaration by the same check. Marking the delivered module existing
would conflict with the explicit record rule prohibiting lean.file when
existing is true. Duplicating the definitions would violate one definition per
notion. Consequently the reviewer-requested public-import superset cannot pass
this gate as implemented. No scripts, live sources or live records were changed;
no repaired delivery was pushed. The launcher instructions require reporting
this wrong gate refusal rather than patching or working around it.

## Retained-packet retry, 2026-10-21

As requested by the repair retry brief, first read this retained report and ran
`deliver2.py NP sk-def-sf-admissible --no-push` on the saved packet. It again
failed with exactly the five public-import declaration refusals quoted above;
nothing was pushed. The current gate therefore still prevents the requested
H13 superset repair.

Rechecked the packet against the refreshed shared base without Git commands:
both node copies differ only in `lean`; the dependency's primary module,
declaration and signature are unchanged, and its declaration list contains the
whole landed list. The Sites module differs by exactly the public import of
`Sheaf.Paper.FiniteTorAmplitude`. Read that imported module and verified all five
rejected declarations and their docstrings. Both delivered Lean files have no
`sorry` or over-width line. Re-ran the prescribed scompile command on both files:
exit 0, all preliminary, sandbox and library checks clean, no warnings. Read-only
inspection of `tools/stage2_delivery.py:217` confirms that `check_lean_text`
tests additional names against directly parsed declarations or `upstream_has`,
without resolving public imports of project modules. No Lean or node repair
was needed beyond the already retained reviewer-required superset, and no gate
or launcher script was edited or bypassed.

## Retained-packet retry 3, 2026-10-21

First inspected the saved report and ran the prescribed unmodified packet through
`deliver2.py NP sk-def-sf-admissible --no-push`. It exited 1 with exactly the same
five public-import declaration refusals, against base `10da8e3fc`; nothing was
pushed. The concrete diagnostic again includes:
`lean.declarations names WeilConjectures.finiteTorConstructible, which the file
 does not declare and which neither Mathlib nor the source has`.

Re-read both delivered modules, the original FiniteTorAmplitude module, the
record, and `tools/stage2_delivery.py` check_lean_text. The gate still checks
additional names only against declarations directly parsed from this file or
upstream_has; it does not resolve the public project import. All five names are
actual declarations in the publicly imported FiniteTorAmplitude module.
Comparison with the refreshed read clone confirms that both node copies change
only lean, the landed dependency primary module/declaration/signature are
unchanged, and its declarations are a superset. The Sites source diff remains
exactly one added public import. Neither delivered Lean file contains sorry or
a line longer than 100 characters.

The prescribed scompile.py command on both delivered files exited 0: all
preliminary, sandbox and library compilations were clean, without warnings.
The reviewer-required repair is retained. No scripts or live sources were
modified, and the public-import gate was neither patched nor bypassed.

## Retained-packet retry 4, 2026-10-21

First inspected the retained report and ran the prescribed saved packet through
`deliver2.py NP sk-def-sf-admissible --no-push`. It exited 1 and again rejected
all five publicly imported pro-etale/integral/field declarations, with the exact
reason `which the file does not declare and which neither Mathlib nor the source has`.
The failure occurs in preflight; nothing was pushed.

Compared the packet with the refreshed current read clone without Git commands.
Both node copies differ only in `lean`. The dependency retains the landed primary
module, declaration and verbatim signature, and its declarations are a superset.
The entire Sites source diff is the one added public import of
`Sheaf.Paper.FiniteTorAmplitude`. Re-read that module: all five names are actual
public definitions or abbreviations with source/blueprint docstrings. Re-read
`tools/stage2_delivery.py` `check_lean_text`: additional declarations still pass
only when parsed directly from the recorded file or found by `upstream_has`.
Project public imports are not resolved. Thus the same gate still refuses the
explicit reviewer-required superset; no legal source or record repair changes
this result without discarding the required superset or duplicating definitions.
No launcher scripts or project tools were patched or bypassed.

Ran the prescribed scompile.py on both delivered modules: exit 0, no errors or
warnings. Preliminary compilation: 7.2/8.8 s; sandbox: 5.4/8.6 s; library:
7.2/8.8 s. Both source files satisfy the 100-character line limit. The approved
mathematical item and reviewer-requested dependency repair remain retained.


## Retained-packet retry 5, 2026-10-21

Inspected the saved report first and ran the required saved-packet dry run:
`deliver2.py NP sk-def-sf-admissible --no-push`. It exited 1 before pushing,
with the same five preflight (c) refusals. The precise diagnostic for the first is:
`lean.declarations names WeilConjectures.finiteTorConstructible, which the file
 does not declare and which neither Mathlib nor the source has`.
The other four rejected names are finiteTorConstructibleCategory,
finiteTorConstructibleIntegral, finiteTorConstructibleIntegralCategory, and
finiteTorFieldCoefficientCategory, in namespace WeilConjectures.

Verified the retained H13 repair against the refreshed shared sources without
Git commands: both node copies differ only in lean; the dependency's primary
module, declaration and verbatim signature remain unchanged; its declarations
are a superset. The Sites source differs by exactly the added public import of
Sheaf.Paper.FiniteTorAmplitude. All five rejected declarations are actually
present in that imported project's module (lines 39, 49, 59, 71 and 84).
Read-only inspection of tools/stage2_delivery.py check_lean_text confirms that
its additional-declaration check only consults declarations parsed directly
from the recorded file and upstream_has; it does not follow the public project
import. This is the concrete tool refusal preventing the reviewer's explicitly
required public-import superset record. Duplicating the definitions or removing
members of that superset would violate the repair requirements. No gate or
launcher script was patched or bypassed.

Re-ran the prescribed scompile.py on both delivered modules: exit 0, no errors
or warnings. Preliminary, sandbox and library checks all passed. Both modules
have no sorry and no line exceeding 100 characters. The reviewer-required
repair remains in the sandbox; no unchanged re-push was attempted.

## Retained-packet retry 6, 2026-10-21

Read the retained report first and ran the required saved-packet dry run with
`deliver2.py NP sk-def-sf-admissible --no-push`. It exited 1 at preflight,
rejecting the same five publicly imported declarations. The first diagnostic is:
`lean.declarations names WeilConjectures.finiteTorConstructible, which the file
does not declare and which neither Mathlib nor the source has`.
The other four names are finiteTorConstructibleCategory,
finiteTorConstructibleIntegral, finiteTorConstructibleIntegralCategory, and
finiteTorFieldCoefficientCategory, all in namespace WeilConjectures. Nothing
was pushed. The tool reported base 8e2e888ce and that sheaf-dag had advanced.

Compared both node copies with the wrapper-refreshed shared clone using JSON
comparison, without Git commands: each changes only lean. The dependency keeps
its landed module, primary declaration and verbatim signature, and the recorded
declarations form a superset. The Sites source differs from current main only
by `public import Sheaf.Paper.FiniteTorAmplitude`. Read both modules and verified
that all five rejected names are actual definitions in the publicly imported
module. Neither delivered Lean file contains sorry or lines over 100 characters.
Read-only inspection of tools/stage2_delivery.py:247-255 confirms that additional
names must occur directly in the file or pass upstream_has; project public
imports are not resolved. This is a faulty gate refusal of the explicitly
reviewer-required superset, not a missing declaration or failed Lean compile.
Removing the names would discard the required superset; duplicating their
implementations would violate the one-definition rule. No tool was patched or
bypassed, and no live source or node was edited.

Re-ran the prescribed scompile.py on both delivered modules. Exit 0, all checks
clean, no warnings: preliminary 7.2/8.8 s, sandbox 5.4/8.6 s, library 7.2/8.8 s.
The reviewer-required repair remains retained for a corrected preflight gate.

## Retained-packet retry 7, 2026-10-21

Read the saved report first and ran the required saved-packet dry run using
`deliver2.py NP sk-def-sf-admissible --no-push`. It exited 1 at preflight with
the same five (c) refusals; nothing was pushed. The first diagnostic remains:
`lean.declarations names WeilConjectures.finiteTorConstructible, which the file
does not declare and which neither Mathlib nor the source has`.
The remaining rejected declarations are finiteTorConstructibleCategory,
finiteTorConstructibleIntegral, finiteTorConstructibleIntegralCategory and
finiteTorFieldCoefficientCategory, all in namespace WeilConjectures.

Rechecked the retained packet against the wrapper-refreshed current main using
JSON and source-text comparisons, without Git commands. Both node copies change
only lean. The dependency preserves the landed primary module, declaration and
verbatim signature; its declarations are a superset. The Sites source changes
only by adding `public import Sheaf.Paper.FiniteTorAmplitude`. Read the imported
module and verified all five rejected definitions are present with public
exposure. Read tools/stage2_delivery.py:247-255: its additional-declaration check
accepts only declarations parsed directly in the recorded file or recognized
by upstream_has, without resolving project public imports. Thus this is the
same wrong gate refusal of the reviewer's explicitly requested superset record.
No launcher or project script was modified, and no gate was bypassed.

Ran prescribed scompile.py on both retained delivery modules: exit 0, no errors
or warnings. Preliminary checks: 7.2/8.8 s; sandbox checks: 5.4/8.6 s; library
checks: 7.2/8.8 s. Neither module has sorry or lines exceeding 100 characters.
The H13 repair remains intact in the sandbox for the preflight correction;
removing the required declaration family or duplicating definitions would not
be a valid repair. No unchanged re-push was attempted.


## Retained-packet retry 8, 2026-10-21

Read the saved report and ran the required initial saved-packet dry run with
`deliver2.py NP sk-def-sf-admissible --no-push`. It exited 1 at preflight on base
`307136823`, with the same five (c) refusals. Nothing was pushed. The first is:
`lean.declarations names WeilConjectures.finiteTorConstructible, which the file
does not declare and which neither Mathlib nor the source has`.
The other names are finiteTorConstructibleCategory, finiteTorConstructibleIntegral,
finiteTorConstructibleIntegralCategory and finiteTorFieldCoefficientCategory.

Read the return at coord/returns/NP.md:55-57 and confirmed its required H13 repair
is retained: both declaration families are listed, the landed Sites primary
module, etale declaration and verbatim signature remain, and Sites publicly
imports FiniteTorAmplitude. JSON comparison against the wrapper-refreshed shared
clone confirms that each node changes only lean; the dependency declaration list
is a superset. Source comparison confirms Sites changes only by that public import.
Read FiniteTorAmplitude and verified that it really declares all five rejected
names. The delivered files contain no sorry and no lines over 100 characters.

Read-only inspection of tools/stage2_delivery.py:247-255 again confirms the gate
checks only declarations parsed directly from the recorded file or found through
upstream_has; it does not follow project public imports. The required superset
therefore cannot pass this gate. Dropping the names would undo the explicit
reviewer correction; duplicating them would violate one definition per notion.
No gate or launcher script was patched, no live source was edited, and no push
was attempted.

Prescribed scompile.py of both delivered modules exited 0, without errors or
warnings. Preliminary checks: 7.2/8.8 s; sandbox checks: 5.4/8.6 s; library checks:
7.2/8.8 s. The reviewer-required H13 repair remains in the sandbox, blocked solely
by the preflight refusal of publicly imported project declarations.


## Retained-packet retry 9, 2026-10-21

First read the saved report and ran the prescribed unmodified packet through
`deliver2.py NP sk-def-sf-admissible --no-push`. It exited 1 with the same five
public-import declaration refusals, and nothing was pushed. For example:
`lean.declarations names WeilConjectures.finiteTorConstructible, which the file
does not declare and which neither Mathlib nor the source has`.

Rechecked against the wrapper-refreshed current main without Git commands:
both node files change only lean, and the dependency preserves the landed primary
module, declaration and verbatim signature while adding all five original names.
The Sites module changes only by adding the required public import of
Sheaf.Paper.FiniteTorAmplitude. Read the imported source: all five names are
real public declarations. Read the H13 return and check_lean_text at
 tools/stage2_delivery.py:247-255: the gate accepts names parsed directly in the
recorded file or found by upstream_has, but does not follow public project
imports. Thus the requested superset remains refused by the tool itself.
No scripts were changed or bypassed, no duplicate definitions were introduced,
and the required superset was retained.

Re-ran scompile.py on both delivered modules: exit 0, no errors or warnings.
Preliminary checks were 7.2/8.8 s, sandbox checks 5.4/8.6 s, and library checks
7.2/8.8 s. Both files contain no sorry and no lines over 100 characters.
No push was attempted because preflight still rejects the required repair.


## Retained-packet retry 10, 2026-10-21

First inspected the saved report and ran the prescribed saved-packet dry run:
`deliver2.py NP sk-def-sf-admissible --no-push`. It exited 1 at preflight
against base `e32e53515`, rejecting the same five publicly imported declarations.
The first diagnostic is `lean.declarations names WeilConjectures.finiteTorConstructible,
which the file does not declare and which neither Mathlib nor the source has`.
The remaining names are finiteTorConstructibleCategory, finiteTorConstructibleIntegral,
finiteTorConstructibleIntegralCategory and finiteTorFieldCoefficientCategory.
Nothing was pushed.

Compared both sandbox nodes to the wrapper-refreshed shared sources without Git
commands: both change only lean. The dependency retains its landed module,
primary declaration and verbatim signature, and its declaration list is a superset.
The Sites source differs only by adding the required public import of
Sheaf.Paper.FiniteTorAmplitude. Read the imported source and confirmed all five
rejected declarations exist. Read check_lean_text in tools/stage2_delivery.py:
its additional-name check accepts directly parsed names or upstream_has, without
following project public imports. The concrete diagnostic is therefore a tool
refusal of the reviewer-required superset. No script was patched or bypassed,
no duplicate definitions were introduced, and no live files were edited.

Ran the prescribed scompile.py on both delivered modules: exit 0, all preliminary,
sandbox and library checks clean, no warnings (7.2/8.8 s preliminary,
5.4/8.6 s sandbox, 7.2/8.8 s library). Both files contain no sorry and no lines
exceeding 100 characters. The required repair remains retained; no unchanged
re-push was attempted.


## Retained-packet retry 11, 2026-10-21

First inspected the retained report and ran the prescribed saved-packet dry run:
`deliver2.py NP sk-def-sf-admissible --no-push`. It exited 1 on base
`dc944f3ef`, rejecting the same five publicly imported declarations; nothing
was pushed. The first diagnostic is:
`lean.declarations names WeilConjectures.finiteTorConstructible, which the file
does not declare and which neither Mathlib nor the source has`.
The other rejected names are finiteTorConstructibleCategory,
finiteTorConstructibleIntegral, finiteTorConstructibleIntegralCategory and
finiteTorFieldCoefficientCategory, all in namespace WeilConjectures.

Re-read the H13 return, both packet modules, the imported FiniteTorAmplitude
module and check_lean_text in tools/stage2_delivery.py:247-255. All five names
are real public declarations in that imported module, but the gate checks only
directly parsed names or upstream_has and does not follow public project imports.
Compared packet JSON/source with the wrapper-refreshed shared clone without Git
commands: both node copies change only lean; the dependency retains its primary
module, declaration and verbatim signature, and its declarations are a superset.
The Sites source changes only by the required public import. Removing these names
would undo the explicit reviewer requirement; duplicating definitions would violate
one definition per notion. No tool was patched or bypassed and no live files edited.

Re-ran prescribed scompile.py on both delivered files: exit 0, no errors or
warnings. Preliminary checks 7.2/8.8 s; sandbox checks 5.4/8.6 s; library checks
7.2/8.8 s. Neither source contains sorry or lines exceeding 100 characters.
The H13 repair is retained; delivery remains blocked by the preflight tool's
refusal of the required publicly imported declaration family.

## Retained-packet retry 12, 2026-10-21

Ran the required saved-packet dry run before changing the packet. It failed
against base `86b5ed4c0`, with exactly the five public-import declaration
refusals already recorded above; nothing was pushed. After the resumed turn,
checked this completed result rather than repeating delivery.

Compared with the wrapper-refreshed shared base: both node files change only
`lean`; the dependency retains its primary module, declaration and verbatim
signature, and its declaration list is a superset. The Sites module changes
only by publicly importing `Sheaf.Paper.FiniteTorAmplitude`. Re-read that
module: all five rejected names are its actual declarations. The gate at
`tools/stage2_delivery.py:250-255` still checks only directly parsed names or
`upstream_has`, without following public project imports.

Prescribed scompile.py completed with exit 0 for both files, no errors or
warnings: preliminary 7.2/8.8 s, sandbox 5.4/8.6 s, library 7.2/8.8 s.
Neither file contains `sorry` or a line over 100 characters. The reviewer-required
H13 repair is retained. No tool was edited or bypassed, no live file was edited,
and no push was attempted. The remaining blocker is the preflight tool's refusal
of the required publicly imported declaration family.


## Retained-packet retry 13, 2026-10-21

Inspected the saved packet first and ran the prescribed unmodified dry run.
`deliver2.py NP sk-def-sf-admissible --no-push` exited 1 against base
`9d44991e6`, with exactly the same five public-import declaration refusals;
nothing was pushed. The first is: `lean.declarations names
WeilConjectures.finiteTorConstructible, which the file does not declare and
which neither Mathlib nor the source has`. The other names are
finiteTorConstructibleCategory, finiteTorConstructibleIntegral,
finiteTorConstructibleIntegralCategory, and finiteTorFieldCoefficientCategory.

Read both delivered modules, the imported FiniteTorAmplitude source, and
check_lean_text in tools/stage2_delivery.py. All five rejected names are real
public declarations in the publicly imported project module. The gate checks
only directly parsed declarations or upstream_has; it does not follow that
public import. The requested superset therefore remains rejected by the tool.
Compared the packet against the refreshed shared clone without Git commands:
both nodes change only lean; the dependency preserves the landed primary
module, declaration and verbatim statement, and its declaration list is a
superset. The Sites module differs only by the required public import.

Re-ran scompile.py on both files together in dependency order: exit 0, no
errors or warnings. Preliminary times were 7.2/8.8 s, sandbox 5.4/8.6 s,
and library 7.2/8.8 s. Neither file contains sorry or a line over 100 characters.
Retained the H13 repair. No script was patched or bypassed, no live file was
edited, and no push was attempted after the failed preflight.


## Retained-packet validation completed, 2026-10-21

The saved packet now passes the prescribed initial dry run unchanged:
`deliver2.py NP sk-def-sf-admissible --no-push` printed
`OK (dry run): commit e4e28207fc4 passes the preflight and compiles; nothing pushed`.
The earlier public-import preflight failures above are historical and no longer
block this packet. No tool was edited or bypassed.

Final self-check against the wrapper-refreshed shared sources confirms both node
copies change only `lean`; the Sites source adds exactly the public import of
FiniteTorAmplitude, and the superset lists the unchanged etale declaration plus
all five original public declarations. Both delivered files contain no sorry,
explicitly disable autoImplicit, and satisfy the 100-character line limit.
The item's mathematical statement and implementation remain unchanged.

Explicit prescribed scompile.py of both delivery files in dependency order
completed with exit 0, no errors or warnings: preliminary 7.2/8.8 seconds,
sandbox 5.4/8.6 seconds, and library 7.2/8.8 seconds. The H13 repair is retained
and is ready for the prescribed delivery wrapper.
