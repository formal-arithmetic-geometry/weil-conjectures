## What changed

Reduced `isN1_adjoin_singleton_of_isNagataRing` without changing its signature or docstring.
The private proved helper `adjoin_singleton_normal_away` chooses one nonzero denominator,
embeds the singleton adjoin in the fraction-field subalgebra representing that localization,
proves it is also the localization of the singleton adjoin, and transports integral closedness.
The main proof establishes finite type and Noetherianity, applies the local N-1 criterion to
both the singleton adjoin and each finite cover, and descends N-1 along the finite extension.

Added three statement modules. `AdjoinSingletonLocalUnramified` is proved from the existing
principal-quotient criterion: it handles the zero generator by finite-over-Nagata and Nagata
localization, and explicitly verifies nonvanishing and maximal-ideal membership otherwise.
`AdjoinSingletonPrincipalQuotientConditions` isolates the kernel/quotient calculation and
its three associated-prime consequences. `AdjoinSingletonMaximalFiniteCover` isolates the
residue-polynomial lift, finite splitting extension, and shifted-generator reduction.
The last two statements remain holes. The cover takes the local calculation as a hypothesis,
so these two remaining items can be worked on independently.

Added proof-only imports of the two new modules used by the main theorem. Public imports
and all existing public signatures are unchanged. No definitions, axioms, interface changes,
or forced adaptations were introduced. All four modules compile together without warnings
through lcompile.py. The delivery dry run supplies the final mechanical check.

## Proved and sorry left

Closed the sole original hole: `isN1_adjoin_singleton_of_isNagataRing`
(lem-weil-pbc-normal-nagata-monogenic-n1). This is a decomposition, not a complete proof
with only the three allowed axioms: the existing N-1 criterion, finite-extension descent,
and analytic-unramifiedness theorems also retain their upstream holes.

New proved declarations: private `adjoin_singleton_normal_away` (Mathlib only), and
`isAnalyticallyUnramified_adjoin_singleton_atPrime_of_mem`
(lem-weil-pbc-monogenic-generator-in-maximal-unramified), proved from named dependencies.

Exactly two new holes, both the entire proof of a public named theorem:

- `adjoin_singleton_atPrime_principal_quotient_conditions`
  (lem-weil-pbc-monogenic-principal-quotient-conditions), in
  `Sheaf.RingTheory.AdjoinSingletonPrincipalQuotientConditions`.
- `exists_finite_cover_adjoin_singleton_atPrime`
  (lem-weil-pbc-monogenic-maximal-finite-cover), in
  `Sheaf.RingTheory.AdjoinSingletonMaximalFiniteCover`.

There are no holes in the item's module or in `AdjoinSingletonLocalUnramified`.
Hole accounting for this delivery: one original hole closed, two holes added; net -1.
No arbitrary witness from either new hole is used to define data: the finite-cover witness
is eliminated only inside the proof of a proposition.

## No longer needed

Removed these seven proof imports from the item's module:

- `Sheaf.RingTheory.AnalyticallyUnramifiedPrincipalCriterion`
  (lem-weil-pbc-analytic-unramified-principal-criterion).
- `Sheaf.RingTheory.FiniteOverNagata`
  (lem-weil-pbc-finite-over-nagata-nagata).
- `Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimes`
  (lem-weil-pbc-normal-domain-fractional-principal-quotient-ass).
- `Sheaf.RingTheory.IsAnalyticallyUnramifiedOfIsNagataRing`
  (lem-weil-pbc-local-nagata-domain-analytically-unramified).
- `Sheaf.RingTheory.JapaneseDomain` (def-weil-pbc-japanese-domain).
- `Sheaf.RingTheory.NagataLocalization` (lem-weil-pbc-nagata-localization).
- `WeilConjectures.AlgebraicGeometry.Regular` (lem-sc-normal-dim1-dvr).

JapaneseDomain remains publicly available through NagataRing. The criterion,
FiniteOverNagata, local-Nagata analytic theorem and NagataLocalization are imported by
the proved local calculation, so this is import relocation rather than removal from the
entire closure. FractionalPrincipalQuotientAssociatedPrimes and the dimension-one DVR
result remain planned dependencies of the new quotient-conditions node; they are not
imported into its currently holed proof. No mathematical part of the Stacks route is dropped.

The following former direct proof dependencies of the main node have moved to the new
finite-cover or quotient-conditions nodes: Zariski's lemma; Nagata localization; normality
of the integral closure in a finite extension; finite-over-Nagata; finite-algebra integrality;
lying over; primes above maximal ideals; leading-coefficient-times-root integrality;
fractional-principal associated primes; normal dimension-one DVRs; the analytic principal
criterion; local-Nagata analytic unramifiedness; finite-algebra Noetherianity; maximal-ideal
contraction; and the integral-closure/finiteness/Japanese definitions. They are not claimed
to be globally unnecessary. The unit's statement and all realized unit steps are preserved.

Complete list of former direct `proof_deps` absent from the new main-node route:

- `def-weil-finitely-generated-module`
- `def-weil-pbc-integral-closure`
- `def-weil-pbc-japanese-domain`
- `def-weil-pbc-normal-ring`
- `lem-sc-normal-dim1-dvr`
- `lem-weil-pbc-analytic-unramified-principal-criterion`
- `lem-weil-pbc-finite-algebra-is-integral`
- `lem-weil-pbc-finite-algebra-noetherian`
- `lem-weil-pbc-finite-over-nagata-nagata`
- `lem-weil-pbc-integral-closure-finite-extension-normal`
- `lem-weil-pbc-integral-injective-lying-over`
- `lem-weil-pbc-integral-maximal-contracts-maximal`
- `lem-weil-pbc-integral-prime-over-maximal-maximal`
- `lem-weil-pbc-leading-coefficient-times-root-integral`
- `lem-weil-pbc-local-nagata-domain-analytically-unramified`
- `lem-weil-pbc-nagata-localization`
- `lem-weil-pbc-normal-domain-fractional-principal-quotient-ass`
- `lem-weil-pbc-zariski-lemma`

`def-weil-pbc-normal-ring` is still expressed by the unchanged domain and
integrally-closed hypotheses and used in the proved normal-open helper; its absence
from direct proof dependencies does not remove the normality assumption.

Second reading also removed the redundant proof import
`Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic` from
`AdjoinSingletonLocalUnramified`; its declarations are already available through
the retained public imports.

## Where the brief, the DAG or earlier work was wrong

The shorter-looking route through `isNagataRing_polynomial` is circular: its monogenic
N-2 dependency reaches this item. import_direction.py rejects that import. It was not used.
No mathematical error was found in the stated Stacks route. The repository's literature
payload is absent on this machine; the source was read from the available local copy of
algebra.tex, Tag 0334, proposition-nagata-universally-japanese, lines 46131--46221.
LeanSearch returned Internal Server Error and is recorded as unavailable, not as no match.
LeanFinder and actual Mathlib/source searches found no direct replacement for either hole.

Edge cases checked: zero generator uses the Nagata local-domain theorem; the nonzero
quotient-conditions statement cannot be invoked for zero; a field with its zero maximal
ideal cannot satisfy the nonzero generator-in-maximal hypothesis; a unit generator makes
that hypothesis impossible. The denominator argument includes x=0, since fraction-field
representations always have a nonzero denominator. The cover has no requirement that the
finite extension be local: all maximal localizations are treated separately, which avoids
the false assumption that localizing a finite algebra at one prime is still finite.

The normal dimension-one DVR lemma remains a tool in the quotient-conditions plan,
as it was in the original node; no new departure from the unit route is proposed.

## New nodes

`lem-weil-pbc-monogenic-principal-quotient-conditions` states exactly the three hypotheses
needed by the existing principal-quotient criterion, for nonzero x in the maximal ideal.
Its source and full kernel-induction, associated-prime, valuation and quotient arguments
are recorded in the module docstring and node. It has no analytic-unramifiedness or N-1
conclusion. Searches of the DAG, blueprint and library found no existing statement of
these combined monogenic conditions.

`lem-weil-pbc-monogenic-generator-in-maximal-unramified` records the proved local
calculation, including the zero-generator case, in its own module. It combines the preceding
strictly algebraic conditions with the existing criterion. It is needed to instantiate the
finite-cover theorem's local-calculation hypothesis.

`lem-weil-pbc-monogenic-maximal-finite-cover` gives a finite injective domain extension
of one maximal localization, a normal principal open, and analytic unramifiedness of its
maximal localizations, assuming the generator-containing local calculation. It concludes
neither global nor local N-1; the two local criteria and finite descent are written in the
main proof. Its source is Tag 0334's residue-polynomial splitting reduction. The extension
and local-calculation universes are Type(max u v), sufficient for the finite splitting-field
and integral-closure construction. No change record is needed because existing interfaces
are preserved and the new statements have their own nodes.

## Second reading by U2

1. **Interfaces:** compared the existing module with the repository by `diff -u`
   and the declaration parser. The target signature and its existing docstring are
   byte-for-byte unchanged; public imports are unchanged. The only new declarations
   are the private normal-open helper and the three declared new-node theorems.
   No existing definition or statement changes and no change records are needed.

2. **Proof and axioms:** compiled all four delivered modules in import order with
   `lcompile.py --all`; no errors or warnings. Inspected every proof, including the
   denominator localization's inclusion, surjectivity and injectivity arguments,
   and the two uses of the local N-1 criterion followed by finite-extension descent.
   Scratch copies with `#print axioms` check every new declaration and the target.
   The private normal-open helper has only `propext`, `Classical.choice`, `Quot.sound`;
   the other declarations additionally depend on `sorryAx`, precisely as expected
   from the two new holes and retained open upstream statements. No forbidden
   declaration, holed definition or data construction from an arbitrary witness.
   The finite-cover existential is eliminated inside a propositional proof only.

3. **Split statements:** read the actual Stacks algebra.tex, Tag 0334, Step 5,
   lines 46131--46221, in /home/ubuntu/work-bp/sheaf/literature/stacks-project/.
   Checked the quotient theorem's nonzero generator and maximal-ideal membership,
   all three associated-prime conclusions, and the finite-cover theorem's finite
   injective map, normal principal open, Noetherian domain and all maximal
   localizations. The local-calculation hypothesis is supplied explicitly in the
   main proof; the Type(max u v) universe accommodates the finite splitting field
   and its integral-closure subring. Neither new hole restates N-1. Their source
   proofs are complete in their docstrings and their matching nodes exist.
   Zero and unit generators and the field/zero-maximal-ideal cases were checked:
   the quotient theorem excludes zero, a unit cannot lie in a maximal ideal, and
   the local theorem handles zero by finite-over-Nagata and Nagata localization.
   For example R=Z, x=2 and m=(2) gives the familiar regular height-one
   localization and reduced-completion prime quotient; x=1/2 is a unit in Z[1/2]
   and cannot meet that local theorem's generator-membership hypothesis.
   Repeated LeanFinder searches with different wording for quotient-associated
   primes and residue-polynomial splitting covers, plus grep of Mathlib,
   upstream WeilConjectures, lean/Sheaf and the DAG. Found localization and
   residue-field ingredients, but no direct substitute for either hole. Neither
   is a few-minute remaining proof. Verdict: a valid decomposition, net -1 hole.

4. **Route and pruning:** verified the normal principal open is genuinely proved
   from Mathlib; analytic unramifiedness is converted to N-1 only in the main
   proof, and the cover is not incorrectly asserted finite after localizing at
   a single prime. Checked sk-thm-p1.json `realized`; this item is below the unit
   steps, so none is bypassed or altered. The polynomial-Nagata shortcut is
   circular through AlgebraicMonogenicNagataDomainN2 and this item. The seven
   old direct imports are correctly reported as removed or relocated, rather
   than all globally pruned. Added the exhaustive old-direct-dependency list,
   including the previously unmentioned normal-ring definition. Removed one
   redundant Mathlib proof import. Localization.Submodule stays public in the
   new statement modules because their signatures require the Noetherian
   localization instance when forming IsAnalyticallyUnramified.

5. **Nodes:** checked all four JSON files against their Lean declarations and
   hypotheses, sources, chapter/unit, creation and blueprint records. Each
   proof_deps is exactly the union of its proof steps' uses. The existing node
   changes only proof, proof_deps and proof_origin; the new main route names
   the actual normal-open, local-calculation, cover, local-criterion and descent
   steps. New nodes are strictly parts of the argument, with searches recorded.
   The two still-open node proofs are their documented plans, not claimed as
   finished Lean proofs. Verdict: metadata agrees with the delivered reduction.

Changes in this second reading: removed the redundant IsIntegral.Basic proof
import; completed the report's old-dependency pruning inventory; added this
independent review. No proof bodies, signatures, definitions or nodes changed.
