## What changed

Proved `AlgebraicGeometry.gabber_absolutely_algebraically_closed` with its signature unchanged.
The proof chooses the quotient presentation with `IsClosedImmersion.Spec_iff`, establishes the
two hypotheses of `Etale.gabberCriterion`, applies it in degree `q.toNat`, and transports its
conclusion back to `Z` using the existing Ext-to-derived comparison and scheme isomorphism.
All five steps of Stacks 09ZC and the unit route are retained.

Four new modules contain proved specializations used by this argument:

- `Sheaf.AlgebraicGeometry.GabberQuotientLocalizations`: constructs the fraction-field algebra
  of the prime localization, applies the proved ring-level 09Z9 lemmas, and applies
  `isStrictlyHenselianLocalRing_quotient` to the kernel of the surjective localization map.
- `Sheaf.AlgebraicGeometry.GabberPrincipalOpenClosedPresentation`: lifts the principal-open
  parameter and constructs its closed presentation over a localization of `R`. Surjectivity
  follows directly from `Localization.awayMap_surjective_iff`, without quotient-commutation
  glue. The zero-lift case uses the initial empty scheme. No proper-ideal hypothesis is added.
- `Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1`: applies the existing 09ZB theorem to that
  presentation and transports through `upperStarConstantSheafIso` and `Sheaf.functorH.mapIso`.
- `Sheaf.AlgebraicGeometry.ConstantEtaleCohomologyIsoComparison`: combines the existing proved
  `Scheme.nonempty_sheafH_extDerivedIso` with `Etale.cohomologyEquiv` and constant pullback.
  It holds for arbitrary abelian groups and schemes, including degree zero.

The item's proof imports are the localizations, principal-H1 and comparison helpers, plus
`Sheaf.Paper.GabberCriterion`; the principal-H1 helper imports the geometric presentation.
Its public imports and all existing declarations' signatures are unchanged. The node's
proof, proof dependencies and proof origin now describe this Lean proof.

All five sandbox modules compile locally without warnings. The delivery dry-run performs
its local axiom probes and the required server/preflight checks. Searches included
LeanFinder, Loogle and ripgrep; LeanSearch returned HTTP Internal Server Error for each
new statement, recorded as unavailable without a verdict.

## Proved and sorry left

Proved the item's sole original sorry:
`AlgebraicGeometry.gabber_absolutely_algebraically_closed`
(node `lem-weil-pbc-gabber-absolutely-algebraically-closed`).

Also proved every new theorem:

- `gabber_quotient_localizations`
  (`lem-weil-pbc-gabber-quotient-localizations`).
- `AlgebraicGeometry.gabber_principal_open_closed_presentation`
  (`lem-weil-pbc-gabber-principal-open-closed-presentation`).
- `AlgebraicGeometry.Etale.gabber_quotient_principal_h1`
  (`lem-weil-pbc-gabber-quotient-principal-h1`).
- `AlgebraicGeometry.Etale.isZero_constant_cohomology_iff_subsingleton_H_of_iso`
  (`lem-weil-pbc-constant-etale-cohomology-iso-comparison`).

No sorry remains in any delivered module; none was split off. The proof uses the existing
statements `Etale.gabberCriterion`, `isStrictlyHenselianLocalRing_quotient`, and
`Etale.isZero_constant_cohomology_one_of_isIntegrallyClosed`, which remain separate project
items with their existing nodes. The Ext-to-derived comparison is already proved.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing`: used in the principal-H1 helper.
- `Sheaf.RingTheory.StrictlyHenselianQuotient`: used in the prime-localization helper.
- `WeilConjectures.ConstructibleSheaf.Defs`: used in the comparison and principal-H1 helpers.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`: replaced by the already proved
  ring-level lemmas in `WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: visible through the new helper's public import.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: visible through the new helpers;
  the proof's inverse-image operations are still used.

The new geometry module needs no import of `Mathlib.RingTheory.Localization.Ideal`.

The complete delivered argument no longer uses these original planned nodes:

- `lem-weil-pbc-spec-domain-stalks-function-field`: work directly with ring localizations.
- `sbc-lem-etale-over-normal`: its scheme-level declaration is unnecessary; use the proved
  normal-local-domain ring lemmas from its source proof.
- `lem-weil-pbc-localization-quotient-commute`: prove surjectivity of `awayMap` directly.
- `lem-weil-pbc-spec-quotient-closed-immersion`: use `IsClosedImmersion.spec_of_surjective`
  for the localized quotient map.

For completeness, the following original direct proof dependencies have become statement
or inherited definition dependencies, rather than unused mathematical lemmas:
`def-weil-pbc-normal-ring`, `def-pc-separably-closed`,
`def-weil-pbc-henselian-terminology`, `def-weil-pbc-inverse-image`,
`def-weil-open-immersion`, and `def-weil-pbc-etale-site` (through constant sheaves and
inverse image). They remain needed notions; their absence as direct proof dependencies
is not a claim that these notions have been eliminated.

The remaining original local-ring, constant-pullback, principal-localization and H1
ingredients are used inside the new proved modules. No unit statement or unit proof step
was pruned. Globally shared modules may have other callers; the list concerns this argument.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement correction was needed. The original node's cohomology
transport and the conversion between derived cohomology and `Sheaf.H` were substantial
implicit glue, not an obstacle: the project already supplies a proved natural comparison
in `Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`. The route now names it.
Typeclass search does not unfold the carrier of `Sheaf.functorH.obj` while finding a
subsingleton instance, so the proof passes that instance explicitly to `Equiv.subsingleton`.

The read-only clone lacks the materialized literature files named by the nodes. The source
proof was checked on the official Stacks page https://stacks.math.columbia.edu/tag/09ZC,
and its quotient citation at https://stacks.math.columbia.edu/tag/05WS. The unit record
`dag/units/sk-thm-p1.json` was read and its route is retained.

## New nodes

`lem-weil-pbc-gabber-quotient-localizations` records the proved local-ring step in
`lean/Sheaf/AlgebraicGeometry/GabberQuotientLocalizations.lean`.

`lem-weil-pbc-gabber-principal-open-closed-presentation` records the proved geometric part
of the principal-open step in
`lean/Sheaf/AlgebraicGeometry/GabberPrincipalOpenClosedPresentation.lean`.

`lem-weil-pbc-gabber-quotient-principal-h1` records the proved H1 specialization in
`lean/Sheaf/AlgebraicGeometry/GabberQuotientPrincipalH1.lean`.

`lem-weil-pbc-constant-etale-cohomology-iso-comparison` records the proved generic transport
and vanishing comparison in
`lean/Sheaf/AlgebraicGeometry/ConstantEtaleCohomologyIsoComparison.lean`.

All four carry their source, complete proof steps, searches and exact Lean signatures.
No new sorry or change record was required.

## Second reading by Q2

1. Compared every delivered module with the read-only repository. Four modules are new;
   the sole existing theorem's signature is byte-for-byte identical up to `:= by`.
   Its docstring and public imports are unchanged. No existing definition or target
   statement changes, and no statement change record is needed. Verdict: pass.
2. All five modules compile without errors or warnings through `lcompile.py`.
   Source inspection found no `sorry`, axiom, unsafe/opaque declaration, external
   implementation, or kernel-check bypass in the delivered Lean. Scratch copies with
   `#print axioms` show only `propext`, `Classical.choice`, and `Quot.sound` for the
   geometric presentation and cohomology comparison. The main theorem, quotient-localization
   helper and principal-H1 helper additionally use `sorryAx` through the existing open
   quotient, H1 and criterion statements. Thus this closes the item's original sorry,
   conditionally on those existing project dependencies, rather than certifying the
   whole target closure as axiom-free. Verdict: pass under the stage-3 rule.
3. No statement was split off with `sorry`. Read all four new proved statements and
   their natural-language proofs: each is a distinct proper part of the argument.
   Checked the unit ideal, zero and unit principal-open parameters, arbitrary abelian
   coefficients in the comparison, degree zero in that comparison, and the main
   theorem's boundary q = 1. There is no added properness or nonemptiness hypothesis.
   Independent LeanFinder search with “quotient spectra” and “rational function field”,
   Loogle search for localization surjectivity, and ripgrep on both library roots found
   ingredients already used, but no complete duplicate. Verdict: pass.
4. Read the proof from its conclusion backwards and checked it against
   [Stacks 09ZC](https://stacks.math.columbia.edu/tag/09ZC) and
   [09Z9](https://stacks.math.columbia.edu/tag/09Z9). The quotient, local-ring,
   principal-H1, criterion and transport steps remain. The unit `sk-thm-p1` and all
   its `realized` entries are unchanged. The ring-level normal-domain lemmas implement
   the local-ring part of 09Z9 directly; they do not bypass a realized unit statement
   or step (the `sk-prop-etale-normal` record has empty `realized` entries).
   Checked every old proof dependency against the delivered nodes; expanded
   “No longer needed” to distinguish retained definition dependencies from the four
   unused planned lemmas. Narrowed public imports as described below. Verdict: pass.
5. Read all five node records with their Lean proofs. The original node changes only
   `proof`, `proof_deps`, and `proof_origin`. For every node, `proof_deps` is exactly
   the union of its proof steps' `uses`. The four new nodes have source, proof,
   searches, provenance, unit/chapter and exact Lean signatures. Changed the
   ring-level henselianity step's `elementary` flag to false: it invokes substantial
   proved theorems, rather than an elementary definition inference. Verdict: pass.

Changes by the second reader: replaced the new comparison helper's public
`TopologicalInvariance` import by public imports for `Sheaf.H`, `HasExt` and the
concrete-coefficient instances, retaining topological invariance as a proof-only import.
The principal-H1 helper now publicly imports the inverse-image and cohomology definition
modules and their required instances instead of the full topological-invariance module.
The comparison gets its sheaf-category instances through its existing public
`LowerShriek` import. No proof or signature was rewritten. Also corrected the elementary
flag and completed the pruning explanation above. No new sorry or change record.
