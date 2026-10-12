## What changed

Kept every existing declaration signature and docstring byte for byte. Proved the
Noetherian conjunct and the Noetherian clause inside `Algebra.IsGeometricallyRegular`
using Mathlib Noetherian instances, `AdicCompletion.isNoetherianRing` and
`Ideal.isNoetherianRing_fiber`. The new proof-only component supplies regularity
for each finite purely inseparable base change. Removed unused proof imports.

## Proved and sorry left

Closed the syntactic hole in
`MvPowerSeries.formalFiber_polynomial_isGeometricallyRegular` (node
`lem-weil-pbc-helper-g-ring-char-p`). Added one named hole:
`MvPowerSeries.formalFiber_polynomial_geometricComponent` (node
`new-lem-weil-pbc-helper-g-ring-char-p-geometric-component`).
The Noetherian clauses are proved independently; the finite purely inseparable
base-change regularity argument remains open. This is a decomposition, not a
complete proof: one hole closed, one added, net zero. Axiom checks allow `sorryAx`
from the component and remaining imported proof dependencies.

## No longer needed

Removed direct imports from the original module:

- `Sheaf.FieldTheory.PurelyInseparableDegreePIntermediate`
- `Sheaf.RingTheory.CompletionFiniteExtension`
- `Sheaf.RingTheory.CompletionFiniteQuotient`
- `Sheaf.RingTheory.CompletionRegularLocal`
- `Sheaf.RingTheory.Derivation.CompletionAndLocalization`
- `Sheaf.RingTheory.Derivation.DetectNonPthPower`
- `Sheaf.RingTheory.FiniteSubalgebraFractionField`
- `Sheaf.RingTheory.HypersurfaceDerivationRegular`
- `Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete`
- `Sheaf.RingTheory.PurelyInseparableIntegralPrimeUnique`
- `Sheaf.RingTheory.RadicialPrimeUniqueDegreeP`
- `Sheaf.RingTheory.RegularLocalLocalization`
- `Sheaf.RingTheory.RegularRingNormal`
- `Sheaf.RingTheory.RegularRingSmoothAscent`

Old proof dependencies no longer directly used by the target proof (the geometric
argument's dependencies remain on the component node):

- `lem-weil-pbc-power-series-field-cohen-regular-complete`
- `lem-weil-pbc-polynomial-ring-smooth`
- `lem-weil-pbc-regular-ring-smooth-ascent`
- `lem-weil-pbc-regular-local-localization`
- `lem-weil-pbc-completion-regular-local`
- `def-weil-pbc-finite-purely-inseparable-extension`
- `lem-weil-pbc-finite-purely-inseparable-degree-p-intermediate`
- `lem-weil-pbc-finite-subalgebra-fraction-field`
- `lem-weil-pbc-finite-algebra-noetherian`
- `def-weil-polynomial-ring`
- `lem-weil-pbc-regular-ring-normal`
- `lem-weil-pbc-normal-domain-of-local-normal`
- `lem-weil-pbc-purely-inseparable-integral-prime-unique`
- `lem-weil-pbc-radicial-prime-unique-degree-p`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-completion-finite-quotient`
- `lem-weil-pbc-completion-finite-extension`
- `lem-weil-pbc-derivation-nonzero-on-non-pth-power`
- `lem-weil-pbc-derivation-extends`
- `lem-weil-pbc-hypersurface-derivation-regular`
- `def-weil-pbc-g-ring`

These are direct dependency removals, not claims that these modules are globally
unreachable. The unit `sk-thm-p1` and all its `realized` fields are unchanged.

## Where the brief, the DAG or earlier work was wrong

The first component repeated the full geometric-regularity predicate, which itself
includes Noetherianity, so it did not isolate the unproved regularity condition.
Its node also depended on the target, making a DAG cycle. It retained unused plan
imports and duplicated two imports in the new module. These faults are repaired.
The component's natural-language statement used a nonexistent polynomial-ring
node name; it now cites the original statement dependencies.

## New nodes

`new-lem-weil-pbc-helper-g-ring-char-p-geometric-component`: regularity of each
finite purely inseparable base change, excluding an explicit original-fibre
Noetherian clause. Its four-step source proof is retained from the original plan,
with the degree-one case, finite algebra models, radicial primes, completion
identifications, and derivation criterion. No existing statement or definition
changed, so there is no change record.

## Second reading by T3

1. Compared the delivered target with the repository using `diff`; the existing
signature, visibility, universes and docstring are byte for byte unchanged. There
are no definitions or forced adaptations in the delivery. PASS.
2. Compiled both modules locally through `lcompile.py` in import order, without
errors or warnings. Only the named component has `sorry`; no forbidden declaration
forms or arbitrary data selected from an unproved existence theorem occur. The
axiom probe checks both declarations, with standard axioms and `sorryAx` only. PASS.
3. Read the source proof of Stacks 07PR in the local Stacks source and checked the
component against the definition of geometric regularity. Cases n=0, m=0, q=0 and
the degree-one extension are covered by the base case; imperfect coefficient fields
are allowed and the derivation argument handles inseparable extensions. Searched
Mathlib with leanfinder, loogle, leansearch and grep using new wording, and searched
upstream and Sheaf for alternative formal-fibre results; no independent shorter
route was found (the complete-local generic-fibre route already uses this target).
The full induction is not a proof that can be closed in a few minutes. PASS after
repairing the component to the regularity condition.
4. Removed unused direct imports and listed every old target proof dependency
absent from the new proof above. Kept statement imports public and proof imports
plain. Checked `dag/units/sk-thm-p1.json`: no unit route is bypassed. PASS.
5. Updated target dependencies to the completion Noetherian theorem, fibre
Noetherian theorem and component. Replaced the component's circular dependency
with the source's four genuine proof steps and their union of dependencies;
checked required new-node fields and the verbatim Lean signature. PASS.

Second reading changed the split statement, its proof docstring and DAG dependencies,
removed unused/duplicate imports, factored the shared Noetherian proof, and corrected
the report's progress and pruning claims.
