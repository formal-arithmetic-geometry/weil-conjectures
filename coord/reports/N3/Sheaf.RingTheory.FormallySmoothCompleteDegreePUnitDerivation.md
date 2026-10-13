## What changed

Proved `Algebra.exists_degree_p_presentation_unit_derivation_of_formallySmoothAdic` in
`lean/Sheaf/RingTheory/FormallySmoothCompleteDegreePUnitDerivation.lean`, with its original
signature and visibility. All added helpers are private and fully proved. No other module
is adapted and no public import is changed.

The proof constructs the degree-p field presentation over the specified intermediate field,
constructs a finite coefficient algebra using an integral basis and denominator clearing,
extends a detecting derivation using formal smoothness and localization, and transports the
polynomial quotient through explicit tensor equivalences. It keeps the original coefficient:
after clearing denominators, the Leibniz rule shows that its derivative is a factor of a unit.
The ideal mapping and relation mapping are proved explicitly.

Added proof imports: `Mathlib.FieldTheory.KummerPolynomial`,
`Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed`,
`Mathlib.RingTheory.DedekindDomain.IntegralClosure`,
`Mathlib.RingTheory.TensorProduct.Finite`, and
`WeilConjectures.RingTheory.Derivation.Localization`.
Updated the existing node's proof and proof dependencies to describe this construction.
The unit's route and all existing statements are preserved.

## Proved and sorry left

Closed one existing hole:
`Algebra.exists_degree_p_presentation_unit_derivation_of_formallySmoothAdic`
(node `lem-weil-pbc-fs-complete-degree-p-unit-derivation`).
There are no `sorry`s left in the delivered module and no holes added or split off.
This is a proof from existing stated dependencies, including
`Derivation.exists_apply_ne_zero_of_not_pth_power`; the remaining holes in that imported theorem's dependency closure are not claimed
closed by this delivery.
Every new helper, including the finite model, localization extension and tensor presentation,
is proved without an additional assumption or hole.

Local compilation passes without warnings. The dry run additionally probes all added constants.
The argument does not assume a nonzero generic fibre: the characteristic computation uses
its structural map from M, and images of field units remain units in a zero ring.
It handles p=2 and arbitrary coefficient-field imperfection. The finite model is constructed
from Mathlib's proved integral-basis theorem, not chosen from any unproved existence theorem.

## No longer needed

Removed `Sheaf.FieldTheory.PurelyInseparablePthRootTower` and the dependency
`lem-weil-pbc-purely-inseparable-pth-root-tower`. The fixed-degree argument uses only the
Mathlib irreducibility leaf `lem-weil-pbc-x-pow-p-minus-t-irreducible` and direct field algebra.

Removed `Sheaf.RingTheory.Derivation.CompletionAndLocalization` as a direct proof import.
No completion of a derivation is needed here. The required localization extension is obtained
from the already proved upstream `IsLocalization.extendDerivation` and packaged privately;
the combined node `lem-weil-pbc-derivation-extends` is therefore also removed from
`proof_deps`. Its completion assertion and canonical-localization wrapper are unnecessary;
the proof uses the upstream construction directly.

Removed the direct `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic` import because the
integral-basis import provides it transitively. Its finite-integral-generators node is still
used and is not pruned. No claim is made that another target ceases to need these modules.
All other original proof imports remain necessary for the constructed argument.

## Where the brief, the DAG or earlier work was wrong

The pth-root tower theorem returns a presentation over its own final intermediate field,
not immediately over the prescribed M. The prime-degree simple-order argument resolves this
without changing that dependency or importing the full tower.

The canonical-localization interface encountered an integer-algebra/semiring instance mismatch
when transporting its result through a ring equivalence. Using the source library's proved
extension construction for the actual localization avoids that mismatch and any forced
adaptation. This is an interface issue, not a mathematical dispute.

The source's finite coefficient model can be obtained from a general integral K-basis;
no separate pure-inseparability scaling proof or additional statement is necessary. The
original docstring remains unchanged, while the node records the shorter implemented route.
Searches used msearch leanfinder, loogle and grep, plus repository and Mathlib rg searches.
No target statement, definition, unit statement or existing public signature was changed.

The resumed worker recompiled the inherited proof without errors or warnings, checked its
original signature and public imports, and read the existing dependency signatures and the
unit realization record. The unit-level nodes are unchanged. Stacks Tag 07PM was read online
because the literature source is absent on this machine. The inherited search log records
leanfinder, loogle and grep searches. The delivery dry run passed; the second reader's section
is intentionally reserved for the next worker.

## Second reading by N3

1. **Interface: pass.** Read the complete 393-line delivered module and its repository
   version and inspected their diff. The sole existing declaration,
   `Algebra.exists_degree_p_presentation_unit_derivation_of_formallySmoothAdic`, has a
   byte-identical signature, visibility, attribute and docstring. The public imports are
   byte-identical. All additions are private proved helpers; there are no adaptations,
   new public definitions, changed hypotheses, changed conclusions or change records.

2. **Proof and axioms: pass, relative to the existing open dependencies.** Compiled the
   module with `lcompile.py --all` without errors or warnings. Searched the delivered
   Lean for forbidden constructs and holes: none. Compiled a scratch copy with explicit
   `#print axioms` commands. `degree_p_coefficient`, `finite_fraction_model`,
   `localized_derivation_extension` and `tensor_degree_p_presentation` use only
   `propext`, `Classical.choice` and `Quot.sound`. The main theorem additionally uses
   `sorryAx` through its imported open dependencies; this is not a claim that the
   theorem's entire import closure is axiom-free. The two private definitions are
   explicit compositions of equivalences and maps, with proved identities. The finite
   model is the adjoin of an integral basis from Mathlib's proved
   `FiniteDimensional.exists_is_basis_integral`, whose proof I read; no arbitrary
   witness of an unproved existence theorem defines data.

3. **Split statements: pass (none).** No new node, public statement or hole is split
   off. Read the helper proofs: the least positive Frobenius exponent produces a root
   outside the base field; prime degree makes its simple intermediate field all of L.
   Clearing basis-coordinate denominators proves the fraction-field property of B.
   Clearing the coefficient denominator preserves the non-pth-power condition.
   Checked the detecting-derivation theorem's domain, characteristic, finite-type and
   complete-local-base hypotheses, and the extension theorem's completeness and
   formal-smoothness hypotheses against their actual declarations. The finite tensor
   model need not be local. All arguments include p=2; a perfect M cannot meet the
   non-pth-power hypothesis. No nontriviality of the generic tensor ring is assumed:
   field units map to units even in the zero ring, and p=0 is transported by its
   algebra map. There is no regularity assumption hidden in a helper.

4. **Route, search and pruning: pass.** Independently read
   [Stacks Tag 07PM](https://stacks.math.columbia.edu/tag/07PM), the degree-p induction
   and final derivation paragraph, and the unit record `dag/units/sk-thm-p1.json`
   including its realized statement and steps. This delivery changes only the
   coefficient/presentation argument below that unit; no realized node is bypassed.
   Ran fresh msearch leanfinder for the prime-degree purely inseparable presentation,
   loogle for `Derivation, RingEquiv`, and grep for simple prime-degree extensions,
   integral bases, minimal-polynomial equivalences and derivation extensions. Also
   searched both project roots and the upstream RingTheory/FieldTheory sources.
   The searches found the ingredients already used, not a theorem replacing the
   complete adic unit-derivation construction. The upstream localization construction
   is already used directly. Checked each proof import against its use. The report's
   pruned nodes are exactly the two old proof dependencies absent from the new list:
   `lem-weil-pbc-purely-inseparable-pth-root-tower` and
   `lem-weil-pbc-derivation-extends`; their direct modules are removed. The redundant
   direct integral-closure import is also listed, while its generator lemma remains
   used. No claim is made that these modules disappear from every target's closure.

5. **DAG agreement: pass.** Compared the old and delivered JSON: only `proof`,
   `proof_deps` and `proof_origin` change. The new proof-dependency list is exactly the
   union of the steps' `uses`. Read the recorded statements/declarations of these
   dependencies. The six steps match the field presentation, finite integral model,
   detecting derivation, complete formally smooth tensor extension, localization and
   conjugation, and quotient transport in Lean. In particular, the final coefficient
   stays g: the Leibniz power rule gives D(e^p)=0, so the unit D(e^p*g) implies that
   D(g) is a unit. The relation and its principal ideal are transported explicitly,
   rather than assumed compatible. The original Lean statement record is unchanged.

**Changes by the second reader:** added this independent review and fresh search records.
No Lean or DAG repair was necessary. One existing hole is closed, zero holes are added,
and zero statements are split off. The result remains relative to imported open lemmas.
