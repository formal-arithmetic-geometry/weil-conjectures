## What changed

Proved `Algebra.popescu_char_p_preparation_quotient` with its original signature unchanged.
The proof explicitly constructs the quotient algebra homomorphism and quotient prime,
proves finite presentation using the finitely generated extended ideal, and proves
minimality directly from the supplied maximal-ideal power containment. Dimension zero
then follows from Mathlib's localization of a minimal prime theorem.

Added the fully proved generic module
`Sheaf.RingTheory.EssentiallySmoothLocalizedQuotientFactorization` and its theorem
`Algebra.essentiallySmooth_localized_quotient_factorization`. It constructs the local
quotient maps, factors them through I and K, constructs the tensor algebra E and both
factorization maps, proves essential smoothness by localization base change, and verifies
the composite by tensor induction. Its private `Algebra.essentiallySmooth_baseChange`
helper is fully proved. No definition, existing statement, or public import was changed.
The new import in the original module is proof-only, as is the Krull dimension import.

Updated the original node's proof, proof dependencies and proof origin to match the Lean
argument. Added one node for the proved generic lemma. The unit's realized statements
and steps are unchanged. The original interface retains unused positive-characteristic
and prior-preparation hypotheses; a declaration-local unused-variable linter setting
preserves those binder names without compiler warnings.

## Proved and sorry left

Closed 1 original hole: `Algebra.popescu_char_p_preparation_quotient`
(node `popescu-char-p-preparation-quotient`).

New fully proved declaration: `Algebra.essentiallySmooth_localized_quotient_factorization`
(node `lem-weil-pbc-essentially-smooth-localized-quotient-factorization`).
The private base-change helper is also proved. There are no sorries in either delivered
module, no added holes, and no decomposition into unproved statements.

Both modules compile together without warnings through the required local compiler.
`#print axioms` for both public theorems reports exactly `propext`, `Classical.choice`,
and `Quot.sound`. All algebra witnesses
are explicit constructions. Destructing the hypothesis's auxiliary data and the proved
essential-smoothness presentation introduces no arbitrary data from an unproved theorem.

## No longer needed

No original imports were removed. The following planned proof dependencies are removed
from the original node and are not used anywhere in the delivered argument:

- `lem-weil-pbc-localization-at-prime-of-quotient`: construct the local quotient maps
  directly with `Localization.localRingHom`; no quotient/localization isomorphism is needed.
- `lem-weil-pbc-finite-presentation-base-change-composition`: use finite presentation of
  a quotient by a finitely generated ideal and restriction of scalars instead.
- `lem-weil-pbc-localization-noetherian`: the prime argument does not require Noetherianity.
- `lem-weil-pbc-noetherian-local-quotient-artinian-local`: minimality and dimension zero
  follow directly from the power bound; no Artinian quotient is used.

These are Mathlib leaves, so no separate Sheaf module is pruned. The smooth base-change
and localization base-change dependencies remain needed in the new proved generic lemma.
Whether these four nodes remain reached by other modules is the maintainer's closure check.

## Where the brief, the DAG or earlier work was wrong

The current statement is usable and no statement repair is needed. The older disputed
interface has already been repaired in the baseline. The DAG's Noetherian-Artinian route
and quotient/localization isomorphisms were longer than needed, not false.

The generic descent statement was checked on J=0, I=K=0, C or D the zero ring, and on
independent universes for the target ring: its construction only requires the stated
quotient prime and local factorization. For the dimension step, quotient nontriviality
comes from q₀ being a prime; dimension zero is never asserted for a trivial local ring.

LeanSearch was unavailable (Internal Server Error); the search record says unavailable,
without drawing a no-match verdict. LeanFinder, Loogle, and source searches worked.
`blueprint_refs.py ancestor popescu-char-p-preparation-quotient` returned None because
this chain has module-valued created.item records; the new node inherits the original
node's explicit blueprint ancestor and adds the original node to its via list.
The cited Stacks source was read from the existing local Stacks source copy.

## New nodes

`lem-weil-pbc-essentially-smooth-localized-quotient-factorization` records the proved,
characteristic-free quotient/tensor descent lemma. It states only the factorization
portion of the original argument, with no dimension, minimal-prime, singular-ideal,
parameter-regularity, finite-presentation, or field hypothesis. Its proof is complete,
including essential smoothness and the universe bound. No change records or forced
adaptations are needed.


## Second reading by G2

1. The original declaration signature was compared byte for byte with the repository version; the
   theorem statement is unchanged, and the proof constructs all quotient and localization data.
   Verdict: passes.
2. Both delivered modules compile with the required local compiler; grep found no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. A scratch `#print axioms` check
   reports only `propext`, `Classical.choice`, and `Quot.sound` for both public theorems. Verdict:
   passes.
3. The split-off generic factorization theorem is characteristic-free, strictly smaller than the
   target, and has a matching DAG node and complete docstring proof. Its edge cases J = 0, I = K = 0,
   zero C or D, and independent universes were checked. Verdict: passes.
4. The proof follows the quotient, finite-presentation, minimal-prime, dimension, and tensor
   factorization route; the four obsolete planned dependencies are removed from the node while the
   unit's realized statements and steps remain unchanged. Proof-only imports are plain imports.
   Verdict: passes.
5. Node proof steps, proof dependencies, proof origin, Lean records, and the new node agree with the
   delivered declarations. No statement or definition changes or forced adaptations were made.
   Verdict: passes.

Changed only the report by recording this second reading; no Lean proof or DAG repair was needed.
