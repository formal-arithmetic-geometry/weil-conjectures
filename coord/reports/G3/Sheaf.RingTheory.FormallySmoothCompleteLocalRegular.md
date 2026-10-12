## What changed

Replaced the sole `sorry` in `RingHom.isRegular_of_formallySmoothAdic` by a complete
proof reducing each prime fibre to the generic fibre over the complete local domain A/p.
The existing signature and all public imports are unchanged. The second reader moved
the unresolved generic-fibre plan's proof-dependency imports into its new module.

The proof obtains flatness from the existing closed-fibre theorem, proves pB proper by
locality, installs complete quotient structures using `quotient_complete_local`, and proves
that the induced quotient map is local. A proved private helper descends formal smoothness
by restricting a lifting problem, then factoring the lift through B/pB; no unproved
transport lemma is needed. Quotient-tensor equivalence and cancellation of base change
identify the generic fibre with the original prime fibre. Another proved private helper
transports geometric regularity along an algebra equivalence, including every finite
purely inseparable field extension.

Added `Sheaf.RingTheory.FormallySmoothCompleteLocalGenericFiber`, stating the remaining
coefficient-ring and degree-p induction argument for a domain and its generic fibre only.
This is a strict part of the source argument: it neither gives flatness of the original
map nor controls its non-generic fibres. The upper proof supplies the prime-quotient
reduction and both transports in Lean. Updated both DAG records to match this division.

## Proved and sorry left

Closed: `RingHom.isRegular_of_formallySmoothAdic`
(lem-weil-pbc-formally-smooth-complete-local-regular). No direct sorry remains in the item.
Its two private helper theorems are completely proved.

Added one hole: `Algebra.isGeometricallyRegular_genericFiber_of_formallySmoothAdic`
(lem-weil-pbc-formally-smooth-complete-local-generic-fiber), with proof exactly `by sorry`.
Its source and full coefficient-ring/denominator-clearing/derivation proof are in its
module docstring and node. This is a decomposition: one upper hole closed, one lower hole
added, net zero. It is not an axiom-free completion of the regularity theorem.

Both delivered modules compile cleanly using lcompile.py --all. No definitions, existing
statements, public visibility, target signatures, or other groups' modules were changed.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.DegreePExtensionRegular`
- `Sheaf.FieldTheory.PurelyInseparablePthRootTower`
- `Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular`
- `Sheaf.RingTheory.Derivation.CompletionAndLocalization`
- `Sheaf.RingTheory.Derivation.DetectNonPthPower`
- `Sheaf.RingTheory.Derivation.FormallySmoothAdicExtension`
- `Sheaf.RingTheory.FiniteModuleComplete`
- `Sheaf.RingTheory.FormallySmoothAdicBaseChange`
- `Sheaf.RingTheory.FsAdicLiftOverFiniteCoefficientMap`
- `Sheaf.RingTheory.GeometricallyRegularFieldExtension`
- `Sheaf.RingTheory.LocalizationOfRegularRing`
- `Sheaf.RingTheory.RegularLocalOfFlatWithRegularClosedFiber`

These modules are not needed directly by the upper quotient-to-generic proof.
They are now ordinary proof imports of the new generic-fibre module; none is
pruned from the target import closure. Their existing
lemmas remain in the new generic-fibre node's proof dependencies: the coefficient-ring
construction, finite-coefficient lift, localization, purely inseparable tower, derivation
construction/extension, finite-module completeness, and degree-p regularity are still
needed by that argument. No claim is made that these nodes are pruned from the complete
mathematical dependency closure. No unit statement or realized step was bypassed.

The main node now uses only the flat closed-fibre theorem, complete quotients, the new
generic-fibre lemma, and the definitions used in the explicit quotient/tensor reduction.
No library node has become globally unnecessary in this delivery; pruned nodes: none.


Old main-node proof dependencies no longer used directly (retained below in the
generic-fibre plan or supplied by its definitions/Mathlib imports):

- `def-weil-pbc-adically-complete-ring`
- `def-weil-pbc-finite-purely-inseparable-extension`
- `def-weil-regular-scheme`
- `lem-weil-pbc-complete-local-domain-finite-over-regular`
- `lem-weil-pbc-degree-p-extension-regular`
- `lem-weil-pbc-derivation-extends`
- `lem-weil-pbc-derivation-nonzero-on-non-pth-power`
- `lem-weil-pbc-finite-module-complete-over-complete-noetherian`
- `lem-weil-pbc-flat-over-regular-with-regular-fibre`
- `lem-weil-pbc-fs-adic-base-change`
- `lem-weil-pbc-fs-adic-lift-derivation`
- `lem-weil-pbc-fs-adic-lift-over-finite-coefficient-map`
- `lem-weil-pbc-geometrically-regular-finitely-generated-extensions`
- `lem-weil-pbc-localization-base-change`
- `lem-weil-pbc-localization-of-regular-ring`
- `lem-weil-pbc-purely-inseparable-pth-root-tower`

## Where the brief, the DAG or earlier work was wrong

The original plan's general formal-smoothness base-change module is unnecessary for the
prime-quotient reduction: a direct lifting proof handles this particular base change.
It remains necessary for the coefficient/derivation argument in the new node.

Read Proposition 07PM in the local Stacks source copy, lines 12028–12115. As already
recorded in the original node, its induction cites descent-fs (07EH) for a base change;
the needed result is base-change-fs (07EG). The new node retains this correction.
The repository's literature/stacks-project/more-algebra.tex is absent on this machine;
the actual source was read at /home/ubuntu/c1-stacks-review/more-algebra.tex.

LeanSearch returned HTTP 500 and is recorded as unavailable, not as a failed match.
LeanFinder, Loogle, Mathlib/source grep, and blueprint searches found no exact shorter
result. The source's domain/generic reduction is therefore retained.

## New nodes

`lem-weil-pbc-formally-smooth-complete-local-generic-fiber`:
`Sheaf.RingTheory.FormallySmoothCompleteLocalGenericFiber`, declaration
`Algebra.isGeometricallyRegular_genericFiber_of_formallySmoothAdic`. It isolates original
steps 3–9 after the now-proved prime-quotient reduction. The node retains the explicit
finite coefficient-field argument, integrality by denominator scaling, the adjustment
f = e^p g, characteristic-zero case, degree induction, and the unit-valued derivation.
Searches are taken from this item's actual searches.jsonl; blueprint searches for generic
fibre, formally smooth, and 07PM found no matching imported blueprint statement.

Edge cases checked: p = 0 uses the original domain; p maximal reduces to a field base;
locality ensures pB is proper in every case. Characteristic zero has no nontrivial finite
purely inseparable extensions; the induction treats degree one separately. Nontriviality
of the domain excludes the zero base, and local rings exclude the zero target. The new
lemma does not require B to be a domain: its generic fibre may be a product or have
multiple prime ideals. Algebra equivalence transport uses the complete geometric
regularity predicate rather than regularity at a chosen point. No change record is needed
because no existing interface changed.

## Second reading by G3

1. PASS: compared the delivered main module with the repository using `diff -u`.
   The complete existing theorem signature and docstring are byte-for-byte unchanged;
   only its proof, ordinary proof imports, and two proved private helpers were added.
   The other module and node are new. No definitions, targets, or other modules changed.
2. PASS: compiled both modules in import order with `lcompile.py --all`, cleanly.
   Checked all delivered Lean for forbidden declarations and hollow definitions: none.
   Explicit scratch-copy `#print axioms` checks show only `propext`, `Classical.choice`,
   and `Quot.sound` for the two private helpers. The upper theorem additionally uses
   `sorryAx` through its open dependencies, and the new named generic-fibre theorem
   uses `sorryAx`. The only direct delivered hole is the new public named theorem.
3. PASS: independently read local Stacks More on Algebra, Proposition 07PM, proof
   lines 12028–12115, and the coefficient-lift, derivation-detection and derivation-lift
   declarations. The generic-fibre theorem is the domain/zero-prime part of that proof;
   it neither supplies arbitrary-prime quotient reduction nor flatness of the original
   map. Its full docstring and matching node include denominator scaling by a pth power,
   the characteristic-zero case, the finite coefficient model, and degree-p induction.
   Tested the argument at A a field, the zero prime, the maximal prime, degree one,
   characteristic zero, and B not a domain. Zero rings are excluded by the local/domain
   hypotheses; locality ensures pB is proper. No arbitrary existence witness is used
   to define data. Independent LeanFinder, Loogle, and grep searches used the query
   "adic lifting property complete local rings regular fraction field tensor algebra"
   and "Algebra.FormallySmooth, IsRegularRing"; no exact shorter result was found.
   Read nearby field, DVR, and polynomial formal-fibre results: their hypotheses or
   conclusions specialize different maps and do not prove this generic-fibre statement.
4. REPAIRED, now PASS: the upper proof follows the shortest explicit quotient reduction
   and transports the entire geometric-regularity predicate across a tensor equivalence.
   The first delivery omitted the new open node's planned proof imports, which could
   incorrectly remove unresolved work from the target import closure. Moved its twelve
   old proof imports into the generic-fibre module, together with the closed-fibre lemma
   and Mathlib localization dependencies. All added imports are ordinary `import`.
   Expanded `No longer needed` to list every old main-node proof dependency removed
   from its direct list. No globally pruned module is claimed. Checked sk-thm-p1's
   `realized`: neither node realizes a unit statement or step, and the unit route stays.
5. PASS: checked both nodes' proof steps, the union of their `uses` against `proof_deps`,
   proof origins, Lean statements, chapter/unit, and the new node's creation, search,
   source and blueprint records. The main node records the actual flatness and quotient
   proof; the new node records exactly the remaining coefficient/derivation induction.
   Existing node changes are confined to allowed proof fields. No change record is needed.

Changed during second reading: restored the unresolved generic-fibre plan's imports,
completed the direct-dependency pruning inventory, and recorded this independent review.
No proof or existing signature needed repair. One upper hole is closed and one strictly
lower hole added: this delivery is a decomposition, with net zero holes closed.
