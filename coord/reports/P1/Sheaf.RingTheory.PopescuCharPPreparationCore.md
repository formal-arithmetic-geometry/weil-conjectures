## What changed

Replaced the hole in `Algebra.exists_popescu_char_p_preparation_core` by a compiling proof
with the original signature and public imports unchanged. The proof first uses Mathlib's
`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes` and finite generation to obtain
a positive power of the localized maximal ideal contained in the extended singular ideal.
It then applies the remaining global coefficient construction and explicitly performs the
quotient base change, constructing the final algebra and both tensor maps.

Added `Sheaf.RingTheory.PopescuCharPPreparationGlobal`, with one open construction theorem.
This theorem takes the already-proved positive power bound rather than minimality, and
stops with the concrete polynomial ring `E = MvPolynomial (Fin t) D'` over a local Artinian
coefficient solution. Its maps are over the unlocalized polynomial base. It neither supplies
an algebra over the final localized quotient nor supplies the target tensor factorization.
The caller constructs `D = (Q/I) ⊗[R/I₀] E`, its quotient algebra and scalar towers, the map
`f` by tensor lifting, and the map `g` by tensor lifting after extending scalars on `b`.
Equality of their composite is checked on the right tensor generators. This isolates the
coefficient construction from the initial power argument and final localized assembly.

Added `Sheaf.RingTheory.EssentiallySmoothBaseChange`, proving
`Algebra.essentiallySmooth_baseChange` from the definition and Mathlib's smooth and
localization base-change theorems. The source and target base rings share universe `u`,
which suffices for `R/I₀` and `Q/I`; the algebra has its independent universe `v`.
The proof tensors the actual smooth localization model and transports the localization
structure. No existence theorem with an unproved proof supplies data to a definition.

Updated the owned node's proof route and added nodes for the open construction, the proved
base-change theorem, and the exact Mathlib minimal-prime localization result. The unit
`sk-thm-p1` and its realized steps are unchanged.

## Proved and sorry left

Closed the original syntactic hole in
`Algebra.exists_popescu_char_p_preparation_core` (node
`popescu-char-p-preparation-core`). The main theorem now has a complete Lean proof.

Proved without `sorry`: `Algebra.essentiallySmooth_baseChange` (node
`lem-weil-pbc-essentially-smooth-base-change`).

Added one hole: `Algebra.exists_popescu_char_p_preparation_global` (node
`lem-weil-pbc-popescu-char-p-preparation-global`). This is the only `sorry` in the
delivered files. Its source and full construction proof are in its docstring and node.
The original module has no remaining hole. This delivery is a decomposition: one original
hole closed and one construction hole added, giving net zero holes removed. It does not
claim that the characteristic-p construction, or the target's entire axiom closure, is proved.

All three delivered modules compile without errors or warnings under `lcompile.py`.
The construction's edge cases were checked against the proof: `d=0` uses a padded zero
parameter and positive exponent; `t=0` is a polynomial ring with no variables; `H=⊤`
is allowed by the power-bound interface and does not require minimality. Essential-smooth
base change permits zero rings and makes no flatness assumption on the base map.

## No longer needed

Removed these proof-only imports from the owned module, because their construction work
belongs to the remaining global theorem:

- `Sheaf.AlgebraicGeometry.Ogoma`
- `Sheaf.RingTheory.EssentiallySmoothComp`
- `Sheaf.RingTheory.ImprovePresentation`
- `Sheaf.RingTheory.PopescuEnlargeSolutionModulo`
- `Sheaf.RingTheory.PopescuSolutionModulo`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`
- `Sheaf.RingTheory.RegularRingSmoothAscent`
- `Sheaf.RingTheory.RegularSequencePolynomialVariables`
- `Sheaf.RingTheory.RegularSequencePowers`
- `Sheaf.RingTheory.SingularIdeal`
- `Sheaf.RingTheory.SingularIdealLocalizationSmooth`
- `Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower`
- `Sheaf.RingTheory.StrictlyStandardBaseChange`

These modules remain needed through the global construction; they are not claimed as
pruned from the targets' closure. The general zero-locus/radical comparison node
`lem-weil-pbc-zero-locus-eq-iff-radical-eq` is no longer a dependency of this construction
route: the exact Mathlib minimal-prime localization theorem replaces it. No existing
module is claimed to become globally unreachable. The finite-generation/radical-power
and localization-Noetherian nodes remain used in the main theorem.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original initial radical argument can be replaced by
an exact Mathlib result. The original construction boundary hid a useful earlier boundary:
`D'[t]` already gives a factorization over `R/I₀` before the final localization. This is the
remaining theorem's conclusion, while its final base change is now proved in the caller.
The retained correction `n=N+de`, with `e=8c`, is the existing repaired route; no new source
correction is introduced.

The source checkout named by the node is not populated in this clone's `literature/`.
Read the available local copy of `smoothing.tex`, including `lemma-resolve-general`,
items `item-power` through `item-eighth-resolve` and the `Ad(item-done)` paragraph.
Blueprint searches for `07FJ`, `essentially smooth`, `polynomial standardizer`, and
`minimal prime` found no duplicate imported blueprint statement. LeanSearch returned
Internal Server Error; this is recorded as unavailable, while Loogle, LeanFinder and
Mathlib/source grep results are recorded as actual searches.

## New nodes

`lem-weil-pbc-popescu-char-p-preparation-global`: the remaining global standardizer and
Artinian coefficient-solution construction. Its module contains the sole new hole. The
explicit positive power bound is an input, and the output coefficient algebra is the
actual polynomial ring over a local Artinian ring, before localization at the prime.

`lem-weil-pbc-essentially-smooth-base-change`: proved generic preservation of essential
smoothness under base change, using a smooth model and localization base change.

`lem-weil-pbc-minimal-prime-localization-radical`: a Mathlib leaf matched exactly to
`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`, with the source file and line.
No new Lean module or hole is introduced for this leaf.

No change record or forced adaptation is needed: existing signatures and public imports
are unchanged, and no other existing module was edited.

## Second reading by P1

1. Compared the delivered core module against the repository version. The theorem signature and all existing declaration statements are unchanged byte for byte; only proof imports and the proof body changed. The two added modules contain new declarations and are recorded by matching DAG nodes.

2. Compiled all three delivered modules with `lcompile.py --all`. Compilation succeeds without errors or warnings. The core proof has no `sorry`; the only remaining `sorry` is the named theorem `Algebra.exists_popescu_char_p_preparation_global`, which has a docstring source/proof and a matching split node. No axioms, unsafe declarations, hollow definitions, or forbidden implementation escapes were found in the delivered source.

3. Checked the new statements against the construction and edge cases. The global theorem takes an explicit positive power bound and returns the pre-localization polynomial coefficient construction; it is strictly weaker than and needed by the core theorem. The base-change theorem is the generic tensor localization argument and has no extra hypotheses. Search records and the node files document that no existing library theorem duplicates either declaration.

4. Checked the proof route and pruning. The core uses the exact Mathlib minimal-prime localization radical theorem, then the global construction, then explicit quotient/tensor assembly and the proved essential-smooth base-change theorem. The removed proof-only imports are no longer referenced by the core proof. The unit `sk-thm-p1` route remains represented by the core node and its dependencies; no unit step was bypassed.

5. Checked DAG agreement. The core node proof steps and dependencies match the implemented radical-power, global-construction, quotient, tensor, and base-change steps. The two new nodes carry statements, sources, proof plans, searches, Lean declarations, chapter, unit, and blueprint metadata matching their modules. No statement change or forced adaptation is present.

Changed in this second reading: added this review section to satisfy the stage-3 report contract. No Lean source or DAG content required repair.
