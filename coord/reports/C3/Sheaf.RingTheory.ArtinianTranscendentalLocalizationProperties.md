## What changed

Proved `Algebra.localization_artinian_transcendental_properties` directly in its original
module, with the original signature byte for byte. Added only the proof import
`Mathlib.RingTheory.HopkinsLevitzki`. Existing public imports and visibility are unchanged.

Reduction of evaluation modulo the residue maps identifies the prime coefficientwise,
using `Ideal.mem_map_C_iff`. Mathlib's Noetherian instances and
`isArtinianRing_iff_isNilpotent_maximalIdeal` prove Artinianity by transporting a nilpotence
exponent through ideal maps. The localization maximal-ideal criterion proves locality.
Explicit ULift polynomial data and the induced localization algebra equivalence witness
`EssentiallySmooth`; no object is chosen from an unproved existence theorem.

Removed the proposed intermediate modules `ArtinianTranscendentalPrime` and
`ArtinianTranscendentalLocalizationStructural`, their two proposed nodes, and the unnecessary
proof-only change record. Both intermediate arguments are now proved in the theorem body.
Updated the original node's proof and proof dependencies to describe this route.

## Proved and sorry left

Hole closed: `Algebra.localization_artinian_transcendental_properties` (node
`lem-weil-pbc-artinian-transcendental-localization-core-structural`).

Holes added: none. Holes left in the delivered module: none. This is a proof, not a
decomposition: one original hole closed, zero new holes. The first proposal's
`Algebra.transcendental_evaluation_prime_eq` and
`Algebra.polynomial_localization_at_coefficient_maximal_structural` are not delivered;
their arguments have complete local proofs instead.

A scratch copy's `#print axioms Algebra.localization_artinian_transcendental_properties`
reports exactly `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
The final module compiles cleanly through `lcompile.py`.

## No longer needed

Removed from the original node's `proof_deps`:

- `def-weil-pbc-flat-ring-map`: flatness is part of the unchanged statement but unnecessary
  for this component, as its original docstring already explains.
- `lem-weil-pbc-finite-type-algebra-noetherian`: the polynomial Noetherian instance directly
  supplies the required special case.
- `lem-weil-pbc-noetherian-local-quotient-artinian-local`: the nilpotent-maximal-ideal
  criterion directly proves Artinianity, without a quotient argument.

No original public import or existing library module is removed. The proposed helper
imports and helper modules were removed from this delivery; their nodes never enter the
library. The attempted explicit proof imports `Mathlib.RingTheory.Polynomial.Basic` and
`Mathlib.RingTheory.Localization.Submodule` were omitted after separate omission tests and
a combined omission test compiled cleanly; they are already available transitively.
Removing `Mathlib.RingTheory.HopkinsLevitzki` fails compilation, so it is retained.

## Where the brief, the DAG or earlier work was wrong

The first proof changed the existing signature (`hflat` to `_hflat`, `letI` to `haveI`),
left two holes after closing one, and omitted an update to the original node's proof.
Its missing-lemmas diagnosis was unnecessary: the residue calculation and structural
argument can both be completed directly from Mathlib. Its change record described no
interface change and contained abbreviated signatures, so it was removed.

Source checked: [Stacks Project, Tag 07FI](https://stacks.math.columbia.edu/tag/07FI),
the transcendental case, together with the pinned Mathlib declaration sources above.
The repository's named `literature/stacks-project/smoothing.tex` is unavailable on this
machine; the official Tag 07FI page supplies the source argument.

Independent searches used `msearch.py` with a residue/coefficient query (LeanFinder),
`Ideal.mem_map_C_iff` (Loogle), and `mem_map_C_iff` (grep). A second set queried the
Noetherian-local nilpotent-maximal-ideal criterion through LeanFinder and Loogle.
These returned `Ideal.mem_map_C_iff` and
`isArtinianRing_iff_isNilpotent_maximalIdeal`, whose pinned source signatures were checked.
Repository `rg` searches found uses of the latter in `PopescuEnlargeSolutionModulo`,
`KollarLocalDichotomy`, and `FiniteCoefficientTensorReductionSurjective`; none supplies the
whole item. No duplicate statement is introduced.

## Second reading by C3

1. **Interface: pass after repair.** Diffed the delivered module against the repository,
   restored the exact original signature including `hflat`, `letI`, and all universes,
   and checked signature text equality programmatically. The final diff contains only
   a plain proof import and the theorem body. Existing definitions, docstrings, and
   public imports are unchanged. No change record is needed.
2. **Proof and trust: pass.** Compiled the proposed modules and the completed final
   module with `lcompile.py`. Checked the final theorem's axioms in a scratch copy:
   precisely `propext`, `Classical.choice`, `Quot.sound`. No remaining `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern`, and no new definition. All witness
   data in the essentially-smooth presentation are explicit constructions.
3. **Split statements: pass after eliminating both holes.** Read both proposed lemmas.
   The coefficient-prime statement follows by residue reduction and transcendence;
   the structural statement follows by nilpotence and smooth polynomial localization.
   In the field case the prime is zero and the localization is the rational-function
   field, consistent with both arguments. For local Artinian rings with nonzero
   nilpotents the mapped nilpotence exponent still works. The local-ring instances
   exclude the zero ring. An algebraic residue, excluded by `hx`, need not give the
   coefficient prime. The structural helper's unused `S` parameter existed solely
   for its lift universe. Repeated independent Mathlib/library searches and proved
   both arguments locally; no split statements or new nodes remain to review.
4. **Route and pruning: pass.** Read `dag/units/sk-thm-p1.json`, including `realized`.
   This auxiliary structural node realizes no fixed unit statement or step; the
   proof retains the residue-prime and structural-localization argument and changes
   nothing in the unit. The shortest available Mathlib routes replace the generic
   finite-type and quotient lemmas. The three removed old dependencies are all
   listed above. Only one new proof import is necessary, verified by omission tests.
5. **DAG: pass after repair.** Opened the original node and both proposed nodes.
   Removed the proposed nodes; updated the original `proof` to describe coefficient
   reduction, Noetherianity/nilpotence, locality, and the explicit lifted localization
   presentation. `proof_deps` is exactly the union of the steps' `uses`.
   The source-based `proof_origin`, statement, statement dependencies, and Lean
   signature record remain unchanged.

Second reading changed: restored the original signature; proved both proposed holes
inside the target; removed two helper modules/nodes and the unnecessary change record;
minimized proof imports; repaired the original DAG proof/dependencies; corrected the
report's hole accounting. One original theorem proved, zero statements split off.
