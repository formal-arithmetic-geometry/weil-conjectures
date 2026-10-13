## What changed

Completed `AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`
in `Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres` with its original
signature and visibility. All five conclusions are combined by a complete Lean proof.
Krull–Akizuki supplies Noetherianity; the existing integral dimension equality and
Mathlib normality give Dedekind; lying over gives surjectivity. Mathlib Dedekind
prime factorization proves finite closed fibres, and Mathlib `Ideal.eq_bot_of_comap_eq_bot` proves the
singleton generic fibre. For closed residue extensions the global finite-length
lemma gives finite length of `C/aC`, which surjects onto the closed residue field.
The generic residue map is conjugate to `K → L`. Proved private helpers transport
these ring statements through the canonical affine stalk isomorphisms.

Added proof imports `Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas` and
`Sheaf.RingTheory.FiniteLengthGlobalSubmodule`. Removed the two localization-route
imports listed below. Updated the original node's `proof`, `proof_deps` and
`proof_origin` to match this route. No definitions, existing signatures, public
imports or other modules were changed; no new nodes or holes were added.

Validation: the module compiles without warnings through `lcompile.py`; the
original signature is unchanged. The node's unit record realizes only
`thm-sc-proper-cohomology`, so this change below the unit preserves its route.
The argument handles zero and nonzero primes separately and assumes neither a
normal base nor separability of `L/K`.

Recovery of the earlier attempt: independently rechecked the complete sandbox proof,
its dependency statements, the unchanged theorem signature, and the node update.
`lcompile.py --all` compiled cleanly. `deliver3.py --no-push` printed OK;
nothing was pushed. The delivery awaits the separate second reader.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`
(node `lem-sc-integral-closure-dedekind-surjective-fibres`). No `sorry` remains
in the assigned module and no new hole was added or split off.

This is a proof from existing stated dependencies, not an axiom-free closure of
the entire branch. It still uses `krullAkizukiNoetherian`
(node `lem-sc-krull-akizuki-noetherian`) and
`Submodule.length_quotSMulTop_lt_top_of_ringKrullDim_eq_one`
(node `lem-sc-finite-length-global-submodule`), both already containing `sorry`.
They are unchanged. `#print axioms` reports `propext`, `Classical.choice`,
`Quot.sound`, and the expected inherited `sorryAx`. The global finite-length
module was already a dependency of
Krull–Akizuki; importing it directly adds no new underlying hole.

## No longer needed

Removed proof imports:
- `Sheaf.RingTheory.DimOneResidueFieldsFinite`, node
  `lem-weil-pbc-dim-one-residue-field-extensions-finite`.
- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`, node
  `lem-weil-pbc-localization-prime-residue-field-iso`.

Neither theorem is used by this proof. The corresponding two nodes were removed
from its `proof_deps`. Their localization-at-maximal-ideal argument is replaced
by the already needed global finite-length theorem and Mathlib Dedekind prime
factorization. This is pruning of this item's route; other targets may still
reach these modules. The second reading also removed direct dependency
`lem-weil-pbc-integral-incomparability`: Mathlib
`Ideal.eq_bot_of_comap_eq_bot` now handles zero contractions directly.
The dimension-equality theorem still uses incomparability internally. Every
other original proof dependency remains needed.

## Where the brief, the DAG or earlier work was wrong

No statement defect or interface correction was needed. The DAG's localization
route was valid, but longer than necessary: the global finite-length theorem
already below Krull–Akizuki suffices for the closed residue fields. The assigned
module's original docstring was updated accordingly. The supplied literature
files are absent in this clone, so the Stacks statements were checked at
https://stacks.math.columbia.edu/tag/09IG and
https://stacks.math.columbia.edu/tag/00PF; the theorem uses the exact existing
Lean statements of these results.

## Second reading by B3

1. PASS: compared the sole delivered Lean module and node against the repository
   with `diff`. The original theorem signature is byte-identical, its visibility
   and all public imports are unchanged, and there are no definitions or
   interface changes. Only the node's `proof`, `proof_deps`, and `proof_origin`
   change. No change record or forced adaptation is needed.
2. PASS: compiled the module locally with `lcompile.py --all`, without errors
   or warnings. Scanned for `sorry`, forbidden declarations and kernel bypasses:
   none occur. A scratch copy prints axioms for every delivered declaration:
   only `propext`, `Classical.choice`, `Quot.sound`, plus the inherited `sorryAx`
   in the closed-residue helper and main theorem. The two existing dependency
   holes are named above; no new hole or data construction from a holed existence
   theorem occurs.
3. PASS: no statement is split off and no new public statement or node is added.
   Read all private helpers and the exact dependency statements. Checked the
   zero-contraction case separately, nonzero-element choice in the closed case,
   maximality for residue-field surjectivity, the scalar towers, and the
   fraction-field identifications. Neither normality of A nor separability of
   L/K is silently assumed. Existing finite-dimensional bases and fraction-field
   equivalences are fully proved Mathlib constructions.
4. PASS after simplification: searched Mathlib with `msearch.py grep` and read
   the relevant source, and searched `lean/Sheaf` and `lean/WeilConjectures`.
   Mathlib's integral-closure Dedekind/finite-module shortcuts require stronger
   base or separability hypotheses and cannot replace this proof. Found
   `Ideal.eq_bot_of_comap_eq_bot`, removed its duplicated private helper, and
   applied the existing lemma at all three zero-contraction uses. Added imports
   are plain proof imports and all retained direct proof imports are used.
   `No longer needed` accounts for every old dependency removed. The unit
   `sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology`; the revised
   route stays below that level and preserves its realization.
5. PASS: checked the node's steps and dependency union against the actual proof.
   Krull–Akizuki, dimension equality, normality/fraction fields, lying over and
   global finite length are retained. Dedekind prime factorization and the
   zero-contraction lemma are explicitly identified as Mathlib results.
   Removed the now unused direct incomparability dependency and updated its
   two proof-step descriptions. No new nodes need validation.

Second-reading changes: replaced the duplicated zero-contraction helper by
Mathlib `Ideal.eq_bot_of_comap_eq_bot`, updated the proof docstring and DAG route,
and recorded this review. One original hole closed, zero added or split off;
no other mathematical proof changes were needed.
