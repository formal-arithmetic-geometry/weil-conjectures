## What changed

Replaced the proof of `RingHom.exists_complete_local_map_regular_presentation` by a
specialization of `RingHom.exists_complete_local_map_cohen_presentation`. The latter supplies
all ring, completeness, map, parameter, flatness, and fibre clauses. The residue equivalence
is constructed from Mathlib's `IsLocalRing.ResidueField.map`, using field-map injectivity
and surjectivity lifted from `q`. All existing signatures and public imports are unchanged.
Only the proof import `Sheaf.RingTheory.CompleteLocalMapCohenPresentation` is added.

## Proved and sorry left

Closed the one original hole:
`RingHom.exists_complete_local_map_regular_presentation`.
Added zero holes, split off zero statements, and left no `sorry` in the delivered module.
This is a reduction to the already-stated Cohen presentation, whose proof is still open;
`#print axioms` includes `sorryAx` through that existing dependency. It is not an
axiom-free proof of the whole import closure.

The second reader removed the first worker's new, unproved
`surjective_local_residue_equiv` and its node `new-surjective-local-residue-equiv`, replacing
its application by the short Mathlib argument inside the original proof.

## No longer needed

Removed direct proof imports:
- `Sheaf.RingTheory.CohenPowerSeriesPresentation`
- `Sheaf.RingTheory.CompleteLocalQuotient`
- `Sheaf.RingTheory.FieldCohenPowerSeriesFormallySmooth`
- `Sheaf.RingTheory.FlatOverRegular`
- `Sheaf.RingTheory.FormallySmoothAdicLiftIntoComplete`
- `Sheaf.RingTheory.PowerSeriesAdicEvaluation`
- `Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete`
- `Sheaf.RingTheory.PowerSeriesQuotientVariables`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`

Every old proof dependency removed from this node's direct route:
- `lem-weil-pbc-cohen-power-series-presentation`
- `lem-weil-pbc-field-cohen-power-series-formally-smooth`
- `lem-weil-pbc-complete-local-quotient`
- `lem-weil-pbc-fs-adic-lift-into-complete`
- `def-weil-pbc-multivariate-power-series`
- `lem-weil-pbc-power-series-field-cohen-regular-complete`
- `lem-weil-pbc-power-series-quotient-variables`
- `lem-weil-pbc-power-series-adic-evaluation`
- `lem-weil-pbc-regular-local-generators-regular-sequence`
- `lem-weil-pbc-flat-over-regular`

These dependencies are encapsulated by the existing stronger Cohen presentation theorem.
They mostly remain transitively reachable through that theorem; this report claims direct
import pruning only, not global unreachability. No unit realization is removed.
The new residue helper module and node are withdrawn before delivery.

## Where the brief, the DAG or earlier work was wrong

The original six-step plan can reuse the existing stronger compatible Cohen presentation.
The first worker's residue lemma was true and strictly smaller, but unnecessary: Mathlib
already provides the induced residue map, whose bijectivity takes a few lines.
The first worker's proof compiled with six `letI` style warnings; ordinary `let` bindings
remove them. Its claim of being proved must be read as a reduction, since the Cohen theorem
still has `sorry`. The local Stacks TeX source is not present on this machine; this reading
checked the existing source-labelled statements and DAG routes, and adds no source claim.

## Second reading by U3

1. Compared the module with the repository using `diff`; extracted the theorem signature
   before `:= by` and checked byte-for-byte equality. No declaration, definition, public
   import or target signature changes. Only the original theorem's proof and proof imports
   change. No change record is needed.
2. Compiled the final module locally using `lcompile.py`: no errors or warnings. Searched
   the delivered source for forbidden constructs and holes: none. A scratch copy prints
   the original theorem's axioms: `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`;
   the last comes from the existing Cohen-presentation dependency. No data definition or
   arbitrary chosen witness is introduced; existential witnesses are eliminated and
   reassembled entirely within a theorem proof.
3. Read the proposed residue helper and checked its hypotheses: locality gives a field
   homomorphism; surjectivity of q lifts every target residue class. It holds for field
   identity maps and quotients of local rings, with no completeness or Noetherian condition
   needed; Mathlib local rings exclude the zero ring. Loogle search for
   `IsLocalRing.ResidueField.map` and grep for `RingEquiv.ofBijective`, plus searches of
   lean/Sheaf and upstream WeilConjectures residue-map lemmas, found the short route.
   Removed the helper and its incomplete new node instead of delivering a redundant hole.
4. Checked the stronger Cohen theorem clause by clause: same A/B hypotheses and universes;
   compatible maps, regular complete R/S, the full parameter extension, flatness and
   regular fibre are retained. Only its extra coefficient and head-parameter conclusions
   are discarded. Read `dag/units/sk-thm-p1.json`: neither this helper nor the old supporting
   nodes realizes a unit statement or step; the unit's realized route is unchanged.
   Enumerated every old direct proof dependency above. Proof-only imports are plain imports;
   the Mathlib residue API is already publicly available from the Cohen theorem's module.
5. Read both regular and Cohen DAG nodes and their Lean statements. Updated the regular
   node's proof to the actual two-step reduction, with sole proof dependency the existing
   Cohen presentation; its second step records the elementary Mathlib residue argument.
   Cohen's current proof dependencies do not cite this item, so this route is not circular.

Changes made by the second reader: closed the proposed residue split directly with
Mathlib, removed its new module/node/import, removed all compiler warnings, made pruning
and proof-status reporting explicit, and aligned the DAG with the final Lean proof.
