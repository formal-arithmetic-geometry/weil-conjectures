## What changed

Replaced the invalid projection from `MakeSeparablyGeneratedAux` with a real strong induction
on `Field.finInsepDegree (IntermediateField.adjoin k s) K`. The degree-one case is proved
using Mathlib's `isSeparable_iff_finInsepDegree_eq_one`; the induction step uses the new
`Sheaf.FieldTheory.InseparableDegreeDrop` module. The proof constructs composite algebra
maps, proves their scalar towers, composes finite purely inseparable extensions, and handles
unequal universes explicitly with `ULift` algebra equivalences. The existing theorem's
signature and docstring are byte-for-byte unchanged.

Removed the former auxiliary module/node and the unnecessary import-change record from the
sandbox. Added proof-only imports of `InseparableDegreeDrop`, `Mathlib.Algebra.Field.ULift`
and `Mathlib.FieldTheory.FinTrdeg`. The new module publicly imports only the Mathlib module
its statement needs and imports `SeparableRootPthPower` privately for its planned proof.
The original module's two public imports are unchanged. No interface change or forced
adaptation is involved.

## Proved and sorry left

Closed the original hole in
`FieldExtension.exists_finitePurelyInseparable_separablyGenerated` (1 of 1 declarations
in the item). Added one named hole:
`FieldExtension.exists_inseparableDegree_drop`, node `lem-weil-pbc-inseparable-degree-drop`,
in `Sheaf.FieldTheory.InseparableDegreeDrop`.
The item itself has no remaining `sorry`. The superseded
`FieldExtension.exists_finitePurelyInseparable_separablyGenerated_tower` and its node are
not delivered.

This is a decomposition, not a completed proof of Tag 04KM: holes closed 1, holes added 1,
net 0 in the import closure. Both modules compiled without errors or warnings (approximately
2–5 seconds each). Scratch `#print axioms` checks for both declarations list only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`; the latter is the explicit one-step hole.
No hollow definitions or arbitrary witness data are introduced: witnesses are eliminated
only in the proof, and all composite algebra structures are constructed from their maps.

## No longer needed

The target's direct proof-only import of `Sheaf.FieldTheory.SeparableRootPthPower` was
removed; that module remains imported by the degree-drop module because it is needed for
the deferred coefficient-root step. No whole module is claimed pruned.

Every former direct proof dependency absent from the target's new `proof_deps`:

- `lem-weil-pbc-char-zero-field-extension-separable`: the degree-one test treats any already
  separable algebraic extension; the degree-drop proof uses perfectness in characteristic zero.
- `lem-weil-pbc-separable-first-purely-inseparable`
- `def-pc-separable-polynomial`
- `def-weil-algebraic-closure`
- `def-weil-ring-frobenius`
- `def-weil-algebraic-element`
- `lem-weil-pbc-compositum-degree-bound`
- `def-kun-transcendence-degree`
- `lem-weil-pbc-separable-root-pth-power`
- `lem-weil-pbc-field-degree-multiplicativity`

The last nine are dependencies of the new one-step construction, not pruned from its plan.
The former strengthened-tower auxiliary module and node are removed from this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier submission merely restated the whole target with extra scalar towers and left
that stronger statement unproved. This is not a legitimate stage-3 reduction, despite the
projection proof compiling; the earlier second-reading verdict is withdrawn.

The original target does not omit any structure needed for its final equality: its square
compares two composite ring homomorphisms, which needs no `Algebra k K'` instance. A common
`Algebra k K'` and scalar towers are useful proof data and are constructed inside this proof.
The new hole asserts only one strict degree decrease; it does not assert eventual separable
generation. Termination, the degree-one case, and transitive tower composition are proved in
Lean in the item's module.

## New nodes

`lem-weil-pbc-inseparable-degree-drop` isolates steps 4–9 of the original Stacks 04KM route:
for a finite extension over a finite transcendence basis with inseparable degree different
from one, the coefficient-root construction supplies a commuting finite purely inseparable
square and a new finite basis whose inseparable degree is strictly smaller. The theorem's
docstring explains the entire one-step proof, including rooted coefficients, independence,
finiteness, the p-th-root lemma, and the compositum/tower degree estimate. It retains no
recursive call and no final separable-generation conclusion. Its fields all live in the same
universe; using subfields of an algebraic closure makes that universe claim valid.

Fresh LeanFinder, Loogle and Mathlib grep searches found degree formulas, monotonicity and
perfect-field separating-basis results, not this coefficient-root/strict-decrease theorem.
LeanSearch returned Internal Server Error, recorded honestly as unavailable. Searches in
`lean/Sheaf` and `lean/WeilConjectures` also found no matching declaration. No change record
is needed: no existing statement, definition, or public import changes.

## Second reading by J2

1. **Existing signatures and visibility: PASS.** Compared the item against the repository by
   `diff`; the existing declaration's signature and docstring are byte-for-byte unchanged.
   No other existing module is delivered. Only the proof and proof-only imports change.
2. **Proof, compilation and axioms: PASS as a decomposition.** Compiled the two delivered
   modules through `lcompile.py` in import order. The item has no direct hole; the new
   theorem has exactly `:= by sorry`. Both scratch axiom probes show only the allowed three
   axioms and the declared lower hole. No forbidden declaration, hollow definition, or
   data definition choosing an arbitrary unproved witness occurs.
3. **New statement and search: PASS.** Read the coefficient-root and strict-decrease
   paragraphs of Stacks [Tag 04KM](https://stacks.math.columbia.edu/tag/04KM), and checked the
   existing plan's steps 4–9 and imported p-th-root statement. The finite-dimensional
   hypothesis excludes degree zero; degree one and characteristic zero cannot enter the
   nonseparable case. An empty basis gives the ordinary finite algebraic case, where the
   same construction works. The one-step output makes no separable-generation claim and
   is strictly part of the original induction. Its docstring and matching node give the
   complete deferred proof. Fresh searches listed above found no ready-made construction.
4. **Shortest route, pruning and unit route: PASS.** Reused the existing Mathlib finite-basis,
   algebraic-finiteness, inseparable-degree-one and transitivity results. Removed redundant
   statement imports from the new module. Listed every former direct DAG dependency no
   longer used by the target. No whole-module pruning is claimed. The item is below the
   realized statement/steps of `dag/units/sk-thm-p1.json`; its construction still follows
   Stacks' induction route and the unit's `realized` record is unchanged.
5. **DAG agreement: PASS.** The existing node now records finite-basis setup, strong
   induction, the one-step dependency, and composite towers. The new node records the
   coefficient-root and degree-drop steps; `proof_deps` is their uses union, its statement
   matches Lean, and its source, searches, blueprint, creation and Lean records are present.

Second reading changed the invalid whole-theorem auxiliary into one strict degree-drop
lemma, wrote the real induction and universe/tower handling in the target, corrected the
report's proof/structure claims, minimized imports, and updated both DAG records.
