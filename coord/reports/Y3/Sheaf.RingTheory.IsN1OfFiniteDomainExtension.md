## What changed

Proved `isN1_of_finite_domain_extension` in
`Sheaf.RingTheory.IsN1OfFiniteDomainExtension`, with its signature unchanged.
Added the proof-only import `Mathlib.RingTheory.Noetherian.Basic`.

The proof follows all four steps of
`lem-weil-pbc-n1-descends-finite-domain-extension`: use `Algebra.compHom` to
restrict the scalar action on `L` and on `integralClosure B L`; use
`IsFractionRing.liftAlgHom` to construct the injective fraction-field map;
map integral elements using `IsIntegral.map` and `IsIntegral.tower_top`;
apply `Module.Finite.trans` and then `Module.Finite.of_injective` to the
resulting linear map between the two integral closures. The Noetherian
instance needed for the last step comes from finiteness over the Noetherian
ring `A`. No definitions, existing statements, or visibility changed.

## Proved and sorry left

Closed one hole: `isN1_of_finite_domain_extension`
(node `lem-weil-pbc-n1-descends-finite-domain-extension`).
No holes remain in the item, and no holes were added or split off.
Local single-file compilation passed without warnings.

## No longer needed

None. No imports were removed. All seven existing proof-dependency nodes
remain relevant to the unchanged four-step argument, with the finite-module
and Noetherian-submodule steps supplied directly by Mathlib. No new nodes
or dependency statement modules are needed. The blueprint unit route is
unchanged; this item is not itself a realized unit statement or step.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing plan can be proved directly
from Mathlib without introducing any additional intermediate theorems.
The cited Stacks source file is not present in this machine's repository;
the source hint and its complete four-step expansion were read from the
existing node and declaration docstring. No new source-dependent claim was
introduced. The dependency records already identify `Module.Finite.trans`
and the Noetherian submodule finiteness result as Mathlib leaves.

## Second reading by Y3

1. **Unchanged interface: PASS.** Compared the only delivered module with the
   repository using `diff -u`. Its theorem signature is byte for byte unchanged;
   the only edits are the proof body and the plain, proof-only import of
   `Mathlib.RingTheory.Noetherian.Basic`. No definition, public import,
   visibility, hypothesis, or conclusion changed. No change record is needed.
2. **Kernel proof: PASS.** Independently compiled the delivered file with
   `lcompile.py` without errors or warnings. A scratch copy with
   `#print axioms isN1_of_finite_domain_extension` reported exactly
   `propext`, `Classical.choice`, and `Quot.sound`; the scratch copy was removed.
   There is no `sorry`, forbidden declaration, or data chosen from an unproved
   existence theorem. The fraction-field lift is Mathlib's actual localization
   construction; the map of integral closures is explicitly constructed.
3. **Split-off statements: PASS (none).** No new declarations, nodes, or holes
   were introduced. Checked the scalar restrictions and the monic-equation
   argument: mapping integrality over A and enlarging the coefficient ring to B
   places each image in the integral closure of B. Injectivity follows from the
   field homomorphism and subtype extensionality. The identity extension A=B
   and the case of fields require no additional assumptions; the zero ring is
   excluded by IsDomain/Field. Independently searched Loogle for
   `integralClosure, Module.Finite`, Lean Finder for finiteness via an injective
   linear map into a finite module over a Noetherian ring, and the repository
   and Mathlib sources for N-1/Japanese descent. The relevant direct leaf is
   already used: `Module.Finite.of_injective`; no shorter descent theorem found.
4. **Route and pruning: PASS.** All four planned steps are present: injective
   fraction-field lift, integral-closure containment, finite scalar restriction,
   and Noetherian submodule finiteness. Read Mathlib's `liftAlgHom`,
   `Module.Finite.of_injective`, and the Noetherian instance for finite modules.
   The added plain import supplies the last two; the public imports provide the
   signature's IsN1, fraction-ring, and Noetherian notions. All seven old
   proof-dependency nodes still describe notions or results used by this proof;
   none is no longer needed. Read `dag/units/sk-thm-p1.json`: this node is not
   one of its realized statement or step nodes, and the unit route is preserved.
5. **DAG agreement: PASS.** Read the item's full node and the Mathlib-leaf nodes
   for finite-module transitivity and Noetherian submodule finiteness. The
   existing four-step `proof`, seven-element `proof_deps`, and agent expansion
   of the source hint in `proof_origin` already match the delivered proof and
   require no edits. Independently read the source at
   [Stacks Tag 032K](https://stacks.math.columbia.edu/tag/032K): its N-1 clause
   and integral-closure containment hint agree with the declaration and proof.

Second reading changed only this report, recording the independent checks and
online source verification. The Lean proof and DAG were correct as delivered.
Closed: `isN1_of_finite_domain_extension` (one of one original holes).
Added or split off: none. Pruned: none. This is a proof, not a decomposition.
