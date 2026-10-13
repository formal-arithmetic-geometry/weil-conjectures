## What changed

Closed `IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth_step` without changing
its signature or existing visibility. The parent now applies Mathlib's proved
`RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero` to the actual quotient
maps, using `Ideal.mk_ker`, quotient-map surjectivity, and an explicit square-zero proof.

Added two fully proved modules, each with a matching node:
`Sheaf.RingTheory.CohenRingModPowFlat` and
`Sheaf.RingTheory.ModPowFormallySmoothReduction`. These are proof-only imports of the
parent. No definition or existing statement changed, and no adaptation is required.
The unit route is preserved: this implements the two steps of the original node,
not a bypass of any node realizing a unit's statement or steps.

Flatness follows from characteristic zero, torsion-freeness over the PID ℤ, and
base change via `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`. The
characteristic-zero argument is kept as a local proof inside the flatness theorem,
so this module does not redeclare the private `cohen_charZero` theorem already
present in `Sheaf.RingTheory.GenericFormalFiberPurelyInseparableRegularAux`.

For the reduction, the kernel of `ZMod.castHom` is computed directly on integer
representatives. The first and third isomorphism theorems identify the two quotients.
The algebra map on the smaller quotient is constructed by `Ideal.Quotient.lift`,
not selected from an unproved existence theorem. Formal smoothness is transported
by composition with the two ring equivalences. Equality with the actual quotient
map follows from `RingHom.ext_zmod` after precomposition with the surjective base
quotient map.

All three delivered modules compiled together, with no compiler warnings and no
remaining `sorry`. The sources checked were Stacks Tags 0329 and 031L online, and
the pinned Mathlib implementations of the quotient, flatness, and smoothness APIs.
The formal axiom probe is part of the delivery dry run.

## Proved and sorry left

Closed one original hole:
`IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth_step`
(`lem-weil-pbc-cohen-ring-mod-pn-formally-smooth-step`).

Also proved `IsDiscreteValuationRing.cohenRing_mod_pow_flat`
(`lem-weil-pbc-cohen-ring-mod-pow-flat`) and
`modPow_formallySmooth_reduction`
(`lem-weil-pbc-mod-pow-formally-smooth-reduction`).

No holes were added or left in any delivered module. This is a proof, not a
decomposition into new unfinished statements: one hole closed, zero holes added.

The flatness lemma includes n=0, where the quotient is the zero ring. The reduction
lemma assumes only n≤m and applies to any commutative Λ: its proof also covers n=m
(the reduction ideal vanishes), n=0 (the smaller quotient is zero), and p=0 or p=1
whenever the displayed algebra structure exists. No positivity, domain, flatness,
or Cohen-ring hypothesis is smuggled into the reduction statement.

## No longer needed

None of the original mathematical dependencies is pruned. PID torsion-free flatness
and quotient flatness remain used through the new flatness lemma; the square-zero
criterion remains used directly. No original import was removed. The reduction module now publicly imports `Mathlib.RingTheory.RingHom.Smooth`
instead of the larger `Mathlib.RingTheory.Smooth.Quotient`; the latter was unused
there. It remains a necessary proof-only import of the parent.

The old direct dependencies `def-weil-pbc-cohen-ring`,
`lem-weil-pbc-pid-torsion-free-module-flat`, and
`lem-weil-pbc-flat-module-quotient-flat` are retained through the flatness lemma
(and the Cohen-ring definition remains in the parent signature). They are not
pruned from the mathematical dependency closure.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's claim that the quotient identifications and flatness APIs
were absent was too strong. Mathlib supplies the quotient tensor equivalence,
first and third isomorphism theorems, and the full flat square-zero formal-smoothness
criterion. The missing glue is now proved, including the exact induced quotient
map and the given algebra structure. Neither the original statement nor its
mathematical route needed repair.

LeanSearch returned Internal Server Error for both new-lemma queries; these are
recorded as unavailable rather than evidence of absence. Loogle, LeanFinder, and
source searches supplied the APIs used. The Stacks source file is not present in
this machine's read-only checkout, so its existing source reference was checked
against https://stacks.math.columbia.edu/tag/0329 and
https://stacks.math.columbia.edu/tag/031L instead.

## New nodes

`lem-weil-pbc-cohen-ring-mod-pow-flat` records the fully proved prime-power quotient
flatness theorem in `Sheaf.RingTheory.CohenRingModPowFlat`, implementing step 1 of
the parent node and retaining its PID-flatness and flat-quotient dependencies.

`lem-weil-pbc-mod-pow-formally-smooth-reduction` records the fully proved quotient
transport theorem in `Sheaf.RingTheory.ModPowFormallySmoothReduction`, implementing
the quotient-identification part of step 2, with weaker hypotheses than the parent
and a strictly smaller conclusion. Neither new node carries a hole. The parent
node's proof and proof dependencies now match the compiled proof.

## Earlier second reading (a previous round; superseded)

1. **Visibility and unchanged interfaces.** I compared all three delivered modules and
the three DAG nodes with the repository versions. The original theorem signature is
byte-for-byte unchanged; the two added modules introduce only the declarations recorded
by their new nodes. No unrelated file or existing declaration changed.

2. **Proof and axioms.** I compiled all three modules together with `lcompile.py --all`.
There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`
constructs in the delivered source. A scratch axiom probe reports only `propext`,
`Classical.choice`, `Quot.sound`, and the pre-existing `sorryAx` inherited through the
open square-zero criterion dependency.

3. **Statements and new nodes.** The flatness and reduction statements are true, have
the hypotheses used by their proofs, and are strictly smaller than the parent step.
Their docstrings give complete arguments and their DAG records identify sources,
dependencies, declarations, and blueprint/unit attachment. Neither duplicates an
existing library theorem.

4. **Route and pruning.** The proof follows the unit's two stated steps: quotient
flatness, then quotient identification and the square-zero criterion. Imports are
minimal for the declarations and proof APIs used; no original import or mathematical
dependency can be removed. The parent and both new node `proof` and `proof_deps` fields
match the compiled terms.

5. **Edge cases and consistency.** The flatness construction includes `n = 0`; the
reduction theorem covers `n = m`, `n = 0`, and arbitrary commutative rings subject only
to the displayed algebra structure. The quotient maps and algebra structures are
constructed explicitly, so no unconstrained witness is selected.

I changed the flatness proof after return: the duplicate private `cohen_charZero`
declaration was removed and its proof was inlined as a local `CharZero` fact. This is
required by the import-pruning check because the library already states that theorem
word for word. The temporary `Scratch.lean` used for the axiom probe remains removed.

## Second reading by E3

1. Compared the target module and existing node against the read-only repository.
   Its existing declaration signature and visibility are byte-for-byte unchanged.
   Only proof imports and the proof body changed; the existing node changes only
   `proof`, `proof_deps`, and `proof_origin`. Both added modules have new nodes.
   No definition, target statement, or unrelated interface changed. Verdict: pass.

2. Compiled all three modules in import order using `lcompile.py --all`; no errors
   or warnings. Searched every delivered source for forbidden constructs and holes:
   none. Scratch copies with `#print axioms` for all three theorems report exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   The earlier second reading's claim of inherited `sorryAx` was incorrect; the
   square-zero criterion is proved in Mathlib. Verdict: pass.

3. Read both new statements and their complete docstring proofs. No statement is
   split off with `sorry`. The flatness lemma proves a strictly smaller part of
   the argument; the quotient-transport lemma requires neither flatness nor the
   Cohen-ring hypothesis. Checked n=0 (unit ideal, zero quotient), n=m (identity
   reduction), p=0 (including the zeroth power), p=1, and the zero ring. The
   constructed maps work uniformly; no arbitrary witness is selected. Independent
   LeanFinder search for mixed-characteristic quotient flatness and quotient
   formal-smoothness transport, Loogle search `RingHom.FormallySmooth, RingEquiv`,
   and source searches found supporting APIs but no duplicate specialization.
   The existing characteristic-zero helpers are private; this proof uses a local
   fact rather than redeclaring them. Verdict: pass.

4. Checked the unit `sk-thm-p1` and its `realized` entries: none is bypassed or
   changed. The proof implements the original flatness and square-zero reduction
   steps. Every former direct proof dependency remains used in the transitive
   argument, as detailed under `No longer needed`. Inspected the Mathlib quotient,
   flatness, and RingHom smoothness APIs for shorter routes. Narrowed the reduction
   module's public import from `Smooth.Quotient` to `RingHom.Smooth`, which supplies
   the formal-smoothness predicate and transport lemmas actually used. Verdict: pass.

5. Read all three nodes, checked their Lean signatures against the declarations,
   and followed each proof step and dependency. New nodes have source, searches,
   creation, blueprint, chapter/unit, and Lean records. The parent uses the two
   proved helpers and Mathlib's square-zero criterion exactly as recorded.
   Verdict: pass.

Second reading changed only the unused broad public import of the new reduction
module, corrected this report's axiom finding, clarified retained dependencies,
and removed the stale top-level `Scratch.lean`. One original hole closed, zero
holes added; no unfinished statements split off and no module pruned.
