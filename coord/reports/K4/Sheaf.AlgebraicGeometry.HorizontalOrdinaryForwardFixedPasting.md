## What changed

Added the component-level theorem `horizontal_ordinary_forward_fixed_pasting_core_aux`.
The original core theorem now introduces an arbitrary component `E` and applies this
strictly smaller theorem. The supplied-comparisons theorem remains proved by substitution.

## Proved and sorry left

`horizontal_ordinary_forward_fixed_pasting` and
`horizontal_ordinary_forward_fixed_pasting_core` are proved. The component-level mate
identity `horizontal_ordinary_forward_fixed_pasting_core_aux` remains `sorry` as the
strictly simpler residual obligation, node
`lem-sc-horizontal-ordinary-forward-fixed-pasting-core-aux`.

## No longer needed

None; all existing imports are used by the definitions and the component theorem.

## Where the brief, the DAG or earlier work was wrong

The prior attempt abandoned without reducing the core. The existing auxiliary node had
been recorded with the full core declaration; it is corrected here to the fixed-component
statement actually introduced by this delivery.

## Second reading by K4

1. **Statements and interfaces.** Compared the delivered module with the repository
   version. Every existing declaration has the same signature; the only added
   declaration is the explicitly split component theorem.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles cleanly.
   The two core-level theorems are proved, and the sole remaining `sorry` is the
   named component theorem recorded below. No forbidden declaration or hollow
   definition was introduced.
3. **Split statement.** Checked the fixed-component statement against the core
   statement: it is strictly simpler (the component `E` is fixed), has the same
   canonical data, and is exactly the residual obligation. It is not a restatement
   of the target. The DAG node and Lean declaration agree.
4. **Pruning and route.** The proof reduces the core by introduction and direct
   application of the component theorem. Existing imports remain needed by the
   definitions and statement; no proof dependency or unit route was bypassed.
5. **DAG and unit consistency.** The auxiliary node records the declaration,
   source, proof plan, and dependencies used by this delivery. The unit route and
   the target statements are unchanged.

Changed the report and added the auxiliary split node; no existing target or
definition was altered.

## New nodes

Added `lem-sc-horizontal-ordinary-forward-fixed-pasting-core-aux`, recording the
fixed-component residual theorem and its proof dependencies. There is no change
record because no existing definition or statement was changed.
