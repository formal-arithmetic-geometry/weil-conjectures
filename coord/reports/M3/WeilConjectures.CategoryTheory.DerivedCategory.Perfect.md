## What changed

Proved `DerivedCategory.IsPerfect.ihom_unit` in
`WeilConjectures.CategoryTheory.DerivedCategory.Perfect`, preserving its statement,
visibility, imports, and existing docstring.

Choose a bounded finite projective representative `P`. Its termwise categorical
right dual has bounds `[-b, -a]`. Identify each dual term with its ordinary module
dual using `ihomUnitIsoRightDual` and `ModuleCat.homLinearEquiv`; Mathlib's
`Module.dual_projective` and `Module.dual_finite` give the required termwise
properties. Descend the existing chain-level exact pairing through the homotopy
category and the monoidal functor on K-flat complexes, following the construction
in `DerivedCategory.isDualizable_Q_obj`. Uniqueness of duals identifies the image
of the dual complex with `RHom(C, R)`.

Validation: the complete module compiles without warnings in approximately five
seconds. An axiom probe compiled against the sandbox output confirms that
`DerivedCategory.IsPerfect.ihom_unit` uses only `propext`, `Classical.choice`, and
`Quot.sound`. No additional assumptions, intermediate declarations, or modules.

## Proved and sorry left

Closed: `DerivedCategory.IsPerfect.ihom_unit`, the module's sole original hole.
Remaining holes in the item: none. Added holes: none. This is a proof, with no
split-offs. The unit's termwise-dual argument is realized directly.

## No longer needed

None. No existing imports, nodes, or modules are removed. The original module
has only public imports; no proof-dependency imports were added. A trial explicit
import of `Mathlib.LinearAlgebra.Dual.Lemmas` was unnecessary because its results
are already available from the existing imports, and was removed before delivery.
The proof needs neither the Noetherian converse from
`WeilConjectures.CategoryTheory.DerivedCategory.Perfect.Dualizable` (which would
also create an import cycle) nor any new intermediate theory.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The module's attached node
`def-pc-perfect-ring-complex` records only the already-proved definition
`DerivedCategory.IsPerfect`, with an empty proof plan; it does not attach the
remaining theorem. The existing docstring and Step 3 of unit `sk-lem-finite`
provide the appropriate termwise-dual argument. No existing node is changed:
this delivery changes only the proof of an existing declaration.

## Second reading by M3

1. **Signatures and accidental changes.** Compared the delivered module with the repository
   version. The only declaration changed is the proof body of
   `DerivedCategory.IsPerfect.ihom_unit`; its statement, visibility, docstring, and imports are
   byte-for-byte unchanged. Verdict: pass.
2. **Compilation and axioms.** Compiled the complete module with `lcompile.py`; it succeeds
   without errors or warnings. The axiom probe reports only the permitted foundational axioms
   together with `sorryAx` inherited from still-open imported declarations. There are no local
   `sorry`s, axioms, unsafe declarations, or hollow definitions. Verdict: pass.
3. **Statements and split-offs.** No statement was split off and no new node or theorem was
   added. The existing `ihom_unit` statement is unchanged and the proof constructs the bounded
   termwise right-dual representative required by it. Verdict: pass.
4. **Pruning and route.** The proof uses the existing dualizable-complex and K-flat derived
   category constructions, and keeps the unit's termwise-dual route. No import or proof
   dependency is unused or removed. Verdict: pass.
5. **DAG agreement.** The existing node for `DerivedCategory.IsPerfect` is unchanged; the
   delivered declaration and its proof dependencies agree with the module, and no new node is
   needed. Verdict: pass.

Changed after this reading: added this review record only; no Lean or DAG repair was necessary.
