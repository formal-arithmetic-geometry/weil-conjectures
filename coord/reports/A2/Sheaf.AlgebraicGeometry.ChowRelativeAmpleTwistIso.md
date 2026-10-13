## What changed

Proved `AlgebraicGeometry.chow_relative_ample_twist_iso` in
`Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwistIso` without changing its signature or
existing docstrings. Evaluate two `Scheme.Modules.nonempty_tensorPullbackComp` comparisons
at the integral Proj twist, identify their composite morphisms by
`ProjectiveSpace.liftBaseChange_toProjInt`, and compose the resulting three isomorphisms.
The DAG copy now records this proof and removes its backward reference to the parent.
Removed the unused public import `Sheaf.AlgebraicGeometry.Ample`; the change record is
`coord/changes/chow-relative-ample-twist-iso-imports.md`.

## Proved and sorry left

Closed the single hole in `AlgebraicGeometry.chow_relative_ample_twist_iso`
(node `lem-pc-chow-relative-ample-twist-iso`). No holes remain in the item; no holes or
modules were added. This is a proof using existing named library declarations, not a
new decomposition. Single-file compilation and the delivery dry run passed, including the axiom probe.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.Ample`. Its ampleness theory is unnecessary for
this component; the parent independently imports it for the properties component.
Removed proof dependency: `lem-pc-chow-relative-ample-twist`, module
`Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwist`. The parent is still needed above this
item and is not globally pruned. No other planned dependency or imported module is removed.
The projective-space, Proj-twist, and tensor-pullback imports are used in the signature
and proof. The properties component is not used here and remains the parent's other conjunct.

## Where the brief, the DAG or earlier work was wrong

The item's old proof dependency pointed to `lem-pc-chow-relative-ample-twist`, whose
Lean proof already calls this item. This was a circular proof plan, not a usable lemma.
The direct functoriality proof eliminates the circular reference. Properness and immersion
are unnecessary for this isomorphism, but every binder and instance hypothesis is preserved.
The unit's route is preserved: this is precisely its Chow twist identification step,
not a bypass of coherence or ampleness. Mathlib searches returned abstract module-pullback
composition; the library's tensor-formula comparison supplies the exact interface needed.
The only direct importer, the unchanged parent, retains its own public Ample import.

The import pruning check passed. A further unchanged-parent compilation was attempted
against the sandbox overlay, but the shared snapshot lacks the existing
`ChowRelativeAmpleTwistProperties.olean`; it therefore could not check the parent.
This missing baseline artifact does not affect the item's clean compilation or dry run.
No downstream module was adapted. The source TeX file named by the existing docstring
is absent locally; the proof uses only the read and compiled library interfaces.

## Second reading by A2

1. **Visible changes.** I diffed the delivered Lean module against the repository copy and
   diffed the DAG node. The theorem signature and existing declarations are unchanged; the
   only interface change is removal of the unused public `Ample` import, recorded above.

2. **Proof validity.** The module compiles with `lcompile.py`; it has no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof constructs the claimed
   isomorphism by evaluating named tensor-pullback comparison isomorphisms and transporting
   the proven morphism equality with `eqToIso`. Its axioms are limited to the permitted
   foundations (the delivery probe checks this).

3. **Statements and dependencies.** No statement was split off. The existing theorem is
   exactly the item's recorded statement, and the node's proof and `proof_deps` now match the
   declarations actually used: tensor-pullback composition and projective-space base change.
   Searches found no duplicate theorem in Mathlib or the library.

4. **Pruning and route.** The former parent-theorem dependency was circular and is removed.
   The proof retains the unit's Chow twist identification route, while removing only the
   unused `Ample` import. No unit statement or realized step is bypassed.

5. **Definitions and edge cases.** No definition or target statement changed. The construction
   works uniformly for every natural number `m` and does not use the properness or immersion
   instances, which remain as required hypotheses of the unchanged interface.

I changed only the proof, its matching DAG proof metadata, the unused import, the import change
record, and this review section. The dry-run delivery checks passed after these edits.
