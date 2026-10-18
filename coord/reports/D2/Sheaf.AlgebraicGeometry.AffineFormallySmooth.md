## What changed

Proved `AlgebraicGeometry.formallySmooth_spec_iff_ringHom_formallySmooth` in
`Sheaf.AlgebraicGeometry.AffineFormallySmooth`, keeping its signature unchanged.
The forward direction applies scheme formal smoothness to spectra of square-zero
quotients and uses full faithfulness of Spec to recover the algebra lift. The
backward direction takes global sections of the first order thickening, obtains a
surjection with square-zero kernel, applies
`Algebra.FormallySmooth.liftOfSurjective`, and translates the lift back with the
Gamma-Spec adjunction. This follows the existing Stacks 02H4 dictionary argument;
Mathlib's surjective lifting API handles quotient normalization.

Repaired the return of branch head `d0c014242`: removed the duplicate private
`specRingHom` definition and the four duplicate private lemmas
`specRingHom_comp`, `specRingHom_spec`, `specRingHom_injective`, and
`specRingHom_lift`. Added the proof-only import
`import all WeilConjectures.AlgebraicGeometry.UniversalThickeningAffineCase`
and used that module's existing private definition and lemmas directly.
No changes to that module or its visibility are needed. The remaining proved
private helper `firstOrderThickening_spec` establishes the square-zero quotient
step from Mathlib's closed-immersion and ideal-sheaf APIs.

The shared repository still contains the original unproved theorem. This delivery
retains the returned proof and repairs its duplication defect against the current
sources. There are no new statements or changes to the mathematical route; all
nine original dependency nodes remain used. The additional import supplies proof
helpers for the existing spectrum dictionary, not the universal-thickening theorem.

Validation: the repaired module compiles through `lcompile.py` with no warnings.
The import-direction check permits the added import. The original universe and
hypotheses are unchanged; the proof requires no nontriviality hypothesis and
covers zero rings and zero ideals.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.formallySmooth_spec_iff_ringHom_formallySmooth`
(node `lem-weil-pbc-affine-formally-smooth-iff-ring-lifting`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The retained returned version already had zero holes; this repair removes its
five duplicated private declarations and reuses the existing library declarations.

## No longer needed

Removed redundant proof imports from the original library file:

- `Sheaf.AlgebraicGeometry.Thickening`;
- `WeilConjectures.AlgebraicGeometry.FormallySmooth`;
- `WeilConjectures.AlgebraicGeometry.Thickening`.

Their declarations are available through the retained public import
`Sheaf.AlgebraicGeometry.FormallySmooth`. No dependency node or module is pruned;
these removals eliminate duplicate import edges only. No new module is required.
The five local spectrum-dictionary declarations of the returned proof are removed
because the added import provides their existing implementations.

## Where the brief, the DAG or earlier work was wrong

The previous delivery copied private dictionary helpers from
`WeilConjectures.AlgebraicGeometry.UniversalThickeningAffineCase`, triggering the
landing duplicate-statement check. The repair imports that module with `import all`
and directly uses its helpers, addressing all four lemmas named in the return.
No mathematical error or unit-level route change was found.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
