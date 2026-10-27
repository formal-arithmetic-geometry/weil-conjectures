## What changed

Changed only `lean/WeilConjectures/WeilSheaf/VerdierDual.lean` and its upper-shriek
conjugacy node. Proved `AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_iso`
using a direct native tensor-Hom chain, the existing compact structure tensor
comparison, Verdier biduality, and the assumed exceptional adjunction. Added the
proved private helper `exists_dualizing_hom_equiv_reversed`: unlike the existing
helper, it retains the right-tensor adjunction order, so projection applies without
extra braidings. The final Yoneda argument includes naturality in every test-object
morphism. No public signatures, definitions, attributes, or imports changed.

The source-library declarations and their original dependency imports are preserved.
No new modules or statements are introduced. The source was present at its normal
path; the quarantine archive named by rework.tsv was neither removed nor replaced.

## Proved and sorry left

Closed 1 of the 3 original holes:
`AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_iso`
(node `lem-sf-weil-upper-shriek-verdier-conjugate`). This is a proof from existing
named statements, including the existing biduality hole, with no new holes.

Two original holes remain unchanged:

- `AlgebraicGeometry.WeilComplex.nonempty_iso_verdierDual_rightOp_comp_verdierDual`
  (`lem-sf-weil-verdier-biduality`).
- `AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso`
  (`lem-pur-weil-smooth-dualizing-complex`).

Holes added: zero. Split-off statements: zero. Validation: remote single-file compile passed in 26.8 seconds; delivery preflight
is run by the delivery command.

## No longer needed

No imports removed; every existing import still supports the existing declarations.
No modules withdrawn. The following old direct proof dependencies of the
upper-shriek conjugacy node are unnecessary for this proof:

- `lem-sf-weil-chosen-duality-hom` and `lem-sf-weil-chosen-duality-exchange`:
  fixed-pair duality data are replaced by actual native currying and biduality.
- `lem-sfb-projection-internal-hom-formal`: the existing native compact structure
  comparison supplies exactly the needed Hom bijection.
- `cor-coef-integral-internal-hom`, `def-weil-derived-pullback-tensor-hom`,
  `sk-def-sf-operations`, `thm-coef-qbar-verdier`, `fix-prop-adjunctions`,
  `fix-prop-projection-formula`, and `def-weil-finite-tor-amplitude`: these no longer
  occur as direct proof dependencies here; the required native constructions and
  comparison theorems already incorporate their relevant conclusions.
- `lem-weil-pbc-adjunction-of-natural-bijection` and `det-sp-unique-right-adjoint`:
  a natural Hom equivalence followed by the already proved private Yoneda helper
  gives the object isomorphism directly.

These dependencies may remain necessary elsewhere, including below the retained
comparison and biduality theorems. The unit route is preserved; its realized fields
contain no prescribed statement or proof-step nodes that this change removes.

## Where the brief, the DAG or earlier work was wrong

The old upper-shriek proof plan invoked fixed-pair comparison packages although
this theorem concerns the native derived category of Weil sheaves. This proof
avoids that bridge: direct native tensor-Hom adjunction and the existing native
projection/composition comparison suffice. Mathlib leanfinder, loogle and grep
searches supplied no specialized Weil duality theorem; generic adjunction
naturality is used directly. No statement is weakened or disputed.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
