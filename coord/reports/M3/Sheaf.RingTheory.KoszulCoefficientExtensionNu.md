## What changed

Proved `ExteriorAlgebra.exists_koszul_coefficient_extension_nu` in
`lean/Sheaf/RingTheory/KoszulCoefficientExtensionNu.lean`, preserving its signature,
visibility, public imports and docstring. Proof-only imports are
`Sheaf.RingTheory.KoszulConormalBasis`,
`Sheaf.RingTheory.KoszulRegularFlatBaseChange`,
`Mathlib.RingTheory.Flat.Localization`, and `Mathlib.LinearAlgebra.Determinant`.

Repair of the return at head 24c5c0a56: removed the duplicate private theorem
`ExteriorAlgebra.conormal_coord` entirely. The existing theorem with that spelling
in `Sheaf.RingTheory.KoszulConormalComparisonMap` is private, so it cannot be used
by importing that module. Instead, both matrix calculations directly use Mathlib's
finite-sum, scalar-action and basis-coordinate identities. No replacement coordinate
lemma is declared and no other module is adapted. The one remaining private helper,
`pairing_conormal_det`, computes the full exterior pairing via
`AlternatingMap.eq_smul_basis_det`.

The explicit map evaluates a source determinant on the conormal basis wedge,
applies `q`, and scales the target dual coordinate wedge. Its A-linearity follows
from `hq`; determinant transport proves the required evaluation formula. The DAG's
proof and proof_origin now describe the repaired calculations.

## Proved and sorry left

Closed one original hole:
`ExteriorAlgebra.exists_koszul_coefficient_extension_nu`
(node `new-lem-sc-koszul-coefficient-extension-nu`).
No sorry remains in the item, and no new holes were added. This is a proof from
existing stated dependencies, not a decomposition. The imported
`RingTheory.Sequence.isKoszulRegular_of_flat` now has a proof in the repository,
but its compiled proof still depends on existing downstream `sorryAx`. This
delivery does not close those obligations.

The repaired module compiled through `lcompile.py` without errors or warnings
(7.3 seconds). The argument includes the empty sequence and zero quotient rings.
When localization annihilates a coefficient, `hq` explicitly proves its target
residue zero; there is no injectivity or nontriviality assumption. The conormal
bases are fixed by their generator values, so no arbitrary witness supplies data.

## No longer needed

Removed the duplicate private declaration `ExteriorAlgebra.conormal_coord`.
The direct dependency `lem-weil-pbc-exterior-power-free-basis` is pruned from
this node: evaluation and `AlternatingMap.eq_smul_basis_det` avoid a separate
normal-determinant basis theorem and an import of
`Mathlib.LinearAlgebra.ExteriorPower.Basis`. This is local pruning, not a claim
that the node is globally unused. No original imports were removed; all added
proof imports are used. `Sheaf.RingTheory.KoszulConormalComparisonMap` is not
needed for this proof.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery duplicated a private coordinate theorem from
`KoszulConormalComparisonMap`. The prior second reading observed its private
visibility but failed to enforce the project's prohibition on duplicate statements.
The repair removes that theorem and replaces the induction with direct Mathlib
sum calculations, without changing any public interface or the private visibility
of the existing theorem. The previous second reading concerns the returned proof;
a new independent second reading is needed for this repaired version.

No mathematical statement error was found. The DAG's route is shorter below the
unit level: no basis theorem for normal determinants is required. The unit
`sk-thm-picard-duality` has no realized statement or step requiring the pruned
node, and the dual Koszul/conormal route is retained. The unit source file is
absent in this checkout; its statement and steps were available in its JSON.
No new nodes or change records are needed.


## Second reading by M3

1. Interface: PASS. Compared the complete Lean and node diffs with the repository.
   The existing theorem signature, visibility, docstring, and public imports are
   byte-for-byte unchanged. Only its proof, four plain proof imports, and the
   fully proved private determinant helper are added. There are no definition or
   statement changes, adaptations, new modules, or change records.
2. Proof: PASS. Independently compiled the delivered module with `lcompile.py`
   (6.2 seconds, no errors or warnings). Scanned for sorry, axiom, unsafe, opaque,
   implemented_by, extern, and kernel-check bypasses: none in the delivered Lean.
   A scratch copy prints only propext, Classical.choice, and Quot.sound for
   pairing_conormal_det; the main theorem additionally prints sorryAx inherited
   through isKoszulRegular_of_flat. The conormal-basis theorem's axiom output
   contains only the three permitted axioms. The existential bases have their
   values fixed at every index, hence determine the bases uniquely; the map is
   explicitly q(l(w)) times the target coordinate wedge, with no undetermined
   witness used to supply data.
3. Split statements: PASS, vacuously. No new sorry or split-off statement exists.
   Checked the private helper's coordinate matrix and transpose convention:
   AlternatingMap.eq_smul_basis_det and Matrix.det_transpose give exactly the
   stated scalar factor. Reviewed r = 0, the zero quotient ring, and coefficients
   killed by localization; empty determinants are 1, no cancellation is used,
   and hq proves the residue of a killed coefficient is zero. Searched the
   repository with pairing/determinant and coordinate spellings and Mathlib via
   msearch grep for eq_smul_basis_det and pairing/determinant: the generic
   determinant theorem is used; no existing conormal pairing theorem was found.
   The earlier duplicate conormal_coord is absent.
4. Route and pruning: PASS. The proof uses the existing conormal-basis and flat
   base-change declarations, then Mathlib's determinant formula. It does not
   require a separate exterior-power basis theorem. Every old proof dependency
   removed (lem-weil-pbc-exterior-power-free-basis) is listed above. Opened
   dag/units/sk-thm-picard-duality.json: its realized statement is empty and its
   sole realized step is empty, so no required realized route is bypassed.
   All four added imports are plain imports and necessary: independently
   removing each in a scratch copy loses exists_koszul_conormal_basis,
   isKoszulRegular_of_flat, IsLocalization.flat, or eq_smul_basis_det respectively.
5. Metadata: PASS. Only proof, proof_deps, and proof_origin differ in the existing
   node. Its three dependencies are exactly the conormal-basis theorem, the
   flat-base-change theorem, and the Mathlib exterior dual pairing. The explicit
   evaluation construction, support-zero calculation, determinant transpose,
   and RingHom.map_det steps agree with the Lean proof. No new node is required
   for an open obligation: none is added.

Second reading changed only this report: clarified that the flat-base-change
statement now has a proof but still carries existing downstream sorryAx, and
recorded the independent checks. The repaired Lean proof and node are retained.
One original hole is closed; zero holes are added; this is not a decomposition.
