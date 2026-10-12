## What changed

Proved `IsLocalRing.exists_coefficient_subring` without changing its signature or
public imports. The proof follows Stacks 032A(1): split the residue characteristic;
in characteristic zero construct a section of the residue map; in prime characteristic
choose the existing Cohen ring and lift its residue isomorphism; take the actual range
of the constructed ring homomorphism as the coefficient subring.

Added three proved modules, each with its own node:
`Sheaf.RingTheory.CoefficientResidueSection`,
`Sheaf.RingTheory.CohenRingLiftToCompleteLocal`, and
`Sheaf.RingTheory.CoefficientSubringOfPrincipalSource`.
The first uses the Mathlib transcendence-basis/separability chain and
`Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`.
The second proves a private square-zero lifting helper from the existing
`cohenRing_mod_pow_formallySmooth`, recursively constructs compatible maps into
`R/m^(n+1)`, and uses `IsAdicComplete.StrictMono.liftRingHom`.
The third proves locality, the ideal identities, and quotient-map bijectivity using
Mathlib, and proves completeness from the existing finite-module completeness theorem.
This avoids classifying the kernel as zero or a uniformizer power.

All four modules compile together, without warnings. The original node and all three
new nodes record the actual proof and dependencies. The unit's own statement and
realized proof steps are unchanged; these are tool lemmas below that level.

## Proved and sorry left

Closed the item's single hole, `IsLocalRing.exists_coefficient_subring`.
Added zero holes. The three new public theorems are proved:
`IsLocalRing.exists_residue_section`,
`IsLocalRing.exists_cohenRing_lift`, and
`IsLocalRing.coefficient_subring_of_principal_source`.
The private helper `IsLocalRing.lift_cohen_square_zero` is proved as well.
There is no `sorry` in any delivered module and no new definition.

The proof still uses the existing holed declarations `exists_cohenRing`,
`IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth`, and
`finite_module_complete_over_complete_noetherian`. They are existing stage-3
items, not new holes or independent axiom-free proofs claimed by this delivery.
The report counts one upper hole closed and zero holes added.

Edge cases: the zero-characteristic branch uses the field's zero maximal ideal and
zero-adic completeness; the positive branch uses the prime-or-zero dichotomy, so no
assumption is added for p=1 or composite p. The image lemma imposes no Noetherianity
or completeness on R, and its proof accommodates either zero or nonzero kernel.
All witnesses are introduced inside theorem proofs; the subring itself is the concrete
ring-homomorphism range. No data definition chooses an undetermined witness.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.RingTheory.CohenRingModPowFormallySmooth` and
`Sheaf.RingTheory.FormallySmoothAdic`.
The first remains needed by the proved Cohen-ring lifting module, where it is imported
and applied; this is relocation, not pruning it from the proof's transitive closure.
The second's adic formal-smoothness definition is not used directly in this argument:
Mathlib's ordinary formal smoothness suffices for characteristic zero, and the explicit
ring-map clause of the Cohen-ring lemma suffices for positive characteristic.
Existing dependency modules may still import it for their own statements or proofs.

The node `lem-weil-pbc-dvr-unit-times-uniformizer-power` is no longer needed on this
proof route. Its kernel-classification step is replaced by finite-module completeness;
there is no separate module to remove for this Mathlib leaf.
The original adic-completion and characteristic-zero formal-smoothness nodes are used
inside the new lifting nodes rather than directly by the item's node.
No claim is made that a module becomes globally unreached from all project targets.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The original step 6 is unnecessary: the image is a finite
module over the complete Noetherian source, so its completeness follows directly from
`lem-weil-pbc-finite-module-complete-over-complete-noetherian` and
`IsAdicComplete.map_algebraMap_iff`. The original docstring remains as its recorded plan;
the node and new image-theorem docstring describe the actual proof.

LeanSearch returned an Internal Server Error for the attempted lifting and image
queries. This is recorded as unavailable, without a mathematical verdict. LeanFinder,
Loogle, local source search, and compiler-checked signatures provided the needed tools.
The Stacks source was read in the local literature copy; no source files were changed.

## New nodes

`lem-weil-pbc-coefficient-residue-section` records the proved characteristic-zero
section, in `Sheaf.RingTheory.CoefficientResidueSection`. It implements original steps
1--3 using the Mathlib smooth-lifting API.

`lem-weil-pbc-cohen-ring-lift-complete-local` records the proved lift of a prescribed
Cohen-ring residue isomorphism, in `Sheaf.RingTheory.CohenRingLiftToCompleteLocal`.
It implements the compatible-lifting and inverse-limit parts of original steps 4--5.

`lem-weil-pbc-coefficient-subring-principal-source` records the proved verification
for the range of a local residue-surjective map from a complete local PID, in
`Sheaf.RingTheory.CoefficientSubringOfPrincipalSource`. It replaces original steps
6--7 with finite-module completeness and explicit algebraic verification.
No change record is needed: no existing statement, definition, or public import changed.

## Second reading by F2

1. Compared the delivered item module with the repository version. The theorem signature and all
existing declarations are byte-for-byte unchanged; only proof imports and proof bodies changed.
Verdict: pass.

2. Compiled all four delivered modules with `lcompile.py --all`. There are no errors, warnings,
`sorry`s, forbidden declarations, or hollow definitions. The delivered proofs use only the permitted
existing open declarations in their imported dependency closure. Verdict: pass.

3. Checked each split-off theorem against the source and local Mathlib declarations. The three
statements are true, strictly smaller than the item, and required by the proof; searches found no
existing duplicate declarations. Their DAG nodes, docstrings, and Lean signatures agree. Verdict:
pass.

4. Read the proof from the target downward. The route uses the concrete range construction and
finite-module completeness, and retains the unit's coefficient-ring route while removing the unused
kernel-classification step. The imports removed from the item are recorded in the report. Verdict:
pass.

5. Checked the DAG node `proof`, `proof_deps`, and `proof_origin` fields against the actual Lean
proofs, and checked the unit's realized route is unchanged. Verdict: pass.

Changed after second reading: added this review section; no Lean, DAG, or proof changes were needed.
