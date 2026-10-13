## What changed

Proved `CommAlgCat.FiniteEtale.exists_finiteEtale_residueField_equiv_of_finite_separable`
in `Sheaf.RingTheory.HenselianFiniteEtaleFieldLift`, without changing its signature,
universes, visibility, or public imports. The proof uses only Mathlib. It lifts the monic
minimal polynomial of a primitive element and explicitly constructs `ULift (AdjoinRoot f)`.
All local glue is proved inside the theorem; no new declaration or module was added.

The derivative is a unit in the monic quotient: every maximal ideal contracts to the
base maximal ideal, and separability rules out a simultaneous root of the reduced polynomial
and its derivative in the corresponding quotient field. Thus the standard etale localization
is isomorphic to the quotient itself. The tensor fibre is identified with the prescribed field
by the base-change equivalence for AdjoinRoot and the primitive-element equivalence.

Added the proof-only import `Mathlib.RingTheory.Etale.StandardEtale`. Removed three old
proof imports, listed below. Updated the existing node's proof, proof_deps and proof_origin.
This is a below-unit refinement: the item is not one of sk-thm-p1's realized statement/step
nodes, and no unit statement or required step was bypassed.

Sources read: [Stacks 04GK](https://stacks.math.columbia.edu/tag/04GK), the field-lifting
paragraph, and [Stacks 00UD](https://stacks.math.columbia.edu/tag/00UD), the monic-polynomial
construction. The derivative-unit refinement is written by Q1 and proved in full.
The existing theorem docstring is preserved; its proof paragraph records the former route.
The inline proof comments and updated DAG describe the actual route.

## Proved and sorry left

Closed 1 original hole:
`CommAlgCat.FiniteEtale.exists_finiteEtale_residueField_equiv_of_finite_separable`
(node `lem-weil-pbc-henselian-finite-etale-field-lift`).
Added 0 holes, split off 0 statements. No sorry remains in the delivered Lean module.
This is a proof, not a decomposition, and it uses no project declaration containing sorry.

Local single-file compilation passes without warnings. The delivery dry run runs the
project's declaration/axiom probe. The field case L = kappa, arbitrary characteristic,
and the independent universes are included; no witness is chosen from an unproved theorem.
The finite quotient is constructed from a monic polynomial lifted through a proved
surjectivity theorem. The existing henselian hypothesis is retained, though this proof
only needs its local-ring instance.

## No longer needed

Removed proof imports:
- `Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition`
- `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime`
- `WeilConjectures.Mathlib.RingTheory.Etale.ResidueField`

The proof no longer uses these planned nodes (their modules/Mathlib declarations are not
needed as the previous black-box steps):
- `lem-weil-pbc-henselian-finite-type-product-decomposition`
- `lem-weil-pbc-etale-ring-map-quasi-finite`
- `lem-weil-pbc-etale-ring-map-prescribed-residue-field`
- `lem-weil-pbc-etale-prime-generates-maximal`
- `lem-weil-pbc-etale-algebra-finite-presentation-localization`

The finite-algebra maximal-ideal contraction fact is still used directly from Mathlib,
so `lem-weil-pbc-finite-algebra-local-radical` is retained. The other DAG dependencies
are existing Mathlib leaves: primitive element, monic quotient finiteness and the minimal
polynomial quotient-field equivalence. No project module is imported by this proof;
whether the removed modules remain reached through other items is for the global ledger.
The tentative explicit imports of `Mathlib.FieldTheory.PrimitiveElement`,
`Mathlib.RingTheory.AdjoinRoot` and `Mathlib.RingTheory.Ideal.GoingUp` were also removed
after a clean compile showed they are already provided by the retained imports.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool fault was found. The earlier route is valid but unnecessarily
uses henselian product decomposition for this single-field existence theorem.
The monic construction of 00UD is already finite over the local base before localization,
and its derivative is a unit there. The proof makes this observation explicit.
No existing statement, definition, or public interface was changed. No forced adaptations.

## Second reading by Q1

1. **Visible changes and statements.** I compared the delivered Lean module and DAG node with the repository versions. The theorem signature and all existing declaration statements are byte-for-byte unchanged; the only Lean changes are proof-only imports and the theorem proof. The node records the changed proof route and dependencies.

2. **Compilation and proof status.** The module compiles cleanly with `lcompile.py`; it contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof constructs the finite algebra explicitly from a lifted monic polynomial, and the local derivative-unit argument is proved rather than assumed. No hollow definition or arbitrary witness from an unproved existence theorem is used.

3. **Statements and dependencies.** The target statement is unchanged and remains the finite separable residue-field lifting assertion. No split-off statement was added. The Mathlib route and the retained project dependency `lem-weil-pbc-finite-algebra-local-radical` are sufficient; the removed decomposition and residue-field modules are genuinely unused by the proof. The derivative-unit and tensor/base-change arguments are local proof terms, so no new DAG nodes are required.

4. **Pruning and route.** The direct monic-polynomial/standard-etale construction is shorter than the former henselian product-decomposition route for this item. It still realizes the unit's required lifting statement and does not alter any unit statement or step. The node's `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof, and the removed imports and dependencies are listed in `## No longer needed`.

5. **Edge cases and adequacy.** The construction works uniformly for degree-one extensions and arbitrary characteristic, with the universe adjustment handled by `ULift`; no extra nontriviality hypothesis is introduced. The final tensor equivalence has the prescribed residue field as a `kappa`-algebra. Verdict: the delivered proof proves the original node exactly as stated and is suitable for delivery.

Changed during second reading: added this review record only; no Lean declarations or statements were changed.
