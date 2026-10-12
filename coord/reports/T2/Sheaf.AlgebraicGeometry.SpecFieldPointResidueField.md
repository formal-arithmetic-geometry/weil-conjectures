## What changed

Completed `AlgebraicGeometry.spec_field_point_residue_field_map` and
`AlgebraicGeometry.spec_field_point_residue_field_generic` in
`lean/Sheaf/AlgebraicGeometry/SpecFieldPointResidueField.lean`.
All four declaration statements, docstrings, and the sole public import are unchanged.

The first proof chooses the actual image point and the canonical induced residue-field map.
Its prime ideal is the kernel because a field has zero maximal ideal. Mathlib's
`Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`,
`Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField`, and faithfulness of
`Spec.map` establish the extension identity. `Ideal.ResidueField.ringHom_ext`
establishes uniqueness.

The second proof specializes the first to the fraction-field algebra map. Injectivity
makes the kernel zero; `PrimeSpectrum.closure_singleton` identifies the closure with
`zeroLocus` of zero. `IsFractionRing.div_surjective` writes every target element as a
ratio of images, and `map_div₀` and the extension identity give a preimage in the
residue field. A field homomorphism is injective, so the map is bijective and an
isomorphism. Cancelling the residue-field identification and point-congruence
isomorphisms gives the exact asserted `descResidueField` isomorphism.

The proof follows the existing node's steps 3–5 and uses only their existing Mathlib
interfaces. The unit's realized statements and proof steps are preserved. No new node,
intermediate statement, or change record is required.

## Proved and sorry left

Proved both remaining sorries:
- `AlgebraicGeometry.spec_field_point_residue_field_map`.
- `AlgebraicGeometry.spec_field_point_residue_field_generic`.

Their node is `lem-weil-pbc-spec-field-point-residue-field`. No sorry remains in this
module and none is added elsewhere. The two previously proved declarations are
unchanged. The module compiles cleanly using the prescribed local compiler. `#print axioms` for
all four declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. No import was added or removed. All five existing Mathlib leaf dependencies
remain used by the four proofs: `lem-weil-pbc-spec-residue-field-identification`,
`lem-weil-pbc-prime-residue-field-algebra`, `lem-weil-pbc-affine-open-spec-points`,
`lem-weil-pbc-residue-field-point-naturality`, and `lem-weil-pbc-morphism-from-spec-field`.
The definition dependencies remain necessary. No DAG node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

None. The planned argument compiles directly from Mathlib. The existing public-import
change record `coord/changes/SpecFieldPointResidueFieldImports.md` was read; this
delivery retains its landed import interface.


## Second reading by T2

1. **Unchanged interface: pass.** Read the entire repository and sandbox modules
   and their unified diff. The diff replaces only the two `sorry` proof bodies;
   all four existing signatures and docstrings are byte for byte unchanged.
   The sole public import supplies objects used in the statements, so it is
   correctly public. The landed import change record was checked; no new
   statement or definition change needs a record.
2. **Proof and trust: pass.** Independently compiled the delivered module with
   `lcompile.py`: no errors or warnings. Compiled a scratch copy with
   `#print axioms` for all four declarations: each uses only `propext`,
   `Classical.choice`, and `Quot.sound`. No `sorry` or forbidden declaration
   mechanism occurs. Read the canonical factorization, Spec faithfulness,
   residue-field extensionality, generic-point closure, and bijectivity arguments.
   The final cancellation proves the exact specified `descResidueField` is an
   isomorphism. Division preservation covers zero as well as nonzero denominators.
3. **Split statements: pass, vacuous.** No statement was split off and no new
   declaration was introduced. Checked the relevant Mathlib source signatures
   and independently searched `Scheme.descResidueField` through Loogle and the
   repository for residue-field comparison and generic-map interfaces. No
   existing theorem replaces either completed argument wholesale.
4. **Route and pruning: pass.** The proofs directly compose existing Mathlib
   interfaces and the preceding theorem, without introducing an open helper.
   The retained import is necessary. Checked every old `proof_deps` against
   its Mathlib match: all five lemma leaves and the spectrum/residue-field
   definition dependencies remain used across the four declarations.
   `No longer needed` is complete. Read `dag/units/sk-thm-p1.json` and its
   `realized` statements and steps: this auxiliary node is below that route,
   and no unit step is bypassed or altered.
5. **DAG agreement: pass.** Read the existing node's statement, five proof
   steps, dependency union, proof origin, and Lean declaration records.
   They describe the completed proofs: kernel by prime comap, extension by
   canonical factorization and Spec faithfulness, uniqueness by residue-field
   extensionality, then zero kernel, generic closure, and fraction surjectivity.
   No node edit or new node is needed.

Second reading changed only this report, adding the independent review evidence.
The Lean proofs required no repair.
