## What changed

The statement of `AlgebraicGeometry.torsionControlled_affine_candidate` is unchanged.
Its proof now implements formal gluing using
`FormalGlueing.exists_map_to_of_torsion_baseChange`. Mathlib supplies flatness of the
Noetherian completion and finite generation of the ideal. A proved private helper,
`completion_quotientMap_bijective`, derives bijectivity modulo the ideal from the
completion evaluation kernel formula.

The gluing theorem's kernel and cokernel equivalences transfer the same positive
uniform exponent using `LinearMap.annihilator_le_of_injective`. The proof constructs
`F` by tilde and pullback along the canonical affine isomorphism, and constructs its
map explicitly. It constructs the formal isomorphism by applying completion to the
restricted glued linear equivalence and inverting the completed tensor unit. Tensor
unit naturality and the gluing factorization prove the required equality.

Three new modules isolate the remaining affine presentation, arbitrary-module quotient
comparison, and annihilation/sheafification dictionary. These are distinct parts of
steps 1 and 3, without an existence assertion for the final algebraic candidate.
The original public import remains; all seven added imports of the item are proof imports.
No existing definition, signature, or visibility changes; no forced adaptations.

The sandbox set compiles without warnings through `lcompile.py --all`. The literature
files cited by the existing node were absent on this machine; the proof was checked
against the official Stacks pages for [087W](https://stacks.math.columbia.edu/tag/087W),
[0888](https://stacks.math.columbia.edu/tag/0888),
[0889](https://stacks.math.columbia.edu/tag/0889), and
[05GG](https://stacks.math.columbia.edu/tag/05GG).

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.torsionControlled_affine_candidate` by a compiling reduction.
This is a decomposition, not an independent proof of the full theorem: one upper
hole closed, three lower holes added (net minus two holes).

Every added hole is a named public theorem with a source, proof in words and DAG node:

- `AlgebraicGeometry.affine_formal_map_presentation`, node
  `lem-weil-pbc-affine-formal-map-presentation`.
- `AlgebraicGeometry.affine_completion_baseChange_unit`, node
  `lem-weil-pbc-affine-completion-baseChange-unit`.
- `AlgebraicGeometry.affine_map_annihilation_sheafification`, node
  `lem-weil-pbc-affine-map-annihilation-sheafification`.

There are no other new holes and no holes left in the item's module. The existing
`FormalGlueing.exists_map_to_of_torsion_baseChange` is used as the stated dependency;
its pre-existing hole is unchanged. The private quotient-map helper is fully proved.

## No longer needed

No original import was removed and no module is claimed pruned from the targets' closure.
Removed redundant imports of `Mathlib.LinearAlgebra.TensorProduct.Tower` from the two
new tensor comparison modules. The candidate retains the explicit Completeness
import: removing it made `AdicCompletion.ker_evalOneₐ_eq_map` unavailable.

The following old direct `proof_deps` are replaced in the candidate's proof by the new
comparison statements; all remain transitive dependencies, so they are not globally pruned:

- `lem-weil-pbc-coherent-formal-modules-affine`.
- `lem-weil-pbc-formal-systems-annihilated-by-power`.
- `lem-weil-pbc-completion-finite-module-tensor`.
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`.
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`.

The completion/tensor formula is never applied to the possibly infinite T.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement or route was found. The planned
signatures do not directly supply the affine-scheme-to-spectrum transport and the
arbitrary-module quotient-system comparison. Those are now separate statements.
The quotient-system unit lemma is valid for infinite modules because it compares
positive quotients; it does not identify their completion with a tensor product.
The new statements were checked at zero ideals, unit ideals, zero modules and the
empty affine scheme; the sheaf-annihilation statement also covers exponent zero.
The unit's route is retained.

## New nodes

`lem-weil-pbc-affine-formal-map-presentation` presents the prescribed formal map as
an S-linear map Q to S tensor P with the affine comparisons and a uniform annihilator
bound. It performs no algebraic gluing and constructs no candidate T.

`lem-weil-pbc-affine-completion-baseChange-unit` says completion inverts the tensor
unit for every A-module. It is the positive-quotient comparison from 05GG and tensor
right exactness, and has no formal-map, gluing, or annihilation hypothesis.

`lem-weil-pbc-affine-map-annihilation-sheafification` transfers a fixed algebraic
kernel/cokernel annihilator bound through tilde, the affine isomorphism, and an arbitrary
target isomorphism. It has no coherent formal module or completed factorization.

All nodes are in `dag/nodes/sec-proper-base-change/`. The existing candidate node's
proof, proof dependencies and proof origin follow the implemented reduction.
There are no change records because no existing interface was changed.

## Second reading by R3

1. **Unchanged interface: pass.** Diffed the candidate against the repository version
   and compared its entire theorem signature byte for byte. Only proof imports, a
   proved private helper, a local heartbeat option and the proof body differ. The
   original docstring, declaration visibility and public import are preserved. There
   are no changed definitions, other existing modules or target statements, and no
   interface change record is required.

2. **Kernel-checked reduction: pass, with explicit remaining dependencies.** All four
   files compile through `lcompile.py --all`. A scratch copy with `#print axioms`
   showed only propext, Classical.choice and Quot.sound for
   `completion_quotientMap_bijective`; the candidate and each of the three split
   theorems additionally use sorryAx. There are exactly the three reported new
   named theorem holes and no forbidden declarations or hollow definitions.
   The existing formal-gluing theorem remains an open dependency. Its existential
   witness is eliminated inside a proof of an existential proposition: no definition
   chooses arbitrary data from it or from the presentation theorem. The actual F is
   `L.obj T`, the actual map is `L.map ψ ≫ ε.hom`, and the actual formal isomorphism
   is `ρ ≪≫ C.mapIso e ≪≫ (asIso (C.map ιT)).symm`.

3. **Split statements: pass.** Read the official Stacks pages
   [087W](https://stacks.math.columbia.edu/tag/087W),
   [0888](https://stacks.math.columbia.edu/tag/0888),
   [0889](https://stacks.math.columbia.edu/tag/0889),
   [05GG](https://stacks.math.columbia.edu/tag/05GG), and
   [0ALK](https://stacks.math.columbia.edu/tag/0ALK).
   The presentation theorem uses coherence only to represent H and N by finite
   modules; 0888 permits increasing the positive exponent, exactly as its conclusion
   does. It asserts no algebraized T or F. The unit theorem needs no finite T:
   `(S ⊗ T)/I^n(S ⊗ T)` is naturally `(S/I^n S) ⊗ T`, hence `T/I^n T` by 05GG.
   These identifications carry the tensor unit to the identity and commute with
   quotient reductions. The sheafification theorem needs neither finite modules nor
   positive t, because localization is exact and ideal annihilation localizes.
   All have source references, proof docstrings and matching nodes. Independently
   searched with msearch LeanFinder for coherent formal morphisms, quotient-preserving
   completion base change and sheaf kernel/cokernel annihilation, with Loogle for the
   evaluation map, and with rg in Mathlib, upstream and Sheaf. Found only the recorded
   algebraic tools, affine formal equivalence and annihilation criteria, not these
   complete affine transport statements. None can be closed by a few-minute direct
   application of an existing declaration.

   Small cases: for I=0, S=A and the unit comparison is the identity; presentation
   reduces to the original constant-system map and the zero ideal kills every module.
   For I=A, S is zero, Q and every quotient system are zero; take P representing H,
   and the presentation kernel/cokernel are zero. For zero modules both transfers
   yield zero. For t=0 in sheafification, the hypotheses force ψ to be an isomorphism,
   so both sheaf kernel and cokernel are zero. An empty affine X has zero section
   ring and only zero module data. No nonzero-ring or nonempty-spectrum premise is
   used. These are mathematical edge-case checks, not additional Lean proofs.

4. **Route and pruning: pass after report repair.** Read the old plan, all three new
   statements, the formal-gluing comparison clauses, and `dag/units/sk-thm-p1.json`
   realized statements and steps. The argument keeps affine presentation, flat gluing,
   then sheafification, all below the unit route. In the gluing step ek and ec go from
   the glued kernel/cokernel to the formal ones, so their injective linear maps give
   precisely the annihilator inclusion used. The factorization calculation uses the
   tensor-unit naturality equation and cancels η.hom; it never identifies completion
   of infinite T with a tensor product. Removed two redundant public Tower imports
   from the new comparison modules and verified compilation. Tried removing the
   candidate's Completeness import, found its kernel formula unavailable, and restored
   it. The five old dependencies removed from the candidate's direct proof_deps are
   now listed explicitly under No longer needed; they remain transitive tools and no
   module is claimed pruned. This delivery is a decomposition: one original hole
   closed by reduction and three new holes added, not a sorry-free proof.

5. **DAG agreement: pass after metadata repair.** The existing node differs only in
   proof, proof_deps and proof_origin. Its three steps match the presentation call,
   quotient/flat-gluing construction, and completion/sheafification calculation.
   Every new node's Lean signature is verbatim and proof_deps equals the union of
   the proof steps' uses. Required fields, search records, chapter, unit and creation
   provenance are present. Corrected the new nodes' blueprint ancestry to inherit the
   existing candidate's recorded finite-etale-lifting ancestor and route, naming
   candidate proof steps 1 or 3, and supplied their empty upstream lean_audit records.
   Added each new module's blueprint identifier to its module docstring. No Lean
   statement, definition or proof body was changed by the second reading.
