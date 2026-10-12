## What changed

Completed `RingHom.finite_coefficient_tensor_reduction_surjective` in
`Sheaf.RingTheory.FiniteCoefficientTensorReductionSurjective`, preserving its signature,
visibility, docstring and imports. No other module was changed.

A proved private helper `RingHom.finite_local_power` implements step 1 of the existing node:
endow A/m₀A with its residue-field algebra structure, transfer module finiteness,
apply `IsArtinianRing.of_finite`, and apply
`isArtinianRing_iff_isNilpotent_maximalIdeal`. Pulling the zero power back through the
quotient gives m_A^n ≤ m₀A.

For steps 2 and 3, regard the tensor product as an A-algebra via the right tensor factor
and B as an A-algebra via φ. The pure-tensor formula makes F an A-algebra homomorphism.
Its linear range L contains ψ(C). Closed-fibre surjectivity gives m_A B + L = B.
The submodule identities for scalar multiplication and sums prove inductively
m_A^k B + L = B for every k. At the exponent from step 1, compatibility ψγ = φα
and locality of γ give m_A^n B ≤ m_C B. Decomposing a quotient representative now
gives an actual tensor preimage.

The unit's route is unchanged. The proof follows all three numbered steps of
`lem-weil-pbc-finite-coefficient-tensor-reduction-surjective`; its existing proof
and proof dependencies remain accurate, so no node file is changed. The two
non-definition proof dependencies are Mathlib leaves and are both used directly.

Source checked: [Stacks Remark 07NS](https://stacks.math.columbia.edu/tag/07NS),
including its nilpotent Nakayama argument and parts (1), (3). The local source
file cited by the node is absent on this machine, so the official page was read.

Validation: single-file compilation succeeds without errors or warnings, with
`autoImplicit = false`. No declaration signatures, definitions or public imports
were changed. The delivery dry run performs the project axiom probe and preflight.

## Proved and sorry left

Closed the sole existing hole:
`RingHom.finite_coefficient_tensor_reduction_surjective`
(node `lem-weil-pbc-finite-coefficient-tensor-reduction-surjective`).

The private helper `RingHom.finite_local_power` is fully proved from Mathlib.
No `sorry` remains in the delivered module; no holes are added or split off,
and no sorry-bearing Sheaf or WeilConjectures dependency is imported.

## No longer needed

None. All original imports remain: tensor-product and residue-field imports supply
the public signature, and Hopkins–Levitzki supplies the Artinian/nilpotence results.
An exploratory explicit `Mathlib.RingTheory.Ideal.Quotient.Operations` import was
removed because the existing imports already provide the quotient operations.
No existing DAG proof dependency, node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The planned finite-sum iteration can
be expressed directly using submodule scalar multiplication, avoiding an explicit
finite-sum induction or a new intermediate statement. The helper allows exponent
zero, which is harmless: its conclusion and the main power induction are valid at
zero, and no positive-exponent hypothesis is needed downstream.

## Second reading by G3

1. **Unchanged public interface — pass.** Read the complete repository and sandbox
   modules and their unified diff. The existing theorem signature, visibility,
   docstring, module header and all imports are byte-for-byte unchanged. Only its
   proof and a proved private helper were added. No definitions, other modules,
   node statements or change records are delivered.
2. **Kernel proof and axiom audit — pass.** Independently compiled the delivered
   module with `lcompile.py` (11.0 seconds, no errors or warnings). Compiled a
   scratch copy with explicit `#print axioms` for both
   `RingHom.finite_coefficient_tensor_reduction_surjective` and the private
   `RingHom.finite_local_power` (8.8 seconds). Both report exactly `propext`,
   `Classical.choice`, `Quot.sound`; neither reports `sorryAx`. The delivered
   source contains no `sorry`, forbidden declaration or kernel-check bypass.
   All local algebra structures are constructed from ring maps or quotient maps;
   the existential exponent is obtained from a proved nilpotence theorem.
3. **Split statements and small cases — pass.** No statements are split off and
   no holes are added. The private helper implements the already-planned first
   step, rather than exporting a new intermediate interface. Its quotient is
   nontrivial because the extended base maximal ideal lies in the target maximal
   ideal. Field and identity-map cases admit exponent one. Exponent zero causes
   no gap: the power induction includes zero, and the helper's containment itself
   supplies everything needed. No injectivity, flatness or finiteness of B is
   smuggled into the proof.
4. **Top-down route, searches and pruning — pass.** Read all three planned steps,
   both Artinian Mathlib dependency nodes and `dag/units/sk-thm-p1.json`, including
   its `realized` fields. The unit route is retained. Independently searched
   LeanFinder for finite local algebra maximal-ideal power containment, Loogle
   for ideal/submodule supremum identities, and repository/Mathlib sources for
   tensor surjectivity and nilpotent lifting. Read
   `RingTheory.surjective_of_surjective_mod_nilpotent`: using it here would require
   additional quotient-module setup, whereas the existing direct power induction
   is short and proves the required relative containment. Mathlib's
   `surjective_of_mk_map_comp_surjective` requires completion/separation hypotheses
   unavailable here; ordinary Nakayama requires finite-generation hypotheses.
   Both public imports support the signature; the Hopkins–Levitzki import is
   correctly proof-only. All old proof dependencies remain used, so `No longer
   needed: None` is complete. No module or node is pruned.
5. **DAG and source agreement — pass.** The unchanged node's `proof`, `proof_deps`
   and `proof_origin` describe the implemented finite-fibre, power-iteration and
   quotient-lifting argument. Its two substantive dependencies are used via their
   recorded Mathlib declarations. Checked the official Stacks Remark 07NS page:
   the nilpotent Nakayama iteration is the cited source argument; this node states
   the isolated finite-coefficient reduction, rather than claiming the whole
   complete-local-ring remark without its hypotheses. No new node is needed for
   the private implementation of its existing first step, and no split-off node
   is missing.

Second-reading changes: appended this independent review and recorded additional
searches. The Lean proof, imports and DAG files needed no repair. One existing
hole is closed, zero holes are added, and zero statements are split off.
