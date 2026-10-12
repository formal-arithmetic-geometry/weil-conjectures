## What changed

The signature and public imports of
`RingHom.exists_fs_adic_lift_over_finite_coefficient_map` are unchanged.
Its proof now compiles from three strictly smaller intermediate statements.
The actual Lean argument proves closedness of the closed-fibre ideal using Krull
intersection, lifts the model map with the existing complete-target lifting theorem,
proves locality and coefficient compatibility, constructs the tensor homomorphism
with `Algebra.TensorProduct.productMap`, proves its surjectivity using finite-module
completeness and Mathlib's complete-source surjectivity theorem, proves the Jacobson
bound using integrality, and kills its kernel with Nakayama.

New modules are `Sheaf.RingTheory.FsAdicClosedFiberModel`,
`Sheaf.RingTheory.FiniteCoefficientTensorReductionSurjective`, and
`Sheaf.RingTheory.FiniteCoefficientTensorKernelReduction`. Each isolates one part
of the original proof and has exactly one named public theorem with a whole-proof
`sorry`. The parent node records the implemented route. A fourth new node records
an already proved Mathlib surjectivity theorem; it adds no Lean module or hole.

All four Lean modules compile together in dependency order through lcompile.py.
The private closed-ideal helper is fully proved. No data is defined by choosing a
witness of an unproved mere-existence theorem: C and maps are unpacked only inside
this theorem proof; the tensor map itself is built explicitly.

## Proved and sorry left

Closed the original hole in
`RingHom.exists_fs_adic_lift_over_finite_coefficient_map`
(node `lem-weil-pbc-fs-adic-lift-over-finite-coefficient-map`).
There is no `sorry` in the item's module.

Added exactly three holes:
- `RingHom.exists_fs_adic_closed_fiber_model`
  (`lem-weil-pbc-fs-adic-closed-fiber-model`): only the smooth closed-fibre model and
  its quotient map; no map into B, finiteness hypothesis, flatness, or tensor map.
- `RingHom.finite_coefficient_tensor_reduction_surjective`
  (`lem-weil-pbc-finite-coefficient-tensor-reduction-surjective`): only the finite
  nilpotent iteration modulo m_C B; no completeness, Noetherianity, or flatness.
- `RingHom.finite_coefficient_tensor_kernel_reduction`
  (`lem-weil-pbc-finite-coefficient-tensor-kernel-reduction`): only K ≤ (m_A D)K
  from tensor exactness and the fibre; no finiteness or Noetherianity, and no claim
  of injectivity. The parent supplies finite generation, the Jacobson bound, and
  Nakayama separately.

This is a decomposition: one upper hole closed and three lower holes added,
not an axiom-free proof of the original result. The unchanged existing
`Algebra.exists_formallySmoothAdic_lift_residue_field` remains a hole used by the
first intermediate node's plan. No existing dependency was edited.

Edge cases checked mathematically: all rings are nonzero because IsLocalRing
includes Nontrivial; m₀=0 and/or m_A=0 give the field and nilpotent-ideal special
cases without division or positive-dimension assumptions. The nilpotence exponent
is positive (increase it if necessary). Residue-density needs no residue
isomorphism, while the kernel argument needs residue surjectivity and the exact
closed-fibre kernel. Finiteness and flatness occur only in their respective steps.
No unit-level statement or realized step is bypassed.

## No longer needed

Removed direct proof imports from the item:
- `Sheaf.RingTheory.CompleteLocalQuotient`: its use belongs to the closed-fibre
  model's proof plan and it remains imported in that new module.
- `Sheaf.RingTheory.FormallySmoothAdicLift`: likewise relocated to the model.
- `Sheaf.RingTheory.FiniteOverCompleteRing`: genuinely unnecessary on this route.
  The parent instead uses the already proved
  `finite_module_complete_over_complete_noetherian` for D, followed by Mathlib's
  `surjective_of_mk_map_comp_surjective`.

The parent no longer needs node
`lem-weil-pbc-finite-over-complete-ring` or module
`Sheaf.RingTheory.FiniteOverCompleteRing` through this item.
It also no longer uses `lem-weil-pbc-finite-algebra-local-radical`; the two
integrality/maximal-ideal nodes prove the needed stronger contraction equalities.
The Artinian nilpotence node remains needed only for the residue-density lemma,
not for the parent's Jacobson bound. Other old dependencies remain needed either
by the parent or by the three intermediate nodes. No additional globally
unreachable modules are claimed without inspecting the entire target closure.

Removed unused public imports from the new model skeleton (TensorProduct.Basic,
RingHom.Flat), and unused Noetherian.Defs and Filtration imports from the new
density skeleton. No existing public import was removed or changed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The original route's use of
finite-over-complete-ring can be shortened using completeness of the finite tensor
ring and direct complete-source surjectivity. Its nilpotence detour for the
Jacobson bound can be replaced by maximal-ideal contraction under integral maps.
The original docstring is retained as the eight-step source plan; the delivered
node records the refined Lean route.

LeanSearch was attempted and returned an Internal Server Error, recorded as an
unavailable search with no verdict. LeanFinder, Loogle and direct source searches
worked. The Stacks source was checked at Tags 07NS, 07NR and 07NJ.
The library's local compile needed explicit Noetherian quotient and local quotient
instances; those are established in the proved closed-ideal helper.

## New nodes

`lem-weil-pbc-fs-adic-closed-fiber-model` in
`lean/Sheaf/RingTheory/FsAdicClosedFiberModel.lean` packages only original steps 1–2.
It retains the existing complete-local quotient and residue-field lift as its
proof dependencies, with scalar and universe transport made explicit.

`lem-weil-pbc-finite-coefficient-tensor-reduction-surjective` in
`lean/Sheaf/RingTheory/FiniteCoefficientTensorReductionSurjective.lean` packages
original step 4 and the finite iteration from step 6. The completeness step is
proved in the parent and is absent from this statement.

`lem-weil-pbc-finite-coefficient-tensor-kernel-reduction` in
`lean/Sheaf/RingTheory/FiniteCoefficientTensorKernelReduction.lean` packages only
tensor exactness and the closed-fibre reduction from original step 7. It ends
before finite generation, Jacobson containment and Nakayama.

`lem-weil-pbc-complete-source-surjective-mod-ideal` records the existing Mathlib
theorem `surjective_of_mk_map_comp_surjective` in
`Mathlib.RingTheory.AdicCompletion.Functoriality`. It adds no hole and no module.

All new nodes use the parent's chapter, unit and blueprint ancestry. There are no
statement changes, forced adaptations, or change records.

## Second reading by T2

1. **Visible declarations and signatures.** I compared the delivered item module with the repository version. The target declaration has the same signature and public imports; only its proof and proof-only imports changed. The three added declarations are new split nodes, and their statements match their DAG node text byte for byte. No existing declaration or definition was weakened, strengthened, or altered.

2. **Compilation and proof hygiene.** I compiled all four delivered modules together with `lcompile.py --all`; they compile without errors. The item target has no `sorry`, and each remaining `sorry` is exactly the named theorem in one of the three new modules. There are no `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations, and no definition contains `sorry`. The private closed-ideal helper is an actual Krull-intersection proof.

3. **New statements and dependencies.** I checked the three split statements against their source descriptions and edge cases. The closed-fibre model statement contains only the model and quotient-map properties; the reduction-surjectivity statement contains only the finite nilpotent iteration; and the kernel-reduction statement stops at the submodule containment before finiteness and Nakayama. Each is strictly smaller than the parent result, has a source, docstring proof plan, and matching DAG node. The parent proof uses the declarations it records, while the relocated complete-local and lifting imports remain in the model module. The Mathlib surjectivity declaration is recorded as an existing dependency and adds no hole.

4. **Pruning and route.** The parent proof uses the explicit tensor product map, finite-module completeness, Mathlib's complete-source surjectivity theorem, integral maximal-ideal contraction, the two split reductions, and Nakayama. The removed direct imports and old finite-over-complete and finite-algebra-local-radical route are no longer needed, as listed above. No unreachable module is claimed beyond those listed removals.

5. **Unit and DAG agreement.** The target node's proof steps still follow the unit route: closed-fibre model, complete local lift, tensor construction and surjectivity, Jacobson containment, kernel reduction, and Nakayama. The parent node's `proof`, `proof_deps`, and `proof_origin` describe the implemented route, and every new node has the required `lean`, source, blueprint, status, and dependency fields. No statement-change or forced-adaptation record is needed.

I changed only this second-reading report section; no Lean declaration, node statement, or proof was changed during review.
