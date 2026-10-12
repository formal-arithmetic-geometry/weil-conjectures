## What changed

In `Sheaf.AlgebraicGeometry.FormalSystemsPullback`, replaced the hole in
`AlgebraicGeometry.exists_formalSystemsPullback` with a complete categorical reduction.
The existing signature and public imports are unchanged. Limits names are opened only
locally at private helpers, leaving the existing command surface unchanged. Private, fully proved helpers construct
cokernel comparisons for every power, prove their projection equation and naturality for
arbitrary reductions m >= n, prove preservation of coherence and annihilation, verify formal
system transitions, and assemble the natural completion comparison. The functors are actual
`ObjectProperty.lift` constructions, and their inclusion equations hold by reflexivity.
Full faithfulness lifts the ambient comparison into coherent formal systems. The open case
uses uniqueness of left adjoints and whiskering; it does not need Noetherianity of an open
subscheme to construct the ambient comparison.

Added the new module `Sheaf.AlgebraicGeometry.ModulePullbackIdealPowerProductImage` for the
remaining algebraic image calculation involving recursive module-subobject powers. Its statement
requires neither Noetherianity nor coherence nor flatness. It is strictly a part of node step 1;
it contains no formal-system functor, transition, completion, or restriction assertion.

Updated the item's proof, proof_deps, and proof_origin to match this reduction.
Both modules compile with lcompile.py. The complete delivery is also checked by deliver3.py.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_formalSystemsPullback` (one original hole).
Added and left: `AlgebraicGeometry.modulePullbackIdealPowerProductImage`
(node `lem-weil-pbc-module-pullback-ideal-power-product-image`, one new hole).
No sorry remains in the item's module; no sorry occurs inside a definition or private helper.
This is a decomposition, not a claim of an unconditional proof: one upper hole is replaced
by one strictly lower image-subobject equality. The net hole change from this delivery is zero.
All categorical glue, including both naturality directions, is proved in Lean.

## No longer needed

Removed direct imports:
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`:
  the proof needs only finite-type preservation and now imports `ModulePullbackFiniteType`.
- `Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient`:
  the module-power quotient comparison is constructed directly from the new image equality.
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`:
  no separate restriction-of-products calculation is used in the main proof.
- `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  the open case follows from the natural functor isomorphism, without a unit comparison.

The main node no longer directly uses `lem-weil-pbc-support-pullback-finite-type`,
`lem-weil-pbc-module-pullback-ideal-quotient`,
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`,
`lem-weil-pbc-module-pullback-structure-sheaf`, or `def-nagata-extended-ideal` as a proof step.
The ideal-quotient and affine ideal-product nodes remain planned dependencies of the new
lower image lemma; extended ideal data remain in the statement. Thus this is direct-import
pruning, not a claim that all these modules have left every target's import closure.
No unit statement or unit proof step is bypassed: the item is absent from its unit's
`realized` lists, and its seven-step route is implemented below the unit level.

## Where the brief, the DAG or earlier work was wrong

The original quotient theorem's Lean interface covers exponent 1 only. Its separate power
identity uses `IdealSheafData` powers, whereas the quotient and formal-system definitions use
recursive `Scheme.idealSheafPower` module subobjects. Applying the exponent-1 theorem to J^n
therefore needs a comparison of inclusions; the DAG had not stated that comparison in Lean.
The new lower image theorem supplies precisely the calculation needed by the cokernel proof.
No existing statement was changed or disputed.

The cited local file literature/stacks-project/coherent.tex was absent on this machine;
the source proofs were checked on the Stacks pages for Tags 0887 and 088B. The displayed
computation of 0887 interchanges its ideal letters, as the original node already observes.
LeanSearch was attempted and returned Internal Server Error. LeanFinder found ideal comap
facts but no recursive module-image comparison; Loogle did not know imageSubobject. Grep
in Mathlib, both library roots, DAG nodes and the imported blueprint found no matching
all-power recursive image statement. Unavailable searches are recorded as unavailable.

## New nodes

`lem-weil-pbc-module-pullback-ideal-power-product-image`, in
`dag/nodes/sec-proper-base-change/`, realized by
`Sheaf.AlgebraicGeometry.ModulePullbackIdealPowerProductImage` and
`AlgebraicGeometry.modulePullbackIdealPowerProductImage`. Source: the ideal-power quotient
calculation of Stacks 0887. Its docstring and node give the affine calculation, induction
identifying recursive powers, tensor-image generators, and sheaf gluing argument.
Edge cases checked in that argument: exponent zero, zero and unit ideals, zero modules,
empty opens and the empty scheme. No flatness is assumed: this is equality of images,
not injectivity of the pulled-back ideal inclusion. No change record is needed because
no existing signature, definition, visibility, instance, or public import was changed.

## Second reading by P1

1. **Existing interface: PASS.** Read the complete diff against the repository module.
   The byte-for-byte text of the existing `exists_formalSystemsPullback` signature,
   docstring and three public imports is unchanged. No existing definition, instance,
   visibility or target statement changes. The added helpers are private; the new
   `noncomputable section` is closed before the original namespace end. The existing
   node changes only `proof`, `proof_deps` and `proof_origin`; no change record is needed.

2. **Proof and data: PASS.** Both delivered modules compile through `lcompile.py --all`.
   Read each helper and the final proof. `powerQuotientIso` compares the monic product
   inclusion with the image of its pulled-back inclusion, takes cokernels, then uses
   left-adjoint preservation of cokernels. Its projection equation proves naturality
   for arbitrary reductions m >= n by cancellation of the cokernel projection.
   `powerProduct_pullback_zero` cancels the target quotient projection after showing
   it is an isomorphism, and then uses monicity of the product inclusion.
   `coherentFormal_pullback` checks coherence, annihilation at n+1, and the transition
   quotient factorization separately. The two lifted functors have the required
   inclusion equations by reflexivity. The completion comparison is natural both in
   the level and the coherent module, and full faithfulness lifts it to formal systems.
   The open comparison uses adjoint uniqueness and the displayed three whiskered
   isomorphisms, with matching endpoints; it requires no extra open-scheme hypothesis.
   All eight private helpers and the existing theorem were checked with `#print axioms`
   in scratch copies, as was the new theorem. Only `propext`, `Classical.choice`,
   `Quot.sound` and `sorryAx` occur. There is one literal sorry, exactly the named new
   theorem listed above; none occurs inside a definition or private helper, and no
   forbidden declaration or attribute occurs. The functors and quotient isomorphisms
   are concrete constructions. Choosing an adjunction by `.some` is permitted here:
   adjoint uniqueness determines the comparison compatible with the units, rather than
   choosing an arbitrary module or functor from a bare existence assertion.

3. **Split-off statement: PASS, still open.** Independently read Stacks
   [0887](https://stacks.math.columbia.edu/tag/0887) and the completion identity in
   [088B](https://stacks.math.columbia.edu/tag/088B), and checked the recursive
   `idealSheafPower`, `idealModuleProductι` and `toModulesι` definitions. The new lemma
   isolates the image calculation, with no formal-system functor, completion or
   naturality assertion, so it is strictly smaller than the original theorem.
   Its affine proof identifies the recursive inclusions with a^n, tensors the product
   inclusion, compares generators with (aB)^n(B tensor_A M), and glues both subobject
   inclusions on an affine basis. This needs quasi-coherence but neither Noetherianity
   nor flatness. At n=0 both images are the whole module; for positive n the zero ideal
   gives zero and the unit ideal gives the whole module. Zero modules and the empty
   scheme cause no exception. Also checked the non-flat example A=Z, B=Z/2, a=(2),
   M=Z: the tensor of a embeds no longer injectively, but its image and the extended
   ideal product are both zero. Thus the lemma correctly asks for image equality.
   The docstring supplies the complete affine-to-sheaf argument and the matching node
   records its source, searches, creation, blueprint ancestor, chapter, unit and Lean.
   Independent LeanFinder search for scalar-extension images found
   `Ideal.map_includeLeft_eq`, `Submodule.baseChange_eq_span` and
   `Ideal.smul_restrictScalars`, useful algebraic pieces but no recursive sheaf theorem.
   Loogle `Submodule.baseChange, Ideal.map` found only `CovBy.length_baseChange`.
   Grep of both library roots and Mathlib confirmed that the existing
   `modulePullbackIdealProductImage` covers n=1; `modulePullbackIdealQuotient` uses
   ideal-data powers, without the needed equality of recursive module inclusions.
   No complete few-minute route to close the remaining lemma was found.

4. **Route and pruning: PASS after import repair.** Checked the old proof dependencies
   against the new list: the report names all five removed node dependencies and all
   four removed direct imports. Read `dag/units/sk-thm-p1.json`, including `realized`:
   the item is not one of its statement/step nodes; the unit route is retained.
   The seven original argument tasks are implemented by the private helpers and final
   proof, even though the updated node groups them into five steps. Removal probes
   showed that `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde` is needed for
   the standard-pullback quasi-coherence instance, and that the new statement needs
   `Mathlib.CategoryTheory.Subobject.Limits` for `imageSubobject`; both were retained.
   The six stated proof dependencies of the still-holed new node had no matching
   direct proof imports. Added their six modules as plain `import`, following
   `coord/brief-stage3.md` section 0 and `tools/README.md` (`add_proof_imports.py`).
   In particular the old quotient and affine-product modules remain reachable through
   this planned lower proof. The pruning claimed here is removal of direct imports
   from the main module, not removal of those modules from the target closure.

5. **Nodes versus Lean: PASS.** The main node's cokernel, coherence, annihilation,
   lifting, completion and open-restriction steps match the actual helpers and terms.
   Its quasi-coherence dependency is the instance used from `Modules.Tilde`; the open
   restriction dependency is the Mathlib leaf realized by adjoint uniqueness. For both
   nodes, `proof_deps` is exactly the union of the steps' `uses`. The new statement
   matches its Lean signature and uses the same recursive powers on both sides.
   Its planned dependencies now have corresponding proof imports, while the five
   public imports provide names appearing in its statement. No new definition or
   statement change is hidden in metadata.

**Changed in this reading:** added the six missing plain proof-dependency imports to
`ModulePullbackIdealPowerProductImage.lean` and recorded this independent review.
No proof, signature, definition, public import, or node field was changed by the reader.
The result remains one closed upper hole and one added lower hole: a decomposition
with net zero holes, not an unconditional proof of the original theorem.
