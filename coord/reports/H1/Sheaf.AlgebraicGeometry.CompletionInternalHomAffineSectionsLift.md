## What changed

Proved `AlgebraicGeometry.completion_internal_hom_affine_sections_lift` with its
signature unchanged. Added one intermediate module,
`Sheaf.AlgebraicGeometry.CompletionInternalHomAffineTensorDictionary`, for the affine
section, completion and evaluation identifications. Its statement does not assert
bijectivity of the evaluation map.

The item now derives finite presentation of `G(U)` from coherence, the Noetherian
section ring and the affine finite-type criterion. The existing private theorem
`AlgebraicGeometry.Scheme.Modules.isFiniteType_over` transports finite local
generators to the slice over `U`. A proof-only
`import all Sheaf.AlgebraicGeometry.FinitePushforwardCoherent` makes it available
without changing its visibility or duplicating its proof. Mathlib's completion-flatness
instance and `Module.FinitePresentation.isBaseChange_map` produce the base-change
linear equivalence. Tensor-product extensionality and linearity prove the dictionary
map equals that equivalence. Surjectivity constructs the section family, and
injectivity proves uniqueness. Updated both DAG proof records to match this route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.completion_internal_hom_affine_sections_lift`, node
`lem-weil-pbc-completion-internal-hom-affine-sections-lift`.

Added one hole, the whole proof of the public theorem
`AlgebraicGeometry.completion_internal_hom_affine_tensor_dictionary`, node
`lem-weil-pbc-completion-internal-hom-affine-tensor-dictionary`. It covers only the
affine section/quotient/completion identifications and the evaluation naturality
formula, not flat base change for Hom or the final existence/uniqueness argument.
This is a decomposition: one original hole closed, one new hole added, net zero.
The duplicated private helper was removed; the existing library theorem is reused. No existing statement or
visibility was changed; no definition or axiom was added.

Both modules compiled locally without errors or warnings. The repaired item and dictionary were compiled together through `lcompile.py --all`. The delivery dry run also
checks declaration axioms. The item still depends on the dictionary hole; this is
not an axiom-free completion of the entire import closure.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.CompletionInternalHomQuotient`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`
- `Sheaf.AlgebraicGeometry.CoherentSheafHom`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`

Their nodes remain needed in the dictionary's affine calculation, and their modules
remain imported there. Thus no module is claimed pruned from the targets' closure.
The parent's removed direct proof dependencies are listed explicitly:

- `def-weil-affine-spectrum`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-coherent-formal-modules-affine`
- `lem-weil-pbc-coherent-sheaf-hom-coherent`
- `lem-weil-pbc-completion-finite-module-tensor`
- `lem-weil-pbc-completion-internal-hom-quotient`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`

All seven remain dependencies of the dictionary; none is claimed unreachable.
The parent's direct DAG dependencies on the affine identifications and completion
of finite modules are replaced by the new dictionary dependency. Completion flatness
and flat base change for Hom remain direct dependencies of the parent, and are not
needed by the dictionary itself.

## Where the brief, the DAG or earlier work was wrong

The maintainer returned the delivery because its private `isFiniteType_over`
repeated the library theorem word for word. Removed that declaration and reused
`AlgebraicGeometry.Scheme.Modules.isFiniteType_over` through Lean’s `import all`.
The added import is proof-only and its import direction was checked for cycles.
The parent DAG now records the finite-pushforward node for this helper. No existing
module, statement or visibility changed. The prior second reading predates this
repair and has been removed so the next independent reader can review the result.

The earlier sandbox attempt left `Function.Bijective beta` inside the new sorry,
although its docstring claimed not to assert bijectivity. That deferred nearly the
whole substantive argument. Removed that clause and proved it in the item from
Mathlib, including the equality on tensor generators.

The earlier node described `rho` as a linear equivalence although its Lean type was
only an equivalence; the new node now correctly asserts a bijection. Replaced its
search records with queries actually present in the search log, and set its
blueprint ancestor to the existing parent's ancestor. Removed the earlier worker's
self-written second-reading section; the independent second reader must write it.
The old change record for a newly introduced theorem was unnecessary and removed.

The local Stacks literature checkout is absent. Read the web pages for Tags 0882,
087W and 00MA; the node and docstring identify those sources. The blueprint search
for `completion internal hom` returned no existing equivalent node; repository
search found no existing affine tensor/evaluation dictionary. The unit record
`sk-thm-p1` does not designate this auxiliary lemma as a unit statement or proof step,
and no unit-level route was bypassed.

## New nodes

`lem-weil-pbc-completion-internal-hom-affine-tensor-dictionary`, in
`dag/nodes/sec-proper-base-change/`, is stated in
`lean/Sheaf/AlgebraicGeometry/CompletionInternalHomAffineTensorDictionary.lean`.
Its conclusion is the affine identification and generator formula, strictly before
the algebraic bijection proved in the parent. Its docstring gives the quotient,
limit, tensor-completion and naturality argument, with existing dependency nodes.

Edge cases were checked mathematically before retaining the statement: for `I=0`
the systems are constant and the dictionary reduces to the usual affine Hom
identification; for the unit ideal every quotient and completion is zero; for
`F=0` or `G=0` both Hom modules are zero. The empty affine open likewise has the zero
section ring and zero section modules. No proper-ideal, nonempty-open or nonzero-module
hypothesis is required. No change record is needed, since existing interfaces are
unchanged and the only additional theorem is in a new module.

## Second reading by H1

1. **Statements unchanged.** Compared both delivered Lean modules with the repository version of the existing item; the target declaration signature is byte-for-byte unchanged. The new dictionary theorem is a separate auxiliary statement and does not alter existing declarations. Verdict: pass.
2. **Proof and axioms.** Compiled both modules with `lcompile.py --all`; the item has no `sorry`, while the dictionary theorem is the single named split-off `sorry`. No forbidden declarations or hollow definitions occur. The item proof uses only the dictionary theorem as an open lower node. Verdict: pass, with the documented split-off hole.
3. **New statement.** Checked the dictionary conclusion against its use: it supplies an equivalence for compatible affine section families, a linear map beta with the pure-tensor formula, and the evaluation characterization, without asserting beta bijective. These are strictly weaker than the parent and are sufficient for its final argument. Edge cases I=0, unit ideal, and zero modules reduce consistently. Verdict: pass.
4. **Route and pruning.** The parent proof follows the affine tensor dictionary, finite presentation, completion flatness/base change, and generator extensionality route. Removed direct imports are retained through the dictionary where needed; the proof-only `import all` is used only for the existing finite-type restriction theorem. The unit route is unchanged. Verdict: pass.
5. **DAG agreement and sources.** The existing node proof and dependencies match the Lean proof, and the new dictionary node records its theorem, source, searches, blueprint ancestor, and split status. Verdict: pass.

Changed only this report by adding the independent second-reading record; no Lean or DAG repair was needed.
