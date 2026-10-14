## What changed

The original theorem `AlgebraicGeometry.Scheme.Modules.tensorGradedAction_projection_second`
is proved, with its statement and visibility unchanged, from the new sheaf-level identity
`tensorGradedAction_kernel_second`. The proof applies the cohomology functor to that
identity, evaluates the canonical coefficient projections, uses a proved naturality
square, and cancels the right unitor under cohomology.

Added `Sheaf.AlgebraicGeometry.TensorGradedActionKernelSecond`, whose single theorem
isolates the homogeneous multiplication calculation before cohomology. It does not
mention the cohomology action rho, a cohomology class, or the cohomology comparison square.
Added `Sheaf.AlgebraicGeometry.TensorBoundaryKernelMapNaturality`, which constructs the
kernel-to-pushforward isomorphism and transported kernel map as explicit composites,
and proves naturality for arbitrary coefficient morphisms and arbitrary input/output
exponents. Its proof uses the existing source and target naturality declarations of
`ModuleCohomologyFMapFunctorial`; no new cohomology hole remains.

The main module gains a proof-only import of `TensorGradedActionKernelSecond`. All its
original public imports remain. The node proof and proof dependencies now reflect the
sheaf identity, general comparison naturality, and explicit projection evaluation.
The unused arguments f and hrestrict and the unused let N are retained exactly as in
the original signature; only this declaration disables their unused-variable linter.
No existing definition, target statement, or consumer module changes.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.tensorGradedAction_projection_second`
(node `lem-sc-square-zero-tensor-graded-action-projection-second`).

Also fully proved
`AlgebraicGeometry.Scheme.Modules.tensorBoundaryKernelMap_naturality`
(node `lem-sc-tensor-boundary-kernel-map-naturality`), together with its private helpers
`edge_naturality` and `comparison_inv_eq`. The two new definitions contain no holes and
choose no arbitrary object: they compose the existing kernel comparison, adjunction
unit isomorphism and coefficient-degree isomorphism.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.tensorGradedAction_kernel_second`
(node `lem-sc-tensor-graded-action-kernel-second`). Its whole proof is `by sorry` and its
docstring gives the local homogeneous calculation, the off-diagonal vanishing, the
identification of the diagonal map, and gluing. The main theorem contains no sorry.
This is a decomposition: one upper hole closed, one strictly earlier sheaf-level hole
added, with the comparison transport and combination genuinely proved. Net holes: zero.

Edge cases checked in the new statements: arbitrary a and b, including zero, for the
naturality square; n=0 and e=0 for multiplication; the zero section and zero ideal.
When n=0, d+n(e+1)=n(e+2) forces d=0, so the summand argument never assumes distinct
section degrees. Local lifts need not exist globally: the proof sketch uses sheaf
surjectivity and local separation. The remaining theorem needs no hrestrict because
hglobal identifies the action with the already supplied sheaf endomorphisms mu.

## No longer needed

No original import was removed. The source module of the homogeneous quotient product
is still needed for `tensorGradedSection`, `tensorGradedCoefficientProjection`, and
`tensorGradedCoefficientProjection_apply`. Its theorem `tensorGradedSection_product`
is not used: quotient multiplication of two sections is not needed for multiplication
of an ideal by one section. Thus `lem-sc-square-zero-tensor-graded-product-projection`
remains as a construction/projection dependency, but its product theorem is pruned from
this proof route.

The main proof no longer applies the original plan's affine-edge, unit-quotient, or
presentation-existence theorems directly. Unit quotient remains needed below the new
sheaf action node for local lifts. The ideal tensor unit and cohomology-map functoriality
remain below the new naturality node. The affine-edge module remains needed by the
existing canonical comparison construction; no claim is made that it leaves the
whole targets' import closure. No whole existing module is newly pruned.

The complete list removed from the item's old direct `proof_deps` is:

- `lem-sc-square-zero-tensor-graded-presentation`;
- `lem-weil-pbc-closed-immersion-unit-quotient`;
- `lem-sc-square-zero-ideal-tensor-unit`;
- `lem-weil-pbc-affine-morphism-cohomology-edge`;
- `lem-weil-pbc-module-cohomology-fmap-functorial`.

They remain construction dependencies or dependencies of the new lower nodes; this
list records direct-route pruning, not removal from the targets' import closure.

Removed the experimental proof-only `import all Mathlib.CategoryTheory.Limits.HasLimits`;
the final proof does not need it. All profiling and pretty-print options were removed.

## Where the brief, the DAG or earlier work was wrong

The DAG's two conceptual steps were not supplied as usable sheaf-action or
coefficient-naturality declarations. Existing presentation and comparison declarations
supply their data, but do not assert the needed sheaf identity. The delivery makes
that first step a separate named node and proves the second from existing functoriality.
The plan's auxiliary section f is irrelevant to the second equation, and restriction
compatibility is already implicit in the given endomorphism mu plus hglobal.

The literature files are absent in this read-only checkout. Read the actual Stacks
pages [09MS](https://stacks.math.columbia.edu/tag/09MS),
[0B8S](https://stacks.math.columbia.edu/tag/0B8S), and
[01F8](https://stacks.math.columbia.edu/tag/01F8). The new sheaf calculation expands the
graded action argument, and is marked agent-written rather than claiming that Stacks
states this exact Lean transport identity.

During verification, broad simp/rw steps produced expensive conversions through the
chosen limit cone or a mismatch in inferred category instances. Explicit functor-map
composition equalities and explicit comparison composites avoid those conversions.
No time limit was raised and no existing interface was altered.

The unit `sk-thm-curveestimate` has no recorded proof-step nodes to bypass, and its
statement node remains untouched. The inherited blueprint origin is preserved.

## New nodes

`lem-sc-tensor-graded-action-kernel-second`, in module
`Sheaf.AlgebraicGeometry.TensorGradedActionKernelSecond`: the pre-cohomology homogeneous
quotient action identity. It is strictly part of the parent argument, with no rho or z.
Its source is the graded ideal sequence in 09MS and quotient action in 0B8S.

`lem-sc-tensor-boundary-kernel-map-naturality`, in module
`Sheaf.AlgebraicGeometry.TensorBoundaryKernelMapNaturality`: the fully proved general
naturality square for the explicit transported kernel map. The module also contains
the two explicit constructions required to state the square. It uses cohomology-map
source/target naturality and the existing canonical comparisons. Both new nodes inherit
the parent's chapter, unit and blueprint origin; blueprint searches found no duplicate.

No change records are needed: no existing interface or definition changed.

## Second reading by M2

1. **Unchanged interface: pass.** Read the repository and sandbox versions and diffed
   the only existing delivered module. The complete text from `theorem
   tensorGradedAction_projection_second` through its result type is byte-identical.
   In particular f, hrestrict, haction, hD and the unused let N are retained. Its
   original docstring and public import are unchanged; the extra import is proof-only.
   Both other modules and their declarations are new. No existing definition or
   statement changes, no forced adaptations, and no change record are needed.

2. **Proof and trust: pass as a decomposition.** Compiled all three modules in import
   order with lcompile.py. Read the full naturality proof: edge_naturality composes
   the source and target naturality equations, comparison_inv_eq expands the actual
   inverse comparison, and the final square cancels tb.inv followed by tb.hom.
   Read the main proof: hk is mapped by H_X, hp evaluates the coefficient projection,
   hn evaluates the proved naturality square, and hr cancels the right unitor.
   Separate scratch copies with `#print axioms` show exactly propext,
   Classical.choice and Quot.sound for both new constructions and the naturality
   theorem. The main theorem and kernel-action theorem additionally use sorryAx.
   A source scan finds exactly one sorry, the named kernel-action theorem, and no
   forbidden declaration or hollow definition. Thus one original hole closes and
   one lower hole is added; net zero. Naturality is fully proved with standard axioms.

3. **Split statement and search: pass.** The remaining hole asserts equality of
   sheaf maps before H^1, without rho or a cohomology class. It is the first part of
   the original argument, not the original conclusion under a new name. I checked
   the actual fields shortExact, b_quotient, b_multiply, k_inclusion, k_colimit,
   k_projection and k_orthogonal of TensorGradedPresentation and the definitions of
   tensorGradedSection, boundarySectionDegreeIso and boundaryCoefficientDegreeIso.
   hD fixes the section transport; local degreewise quotient lifts suffice. Mono i
   makes hlocal determine the action on each lifted homogeneous section; hglobal
   identifies its restrictions with the supplied module endomorphism, so hrestrict
   is unnecessary in this lower statement. In a generator ell the product sends
   r ell^d and a ell^(n(e+1)) to ar ell^(d+n(e+1)), with r in J. The canonical
   comparisons preserve these generator tensors, including exponent-zero unitors.
   Equality d+n(e+1)=n(e+2) is equivalent to d=n; this includes n=0 and e=0.
   Zero x and J=0 give zero maps, and an empty scheme gives the unique zero maps.
   The naturality theorem permits arbitrary a,b and v, including zero and identity;
   its inverse-cancellation proof imposes no extra hypotheses on v.
   Read [Stacks 09MS](https://stacks.math.columbia.edu/tag/09MS),
   [0B8S](https://stacks.math.columbia.edu/tag/0B8S), and
   [01F8](https://stacks.math.columbia.edu/tag/01F8): these supply the graded ideal
   sequence, quotient action and functoriality, respectively; the exact transport
   identities are agent-written expansions. Searched independently with LeanFinder
   for sheaf graded-algebra ideal multiplication and homogeneous projections,
   Loogle for Functor.mapIso, and rg for graded actions and kernel/comparison
   naturality in both Lean roots. The graded-ring hits do not supply the sheaf
   identity. ModuleCohomologyCoefficientFactor only supplies source factorization;
   the existing FMap naturality declarations are already used. No duplicate found.

4. **Route and pruning: pass.** The existing public import provides types and
   projection constructions; the new public imports provide the types and explicit
   kernel map appearing in the new signatures. FMapFunctorial is proof-only in the
   naturality module, and KernelSecond is proof-only in the main module. No unused
   import remains. The main proof uses the pre-cohomology action, projection
   evaluation and comparison naturality and cannot be shortened by the search hits.
   I added the complete five-node list removed from the old direct proof_deps under
   No longer needed. Those modules remain available transitively, so no whole module
   is claimed pruned. sk-thm-curveestimate.realized has statement
   thm-sc-proper-cohomology and no recorded steps; neither is changed or bypassed.

5. **DAG: pass after metadata repair.** Existing-node changes are confined to proof,
   proof_deps and proof_origin (the unnecessarily normalized lean.statement was
   restored). Both new nodes have their chapter, unit, source, agent proof origin,
   searches, split status, created record, blueprint ancestry and Lean record.
   Each proof_deps equals the union of its steps' uses. I added the missing
   lem-sc-tensor-boundary-kernel-map-naturality statement dependency to the kernel
   node, and corrected the naturality node's source and origin to 09MS, 01XC and
   01F8 rather than quotient multiplication. All statement citations now occur in
   stmt_deps. Searches from this reading are recorded in both new nodes.

Second reading changed only the remaining hole's proof docstring (explicit hD
substitution and the coefficient/generator calculation, wrapped to 100 columns),
its matching proof plan, the metadata and pruning-report corrections above, and
this independent review. No Lean proof body, signature, definition or import changed.
