## What changed

The original theorem `AlgebraicGeometry.Scheme.Modules.coherent_property_devissage_integral_subschemes`
is proved by well-founded induction on closed subsets of X, followed by finite-filtration induction.
Its statement, universes, visibility and public imports are unchanged. The original nine-step route
is retained: steps 1–5 and 9 are implemented, while the generic-point argument of steps 6–8 is a
single explicitly stated smaller theorem in the new module
`Sheaf.AlgebraicGeometry.CoherentPropertyIntegralIdealsOfSmallSupport`.

Proved private helpers transport finite local generators and coherence under isomorphisms, derive
coherence of zero from the kernel of an identity, derive invariance of P under isomorphisms from
extension closure and P(0), compare supports under monomorphisms/cokernels/isomorphisms, identify
the support of a nonzero integral ideal pushforward, and assemble finite coherent filtrations.
The induction claim covers every ideal pushforward whose closed image is contained in the current
closed subset. The smaller-support hypothesis of the new theorem is supplied by a real Lean proof:
filter the module, identify the integral quotient supports, prove their strict containment using
the vanishing generic stalk, and use the well-founded induction hypothesis.

The scoped `linter.unusedVariables` option preserves the existing named `hclosure` binder inside
the integral hypothesis while suppressing its unused-binder warning. It has no effect on the
statement, proof, or downstream elaboration. All files compile without warnings via lcompile.py.
The unchanged direct caller `Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian`
also compiled without warnings against the delivered sandbox build.
No source definition or existing interface is changed; no adapted modules or change records are needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.coherent_property_devissage_integral_subschemes`.
There are no direct sorries in the original module.

Added exactly one hole, the entire public theorem
`AlgebraicGeometry.Scheme.Modules.coherent_property_integral_ideals_of_small_support`, in
`Sheaf.AlgebraicGeometry.CoherentPropertyIntegralIdealsOfSmallSupport`, node
`lem-weil-pbc-coherent-property-integral-ideals-of-small-support`.
It states only generic-point patching for ideals on ONE fixed integral closed subscheme, with
P already assumed for coherent modules supported there and vanishing at the generic point.
It does not assert global devissage or quantify over all coherent modules in its conclusion.
This is a decomposition (one hole closed, one added), not an axiom-free completion; the existing
filtration, integral-stalk, support-closedness and coherent-kernel/cokernel dependencies may
also still contain sorries. No new definitions, axioms, or choices of arbitrary data are introduced.

The finite-filtration proof handles m=0. The fixed-support statement includes the zero ideal,
using P(0); it does not assume the embedded sum has positive rank, which must be derived from
the nonzero generic stalk of the distinguished module. For an empty X no integral closed
immersion exists; the final coherent-filtration proof still handles the zero module. For a field
scheme, the vanishing-generic-stalk case is the zero module, and the new statement reduces to the
expected ideal/sum argument. Positive-dimensional cases use precisely the small-support
hypothesis. Intersections of nonzero ideals are justified on a nonempty affine domain, not by
an unsupported intersection-nonzero assertion.

## No longer needed

Removed these DIRECT proof imports from the original module:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` (node `def-pur-sheaf-tensor-product`):
  its definition remains available through the unchanged public ideal-product import, and its
  multiplication argument belongs to the new generic-point theorem.
- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`
  (node `lem-weil-pbc-closed-immersion-coherent-equivalence`): the outer proof transports
  coherence from filtration cokernels and obtains the support formula directly from closed
  pushforward stalks and closedness; the new theorem can use finite pushforward coherence.
- `Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion`
  (node `lem-weil-pbc-coherent-generic-point-ideal-inclusion`): moved to the new theorem.
- `Sheaf.AlgebraicGeometry.TensorPullback` (node `def-pc-module-pullback`): no tensor
  pullback is used; the ordinary module pushforward is Mathlib's existing construction.
- `Sheaf.Paper.SchemeTheoreticSupport` (node `lem-weil-pbc-scheme-theoretic-support`):
  moved to the new theorem, where its annihilator is required.

The parent's proof_deps also no longer directly include the module-isomorphism-on-stalks,
immersion-base-change/lft, locally-Noetherian/lft, ideal-product-stalk, ideal-intersection,
closed-immersion, integral-scheme, irreducible-components, and module-pullback nodes.
Those used to state objects, or used by the new theorem and existing proof dependencies,
remain needed there. This report claims direct route/import pruning only: it does not claim
these modules disappear from the global target closure or can be deleted from the library.
The new theorem does not need the integral-filtration theorem or Noetherian closed-subset
induction: both steps have already been proved by its caller. No blueprint unit statement or
realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The nearby `CoherentPropertyDevissage` and
`CoherentPropertyIrreducible` statements require two-out-of-three, so they do not apply to the
extension-only hypothesis here. The existing closed-immersion equivalence is unnecessary for
the outer support calculation. The existing kernel/cokernel statement and stalk-exactness
statement fit the proof after spelling out sectionwise mono preservation and the differing
stalk wrappers explicitly; their signatures were not changed.

The local literature checkout is absent. I read the source proof online at
https://stacks.math.columbia.edu/tag/01YL. The new theorem follows its generic-point and
intersection paragraphs, using the parent's already planned annihilator refinement and
explicit zero hypothesis. LeanSearch returned Internal Server Error and is recorded as
unavailable; LeanFinder, Loogle, Mathlib grep, local library rg and blueprint searches were run.
The coherent/finite-type criterion is the existing generic tool lemma already used by the
parent; no new route departure is introduced.

## New nodes

`lem-weil-pbc-coherent-property-integral-ideals-of-small-support` records the new module's sole
public theorem. Its self-contained statement includes extension closure, P(0), descent from
positive sums, a fixed integral closed immersion and generic point, the small-support
hypothesis, and the distinguished module with its ideal-product subobject condition.
The conclusion concerns only ideal pushforwards on that fixed subscheme. Source: Stacks 01YL,
the generic-point and final ideal-intersection paragraphs, with the zero case made explicit.
Its four proof steps and the declaration docstring explain the generic embedding, annihilator,
pullback subobject, extension/summand argument and intersection argument. The Mathlib and
source-library searches above found no matching theorem; the blueprint searches for
higher-rank and 01YL found no blueprint duplicate. The node inherits the parent's chapter,
unit and blueprint ancestor and records the exact new signature. The parent node's proof,
proof_deps and proof_origin now follow the implemented support/filtration induction.

## Second reading by Y3

1. Compared the delivered parent module with the repository version. Existing theorem signatures and
visibility are unchanged; the only interface addition is the explicitly documented split theorem.
Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all`. The parent theorem has no `sorry`; the
only remaining `sorry` is the named public split theorem, with no hollow definitions, axioms, unsafe,
opaque, extern, or implemented_by declarations. Verdict: pass.

3. Checked the split theorem against the generic-point and ideal-intersection argument of Stacks 01YL,
its edge cases (zero ideal, zero module, and positive summand count), and searched the local library and
Mathlib for duplicates. The statement is true, strictly smaller than the parent target, and needed by
the proof. Its DAG node and Lean signature agree. Verdict: pass.

4. Checked the proof route, imports, and pruning. The parent keeps the filtration and Noetherian
closed-support induction; removed imports are listed above, and the new theorem carries the generic
point argument. The unit route remains realized. Verdict: pass.

5. Checked DAG `proof`, `proof_deps`, `proof_origin`, the new node metadata, and the report against the
compiled Lean code. They agree, including the one split hole and its source documentation. Verdict: pass.

Changed only the parent proof/imports, added the generic-point split module and node, and added this
second-reading record. No target statement or existing declaration signature was changed.
