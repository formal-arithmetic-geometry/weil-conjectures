## What changed

The original theorem is reduced to one strictly smaller chart compatibility theorem.
The tilde/global-sections argument on Spec is fully proved using the invertible source
counit, the adjunction Hom equivalence, and its right triangle identity. A new module
constructs the section and morphism chart equivalences explicitly, using Mathlib's
over-site equivalence and restriction APIs. All construction data are implemented;
none are chosen from an unproved existence theorem.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.affine_internalHom_evaluation_bijective`.
The private helper `AlgebraicGeometry.spec_map_bijective` is proved without new holes.

Hole added: `AlgebraicGeometry.internalHom_evaluation_chart_compare`, node
`lem-sc-internal-hom-affine-chart-evaluation`. This is an equality of the terminal
components of explicitly constructed equivalences, for arbitrary source and target
modules, with no quasi-coherence hypothesis. The delivery is a decomposition: one
upper hole closed and one strict transport hole added, net zero holes.

## No longer needed

No original imports, nodes, or modules are pruned. The original affine adjunction and
internal-Hom route are kept. The unit realization is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The local literature files were absent; the Stacks
pages for Tags 01I7 and 0BUZ were read online to verify the cited mapping property. The original plan left implicit the component comparison
between the over-site and the affine chart. The explicit equivalences are implemented,
and their component compatibility is isolated for the next worker. The helper has no
quasi-coherence requirement and applies to empty opens. On Spec, the only use of
quasi-coherence is invertibility of the source counit; the target remains arbitrary.

The next proof step is exactly the equality transports at the terminal object:
`restrictFunctorComp_hom_app_app` and its inverse, the reflexive additive component
identities of `overFunctorEquiv`, and naturality along the terminal over-object
isomorphism. Scratch experiments already verified the additive component identities
by `rfl`; broad unfolding of all nested restriction functors was unproductive.

## New nodes

`lem-sc-internal-hom-affine-chart-evaluation`:
`AlgebraicGeometry.internalHom_evaluation_chart_compare` in
`Sheaf.AlgebraicGeometry.InternalHomAffineChartEvaluation`. Its docstring explains
how the forgetful functor, over-site equivalence, chart restriction, and image-open
transports preserve the terminal component. The accompanying three definitions
construct the equivalences used in its statement. No change record is needed: no
existing public signature or definition changes.

## Second reading by S3

1. Compared the delivered affine module with the repository version. The theorem signature and all existing declaration signatures are byte-for-byte unchanged; only the proof and one proof-only import were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry` is the named chart comparison theorem, and no forbidden declarations or hollow definitions occur. Verdict: pass.
3. Checked the split-off chart comparison statement against its construction and node. It is a strict component-equality reduction, applies to arbitrary modules, and has a complete proof plan in its docstring; no duplicate library statement was found. Verdict: pass.
4. Reviewed the proof route and imports. The affine adjunction and chart route are retained, and no unused original import or proof dependency was identified. Verdict: pass.
5. Compared the DAG nodes with the Lean declarations and verified the unit and realized route remain unchanged. Verdict: pass.

Changed after second reading: added this audit record only; no Lean proof or statement changes were needed.
