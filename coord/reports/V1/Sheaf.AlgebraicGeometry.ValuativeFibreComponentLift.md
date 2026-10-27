## What changed

Proved `AlgebraicGeometry.exists_valuative_fibre_component_lift` in
`Sheaf.AlgebraicGeometry.ValuativeFibreComponentLift`, preserving its signature and
all existing public imports. Added the private proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` for reducedness of
Mathlib's vanishing-ideal subscheme. Four proved private helpers record fibre
point lifting, the value of the fibre inclusion, existence of a component generic
point generalizing a given point, and rigidity of a component generic point
under generalization.

The proof follows Stacks 0GSH, `lemma-make-base-change`, read in
`literature/stacks-project/more-morphisms.tex`, lines 5093–5163. Realize the
specialization directly inside Y using the existing valuation-subring theorem.
Its pullback lift gives the section. Choose a component generic point above its
generic point, construct the reduced closure using the actual vanishing ideal,
and choose a component generic point above the section's special point in that
closure. Specialization reflected by the fibre and closed immersion embeddings,
followed by maximality of the given component, proves the final image equality.
Only a lift of the special point into the reduced closure is needed; the proof
does not need a scheme morphism factoring the entire section through that closure.

Single-file lcompile verification passed without errors or warnings (9.1 s).
No definitions or statements changed, and no consumers require adaptation.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_valuative_fibre_component_lift`
(node `lem-trf-valuative-fibre-component-lift`). Proved 1 of 1 original sorries.
Zero sorries remain, zero holes were added, and zero results were split off.
The additional private helpers are all proved.

## No longer needed

None. The proof uses the declared valuation-specialization input and the
original fibre-product, integral-scheme, fibre, generic-point and
irreducible-component dependencies. No node or module is withdrawn.
No unused private proof imports remain. Existing public imports are retained as
the module's public interface.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The existing plan is realized by constructing the
valuation map in Y directly. For its final step, point membership in the reduced
closure suffices in place of the stronger section factorization mentioned in the
plan. The theorem also covers a field valuation ring (generic point equals
closed point) without a separate case. Empty fibres are excluded by the supplied
point x, and neither Noetherianity nor finite-type hypotheses are used.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
