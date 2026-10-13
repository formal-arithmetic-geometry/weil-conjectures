## What changed

Proved `AlgebraicGeometry.etale_finiteFactorizationDataDescent` in
`Sheaf.AlgebraicGeometry.EtaleFiniteFactorizationDataDescent`, with its signature and
visibility unchanged. Replaced the proof-only import of
`Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit` by
`Sheaf.AlgebraicGeometry.AffineEtaleFiniteDiagramObjects`.

Use the existing `Scheme.affineEtale_common_models` to model the sources, and base
change above both its stage and i₀. The proved private helper `finite_maps_from_models`
applies Mathlib's local-finite-presentation map-factorization theorem to the
base-change limit of each source model and selects a common stage for finitely
many arrows. Apply it to `Fin n × Bool` to descend both families at once.
The source model and its isomorphism depend only on `q`, so both displayed
comparison equations use the same source isomorphism. The final equations are
proved by both pullback projections.

Sources checked: [Stacks 0EYL](https://stacks.math.columbia.edu/tag/0EYL), qcqs
object-descent paragraph; [01ZC](https://stacks.math.columbia.edu/tag/01ZC), clause (3);
and [01YZ](https://stacks.math.columbia.edu/tag/01YZ), base-change limit.
No covering descent is used. No quasi-compactness or quasi-separatedness of the
arbitrary targets `U q` is assumed. The empty-family case works through the same
finite cofiltered-stage selection, without a separate nonempty-family hypothesis.

Updated the existing node's proof, proof dependencies and proof origin to match
this route. No public import, definition or declaration signature changed.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.etale_finiteFactorizationDataDescent`
(node `lem-weil-pbc-etale-finite-factorization-data-descent`).

No sorry remains in the item's module. No holes added or split off. The private
helper `AlgebraicGeometry.finite_maps_from_models` is fully proved. The theorem
uses existing library results; their upstream proof dependencies remain their
own items. This is a completed proof from existing declarations, not a decomposition.

Local single-file compilation passed; the delivery dry run also runs the axiom
probe and static preflight. No library-wide build was run.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`.
Removed direct proof dependency: `lem-weil-pbc-affine-etale-site-colimit`.
This theorem needs neither site strictification, the category-colimit presentation,
covering descent, nor the site-colimit theorem's full faithfulness and eventual
equality clauses. Their modules are not added as proof imports. This is pruning
of this item's route, not a claim that all other users of those modules disappear.

Retained `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` for the
base-change diagram/cone, its limit, and cartesian source lift. Added the already
proved common-model module named above; no other import is unused.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The old DAG routed source
and W-arrow descent through the much larger affine etale site-colimit theorem.
Both arrow families instead descend by the same Mathlib 01ZC(3) theorem once
source models are fixed. The original declaration docstring is preserved; its
more specific order (descend W-arrows first) and suggested identity stage for
n=0 describe the old plan, not a requirement of the unchanged conclusion.

`lem-pbc-affine-etale-common-models` is used as an existing object-descent tool;
its unit is `sk-thm-p1`, while this item belongs to `sk-thm-iff`. It supplies only
finite source models for the same 0EYL descent argument. No unit statement or
realized unit step is bypassed or changed.

## Second reading by E2

1. I compared the delivered module with the repository version. The theorem
   signature, statement, visibility, and docstring are unchanged; only the
   proof-only import, a private helper, and proof terms changed. The DAG node
   records the corresponding route and dependencies.
2. I compiled the delivered module with `lcompile.py`; it succeeds with no
   errors. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by` declarations in the delivered Lean file. The helper and
   target are ordinary proved declarations.
3. No statement was split off and no new node was added. The existing target
   statement is unchanged and the proof uses the existing common-model and
   finite-presentation descent declarations. The finite Bool-indexed family
   handles both arrow families, including the empty-family case.
4. The proof takes a shorter route than the old site-colimit route: it uses
   common affine source models followed by Mathlib's locally-finitely-presented
   morphism factorization. The removed site-colimit import and dependency are
   therefore genuinely unused; the retained imports are used by the proof.
5. The unit `sk-thm-iff` and its realized route are preserved. The common-model
   declaration is used as an existing lower-level descent tool; no unit
   statement or realized step is changed or bypassed.

Changed in this second reading: added this audit section to the report only.
