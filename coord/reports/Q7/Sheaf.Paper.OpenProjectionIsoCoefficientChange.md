## What changed

Proved `WeilConjectures.PurCompactSupport.openProjectionIso_coefficient_change` in
`Sheaf.Paper.OpenProjectionIsoCoefficientChange`, preserving its signature and all public imports.
Added private proved helpers for the scalar mate, localized open mate, iterated conjugate,
and the general adjunction/tensor calculation. The last calculation adapts the existing
private `tensor_square` argument in `Sheaf.SixFunctors.OpenScalarTensorNormalization`, with
objectwise projection isomorphisms so no auxiliary naturality assumption is required.

The scalar comparison is identified using `proEtaleRingSheafChangeAdjunction` and composite
adjunction uniqueness. Exact localization identifies the actual open restriction mate.
Iterated mates then identify the actual open coefficient comparison with the conjugate
isomorphism. The inverse tensor-coherence equation and the defining adjuncts of the two
open projections give the required square by injectivity of the open Hom equivalence.
The source read was sites-modules.tex, `lemma-j-shriek-and-tensor` (Tag 0E8I), and
sites-cohomology.tex, `lemma-j-shriek-and-tensor` (Tag 0GL1), together with the stated
coefficient-square and localization dependencies. Updated the item's node to record the
actual argument and its dependencies.

Validation: the complete item compiled cleanly through `lcompile.py` in 11.4 seconds.
The theorem signature is byte-for-byte identical to the original; all Lean lines
have at most 100 characters. The delivery tool performs the final axiom/sorry probe.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.PurCompactSupport.openProjectionIso_coefficient_change`.
The item contains zero remaining `sorry`; the delivery adds zero holes and no new modules.
All private helper proofs are complete. This is a proof from the existing declarations,
not a decomposition into new obligations.

## No longer needed

None. No imports were removed, and both original declared dependencies are used.
The proof does not require the separate `openComparison_isIso` theorem: invertibility
follows from the iterated-mate identification with a conjugate isomorphism.
The constant-coefficient normalization module itself is not imported; its elementary
categorical calculation is adapted locally, avoiding its specialized model dependencies.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node cites Tag 0E8I under sites-cohomology.tex; that ordinary tensor lemma is
in sites-modules.tex. Its derived analogue is Tag 0GL1 in sites-cohomology.tex.

The original DAG compressed the normalization of the two specified coefficient maps into
one sentence. The existing sheaf-change adjunction and exact-localization inverse-mate
interfaces suffice to supply that normalization; it requires no new theorem with `sorry`.
The unit route and the mathematical statement are unchanged. The two additional
DAG dependencies, `lem-weil-pbc-ring-sheaf-change-adjunction` and
`lem-sf-exact-localization-inverse-mate`, are generic tools for identifying the
already specified maps; they do not replace a mathematical step of the unit route.
The categorical proof also includes empty or identity opens, zero tensor factors,
and nonflat coefficient changes, since it imposes no extra hypothesis on these data.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
