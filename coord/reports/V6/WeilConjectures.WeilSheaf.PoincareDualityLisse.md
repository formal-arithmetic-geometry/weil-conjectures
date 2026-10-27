## What changed

Completed `WeilConjectures.WeilSheaf.PoincareDualityLisse`, preserving the existing theorem
signature, public imports, and docstrings. Added private proof imports of
`WeilConjectures.WeilSheaf.VerdierDualFinite` and
`WeilConjectures.WeilSheaf.StalkRationalPoint`.

The proof uses Verdier exchange on `Ra_! F`, the smooth lisse identification
`D_X F ≅ F^∨(d)[2d]`, and duality on the point. Taking degree `-i` gives a
Frobenius-equivariant linear equivalence
`H^j(F^∨(d)) ≃ H_c^i(F)^∨`, since `2*d-i=j`.
Pulling back the ordinary evaluation pairing along this equivalence gives perfectness.
The dual Frobenius acts by precomposition with inverse Frobenius, so simultaneous
Frobenius on the two arguments cancels exactly.

The three proved private helpers for contravariant dual equivalences, global sections of
a dual sheaf on the point, and arbitrary-degree cohomology of the Verdier dual were reused
from `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse`.
That module remains unchanged. The arbitrary-degree helper shifts the existing degree-minus-one
Verdier duality theorem and then uses the finite-scheme duality and stalk/global-section
comparison. Every helper has a complete Lean proof.

Validation: the complete module compiled without errors or warnings using `lcompile.py`
(11.5 seconds). Both private imports passed `tools/import_direction.py may`.
Mathlib searches through `msearch.py` used LeanFinder for the cohomological pairing,
Loogle for `LinearMap.IsPerfPair`, and grep for `IsPerfPair`; the useful algebraic API is
`Module.Dual.eval` and `LinearMap.IsPerfPair.compl₁₂`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`.
Original holes: 1. Closed: 1. Added: 0. Remaining in the delivered module: 0.
No statements are split off. The proof uses existing library theorems, including the
still-unfinished general Verdier exchange, exceptional-adjunction existence, smooth dualizing
complex, and lisse internal-Hom interfaces. This delivery completes the local proof from those
interfaces; it does not claim to close their existing transitive holes.

## No longer needed

None. No public or private imports were removed, and no node or module is withdrawn.
The unit's argument remains derived duality followed by cohomology of the dual over the
coefficient field; the existing Weil/Frobenius interfaces supply this argument directly.
The finite-field-only étale `degreewise_duality` and degreewise pairing theorems were examined
but are not imported: their finite coefficient hypothesis does not apply to `PadicAlgCl l`.
This is not a claim that those declarations can be removed from the library.

## Where the brief, the DAG or earlier work was wrong

There is no node with `lean.module` equal to this upstream module in the current checkout.
Its docstring points to the general degreewise-perfectness and twisted-equivariance nodes;
those are broader than this existential lisse specialization. Their unit records have no
realized attachments to change. No DAG statement, dependency, or unit route is altered.

The source module's implementation note predates the existing Weil Verdier-duality API.
The archived module already supplies the proved point-duality helpers, but does not supply
the main theorem. The completed proof combines those helpers with the current public
Verdier exchange and smooth-lisse interfaces. Existing source docstrings were preserved.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
