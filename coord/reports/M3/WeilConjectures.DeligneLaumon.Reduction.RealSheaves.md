## What changed

Reduced `AlgebraicGeometry.WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar`
to a connected finite etale irreducibility detector and the existing Bertini theorem.
The dimension-one case is proved by the identity immersion of the geometric fibre,
identity-pullback invariance of irreducibility, and the geometric Galois Frobenius with m=1.
For d>=2 the proof obtains the detecting cover, applies Bertini, and returns its geometric,
point-containment and Frobenius witnesses together with the detector's irreducibility conclusion.

Added `Sheaf.DeligneLaumon.ProEtaleIrreducibilityDetector`, privately imported by the item,
with one public statement for the finite-cover argument and its complete proof in words.
It asserts no existence of a curve and is independent of finite-field models and Weil structures.
The item's existing signatures, attributes, public imports and docstrings are unchanged.
The curve-testing node now records this exact assembly. The mixedness theorem is untouched.

## Proved and sorry left

Original holes: 2. Closed in the item: 1, the curve-testing theorem
`AlgebraicGeometry.WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar`
(node `lem-zl-curve-testing-irreducibility`). Added holes: 1. This is a decomposition,
not a net proof gain: the curve existence and dimension-one arguments are complete, while
finite-cover detection is a strictly separate step. Net textual hole reduction is zero.

Remaining original hole:
`AlgebraicGeometry.WeilSheaf.IsReal.isMixed` (node `thm-zl-real-mixed-by-curves`), unchanged.
Its existing Noetherian-induction reduction remains intact, including its unfinished
nonempty-open argument.

New hole:
`AlgebraicGeometry.ProEtale.exists_connected_finiteEtale_irreducibility_detector`
(node `lem-zl-proetale-irreducibility-detector`). Its whole proof is `:= by sorry`.
It is the finite-representation/common-cover part of the current curve-testing proof,
plus the connected-restricted-torsor implication; Bertini is not part of its conclusion.

The detector includes r=0, using the identity cover. Nonzero irreducible local systems
exclude zero representations. Both bases are connected and smooth affine, so the
Noetherian regular lisse monodromy setting applies. No dimension restriction on X is
needed for this cover lemma, and the curve need not be a closed immersion. The item uses
it only in dimension at least two; dimension one is proved without this hole.

## No longer needed

The new module omits a redundant direct Smooth import because its Etale import already
publicly supplies that interface. No existing source imports were removed: every existing public import belongs to the adopted
source-library interface and remains verbatim. No source declaration or module is withdrawn.

The main curve-testing node no longer directly lists
`cor-galois-lisse-representations`, `def-pod-lisse-l-adic-sheaves`,
`def-wf-fundamental-representation`, `lem-galois-finite-etale-connected-object`,
`lem-galois-transitive`, `lem-zl-common-irreducibility-detecting-cover`, and
`thm-galois-fundamental`. The finite-representation and Galois arguments are allocated
to the detector node rather than the geometric assembly. They are not claimed as globally
pruned: the new node still cites the existing detecting-cover and representation inputs,
and no dependency of an existing proved source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The declared common detecting-cover lemma is in the etale `LisseAlgebraicSheaf` interface,
whereas the item's carriers are pro-etale `AdicSheaf`. There is no immediate application
between these types. The new detector isolates exactly the needed pro-etale conclusion;
its proof can transport the existing cover through the lisse comparison or perform the
same finite-matrix construction on pro-etale monodromy representations. The source already
has proved pro-etale lisse monodromy and its pullback compatibility, but those do not by
themselves supply the finite coefficient/lattice detector in this interface.

Likewise the mixedness node's declared filtration, constant-extension, two-point-purity,
stratification and gluing inputs concern the common-stage constructible heart, not the
source `WeilSheaf` type. They cannot be applied by changing only an import. This delivery
preserves the original mixedness theorem and its remaining hole rather than asserting
an unstated equivalence of these hearts. No mathematical statement is disputed.

The current blueprint explicitly separates finite reduction quotients, Bertini, and the
dimension-one identity argument. This delivery follows those steps and preserves the unit
route; it does not substitute a different proof of the unit's theorem.

## New nodes

`lem-zl-proetale-irreducibility-detector` is in
`dag/nodes/sec-deligne-laumon-general/lem-zl-proetale-irreducibility-detector.json`.
It records the finite-cover portion of the current blueprint curve-testing proof and the
transitivity-to-irreducibility implication, with Lean attachment, three kinds of library
search and the exact source. Its new module contains only this theorem. The parent node
is updated in the same delivery. No existing statement or definition changed, so no
consumer adaptation or interface change record is required.

Validation: both Lean files compiled on the remote server with no errors or warnings.
The final item compile completed in 22.0 seconds. Delivery preflight checks the axiom inventory. The private import direction
was checked with `tools/import_direction.py may`. The node signature matches the Lean parser.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
