## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.exists_localizingExceptionalAdjoint`
in `Sheaf.Paper.LocalizingExceptionalAdjoint`, preserving its entire signature and both
existing definitions/instances. All added imports are proof-only. Two proved private helpers
transport compactness under isomorphism and detect isomorphisms using shifted generators.

The proof uses `brownHypotheses` for both schemes and `compactification_localizing` for the
specified boundary compactification. It transfers ambient coproduct preservation to the
full subcategories, explicitly reindexing from `u + 2` to `u + 1` through `ULift` and a final
functor. Essential smallness and local smallness produce small models of Dctf. The existing
`brownHomRepresentabilityLocallySmall` theorem supplies the right adjoint without imposing
larger coproducts. Mathlib constructs its coherent shifts, proves its exactness, and supplies
the counit-compatible comparison isomorphism; Hom-equivalence injectivity proves uniqueness.

For coproduct preservation, the source test objects are all integer shifts of the chosen
small model. Repleteness transfers the thick Dctf property along the inclusion's canonical
shift isomorphism. The Brown theorem on Y makes their images compact. A direct distinguished
cone argument proves detection, then the already-proved
`compactTests_rightAdjoint_preservesCoproducts` supplies preservation, including empty sums.
The direct cone proof uses the general Brown weak-generator conclusion and works for an
empty family. The existing node's proof/proof_deps/proof_origin now follow this argument.
The retained proof was checked against the current sources and compiled again cleanly
on the server in 34.6 seconds (within the 60-second limit). Its theorem signature,
existing definition and shift instance are textually unchanged from the current sources.

Generic tools used: `lem-pc-brown-hom-representability-locally-small` is the existing
universe-transfer form of the same Brown application; `lem-sc-compact-tests-right-adjoint-coproducts`
is a proved generic adjunction/compact-Hom calculation. Neither replaces a geometric unit
step. `det-def-localizing-closure-existence` supplies ambient sums and closure under existing
sums of the recorded localizing subcategory.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.exists_localizingExceptionalAdjoint`
(node `sk-prop-sf-existence`). Added 0 holes; split off 0 statements. No `sorry` remains in
the delivered module. Imported named hypotheses remain the separately assigned obligations.

## No longer needed

Removed direct imports `WeilConjectures.Compactification.Dense` and
`Mathlib.CategoryTheory.Yoneda`. Replaced the direct proof import
`Sheaf.CategoryTheory.BrownRepresentabilityRightAdjoint` with
`Sheaf.CategoryTheory.BrownRepresentabilityHomLocallySmall`, which invokes the former after
shrinking Hom universes; the original Brown theorem remains an indirect dependency.

Removed direct proof dependencies `sk-thm-nagata-compactification` (the statement already
supplies c), `lem-galois-yoneda-fully-faithful` (canonical adjoint shifts are supplied directly
by Mathlib), `lem-pc-brown-representability-right-adjoint` (used through its existing
locally-small wrapper), and `det-brown-hypotheses-generation` / its module
`Sheaf.Paper.BrownHypothesesGeneration` (its finite-field specialization is unnecessary:
`brownHypotheses` already gives the required general weak-generator conclusion).
The obsolete top-level tool approvals for the direct Brown and Yoneda uses were removed;
the uniqueness approval remains. No library module is withdrawn; these facts may still be
used by other items.

## Where the brief, the DAG or earlier work was wrong

The old plan's finite-field generation lemma does not apply to this arbitrary
positive-characteristic field; the bundled general Brown-hypotheses conclusion is sufficient
and is used in the explicit cone proof. Nagata is unnecessary because the theorem takes a
boundary compactification as an argument. The full-subcategory shift is not definitionally
the ambient shift, so the Dctf test uses the inclusion's canonical shift isomorphism.
The old unit record still contains the master-snapshot statement; this delivery follows the
current main-20261015 node and blueprint, as the existing node's split report directs.

No statements, definitions, public imports, target signatures, or consumer modules changed.

Previous attempts encountered shared worktree/fetch delays and a 600-second checkout
timeout. Their completed proof work is retained. The retained required dry-run result is
`OK`: commit `0d322a0eaf` compiles and passes preflight, classified CODEX because the
proof route updates a node file. The actual delivery is being retried through the
required tool. No launcher script was edited or bypassed.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
