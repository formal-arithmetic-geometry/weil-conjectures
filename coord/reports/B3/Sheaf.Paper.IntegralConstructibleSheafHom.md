## What changed

The unchanged statement
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_sheaf_hom_colimit`
now has a categorical reduction: good truncation gives a common termwise lower bound;
a finite locally closed extension tower and distinguished extension closure reduce to
locally finitely presented pieces; compatible costalk comparisons reduce each piece to
integral local finite presentation; a two-term locally finite free resolution then uses
existing finite-free Hom continuity.

Eight new auxiliary modules and their nodes record these steps. Six auxiliary statements
have complete Lean proofs; two geometric statements remain open, listed below. The returned
delivery's four duplicate helpers have been removed. The item now uses `import all
Sheaf.Paper.CondensedLocalPieceHomContinuity` to reuse the existing private generic helpers.
That library module is unchanged and is not delivered. No existing signature, definition,
visibility, or public import changed, and no change record or forced adaptation is needed.

The second reader also removed an empty namespace and the redundant direct proof import
of `Sheaf.Paper.CondensedLocalPieceCostalkModel`. That theorem remains used transitively
by the existing generic helpers.

## Proved and sorry left

One existing hole is closed by a reduction:
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_sheaf_hom_colimit`.
Two new holes are added:

- `AlgebraicGeometry.ProEtale.localFinitePresentation_of_surjective_closed_pullback`
  (`lem-weil-pbc-proetale-module-lfp-closed-reflection`).
- `AlgebraicGeometry.ProEtale.integral_lfp_locallyFree_resolution`
  (`lem-weil-pbc-integral-lfp-locally-free-resolution`).

This is a decomposition, not a completed proof of the item's import closure. The local
hole count is one closed and two added; any closure-wide progress is for the pinned
sorry ledger to measure. The two new statements are strictly smaller geometric inputs:
one reflects presentations under a surjective closed immersion, and one resolves a
locally finitely presented integral sheaf on its own scheme. Neither restates shifted
Hom continuity for a constructible source.

The six other new public theorems have complete proof bodies:
`localFinitePresentation_upperStar_of_range_subset`,
`homColimitProperty_of_strictly_bounded`, `condensed_constructible_generic_lfp`,
`condensed_locallyClosed_one_step`, `exists_condensedLocallyClosed_extension_tower`, and
`integral_lfp_hom_continuity` (the five geometric theorems are in
`AlgebraicGeometry.ProEtale`; the truncation theorem is in `CategoryTheory`).

There are exactly two `sorry` terms in the nine delivered modules, each the whole proof
of its named public theorem, with a source, full prose proof, and matching node.
`#print axioms` of all nine public declarations shows only `propext`, `Classical.choice`,
`Quot.sound`, and, where dependencies remain open, `sorryAx`. The truncation theorem uses
only the three allowed axioms. No definition or data construction was added.

## No longer needed

The item's original direct proof imports are removed:

- `Sheaf.Paper.CondensedFiniteFreeHomContinuity`;
- `Sheaf.Paper.CondensedOpenClosedRecollement`;
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`.

The corresponding old proof dependencies are no longer direct dependencies of the item:
`lem-weil-pbc-condensed-finite-free-hom-continuity`,
`lem-weil-pbc-condensed-open-closed-recollement`, and
`lem-weil-pbc-condensed-qcqs-pushforward-continuity`. They remain in the import closure
through the actual intermediate proofs. The old proof dependency
`def-weil-pbc-continuous-integral-coefficients` is now a statement dependency only; its
module remains publicly imported, as required by the unchanged signature.

The redundant direct costalk-model import from the first worker is also removed; its node
remains a proof dependency because the reused generic helper uses it. No whole module is
claimed pruned from the targets' closure, and no DAG node is withdrawn. The four duplicate
helper declarations and the proposed visibility adaptation are absent from this delivery.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated four statements already implemented privately in
`CondensedLocalPieceHomContinuity`. Its repair then exposed them publicly and added a
public import to that module. Neither copying nor changing that interface is necessary:
Lean's `import all` makes the existing private implementation available to this proof.
The second reader verified the item compiles with the original helper module unchanged.

The original plan's sequential telescope is unnecessary after filtered finite-free
continuity and good truncation. The actual reduction is recorded in the item's `proof`,
`proof_deps`, and `proof_origin`. Integral torsion is retained: local finite presentation
is not replaced by local freeness. The global integral resolution is an open obligation,
not an inference that the cited paper supplies a global finite free resolution outright.

## New nodes

- `lem-weil-pbc-hom-colimit-good-truncation`: proved canonical-cocone reduction from a
  cohomological bound to a strict termwise bound, preserving the supplied comparison.
- `lem-weil-pbc-proetale-module-lfp-immersion-transport`: proved cartesian reduction from
  image containment to presentation reflection across a surjective closed immersion.
- `lem-weil-pbc-proetale-module-lfp-closed-reflection`: open presentation-reflection step,
  using pro-etale topological invariance; no noetherianity or uniform nilpotence assumed.
- `lem-weil-pbc-condensed-constructible-generic-lfp`: proved nonempty open presentation
  locus, with the empty-scheme case handled separately by zero modules.
- `lem-weil-pbc-condensed-locally-closed-one-step`: proved open/closed distinguished
  decomposition, including the exact closed-pushforward witness and strict support drop.
- `lem-weil-pbc-condensed-locally-closed-extension-tower`: proved noetherian induction
  on closed supports, carrying towers through exact closed pushforward.
- `lem-weil-pbc-integral-lfp-locally-free-resolution`: open global two-term locally finite
  free resolution; its proof explains local DVR models, finite torsors, and finite etale
  pushforward without division by the covering degree.
- `lem-weil-pbc-integral-lfp-hom-continuity`: proved rotation of the short exact single
  triangle and closure under shifts and distinguished extensions.

No change record is needed: no previously published statement or definition changes.

## Second reading by B3

1. **Existing interfaces: PASS.** Diffed every delivered module against the shared
   repository. The item is the only changed existing module. Extracted its complete
   theorem signature through `:= by` and checked byte-for-byte equality, including all
   hypotheses, universe annotations, and conclusion. The coefficient variables and the
   three public imports are unchanged. Restored `CondensedLocalPieceHomContinuity` byte
   for byte, compiled it, and then compiled the item with `import all`; removed that
   unchanged file from the delivered set. There is no interface adaptation to justify.

2. **Proofs and axioms: PASS as a decomposition.** Read all nine modules, including
   quasi-isomorphism preservation by exact colimits, cocone-leg compatibility, pullback
   composition, the zero-scheme branch, the transported recollement triangle, strict
   closed-support induction, and the rotated single-sheaf triangle. Compiled the whole
   sandbox in import order. Independently queried axioms against the current sandbox
   overlay: only the allowed three axioms and `sorryAx` from open dependencies appear.
   The only delivered `sorry`s are the two named statements above. There are no new
   definitions, forbidden declarations, or choices of data from arbitrary existence.

3. **Split statements: PASS.** Read Bhatt--Scholze Lemma 5.4.2 and its affine ind-etale
   basis argument (Theorem 2.3.4), Definition 6.8.10, Proposition 6.8.11(3), Lemma 6.8.12,
   Remark 7.3.2, and Lemma 7.3.9 in the sandbox source text. Checked the two prose proofs:
   a surjective closed immersion is universally homeomorphic, so basis presentations,
   regular modules, finite sums and cokernels transport with the adjunction; the integral
   resolution keeps torsion, uses the finite splitting torsor under Hom(L,T), and the
   finite-etale counit is a surjective sum map, not an average. Tested empty schemes,
   identity and nonreduced closed thickenings, zero modules, free modules, O_E/pi^n,
   finite monodromy, and cover degrees divisible by ell. Neither new hole contains a
   Hom-colimit conclusion. Fresh leanfinder/loogle/grep searches were run through
   msearch.py, and rg searches checked the library's constructible pullback, extension,
   integral matrix, finite-free continuity, and topological invariance APIs. The loogle
   queries for project-only identifiers were unavailable (unknown identifier), not
   evidence of absence. The actual generic search hits do not close these geometric
   statements; the applicable existing APIs are reused. The two holes cannot be closed
   by a short specialization of those results.

4. **Top-down route and pruning: PASS.** The main proof uses good truncation, the finite
   extension tower, existing generic piece continuity, and integral lfp continuity,
   followed by extension induction. Integral lfp continuity uses the existing finite-free
   theorem and extension/shift closure. This is an actual reduction, not a renamed hole.
   Direct import pruning and every removed old proof dependency are listed above.
   Read `dag/units/sk-thm-properbasechange.json`: none of its `realized` statement or
   step nodes is removed or bypassed; all new reductions lie below that unit route.

5. **Nodes versus Lean: PASS.** Opened all nine node files and compared each recorded
   declaration, source, proof steps, and proof dependencies with its module. Checked
   every new node has the required identity, statement, source, searches, creation,
   blueprint ancestry, chapter/unit, and Lean record. Checked `proof_deps` equals the
   union of `uses` in every node's proof. The main node records the private generic API
   supplied by the existing local-piece module and retains the actual costalk dependency.
   Added fresh independent search results for both open inputs and corrected the
   one-step node's notation for closed pushforward.

Changes made by this second reader: replaced the public helper adaptation with a plain
proof-only `import all` in the item; removed the unchanged adapted module, a redundant
costalk-model import, and an empty namespace; corrected one DAG phrase and the origin
note; completed the pruning list, explicit closed/added-hole accounting, search evidence,
and this independent review. No mathematical statement or definition changed.
