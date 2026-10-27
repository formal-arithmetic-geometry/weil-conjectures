## What changed

Restored `lean/Sheaf/Paper/CompactFiberStalk.lean` from the exact quarantine path recorded in `coord/rework.tsv`, retaining its Lean attachment and every dependency. Repaired the final proof of `WeilConjectures.PurityFiniteSetting.compactFiber_qbar`: construct the conjunction first, prove model existence, introduce the model, and then project its componentwise invertibility. This prevents elaboration of a single dependent tuple from expanding the large normalized exchange model. Every existing signature, definition body, public import, visibility and the existing 10000-heartbeat bound is preserved. No other Lean module changes.

The finite proof obtains bounded etale origin and specializes the published compact-support exchange. The integral proof obtains detailed constructible-complete membership and applies completed exchange. The rational proof localizes that same isomorphism. The Qbar proof specializes the normalized common-stage theorem after deriving the geometric hypotheses from the purity setting. The DAG proof and proof origin now record the restoration and refer to the current blueprint; the proof dependencies are retained.

Validation: the full restored module compiled through the prescribed `lcompile.py` in 50.4 seconds without diagnostics. The preceding combined-tuple attempt reached the deterministic 10000-heartbeat timeout at the final Qbar projection (48.7 seconds); the separated proof succeeds with the same bound. Delivery preflight performs the declaration and axiom probe. Change record: `coord/changes/V9-compact-fiber-stalk-restoration.md`.

## Proved and sorry left

This is a quarantined-module repair with zero initial holes, not a new closure of the four holes closed by E7. Holes closed in this delivery: 0. Holes added: 0. Sorries left: 0. Split off: 0.

Restored complete proofs, all attached to `lem-pur-cfiber-stalk`:

- `WeilConjectures.PurityFiniteSetting.compactFiber_finite`
- `WeilConjectures.PurityFiniteSetting.compactFiber_integral`
- `WeilConjectures.PurityFiniteSetting.compactFiber_rational`
- `WeilConjectures.PurityFiniteSetting.compactFiber_qbar`

The private helper `compactFiber_integral_membership` remains proved. Existing dependencies retain their own proof status; this is not a claim that their transitive axiom closures contain no sorry.

## No longer needed

None in this repair. No import, declaration, module, DAG dependency or tool approval is removed. The earlier E7 pruning is preserved exactly and is not counted again. No withdrawal is requested; the quarantined file is restored rather than replaced by an empty module.

## Where the brief, the DAG or earlier work was wrong

The missing live source is quarantine, not withdrawal: `coord/rework.tsv` records `quarantine/Sheaf/Paper/CompactFiberStalk.lean` and preserves the node attachment. The archived module already has zero sorry, so this assignment repairs restoration and elaboration rather than closing an additional mathematical hole.

The final dependent tuple makes Lean elaborate the entire Qbar model while checking its projected conclusion. Introducing the conjunction and its quantified model separately avoids that expansion without changing the definition or weakening the theorem. The current blueprint reads the fibre comparison as compact-support base change; the retained four statements already fix the actual finite, completed, localized and descended arrows. Their existing specializations prove precisely those statements. No new category or arbitrary exchange is introduced, and no unit-level route is bypassed.

There are no current Lean importers in either the live or quarantined source trees. DAG parents still depend on this lemma, including `lem-pur-line-zero-class-exchange`, `thm-pur-rank-one-thom` and `thm-pur-vector-bundle-thom`; all see the identical restored interface and need no adaptation. `tools/downstream.py` reports the absent live module as unknown, so consumer checks also searched both source trees directly.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
