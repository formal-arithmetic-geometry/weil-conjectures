# intrinsicPresentationRoundTrip_exists and intrinsicCompletionUnitComponent_comm

## Reason

Complete two existing proof holes in the unclaimed dependency
`Sheaf.Paper.IntrinsicCompletion`, needed by D8's explicit coefficient and site
comparison. The first establishes the normalization of its specified round trip;
the second establishes the chain-map law of the prescribed completion unit.
No statement, data definition, import or visibility is changed.

## Old

```lean
theorem intrinsicPresentationRoundTrip_exists :
    ∃! e : 𝟭 (pbcModules T (pbcAdicCompletion T d)) ≅
        intrinsicPresentationModules T d ⋙ intrinsicPresentationModulesBack T d,
      ∀ (M : pbcModules T (pbcAdicCompletion T d)) (U : T.ProEtᵒᵖ)
        (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  sorry

theorem intrinsicCompletionUnitComponent_comm (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (q k : ℤ) :
    intrinsicCompletionUnitComponent T d r a C q ≫
        (intrinsicCompletionComplex T d r a C).d q k =
      C.d q k ≫ intrinsicCompletionUnitComponent T d r a C k := by
  sorry
```

## New

The signatures above are unchanged. The first proof constructs the sectionwise
restriction-composition isomorphism and composes with restriction along the
identity. The inverse/hom ring identity proves linearity. Site naturality and
module naturality are identity on sections, as is the normalization. Extensionality
proves uniqueness. The second proof maps the published chain-map equation by the
backward restriction and then uses naturality of this round trip. Scoped
`backward.isDefEq.respectTransparency false` permits elaboration through the
existing module restrictions; no data definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntrinsicCompletion | unclaimed | Both existing proofs completed; exact signatures retained. |
| Sheaf.Paper.WeilCompletedKoszulRoosComparison | new in D8 delivery | Uses the same intrinsic completion definitions; no signature adaptation. |
| Sheaf.Paper.WeilCompletedTensorReflector | D8 | Uses the same completion object and prescribed unit. |

`tools/downstream.py Sheaf.Paper.IntrinsicCompletion --uses
intrinsicPresentationRoundTrip_exists intrinsicCompletionUnitComponent_comm`
reports 1,597 transitive consumers and only this module itself as a textual user
of either theorem. Every consumer's statements and data definitions remain
identical by proof irrelevance; none needs adaptation. This is a proof-only
change, not a statement or definition repair requiring consumer edits.

## Status

landed 20261019T192713-L-1857039 2026-10-19 (merge of deliver/D8/Sheaf.Paper.WeilCompletedTensorReflector)
