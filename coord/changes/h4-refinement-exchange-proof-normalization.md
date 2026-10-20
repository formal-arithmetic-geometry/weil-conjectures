# Sheaf.Paper.RefinementExchangeCoherence proof normalization

## Reason

Complete the seven-clause refinement coherence proof without expanding the entire
section, module, tower and derived-functor constructions at each categorical rewrite.
The preflight interface scanner flags the added local elaboration commands and a
changed private factorization lemma. Record both explicitly for independent review.

## Old

The module had no local irreducibility attribute for the strict-tower operations,
no backward-definitional-equality options in its proof section, and no scoped
unused-variable linter setting on the coherence theorem.

The private factorization lemma was:

```lean
private theorem refinementComparison_factor {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (hf : QuasiCompact f) :
    let : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion hf
    let : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion hf
    refinementComparison B r hf =
      refinementPasting (J B c₁.i) (J B c₂.i) (R B (𝟙 X)) (R B r.hom)
        (R B c₂.g) (R B c₁.g) (rId B X) (refinementR B r)
        (gamma B c₁.i (𝟙 X) r.hom c₂.i
          (r.i_hom.trans (Category.id_comp c₂.i).symm)) := rfl
```

## New

The proof section uses the following module-local elaboration settings:

```lean
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] G R J rId rComp gamma adj exchange
  towers_hasDerivedCategory
```

The theorem alone uses `set_option linter.unusedVariables false in` to retain the
published names of proof hypotheses that Lean can discharge by proof irrelevance.
The attribute is local; it exports no changed attributes on imported operations.

The private factorization lemma now uses the uniquely specified representatives
whose equalities to the original operations are proved:

```lean
private theorem refinementComparison_factor {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (hf : QuasiCompact f) :
    let : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion hf
    let : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion hf
    refinementComparison B r hf =
      refinementPasting (J B c₁.i) (J B c₂.i) (R B (𝟙 X)) (R B r.hom)
        (R B c₂.g) (R B c₁.g) (rId B X) (refinementR B r)
        (refinementGamma B c₁.i (𝟙 X) r.hom c₂.i
          (r.i_hom.trans (Category.id_comp c₂.i).symm)) := by
  dsimp only
  unfold refinementComparison compositionC refinementR
  rw [refinementGamma_eq, rCompEq_eq]
  rfl
```

The private `refinementR` now uses `rCompEq` with its proved equation to the original
compositor and equality transport. The new public API is recorded completely in
`lem-cbc-strict-tower-direct-image-coherence`; it changes no existing operation.
The two existing public comparison definitions and all existing public theorem
signatures, including the target's entire seven-clause statement, stay verbatim.

## Users

`tools/downstream.py Sheaf.Paper.RefinementExchangeCoherence --uses
refinementComparison refinementCommonComparison refinementExchangeCoherence
refinementComparison_factor` reports no downstream modules. Each name occurs only
in the item itself; the factorization lemma is private.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RefinementExchangeCoherence | H4 | Private proof normalization and the completed coherence proof; no public signature or existing public definition changes. |
| Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence | H4 (new module) | Proved API for the canonical direct-image compositors and their mates; no existing consumers require adaptation. |

No existing source-library or other group's module is adapted. DAG parents and the
unit route retain the item's original statement and Lean attachment.

## Status

landed 20261020T233148-L-900775 2026-10-20 (merge of deliver/H4/Sheaf.Paper.RefinementExchangeCoherence)
