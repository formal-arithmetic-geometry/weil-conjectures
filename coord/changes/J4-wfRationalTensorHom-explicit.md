# AlgebraicGeometry.Scheme.wfRationalTensorHom

## Reason

Construct the localized bilinear Hom action explicitly by tensor-product base change,
rather than extracting its data from a unique-existence proof. The named construction
has a pure-tensor computation API, avoiding repeated elaboration of the completed
tensor and its linearity proofs. Its data are entirely constructed; no unproved
existence witness supplies any data.

The new theorem `wfRationalTensorHom_eq_choose` proves equality with the former
unique-witness expression. This preserves the map itself, including denominator
normalization, rather than merely an isomorphism class. No target statement or
hypothesis changes. The generic construction works also for the zero coefficient
ring, zero objects, and p=0; no nonzero or invertibility hypothesis is introduced.
As a definition used by the targets changes, reopen their semantic review under
AGENTS.md §4. No source-library declaration is changed.

## Old

```lean
def wfRationalTensorHom (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :=
  (wfRationalTensorHom_exists X d r a ha p M M' N N').exists.choose

```

## New

```lean
def wfRationalTensorHom (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :
    (M ⟶ M') →ₗ[Localization.Away p] (N ⟶ N') →ₗ[Localization.Away p]
      (wfRationalTensorObj X d r a ha p M N ⟶ wfRationalTensorObj X d r a ha p M' N') :=
  wfBilinearScalarHom (wfIntegralTensor X d r a ha) (wfIntegralTensor_linear X d r a ha) p
    M.obj M'.obj N.obj N'.obj
```

`wfBilinearScalarHom` curries the base change of the integral bilinear action,
composed with the inverse tensor base-change distributivity isomorphism.
`wfBilinearScalarHom_tmul` proves its formula and `wfBilinearScalarHom_spec`
proves uniqueness. All these declarations and `wfIntegralTensor_linear` are proved.

## Users

The direct declaration-user search (`tools/downstream.py
Sheaf.Paper.WeilTensorProduct --uses
AlgebraicGeometry.Scheme.wfRationalTensorHom`) lists only this item module.
No external module uses the old choice projections, and no forced adaptation
is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.WeilTensorProduct | J4 | The concrete map equals the former unique witness. | Downstream users of `wfRationalTensor` retain
its objects and its exactly equal map action.

## Status

landed 20261020T221221-L-4159364 2026-10-20 (merge of deliver/J4/Sheaf.Paper.WeilTensorProduct)
