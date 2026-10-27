# WeilConjectures.WfTensorUnitSquare.tensor and beta

## Reason

Restore the quarantined definition module after its global-build failure.
The archived source leaves site-size universes unresolved while constructing total
tensor complexes and their maps. The baseline compiler reports
`u + 1 =?= max (u + 1) ?u` at `tensor` and `beta`, followed by an `alpha` mismatch.
The synthesis trace selects `integralOperationsSiteSmall` (and, when suppressed,
`scalarReductionSiteSmall`), whose maximum coefficient universe leaves an
auxiliary universe undetermined. Fix the existing site-smallness witness in the
actual coefficient universe `u + 1` locally inside the two definitions. Explicitly
set the padding universe of `essentiallySmallSelf` to zero; omitting that argument
reproduces the same underdetermined maximum.

This adds only proofs of `EssentiallySmall`, constructed by `essentiallySmallSelf`.
Proof irrelevance preserves the same total complex and induced morphism. Remove
the two file-wide overrides disabling transparency, and the now-redundant scoped
settings enabling it on `beta`. No mathematical construction, declaration
signature, or public import changes. No new attribute or instance is exported.

## Old

The file disabled `backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` globally, then enabled both on `beta`.
The definitions were:

```lean
def tensor (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :
    CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ :=
  CochainComplex.mapBifunctor U V
    (proEtaleOrdinaryTensor X (ring X d))

def beta (k : constants X d ⋙ transport X d e ≅ constants X d)
    (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) (m : ℕ) :
    (complexes X d e).obj (tower X d p (tensor X d U V) m) ⟶
      tower X d p (tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V)) m := by
  let q : (complexes X d e).obj (koszul X d p m) ⟶ koszul X d p m :=
    (NatIso.mapHomologicalComplex k (.up ℤ)).hom.app
      (completedKoszulPower (A := A) 1 (fun _ ↦ p) m)
  let a : (complexes X d e).obj (tensor X d U V) ⟶
      tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V) :=
    (alpha X d e U V).hom
  exact (proEtaleTensorPullbackTotalIso e.hom (ring X d) (ring X d)
      (coefficientIso X d e) (tensor X d U V) (koszul X d p m)).inv ≫
    HomologicalComplex.mapBifunctorMap a q (proEtaleOrdinaryTensor X (ring X d)) (.up ℤ)
```

## New

The transparency settings use their defaults. The definitions are:

```lean
def tensor (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :
    CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  CochainComplex.mapBifunctor U V
    (proEtaleOrdinaryTensor X (ring X d))

def beta (k : constants X d ⋙ transport X d e ≅ constants X d)
    (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) (m : ℕ) :
    (complexes X d e).obj (tower X d p (tensor X d U V) m) ⟶
      tower X d p (tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V)) m := by
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let q : (complexes X d e).obj (koszul X d p m) ⟶ koszul X d p m :=
    (NatIso.mapHomologicalComplex k (.up ℤ)).hom.app
      (completedKoszulPower (A := A) 1 (fun _ ↦ p) m)
  let a : (complexes X d e).obj (tensor X d U V) ⟶
      tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V) :=
    (alpha X d e U V).hom
  exact (proEtaleTensorPullbackTotalIso e.hom (ring X d) (ring X d)
      (coefficientIso X d e) (tensor X d U V) (koszul X d p m)).inv ≫
    HomologicalComplex.mapBifunctorMap a q (proEtaleOrdinaryTensor X (ring X d)) (.up ℤ)
```

## Users

`tools/downstream.py` reports this module unknown because it is quarantined.
Searching both `lean/` and `quarantine/` for direct imports finds exactly these
three consumers. The existing DAG attachment and every dependency are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.WfCompletedConstantPullbackNormalization | unclaimed in shared snapshot | Same definitions and signatures; compile against restored interface. |
| Sheaf.Paper.WfNormalizedKoszulFiberUnitTransport | unclaimed in shared snapshot | Same definitions and signatures; compile against restored interface. |
| Sheaf.Paper.WfTensorPullbackCompletionUnitSquare | unclaimed in shared snapshot | Same definitions and signatures; compile after its two dependencies. |

The target statements and the mathematical meaning of their definitions do not
change. No source-library file is modified.

This complete record is delivered as `coord/changes/C4-wf-tensor-unit-square-universes.md`.
For a reviewer correction via `--apply-fixes`, the supported flattened filename is
`C4-wf-tensor-unit-square-universes.change.md`; the plain `.md` basename is not an override alias.
The retry of returned head `9bb0dae0464` preserves this reviewed Lean repair.
It drops the obsolete separate prerequisite adaptation because the current
published build no longer registers `scalarReductionSiteSmall` as an instance.
This record is supplied directly, without requiring a reviewer override.

## Status

landed 20261026T142202-L-289291 2026-10-26 (merge of deliver/C4/Sheaf.Paper.WfTensorUnitSquareData)
