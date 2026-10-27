# AlgebraicGeometry.Scheme.cbcRefinementMap

## Reason

The component formula expands several derived functors during naturality checking,
exceeding the compile limit. Store its actual composite as the irreducible public
natural transformation `cbcRefinementTransformation`, and obtain the component by
projection. This is real data built from the existing proper/open mate, the inverse
proper identity comparison, and the proper compositor; no existence theorem chooses
it and no new proof assumption determines its data. The explicit left unitor and
associator have identity components. Their components simplify using functorial
preservation of identity and the category unit laws to precisely the old formula.
The mathematical map, its direction, all hypotheses, and its signature are unchanged.

This changes a definition used in the targets' closure, so the targets' statement
review must be reopened according to AGENTS.md section 4, despite the unchanged
meaning and unchanged target text. No adopted source-library file is changed.

## Old

```lean
def cbcRefinementMap {X Y : Scheme.{t}} {f : X ⟶ Y} [qf : QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (K : d.derived X) :
    (cbcSupport d c₂).obj K ⟶ (cbcSupport d c₁).obj K :=
  letI : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion qf
  letI : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion qf
  (d.push c₂.g).map
    ((cbcJ d c₂.i).map ((d.pushId X).inv.app K) ≫
      (cbcProperOpenGamma d c₁.i (𝟙 X) u.hom c₂.i
        (u.i_hom.trans (Category.id_comp _).symm)).app K) ≫
    (d.pushComp u.hom c₂.g).hom.app ((cbcJ d c₁.i).obj K) ≫
      (eqToIso (congrArg (fun f ↦ d.push f) u.hom_g)).hom.app ((cbcJ d c₁.i).obj K)
```

## New

```lean
def cbcRefinementMap {X Y : Scheme.{t}} {f : X ⟶ Y} [qf : QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (K : d.derived X) :
    (cbcSupport d c₂).obj K ⟶ (cbcSupport d c₁).obj K :=
  (cbcRefinementTransformation d u).app K
```

The new public construction in the same module is recorded by
`def-cbc-completed-refinement-transformation`:

```lean
@[irreducible]
def cbcRefinementTransformation
    {X Y : Scheme.{t}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) :
    cbcSupport d c₂ ⟶ cbcSupport d c₁ := by
  let : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion inferInstance
  let : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion inferInstance
  let e₁ := Functor.whiskerRight (d.pushId X).inv (cbcJ d c₂.i)
  let e₂ := cbcProperOpenGamma d c₁.i (𝟙 X) u.hom c₂.i
    (u.i_hom.trans (Category.id_comp _).symm)
  exact Functor.whiskerRight (Functor.leftUnitor (cbcJ d c₂.i)).inv (d.push c₂.g) ≫
    Functor.whiskerRight (e₁ ≫ e₂) (d.push c₂.g) ≫
    (Functor.associator (cbcJ d c₁.i) (d.push u.hom) (d.push c₂.g)).hom ≫
    Functor.whiskerLeft (cbcJ d c₁.i) (d.pushComp u.hom c₂.g).hom ≫
    Functor.whiskerLeft (cbcJ d c₁.i)
      (eqToIso (congrArg (fun f ↦ d.push f) u.hom_g)).hom
```

Its irreducibility keeps structural naturality from unfolding derived-functor data.
The complete item compiled in 32.5 seconds.

## Users

`tools/downstream.py Sheaf.Paper.CompleteCompactSupportProetale --uses cbcRefinementMap`
lists these seven modules. Each statement still refers to exactly the same map.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportExchangeDomains | unclaimed | Compiled unchanged with temporary profiling: 31.2 s against this item; 42.6 s against the published item. |
| Sheaf.Paper.CompleteCompactSupportProetale | Q3 | Component signature unchanged; naturality uses stored transformation. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Existing timeout: profiled original took 71.1 s against the published item and 70.1 s against the repaired item, both over 60 s. Same hot spots; no adaptation. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | P9 | Compiled unchanged against the repaired item in 40.0 s. |
| Sheaf.Paper.SemilinearExchangeReindexing | U2 | Compiled unchanged against the repaired item in 59.8 s. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | G3 | Compiled unchanged against the repaired item in 21.8 s. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | T2 | Compiled unchanged against the repaired item in 30.6 s. |

## Status

landed 20261026T002202-L-64499 2026-10-26 (merge of deliver/Q3/Sheaf.Paper.CompleteCompactSupportProetale)
