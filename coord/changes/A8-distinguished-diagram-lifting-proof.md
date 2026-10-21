# AlgebraicGeometry.Scheme.pbcDistinguishedDiagramLifting

## Reason

Prove simultaneous lifting of finite expressions, equations and distinguished rows.
The proof adds only private constructed helpers and proof imports. Every public
signature, definition body and public import stays unchanged.

## Old

The following public theorem had body `by sorry`:

```lean
theorem pbcDistinguishedDiagramLifting
    {A : Type a} {B : Type b} {J : Type e} {R : Type r}
    [Finite A] [Finite B] [Finite J] [Finite R]
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out)
    (s t : B → Vertex A)
    (f : ∀ k : B, pbcDiagramVertex l Ω T X (s k) ⟶ pbcDiagramVertex l Ω T X (t k))
    (eqs : J → Equation s t) (rows : R → Row s t)
    (heqs : ∀ j : J,
      (eqs j).lhs.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f =
        (eqs j).rhs.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f)
    (hrows : ∀ k : R, pbcCommonStageDistinguished l Ω T
      ((rows k).triangle (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f))
    (M0 : Padic.FiniteCoefficientFields l Ω) :
    ∃ (M : Padic.FiniteCoefficientFields l Ω) (_ : M0 ≤ M)
      (h : ∀ j : A, (X j).stage ≤ M)
      (u : ∀ k : B, pbcDiagramStageVertex l Ω T X M h (s k) ⟶
        pbcDiagramStageVertex l Ω T X M h (t k)),
      (∀ (x y : Vertex A) (p : Expr s t x y),
        PairCategory.mkHom (X := pbcDiagramVertex l Ω T X x)
          (Y := pbcDiagramVertex l Ω T X y) M (h x.index) (h y.index)
          (p.eval (pbcDiagramStageVertex l Ω T X M h) (pbcDiagramStageShift l Ω T X M h) u) =
        p.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f) ∧
      (∀ j : J,
        (eqs j).lhs.eval (pbcDiagramStageVertex l Ω T X M h)
            (pbcDiagramStageShift l Ω T X M h) u =
          (eqs j).rhs.eval (pbcDiagramStageVertex l Ω T X M h)
            (pbcDiagramStageShift l Ω T X M h) u) ∧
      (∀ k : R,
        (rows k).triangle (pbcDiagramStageVertex l Ω T X M h)
            (pbcDiagramStageShift l Ω T X M h) u ∈ distTriang (pbcStageCategory l Ω T M)) ∧
      (∀ (x y : Vertex A) (p : Expr s t x y),
        (pbcDiagramVertexIso l Ω T X M h x).hom ≫
            ((pbcScalarSystem l Ω T hDim.out hInv.out).ι M).map
              (p.eval (pbcDiagramStageVertex l Ω T X M h)
                (pbcDiagramStageShift l Ω T X M h) u) =
          p.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f ≫
            (pbcDiagramVertexIso l Ω T X M h y).hom) ∧
      (∀ k : R, ∃ q :
        (rows k).triangle (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f ≅
          ((pbcScalarSystem l Ω T hDim.out hInv.out).ι M).mapTriangle.obj
            ((rows k).triangle (pbcDiagramStageVertex l Ω T X M h)
              (pbcDiagramStageShift l Ω T X M h) u),
        q.hom.hom₁ = (pbcDiagramVertexIso l Ω T X M h (rows k).first).hom ∧
        q.hom.hom₂ = (pbcDiagramVertexIso l Ω T X M h (rows k).second).hom ∧
        q.hom.hom₃ = (pbcDiagramVertexIso l Ω T X M h (rows k).third).hom)
```

## New

The signature is exactly the one displayed under Old. Its complete proof first
represents the finite arrows, then refines for equations and finally for
distinguished-row witnesses. Private helpers prove expression representation and
transport, eventual invertibility, triangle-isomorphism descent, exact transport
of corrected rows, and canonical recovery with the prescribed vertex maps.
They construct every isomorphism explicitly; no data is obtained from a new
unproved existence assertion. The private finite-stage exactness import reuses
`qbarScalarExtensionExact` from `Sheaf.Paper.PbcVerdierAxioms`; no theorem about
Verdier axioms in the pair category is used. The import-direction check accepts
this import. The public theorem specializes a completely proved private theorem
for general stage systems. Linter options are scoped to the private helper
section only; no exported attribute or instance changes. All endpoint comparisons
use explicit unfoldings and ordinary kernel-checked equality rewrites.

## Users

`python3 tools/downstream.py Sheaf.Paper.PbcDistinguishedDiagramLifting --direct`
reports zero direct importers. Existing public declarations are all unchanged;
there are no forced adaptations and no consumer statement changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | A8 | Close the sole theorem hole. |

## Status

landed 20261021T140755-L-2744083 2026-10-21 (merge of deliver/A8/Sheaf.Paper.PbcDistinguishedDiagramLifting)
