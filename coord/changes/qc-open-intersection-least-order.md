# AlgebraicGeometry.Scheme.qcOpenIntersection_spectral_presentation

## Reason

The implicit ambient type of `IsLeast` elaborated to the ordinary subtype of opens,
with inclusion order, although its element was annotated as the definitionally equal
`OrderDual` type. Thus the chosen open was asserted contained in every smaller open.
For a nonempty scheme, the family consisting of the empty and whole opens satisfies
all hypotheses but falsifies this clause when the whole open is chosen.
Explicitly setting `α := qcOpenIntersectionIndex U i₀` makes the clause use reverse
inclusion, exactly as the DAG and the Stacks reduction require. This corrects an
intermediate statement; no target signature or definition changes.

## Old

```lean
theorem qcOpenIntersection_spectral_presentation (X : Scheme.{u}) [QuasiSeparatedSpace X]
    {I : Type v} [Nonempty I] (U : I → X.Opens)
    (hU : ∀ i : I, IsCompact (U i : Set X))
    (hdir : ∀ i j : I, ∃ k : I, U k ≤ U i ⊓ U j) (i₀ : I) :
    Small.{u} (qcOpenIntersectionIndex U i₀) ∧
    Nonempty (qcOpenIntersectionIndex U i₀) ∧
    IsDirected (qcOpenIntersectionIndex U i₀) (· ≤ ·) ∧
    IsLeast Set.univ (⟨U i₀, ⟨⟨i₀, rfl⟩, le_rfl⟩⟩ : qcOpenIntersectionIndex U i₀) ∧
    (∀ i : I, ∃ V : qcOpenIntersectionIndex U i₀, V.val ≤ U i) ∧
    (⋂ i : I, (U i : Set X)) = ⋂ V : qcOpenIntersectionIndex U i₀, (V.val : Set X) ∧
    (∀ V : qcOpenIntersectionIndex U i₀,
      QuasiSeparatedSpace V.val.toScheme ∧ SpectralSpace V.val.toScheme) ∧
    (∀ (V W : (qcOpenIntersectionIndex U i₀)ᵒᵖ) (f : V ⟶ W),
      IsSpectralMap ((qcOpenIntersectionDiagram U i₀).map f)) ∧
    Nonempty (IsLimit (qcOpenIntersectionCone U i₀)) ∧
    (∀ t : (V : (qcOpenIntersectionIndex U i₀)ᵒᵖ) →
        (qcOpenIntersectionDiagram U i₀).obj V,
      (∀ (V W : (qcOpenIntersectionIndex U i₀)ᵒᵖ) (f : V ⟶ W),
        (qcOpenIntersectionDiagram U i₀).map f (t V) = t W) →
      ∃! x : (qcOpenIntersectionCone U i₀).pt,
        ∀ V : (qcOpenIntersectionIndex U i₀)ᵒᵖ,
          (qcOpenIntersectionCone U i₀).π.app V x = t V) ∧
    (inferInstance : TopologicalSpace (qcOpenIntersectionCone U i₀).pt) =
      ⨅ V : (qcOpenIntersectionIndex U i₀)ᵒᵖ,
        TopologicalSpace.induced ((qcOpenIntersectionCone U i₀).π.app V)
          (inferInstance : TopologicalSpace ((qcOpenIntersectionDiagram U i₀).obj V))
```

## New

```lean
theorem qcOpenIntersection_spectral_presentation (X : Scheme.{u}) [QuasiSeparatedSpace X]
    {I : Type v} [Nonempty I] (U : I → X.Opens)
    (hU : ∀ i : I, IsCompact (U i : Set X))
    (hdir : ∀ i j : I, ∃ k : I, U k ≤ U i ⊓ U j) (i₀ : I) :
    Small.{u} (qcOpenIntersectionIndex U i₀) ∧
    Nonempty (qcOpenIntersectionIndex U i₀) ∧
    IsDirected (qcOpenIntersectionIndex U i₀) (· ≤ ·) ∧
    IsLeast (α := qcOpenIntersectionIndex U i₀) Set.univ
      (⟨U i₀, ⟨⟨i₀, rfl⟩, le_rfl⟩⟩ : qcOpenIntersectionIndex U i₀) ∧
    (∀ i : I, ∃ V : qcOpenIntersectionIndex U i₀, V.val ≤ U i) ∧
    (⋂ i : I, (U i : Set X)) = ⋂ V : qcOpenIntersectionIndex U i₀, (V.val : Set X) ∧
    (∀ V : qcOpenIntersectionIndex U i₀,
      QuasiSeparatedSpace V.val.toScheme ∧ SpectralSpace V.val.toScheme) ∧
    (∀ (V W : (qcOpenIntersectionIndex U i₀)ᵒᵖ) (f : V ⟶ W),
      IsSpectralMap ((qcOpenIntersectionDiagram U i₀).map f)) ∧
    Nonempty (IsLimit (qcOpenIntersectionCone U i₀)) ∧
    (∀ t : (V : (qcOpenIntersectionIndex U i₀)ᵒᵖ) →
        (qcOpenIntersectionDiagram U i₀).obj V,
      (∀ (V W : (qcOpenIntersectionIndex U i₀)ᵒᵖ) (f : V ⟶ W),
        (qcOpenIntersectionDiagram U i₀).map f (t V) = t W) →
      ∃! x : (qcOpenIntersectionCone U i₀).pt,
        ∀ V : (qcOpenIntersectionIndex U i₀)ᵒᵖ,
          (qcOpenIntersectionCone U i₀).π.app V x = t V) ∧
    (inferInstance : TopologicalSpace (qcOpenIntersectionCone U i₀).pt) =
      ⨅ V : (qcOpenIntersectionIndex U i₀)ᵒᵖ,
        TopologicalSpace.induced ((qcOpenIntersectionCone U i₀).π.app V)
          (inferInstance : TopologicalSpace ((qcOpenIntersectionDiagram U i₀).obj V))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QcOpenIntersectionSpectralPresentation | E8 | Correct the order in the least-element clause; prove the corrected theorem. |

`tools/downstream.py ... --uses qcOpenIntersection_spectral_presentation` finds zero
downstream modules. The only DAG parent is
`lem-a1-sections-intersection-structure-colimit`, whose planned use is preserved:
it needs the reverse-inclusion least element. Its current module
`Sheaf.AlgebraicGeometry.IntersectionStructureSections` (held by D6) does not import
this module or use its declarations, and needs no adaptation. No target statement
uses a changed definition: all definitions remain unchanged.

## Status

landed 20261023T104935-L-3466107 2026-10-23 (merge of deliver/E8/Sheaf.AlgebraicGeometry.QcOpenIntersectionSpectralPresentation)
