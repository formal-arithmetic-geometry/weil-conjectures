# AlgebraicGeometry.VectorProjectiveCompletion.Presentation and chart definitions

## Reason

Separate the existing definitions from their theorem so local construction lemmas can import
those definitions without an import cycle. This is an ownership/import refactor only: the
seven declarations retain their exact names, universes, signatures and bodies. The original
module publicly imports the new data module, preserving the interface seen by importers.
The target statements and the mathematical meaning of their definitions are unchanged.

## Old

The following declarations were in
`lean/Sheaf/AlgebraicGeometry/VectorProjectiveCompletion.lean`:

```lean
structure Presentation (S : Scheme.{u}) (F : S.Modules) where
  algebra : S.GradedAlgebraData
  equiv (V : S.affineOpens) :
    SymmetricAlgebra Γ(S, V.1) (Γ(S, V.1) × F.val.obj (op V.1)) ≃ₐ[Γ(S, V.1)] algebra.obj V
  grade_eq (V : S.affineOpens) (n : ℕ) :
    algebra.grading V n =
      ((LinearMap.range (SymmetricAlgebra.ι Γ(S, V.1)
        (Γ(S, V.1) × F.val.obj (op V.1)))) ^ n).map (equiv V).toLinearMap
  restriction (U V : S.affineOpens) (h : U.1 ≤ V.1)
      (a : Γ(S, V.1)) (m : F.val.obj (op V.1)) :
    algebra.res h (equiv V (SymmetricAlgebra.ι _ _ (a, m))) =
      equiv U (SymmetricAlgebra.ι _ _
        (S.presheaf.map (homOfLE h).op a, F.val.map (homOfLE h).op m))

/-- The degree-one coordinate from the first summand, namely t = j(1,0).
Source: Stacks Tag 01OA (blueprint: lem-amb-vector-projective-completion). -/
def t {S : Scheme.{u}} {F : S.Modules} (P : Presentation S F) (V : S.affineOpens) :
    P.algebra.obj V :=
  P.equiv V (SymmetricAlgebra.ι _ _ (1, 0))

/-- The degree-one coordinate from a section of F, namely x(m) = j(0,m).
Source: Stacks Tag 01OA (blueprint: lem-amb-vector-projective-completion). -/
def x {S : Scheme.{u}} {F : S.Modules} (P : Presentation S F) (V : S.affineOpens)
    (m : F.val.obj (op V.1)) : P.algebra.obj V :=
  P.equiv V (SymmetricAlgebra.ι _ _ (0, m))

/-- D_+(t), formed from the canonical local Proj opens, over the affine basis of S.
Source: Stacks Tags 01OA and 01NG (blueprint: lem-amb-vector-projective-completion). -/
def chartOpen {S : Scheme.{u}} {F : S.Modules} (P : Presentation S F) :
    P.algebra.relProj.Opens :=
  ⨆ V : S.affineOpens,
    (P.algebra.relProjι V).opensFunctor.obj (Proj.basicOpen (P.algebra.grading V) (t P V))

/-- The whole affine open V, viewed as an affine open of its own scheme.
Source: Stacks Tag 01OA (blueprint: lem-amb-vector-projective-completion). -/
def affineTop {S : Scheme.{u}} (V : S.affineOpens) : V.1.toScheme.affineOpens :=
  ⟨⊤, isAffineOpen_top V.1.toScheme⟩

/-- The canonical local Proj embedding into the recorded relative projective space
on an affine base. Its charts are RelativeProjectiveSpace.localChart.
Source: Stacks Tags 01OA and 01NG (blueprint: lem-amb-vector-projective-completion). -/
def projectiveChart {S : Scheme.{u}} (V : S.affineOpens) (d : ℕ) :
    (RelativeProjectiveSpace.algebra V.1.toScheme d).localProj (affineTop V) ⟶
      RelativeProjectiveSpace.scheme V.1.toScheme d :=
  ((RelativeProjectiveSpace.construction V.1.toScheme d).restrictionIso (affineTop V)).inv ≫
    (RelativeProjectiveSpace.π V.1.toScheme d ⁻¹ᵁ ⊤).ι

/-- The local map from Spec Sym(F(V)) to the completion, induced by dehomogenization,
then the recorded homogeneous-localization Proj chart and the relative Proj embedding.
Source: Stacks Tag 01NG (blueprint: lem-amb-vector-projective-completion). -/
def chartMap {S : Scheme.{u}} {F : S.Modules} (P : Presentation S F)
    (ht : ∀ V : S.affineOpens, t P V ∈ P.algebra.grading V 1)
    (a : ∀ V : S.affineOpens, SymmetricAlgebraSheaf.sections F (op V.1) ≃+*
      HomogeneousLocalization.Away (P.algebra.grading V) (t P V))
    (V : S.affineOpens) :
    Spec (.of (SymmetricAlgebraSheaf.sections F (op V.1))) ⟶ P.algebra.relProj :=
  Spec.map (CommRingCat.ofHom (a V).symm.toRingHom) ≫
    Proj.awayι (P.algebra.grading V) (t P V) (ht V) Nat.one_pos ≫
      P.algebra.relProjι V
```

## New

The exact declarations above now occur in
`lean/Sheaf/AlgebraicGeometry/VectorProjectiveCompletionData.lean`.
The original module has `public import Sheaf.AlgebraicGeometry.VectorProjectiveCompletionData`.
No declaration body or signature changes.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.VectorProjectiveCompletion --uses
Presentation t x chartOpen affineTop projectiveChart chartMap exists_projective_completion`
initially reported zero downstream modules on 2026-10-21. A consumer landed while this
packet was being checked: `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation`.
It imports the original module at line 11, and contains no direct occurrence of any moved
definition or of `exists_projective_completion`. The original public import of the data
module preserves all those declarations and their original public imports transitively.
No consumer edit is necessary. Unfinished DAG parents retain their dependencies and
original theorem interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed; landed Q69 module | Existing private import resolves the unchanged interface through the data module; no edit. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletion | H1 | Definitions supplied by public import; theorem statement unchanged. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletionData | new, H1 | Exact moved definitions. |
| Sheaf.AlgebraicGeometry.VectorProjectivePresentation | new, H1 | Imports the definitions to construct a presentation. |
| Sheaf.AlgebraicGeometry.VectorProjectiveDehomogenization | new, H1 | Imports the definitions for affine charts. |
| Sheaf.AlgebraicGeometry.VectorProjectiveFrameModel | new, H1 | Imports the definitions for frame charts. |

No source-library declaration was edited. No other group's module requires adaptation.
There is no definition change requiring a renewed target-meaning review.

## Status

landed 20261021T154030-L-2769114 2026-10-21 (merge of deliver/H1/Sheaf.AlgebraicGeometry.VectorProjectiveCompletion)
