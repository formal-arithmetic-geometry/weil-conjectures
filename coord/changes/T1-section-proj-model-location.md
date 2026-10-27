# AlgebraicGeometry.AlgebraicSpace.SectionProjModel

## Reason

Move the existing adapter structure to its own definition module so the new affine
presentation and comparison lemmas can depend on it without an import cycle. The item
publicly imports this definition module, preserving the name, signature, fields and
visibility of the structure and of section_proj_etale_embedding. This is a declaration
relocation, with no mathematical definition or target-statement change.

## Old

In lean/Sheaf/TraceFormula/SectionProjEtaleEmbedding.lean:

```lean
structure SectionProjModel {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (f : F ⟶ yoneda.obj T) (L : TestLineFamily F) where
  sections : SpaceSectionAlgebra f L
  affine : T.left.GradedAlgebraData
  degreeIso (V : T.left.affineOpens) (n : ℕ) :
    Γ(sections.degree n, V.1) ≃ₗ[Γ(T.left, V.1)] affine.grading V n
  mul (V : T.left.affineOpens) (m n : ℕ)
      (a : Γ(sections.degree m, V.1)) (b : Γ(sections.degree n, V.1)) :
    (degreeIso V (m + n) (sections.graded.mul m n V.1 a b) : affine.obj V) =
      (degreeIso V m a : affine.obj V) * (degreeIso V n b : affine.obj V)
  unit (V : T.left.affineOpens) (r : Γ(T.left, V.1)) :
    (degreeIso V 0 (sections.graded.unit.val.app (op V.1) r) : affine.obj V) =
      algebraMap Γ(T.left, V.1) (affine.obj V) r
  restriction (V V' : T.left.affineOpens) (j : V ≤ V') (n : ℕ)
      (a : Γ(sections.degree n, V'.1)) :
    (degreeIso V n ((sections.degree n).val.map (homOfLE j).op a) : affine.obj V) =
      affine.res j (degreeIso V' n a)
  evaluation : GradedLineMap f affine L
  evaluation_eq (W : SchemeTests F) (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1)
      (n : ℕ) (a : Γ(sections.degree n, V.1)) :
    evaluation.component W V h n (degreeIso V n a) = sections.image V.1 W h n a
```

## New

In lean/Sheaf/TraceFormula/SectionProjModel.lean, publicly imported by the item:

```lean
structure SectionProjModel {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (f : F ⟶ yoneda.obj T) (L : TestLineFamily F) where
  sections : SpaceSectionAlgebra f L
  affine : T.left.GradedAlgebraData
  degreeIso (V : T.left.affineOpens) (n : ℕ) :
    Γ(sections.degree n, V.1) ≃ₗ[Γ(T.left, V.1)] affine.grading V n
  mul (V : T.left.affineOpens) (m n : ℕ)
      (a : Γ(sections.degree m, V.1)) (b : Γ(sections.degree n, V.1)) :
    (degreeIso V (m + n) (sections.graded.mul m n V.1 a b) : affine.obj V) =
      (degreeIso V m a : affine.obj V) * (degreeIso V n b : affine.obj V)
  unit (V : T.left.affineOpens) (r : Γ(T.left, V.1)) :
    (degreeIso V 0 (sections.graded.unit.val.app (op V.1) r) : affine.obj V) =
      algebraMap Γ(T.left, V.1) (affine.obj V) r
  restriction (V V' : T.left.affineOpens) (j : V ≤ V') (n : ℕ)
      (a : Γ(sections.degree n, V'.1)) :
    (degreeIso V n ((sections.degree n).val.map (homOfLE j).op a) : affine.obj V) =
      affine.res j (degreeIso V' n a)
  evaluation : GradedLineMap f affine L
  evaluation_eq (W : SchemeTests F) (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1)
      (n : ℕ) (a : Γ(sections.degree n, V.1)) :
    evaluation.component W V h n (degreeIso V n a) = sections.image V.1 W h n a
```

The two structure declarations above are byte-identical. Its docstring now points to
its own definition node. The parent node's declaration list relinquishes the structure
to that node, and adds that definition as a statement dependency. The theorem signature
is unchanged. The old public import of SpaceLineModuleProjMap is removed: the statement
needs only the input types already exported by SectionProjModel, and the proved descent
module privately imports the canonical-map theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.SectionProjEtaleEmbedding | T1 | Publicly reexports the identical structure and uses the new proof lemmas. |

Source search found no current Lean importers of the item, and no other existing module
mentions SectionProjModel. The unfinished DAG parent lem-trf-algebraic-space-ample-local
still depends on the unchanged theorem; its dependency and its route are preserved.
New modules of this delivery use the structure at its new location. No other existing
module or node is changed. There are therefore no direct importers requiring adaptation
or compilation against the relocation. All delivery modules are checked together through
lcompile.py --all before delivery.

## Status

landed 20261026T082953-L-2244986 2026-10-26 (merge of deliver/T1/Sheaf.TraceFormula.SectionProjEtaleEmbedding)
