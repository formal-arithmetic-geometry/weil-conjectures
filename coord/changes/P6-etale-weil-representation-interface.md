# etaleLisseWeilRepresentations and etaleWeilTensorCompatibility

## Reason

The independent Hom, reconstruction, and tensor arguments need the representation
subcategory and tensor predicate in their statements. Extract the two existing
definitions to `Sheaf.Paper.EtaleWeilRepresentationData` to avoid an import cycle.
The original module publicly imports this interface and retains every old public
import. Both declaration names, universes, binders, attributes, visibility and
bodies are identical. No mathematical definition or target statement changes.
No adopted source-library module is edited.

## Old

In `Sheaf.Paper.EtaleWeilSheafEquivalence`, in the unchanged variable context:

```lean
@[reducible] def etaleLisseWeilRepresentations (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    (d : Monodromy.DegreeDatum G) (D : EtaleWeilDegreeData h t G d) :=
  ObjectProperty.FullSubcategory (fun V : Rep.{u + 1} Q G ↦
    Representation.IsLAdic l Q (ProfiniteGrp.of (Aut (fiber t))) V.V
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv Q V.V).toMonoidHom.comp
        (Representation.asGroupHom
          (V.ρ.comp (d.deg.ker.subtype.comp D.geom.toMonoidHom)))))

/-- Tensor compatibility refers to the recorded levelwise etale tensor and unit.
The two forgetful functors are monoidal, so the Weil and representation tensor
structures use those actual underlying operations.
Source: Weil II (1.1.1), (1.1.10)
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
def etaleWeilTensorCompatibility
    (e : EtaleLisseWeilSheaf l Q h ≌ etaleLisseWeilRepresentations l Q h t d D) : Prop :=
  ∃ m₀ : MonoidalCategory (LisseAlgebraicSheaf l Y Q),
    m₀.toMonoidalCategoryStruct.tensorObj = lisseAlgebraicTensor l Y Q ∧
    m₀.toMonoidalCategoryStruct.tensorUnit = lisseAlgebraicUnit l Y Q ∧
    ∃ (mW : MonoidalCategory (EtaleLisseWeilSheaf l Q h))
      (mR : MonoidalCategory (etaleLisseWeilRepresentations l Q h t d D)),
      Nonempty (@Functor.Monoidal (EtaleLisseWeilSheaf l Q h) _ mW
        (LisseAlgebraicSheaf l Y Q) _ m₀
        (Endofunctor.IsoAlgebra.forget (lisseAlgebraicAutomorphismPullback h l Q))) ∧
      Nonempty (@Functor.Monoidal (etaleLisseWeilRepresentations l Q h t d D) _ mR
        (Rep.{u + 1} Q G) _ _ (ObjectProperty.ι _)) ∧
      Nonempty (@Functor.Monoidal (EtaleLisseWeilSheaf l Q h) _ mW
        (etaleLisseWeilRepresentations l Q h t d D) _ mR e.functor)
```

## New

The exact same declarations and variable context now occur in
`Sheaf.Paper.EtaleWeilRepresentationData`:

```lean
@[reducible] def etaleLisseWeilRepresentations (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    (d : Monodromy.DegreeDatum G) (D : EtaleWeilDegreeData h t G d) :=
  ObjectProperty.FullSubcategory (fun V : Rep.{u + 1} Q G ↦
    Representation.IsLAdic l Q (ProfiniteGrp.of (Aut (fiber t))) V.V
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv Q V.V).toMonoidHom.comp
        (Representation.asGroupHom
          (V.ρ.comp (d.deg.ker.subtype.comp D.geom.toMonoidHom)))))

/-- Tensor compatibility refers to the recorded levelwise etale tensor and unit.
The two forgetful functors are monoidal, so the Weil and representation tensor
structures use those actual underlying operations.
Source: Weil II (1.1.1), (1.1.10)
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
def etaleWeilTensorCompatibility
    (e : EtaleLisseWeilSheaf l Q h ≌ etaleLisseWeilRepresentations l Q h t d D) : Prop :=
  ∃ m₀ : MonoidalCategory (LisseAlgebraicSheaf l Y Q),
    m₀.toMonoidalCategoryStruct.tensorObj = lisseAlgebraicTensor l Y Q ∧
    m₀.toMonoidalCategoryStruct.tensorUnit = lisseAlgebraicUnit l Y Q ∧
    ∃ (mW : MonoidalCategory (EtaleLisseWeilSheaf l Q h))
      (mR : MonoidalCategory (etaleLisseWeilRepresentations l Q h t d D)),
      Nonempty (@Functor.Monoidal (EtaleLisseWeilSheaf l Q h) _ mW
        (LisseAlgebraicSheaf l Y Q) _ m₀
        (Endofunctor.IsoAlgebra.forget (lisseAlgebraicAutomorphismPullback h l Q))) ∧
      Nonempty (@Functor.Monoidal (etaleLisseWeilRepresentations l Q h t d D) _ mR
        (Rep.{u + 1} Q G) _ _ (ObjectProperty.ι _)) ∧
      Nonempty (@Functor.Monoidal (EtaleLisseWeilSheaf l Q h) _ mW
        (etaleLisseWeilRepresentations l Q h t d D) _ mR e.functor)
```

The original module adds `public import Sheaf.Paper.EtaleWeilRepresentationData`.
Its theorem has the same signature and now combines full faithfulness,
essential surjectivity, abelian transfer and the actual tensor clause.
The new realization functor chooses only the Hom equivalence whose underlying
linear map is explicitly fixed on every arrow. Two such intertwiners are equal
by linear-map extensionality; hence two such Hom equivalences are equal by
function extensionality. This is a uniquely determined map, not arbitrary data
chosen from mere existence. Objects are explicitly `Rep.of etaleFundamentalRep`.

No target meaning changes under this relocation, because the definition bodies
are verbatim. The attached original node now lists only its theorem; the new
interface node attaches both relocated declarations.

## Users

`tools/downstream.py Sheaf.Paper.EtaleWeilSheafEquivalence --uses
etaleLisseWeilRepresentations etaleWeilTensorCompatibility` lists these three
transitive consumers. Neither relocated name occurs in any of their source
statements or proofs. No consumer adaptation is necessary. Their original
public import continues to expose exactly the old declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleWeilSheafEquivalence | P6 | Definitions reexported; theorem signature unchanged. |
| Sheaf.Paper.DenseOpenPiOneSurjective | not adapted | Same public imported interface. |
| Sheaf.Paper.RealSheafSections | not adapted | Same public imported interface. |
| Sheaf.Paper.WeilKernelHenselianInertia | not adapted | Same public imported interface. |

The other delivered files are new modules with their own nodes. There are no
forced adaptations and no changed existing signatures.

## Status

landed 20261021T143941-L-27799 2026-10-21 (merge of deliver/P6/Sheaf.Paper.EtaleWeilSheafEquivalence)
