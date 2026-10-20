# Retire Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjectiveCore

## Reason

Complete the listed retirement repair in coord/retire-items.tsv under the human's
2026-10-20 twin-retirement instruction. The upstream twin has the identical
closed-immersion theorem and complete proof. The extra surjectivity lemma is
unused and has the proved upstream equivalent
AlgebraicGeometry.surjective_of_isClosedImmersion_SpecMap in
WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateModel.

The current shared tree has already retired the historical consumer
Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjective. Its upstream twin
imports the upstream core and uses the upstream surjectivity lemma. Searches over
both Lean roots and downstream.py find no remaining importer or external
reference to either declaration of the Sheaf copy.

## Old

The retired module contains these two proved declarations:

```lean
theorem Scheme.isClosedImmersion_specMap_tensor_functionField
    (X : Scheme.{u}) [IsIntegral X]
    [hsep : X.IsSeparated]
    (U : X.Opens) (hU : IsAffineOpen U) [hUn : Nonempty U]
    (x : X) (hx : x ∉ U)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    let A : Type u := Γ(X, U)
    let B : Type u := X.presheaf.stalk x
    let K : Type u := X.functionField
    let φ : TensorProduct ℤ A B →ₐ[ℤ] K :=
      Algebra.TensorProduct.lift
        (X.germToFunctionField U).hom.toIntAlgHom
        (algebraMap B K).toIntAlgHom
        (fun _ _ => Commute.all _ _)
    IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))
```

```lean
theorem surjective_of_isClosedImmersion_specMap
    (R S : CommRingCat.{u}) (f : R ⟶ S)
    [IsClosedImmersion (Spec.map f)] : Function.Surjective f
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/SeparatedAffineFunctionFieldSurjectiveCore.lean
through deleted.txt. Point the existing node
lem-sc-separated-affine-function-field-surjective-core at
WeilConjectures.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjectiveCore and
the same declaration, AlgebraicGeometry.Scheme.isClosedImmersion_specMap_tensor_functionField.
Its statement and proof dependencies are unchanged. No upstream source is edited.
The unused lowercase-specMap helper is removed with the duplicate; its upstream
replacement has implicit ring binders and otherwise the same proposition.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjectiveCore | H4 | Withdraw the duplicate, which has no current importers or external declaration users. |

Both downstream.py --uses queries returned only the declaration's own module and
zero downstream modules. The historical consumer listed in the retirement table
is already absent. Its upstream twin needs no adaptation: it imports the upstream
core and applies surjective_of_isClosedImmersion_SpecMap. No target, definition,
unit route, or surviving public declaration changes meaning.

## Status

landed 20261020T135411-L-1819460 2026-10-20 (merge of deliver/H4/Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjectiveCore)
