# AlgebraicGeometry.Etale.IsEtaleHomTranspose

## Reason

The comparison and exactness lemma need a common interface without an import cycle.
Move the original fourteen interface declarations to
`Sheaf.SixFunctors.EtaleHomComparisonModels`, publicly reexported by the original item.
Their namespaces and signatures are preserved. The definitional Hom-object
spelling below and the equivalent named normalization predicate (recorded in
`K2-etale-hom-tensor-normalization.md`) are the two definition-body changes. In this spelling the tensor-Hom adjunction sees
its actual right-adjoint object directly, avoiding expensive unfolding of `Functor.flip`.
The chosen scalar adjunction, tensor normalization, quadratic Hom-shift sign and all
four shift structures in the exactness predicate are unchanged.

## Old

```lean
def IsEtaleHomTranspose (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M) : Prop :=
  ∀ K : DerivedCategoryModule A X,
    (etaleHomTensorComparison X φ K
        (((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).obj (op K))).hom ≫
        (scalarExtension φ X).map
          ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) (X := X) K).counit.app M) =
      ((derivedTensorHomAdjunction (ModuleCat.{u + 1} B) (X := X)
          ((scalarExtension φ X).obj K)).homEquiv _ _).symm (v.app (op K))
```

All fourteen interface declarations were defined in
`Sheaf.SixFunctors.EtaleHomThickLocus`.

## New

```lean
def IsEtaleHomTranspose (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M) : Prop :=
  ∀ K : DerivedCategoryModule A X,
    (etaleHomTensorComparison X φ K
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).hom ≫
        (scalarExtension φ X).map
          ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) (X := X) K).counit.app M) =
      ((derivedTensorHomAdjunction (ModuleCat.{u + 1} B) (X := X)
          ((scalarExtension φ X).obj K)).homEquiv _ _).symm (v.app (op K))
```

The same fourteen declarations are defined in
`Sheaf.SixFunctors.EtaleHomComparisonModels`; the original module publicly imports it.
The new spelling reduces by the definition of `Functor.flip` to the old spelling.
No mathematical definition, hypothesis or conclusion changes. The definitions used by
the targets therefore retain their meanings; this is a relocation and definitional
presentation change, recorded for independent review.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed in inspected claim records | Public reexport preserves the interface; no edit required. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed in inspected claim records | Public reexport preserves the interface; no edit required. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed in inspected claim records | Public reexport preserves the interface; no edit required. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed in inspected claim records | Public reexport preserves the interface; no edit required. |
| Sheaf.Paper.EtaleGeometricBiduality | unclaimed in inspected claim records | Public reexport preserves the interface; no edit required. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed in inspected claim records | Public reexport preserves the interface; no edit required. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed in inspected claim records | Public reexport preserves the interface; no edit required. |
| Sheaf.SixFunctors.EtaleOpenTensor | unclaimed in inspected claim records | Public reexport preserves the interface; no edit required. |
| Sheaf.SixFunctors.EtaleHomThickLocus | K2 | Uses the reexported interface and the new exactness lemma. |
| Sheaf.SixFunctors.EtaleHomComparisonModels | new K2 module | Owns the identical interface. |
| Sheaf.SixFunctors.EtaleHomTransposeExact | new K2 module | Imports the common interface. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed in inspected claim records; source authored by Q74 | Uses `etaleHomTensorComparison`; public reexport preserves it, no edit required. |

The 352 transitive downstream imports were inspected with `tools/downstream.py`;
the table includes all direct users of the changed/moved declarations and selected
transitive consumers. No transitive importer needs an adaptation.
The direct consumer of the tensor comparison is `Sheaf.SixFunctors.EtaleOpenTensor`;
there is no external direct use of `IsEtaleHomTranspose`. No source-library module
is edited, no forced adaptation is included, and no target signature is changed.

## Status

landed 20261020T230801-L-612184 2026-10-20 (merge of deliver/K2/Sheaf.SixFunctors.EtaleHomThickLocus)
