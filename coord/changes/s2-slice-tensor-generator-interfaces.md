# SheafOfModules.SliceTensorGenerator generator interfaces

## Reason

Extract the existing scalar-extension and normalization interfaces to
`Sheaf.CategoryTheory.SliceTensorGeneratorInterfaces`, to let the scalar,
tensor-transport and tower-assembly lemmas be independent modules without
an import cycle. This is an argument decomposition, not a compilation-time
workaround. No existing definition body, declaration name, signature,
attribute or target meaning changes. The original module publicly imports
the extracted module, preserving its existing exported interface.

## Old

The following declarations were in `SliceTensorGeneratorCoherence`:

```lean
/-- Package the existing scalar-extension objects and maps as their functor.
Source: Stacks 03EK (blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
def extend {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) :
    Modules.{c, v, r} R ⥤ Modules.{c, v, r} S where
  obj M := changeOfRingsOfUniverses.{v, c, max c v r, max c v r} (J := J) a M
  map f := changeOfRingsHomOfUniverses.{v, c, max c v r, max c v r} (J := J) a _ f
  map_id M := scalarExtension_map_id a M
  map_comp f g := scalarExtension_map_comp a f g

/-- Identify the actual underlying tensor with scalar extension followed by restriction.
Source: Stacks 03EK and 03D7
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
abbrev TensorLift (R : Sheaf J CommRingCat.{max c v r}) (A : Under R) :=
  MonoidalCategory.tensorRight (algebraModule.{c, v, r} R A) ≅
    extend.{c, v, r} A.hom ⋙ scalars.{c, v, r} R A

/-- The identification keeps the original scalar tensor and its sheafification unit.
Source: Stacks 03EK and 03CY
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
def TensorLiftNormalized (R : Sheaf J CommRingCat.{max c v r}) (A : Under R)
    (t : TensorLift.{c, v, r} R A) : Prop :=
  ∀ (M : Modules.{c, v, r} R) (W : Cᵒᵖ) (m : M.val.obj W)
    (s : A.right.obj.obj W),
    (t.hom.app M).val.app W (SheafOfModules.LocalizedStrictTensor.pure.{c, v, r} R M _ W m s) =
      scalarExtensionSection.{c, v, max c v r, max c v r} A.hom M W s m

variable (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The scalar-linear comparison uses actual scalar extension on both sides.
Source: Stacks 0E8I and 03EK
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
abbrev LinearComparison (A : Under R) :=
  localizedSystemExtension.{c, v, r} R V ⋙ extend.{c, v, r} A.hom ≅
    extend.{max c v, v, r} ((sliceAlgebras.{c, v, r} R V).obj A).hom ⋙
      localizedSystemExtension.{c, v, r} A.right V

/-- Normalization on actual direct-sum and scalar tensor sheafification units.
Scalar extension writes the scalar first: `s ⊗ m` represents the paper's `m ⊗ s`.
Source: Stacks 03DI, 03CY, 03EK and 0E8I
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
def LinearNormalized (A : Under R) (e : LinearComparison.{c, v, r} R V A) : Prop :=
  ∀ (M : Modules.{max c v, v, r} (R.over V)) (W : C) (a : W ⟶ V)
    (m : M.val.obj (op (Over.mk a))) (s : A.right.obj.obj (op W)),
    (e.hom.app M).val.app (op W)
      (scalarExtensionSection.{c, v, max c v r, max c v r} A.hom _ (op W) s
        (extensionSection.{c, v, r} R V M W a m)) =
      extensionSection.{c, v, r} A.right V _ W a
        (scalarExtensionSection.{max c v, v, max c v r, max c v r}
          ((sliceAlgebras.{c, v, r} R V).obj A).hom
          M (op (Over.mk a)) s m)

```

## New

Exactly the declarations above, verbatim (including variable declarations),
in `Sheaf.CategoryTheory.SliceTensorGeneratorInterfaces`. The original module
adds `public import Sheaf.CategoryTheory.SliceTensorGeneratorInterfaces`.
Its `Coherence`, `Coherence.onComplexes` and `coherence_exists` signatures
remain verbatim. The new definition node records the moved declarations;
the parent node retains its full mathematical statement and statement dependencies.
All original public imports remain exported through the extracted module.
Only redundant private imports of PreservesSheafification, LocallyBijective
and LocallySurjective are removed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.LocalizedStrictTensorDescent | unclaimed | Same exported names, signatures and bodies; no adaptation. |
| Sheaf.Algebra.Homology.OpenTensorNormalizedComparison | unclaimed | Same exported names, signatures and bodies; no adaptation. |
| Sheaf.Algebra.Homology.OpenTensorScalarUnitAugmentation | unclaimed | Same exported names, signatures and bodies; no adaptation. |
| Sheaf.Algebra.Homology.OpenTensorScalarUnitData | unclaimed | Same exported names, signatures and bodies; no adaptation. |
| Sheaf.Algebra.Homology.OpenTensorScalarUnitPairing | unclaimed | Same exported names, signatures and bodies; no adaptation. |
| Sheaf.Algebra.Homology.OpenTotalTensorCoefficientCoherence | unclaimed | Same exported names, signatures and bodies; no adaptation. |
| Sheaf.Algebra.Homology.OpenTotalTensorCoefficientData | unclaimed | Same exported names, signatures and bodies; no adaptation. |
| Sheaf.Algebra.Homology.OpenTotalTensorCoefficientInterchange | X5 | Same exported names, signatures and bodies; no adaptation. |
| Sheaf.Algebra.Homology.OpenTotalTensorCoefficientNormalization | unclaimed | Same exported names, signatures and bodies; no adaptation. |
| Sheaf.Paper.CompletedSupportIntermediateTower | unclaimed | Same exported names, signatures and bodies; no adaptation. |
| Sheaf.CategoryTheory.SliceTensorGeneratorCoherence | S2 | Same exported names, signatures and bodies; no adaptation. |

The three direct importers are checked against the extracted interface by
single-file compilation. The transitive consumers see the identical exports.
No adopted `WeilConjectures` declaration is edited, and no target is restated.

## Status

landed 20261025T101330-L-3683306 2026-10-25 (merge of deliver/S2/Sheaf.CategoryTheory.SliceTensorGeneratorCoherence)
