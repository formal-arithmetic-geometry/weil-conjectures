# SheafOfModules.ScalarTowerTensorModel.AugmentationCoordinates

## Reason

The static preflight treats added namespace, variable, omit/include and open commands as an
interface change. This record documents their scope for independent review. Both original
public theorem signatures, every public definition and all public imports are unchanged.
The earlier packet also had a whitespace-only difference after the tensor notation's comma;
that definition is now restored byte for byte from the shared source.

The additional private helpers lie either outside `SheafOfModules`, within the new namespace
`SheafOfModules.ScalarComparisonProof`, or within the original namespace. Each declaration is
private and proved. The new namespace closes before the original public structure. Its
variables and `include hq` are local to that namespace. Single-declaration `omit ... in`
commands omit unused helper assumptions. `open ScalarComparisonProof` exposes only its private
helper names for proofs in this file. No global instance or attribute is added.
No mathematical definition changes and no target statement needs semantic revision.

## Old

The original public definition is:

```lean
def AugmentationCoordinates (β : M.F ⟶ M.G) : Prop :=
  (∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ) (i : ℤ),
    (β.app P).f (i + 1) ≫
      (roosχ ((M.V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) i).hom ≫
        biprod.fst = 0) ∧
  ∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ)
    (i : ℤ) (n : ℕ) (U : Cᵒᵖ) (x : (P.X i).val.obj U) (s : S.obj.obj U),
    ((((M.eE (P.X i)).inv ≫
        (β.app P ≫ roosEval
          ((M.V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) n).f i ≫
        (M.eV (P.X i) n).hom).val.app U)
      ((toSheafify J (changeOfRingsPresheaf φ (P.X i)).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) =
      (toSheafify J (changeOfRingsPresheaf (φ ≫ c n) (P.X i)).presheaf).app U
        (((c n).hom.app U s) ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] x)
```

The file had no namespace `SheafOfModules.ScalarComparisonProof`, no corresponding
`open ScalarComparisonProof`, and none of the helper-local variable/omit/include commands.

## New

The public definition above remains byte for byte identical. The added scope commands are:

```lean
namespace SheafOfModules.ScalarComparisonProof
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
variable {R S T : Sheaf J CommRingCat.{u}}
  (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T) (hq : f ≫ q = g)
  (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
-- Fully proved private helpers and their local include/omit commands.
end SheafOfModules.ScalarComparisonProof
-- Later, in the original namespace:
open ScalarComparisonProof
```

Additional `omit ... in` commands immediately precede individual private helper declarations.
They have no effect on any public declaration. All changes to original theorem bodies are
proofs replacing the two original sorries.

## Users

`tools/downstream.py Sheaf.Paper.QuotientScalarComparisonDescent --uses
SheafOfModules.ScalarTowerTensorModel.AugmentationCoordinates` reports zero downstream
modules and the item itself as the sole direct declaration user.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.QuotientScalarComparisonDescent` | C6 (dispatched item) | Both holes closed; unchanged public definitions and signatures. |

No consumer adaptation is required. No module other than the item is delivered.

## Status

landed 20261021T111015-L-3893409 2026-10-21 (merge of deliver/C6/Sheaf.Paper.QuotientScalarComparisonDescent)
