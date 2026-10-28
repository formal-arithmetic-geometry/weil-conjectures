# AlgebraicGeometry.ProEtale.siteHomTensorParameterShift, siteHomSourceShift, siteHomOppositeSourceShift, siteHomSignedSourceComponent

## Reason

Repair of the returned delivery at `c1773f63b5e`: this record is delivered at
`coord/changes/P7-native-hom-source-shift-data.md`. The stage-3 landing tool names a
reviewer override for this path `P7-native-hom-source-shift-data.change.md`, as specified
by its change-record mapping. The failed landing supplied
`P7-native-hom-source-shift-data.md` as the override basename; that basename does not map
to a delivery file. The record is included directly in this repaired packet. If it
needs a further reviewer edit, the override must use the `.change.md` basename above.
This corrects the packet's handoff instructions without changing the accepted Lean
argument or its DAG records.

The all-integer coherence proof is reduced to a degree-one raw recurrence. To state that
strictly smaller lemma without an import cycle, relocate the four explicit map definitions
from NativeHomSignedShiftLaws into NativeHomSourceShiftData and publicly import the latter
from the original module. This is solely a relocation: all four names, signatures, bodies,
visibility and irreducibility attributes remain identical. The assigned theorem's signature
also remains identical. No target or definition meaning changes.

## Old

In `Sheaf.CategoryTheory.NativeHomSignedShiftLaws`:

```lean
section Shift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- The existing tensor shift in its parameter, assembled as a natural isomorphism.
Source: Stacks 08JC, total-tensor signs
(blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomTensorParameterShift (K : D) (n : ℤ) :
    tensorLeft (K⟦n⟧) ≅ tensorLeft K ⋙ shiftFunctor D n :=
  NatIso.ofComponents (fun M ↦ (((curriedTensor D).flip.obj M).commShiftIso n).app K)
    (fun f ↦ (NatTrans.shift_app_comm ((curriedTensor D).flip.map f) n K).symm)

/-- The canonical source-Hom shift, as the right-adjoint mate of total-tensor shift.
This is the fixed-coefficient counterpart of the recorded ringed source shift, with
orientation H(K[n],-) → H(K,-)[-n]. Its opposite exact structure includes the correction
(-1)^(n(n+1)/2), prescribed below, rather than treating the raw shifts as coherent.
Source: Stacks 0A8X, 08JC (blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomSourceShift (K : D) (n : ℤ) :
    ihom (K⟦n⟧) ≅ ihom K ⋙ shiftFunctor D (-n) :=
  (ihom.adjunction (K⟦n⟧)).rightAdjointUniq
    (((shiftEquiv D n).toAdjunction.comp (ihom.adjunction K)).ofNatIsoLeft
      ((tensorLeft K).commShiftIso n ≪≫ (siteHomTensorParameterShift K n).symm))
/-- The same canonical source shift with the opposite-category integer parameter.
The equality transport records -(-n)=n explicitly. Source: Stacks 08JC
(blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomOppositeSourceShift (K : D) (n : ℤ) :
    ihom (K⟦-n⟧) ≅ ihom K ⋙ shiftFunctor D n :=
  siteHomSourceShift K (-n) ≪≫
    Functor.isoWhiskerLeft (ihom K) (eqToIso (congrArg (shiftFunctor D) (neg_neg n)))

end Shift

section SignedShift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- The prescribed signed source-Hom map for the triangulated opposite shift.
Source: Stacks Project, Tag 08JC
(blueprint: lem-sf-native-hom-signed-shift-laws). -/
def siteHomSignedSourceComponent (M : D) (n : ℤ) (X : Dᵒᵖ) :
    (MonoidalClosed.internalHom.flip.obj M).obj (X⟦n⟧) ⟶
      ((MonoidalClosed.internalHom.flip.obj M).obj X)⟦n⟧ :=
  (n * (n + 1) / 2).negOnePow • (siteHomOppositeSourceShift X.unop n).hom.app M

end SignedShift
```

## New

The exact same declarations are in `Sheaf.CategoryTheory.NativeHomSourceShiftData`:

```lean
section Shift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- The existing tensor shift in its parameter, assembled as a natural isomorphism.
Source: Stacks 08JC, total-tensor signs
(blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomTensorParameterShift (K : D) (n : ℤ) :
    tensorLeft (K⟦n⟧) ≅ tensorLeft K ⋙ shiftFunctor D n :=
  NatIso.ofComponents (fun M ↦ (((curriedTensor D).flip.obj M).commShiftIso n).app K)
    (fun f ↦ (NatTrans.shift_app_comm ((curriedTensor D).flip.map f) n K).symm)

/-- The canonical source-Hom shift, as the right-adjoint mate of total-tensor shift.
This is the fixed-coefficient counterpart of the recorded ringed source shift, with
orientation H(K[n],-) → H(K,-)[-n]. Its opposite exact structure includes the correction
(-1)^(n(n+1)/2), prescribed below, rather than treating the raw shifts as coherent.
Source: Stacks 0A8X, 08JC (blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomSourceShift (K : D) (n : ℤ) :
    ihom (K⟦n⟧) ≅ ihom K ⋙ shiftFunctor D (-n) :=
  (ihom.adjunction (K⟦n⟧)).rightAdjointUniq
    (((shiftEquiv D n).toAdjunction.comp (ihom.adjunction K)).ofNatIsoLeft
      ((tensorLeft K).commShiftIso n ≪≫ (siteHomTensorParameterShift K n).symm))
/-- The same canonical source shift with the opposite-category integer parameter.
The equality transport records -(-n)=n explicitly. Source: Stacks 08JC
(blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomOppositeSourceShift (K : D) (n : ℤ) :
    ihom (K⟦-n⟧) ≅ ihom K ⋙ shiftFunctor D n :=
  siteHomSourceShift K (-n) ≪≫
    Functor.isoWhiskerLeft (ihom K) (eqToIso (congrArg (shiftFunctor D) (neg_neg n)))

end Shift

section SignedShift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- The prescribed signed source-Hom map for the triangulated opposite shift.
Source: Stacks Project, Tag 08JC
(blueprint: lem-sf-native-hom-signed-shift-laws). -/
def siteHomSignedSourceComponent (M : D) (n : ℤ) (X : Dᵒᵖ) :
    (MonoidalClosed.internalHom.flip.obj M).obj (X⟦n⟧) ⟶
      ((MonoidalClosed.internalHom.flip.obj M).obj X)⟦n⟧ :=
  (n * (n + 1) / 2).negOnePow • (siteHomOppositeSourceShift X.unop n).hom.app M

end SignedShift
```

The original module now begins with:

```lean
public import Sheaf.CategoryTheory.NativeHomSourceShiftData
import Sheaf.CategoryTheory.NativeHomSourceShiftSuccessor
```

The new definition node owns the four relocated declaration attachments. The original
node retains the original theorem attachment and records its proved induction argument.
No existing module besides the item is edited. Both direct importers compiled
against the complete sandbox without changes: NativeHomLocalizedConeBoundary (3.2 seconds)
and NativeDerivedHomSignedExact (6.3 seconds). Their unchanged validation copies were removed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.NativeHomSignedShiftLaws | P7 | Original theorem signature; definitions publicly reexported |
| Sheaf.CategoryTheory.NativeDerivedHomSignedExact | unclaimed in shared snapshot | Direct importer; identical definitions and public names |
| Sheaf.CategoryTheory.NativeHomLocalizedConeBoundary | P6 | Direct importer; identical signed component |
| Sheaf.CategoryTheory.ExactDerivedHomComparisonShift | unclaimed in shared snapshot | Identical source-shift definitions through public imports |
| Sheaf.AlgebraicGeometry.SiteHomComparisonThick | unclaimed in shared snapshot | Identical opposite source-shift definition through public imports |

These are all modules mentioning any moved name in `tools/downstream.py --uses`, plus
both direct importers. Other transitive importers retain the same public declarations.

## Status

landed 20261028T020631-L-2532616 2026-10-28 (merge of deliver/P7/Sheaf.CategoryTheory.NativeHomSignedShiftLaws)
