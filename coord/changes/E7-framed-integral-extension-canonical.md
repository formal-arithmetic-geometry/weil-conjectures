# divisorRelativeExtension

## Reason

Use the existing relative-extension construction directly. The former duplicate characterization expressed supported one by restriction from the terminal object; the canonical characterization uses the sheafification unit at each object. Naturality identifies these sections. Keeping two choice terms caused expensive normalization whenever functoriality compared their classes. The mathematical object and all signatures are unchanged.

## Old

```lean
@[irreducible] def DivisorRelativeExtension {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
    (β : Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1) : Prop :=
  ∃ (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : T.gmSheaf ⟶ E)
    (b : E ⟶ (Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z))
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (f : (divisorFrameTorsor L).sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1}),
    (∀ V g p, @id (E.obj.obj V) (f.app V ((divisorFrameTorsor L).vadd V g p)) =
      @id (E.obj.obj V) (f.app V p) + a.hom.app V g) ∧
    (∀ V p, b.hom.app V (f.app V p) =
      ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
        (Etale.supportedIntegralConstant Z)).obj.map
          ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).from V.unop).op
          ((Etale.supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
            (Etale.supportedIntegralOne T))) ∧
    @id (E.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
      (f.app (op (Scheme.Etale.mk i.openComplement.ι)) s) = 0 ∧ β = hE.extClass

@[irreducible] def divisorRelativeExtension {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))) :
    Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1 :=
  Classical.choose (divisorRelativeExtension_existsUnique i L s)
```

## New

```lean
@[irreducible] def DivisorRelativeExtension {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
    (β : Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1) : Prop :=
  Etale.RelativeExtensionRepresents i ⟨divisorFrameTorsor L, s⟩ β

@[irreducible] def divisorRelativeExtension {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))) :
    Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1 :=
  Etale.relativeExtension i ⟨divisorFrameTorsor L, s⟩
```

The existence proof now applies `Etale.relativeExtension_existsUnique`. The naturality calculation identifying the two fibre equations is retained in the integral forget-support proof. This works for empty support and empty complement. Target statements that transitively use this definition should have their semantic review refreshed; their mathematical meaning is unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.DivisorNormalizedRealization | E7 | Same class and frame; statements unchanged. Proof uses the canonical construction. |
| Sheaf.Paper.FramedRealizationAdditive | unclaimed | Same class and frame; statements unchanged. No adaptation required. |
| Sheaf.Paper.FramedRealizationEnlarge | unclaimed | Same class and frame; statements unchanged. No adaptation required. |
| Sheaf.Paper.FramedRealizationIso | unclaimed | Same class and frame; statements unchanged. No adaptation required. |
| Sheaf.Paper.FramedRealizationProperty | unclaimed | Same class and frame; statements unchanged. No adaptation required. |
| Sheaf.Paper.FramedRealizationPullback | unclaimed | Same class and frame; statements unchanged. No adaptation required. |
| Sheaf.Paper.FramedTransport | unclaimed | Same class and frame; statements unchanged. No adaptation required. |
| Sheaf.Paper.FramedIntegralExtension | unclaimed | Existence proof uses the canonical characterization; no hypotheses change. |

## Status

landed 20261025T143145-L-959832 2026-10-25 (merge of deliver/E7/Sheaf.Paper.DivisorNormalizedRealization)
