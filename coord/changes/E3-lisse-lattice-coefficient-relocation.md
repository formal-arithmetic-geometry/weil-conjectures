# Lisse lattice coefficient declarations

## Reason

The two parts of the lattice argument need the original coefficient definitions, while the
item theorem imports those parts. Extract the definitions to avoid an import cycle. The item
publicly imports the new module. The six qualified names, signatures, definition bodies,
visibility and universe parameters are unchanged. The item theorem statement and all target
statements are unchanged. Its former public imports are now public imports of the new module,
so their entire public interface remains visible through the item.

This is a relocation of definitions, not a change of their meaning. No target statement review
is reopened by a changed definition: the definitions below are byte-for-byte identical.

## Old

In `lean/Sheaf/AlgebraicGeometry/LisseLatticeEtaleLocal.lean`:

```lean
noncomputable def lisseContinuousCommRingSheaf (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  ⟨{ obj := fun U ↦ CommRingCat.of (ULift.{u + 1} C(U.unop.left, T))
     map := fun f ↦ CommRingCat.ofHom ((continuousMapRingPresheaf X T).map f).hom
     map_id := fun _ ↦ rfl
     map_comp := fun _ _ ↦ rfl },
   Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
     (isSheaf_continuousMapRingPresheaf X T)⟩

/-- The continuous coefficient sheaf, with the canonical extension of the p-adic norm.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseFieldSheaf (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  lisseContinuousCommRingSheaf X E

/-- The integral coefficient sheaf, with the topology induced from the coefficient field.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseIntegerSheaf (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  lisseContinuousCommRingSheaf X (Padic.coefficientExtensionIntegers l E)

/-- Postcomposition with the valuation-ring inclusion is the scalar extension map.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseIntegerToField (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    lisseIntegerSheaf l E X ⟶ lisseFieldSheaf l E X :=
  letI := spectralNorm.normedField ℚ_[l] E
  ⟨{ app := fun U ↦ CommRingCat.ofHom
       ((continuousMapRingPresheafMap X (Padic.coefficientExtensionIntegers l E).subtype
         continuous_subtype_val).app U).hom
     naturality := fun _ _ _ ↦ rfl }⟩

/-- Composition with an etale arrow embeds its small pro-etale site into the ambient site.
Source: Bhatt--Scholze, Proposition 6.8.4(6), slice-site restriction
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseEtaleSiteInclusion {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    Y.ProEt ⥤ X.ProEt where
  obj V := Scheme.ProEt.mk (V.hom ≫ f)
  map {V W} a := MorphismProperty.Over.homMk a.left
    ((Category.assoc a.left W.hom f).symm.trans
      (congrArg (fun b : V.left ⟶ Y ↦ b ≫ f) a.w))

/-- The slice coefficient identification is the identity on continuous functions.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseEtaleCoefficientIdentification (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E Y)).obj ⟶
    (lisseEtaleSiteInclusion f).op ⋙
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)).obj :=
  { app := fun _ ↦ 𝟙 _
    naturality := fun _ _ _ ↦ rfl }
```

## New

In `lean/Sheaf/AlgebraicGeometry/LisseLatticeCoefficients.lean`, publicly imported by the item:

```lean
noncomputable def lisseContinuousCommRingSheaf (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  ⟨{ obj := fun U ↦ CommRingCat.of (ULift.{u + 1} C(U.unop.left, T))
     map := fun f ↦ CommRingCat.ofHom ((continuousMapRingPresheaf X T).map f).hom
     map_id := fun _ ↦ rfl
     map_comp := fun _ _ ↦ rfl },
   Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
     (isSheaf_continuousMapRingPresheaf X T)⟩

/-- The continuous coefficient sheaf, with the canonical extension of the p-adic norm.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseFieldSheaf (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  lisseContinuousCommRingSheaf X E

/-- The integral coefficient sheaf, with the topology induced from the coefficient field.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseIntegerSheaf (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  lisseContinuousCommRingSheaf X (Padic.coefficientExtensionIntegers l E)

/-- Postcomposition with the valuation-ring inclusion is the scalar extension map.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseIntegerToField (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    lisseIntegerSheaf l E X ⟶ lisseFieldSheaf l E X :=
  letI := spectralNorm.normedField ℚ_[l] E
  ⟨{ app := fun U ↦ CommRingCat.ofHom
       ((continuousMapRingPresheafMap X (Padic.coefficientExtensionIntegers l E).subtype
         continuous_subtype_val).app U).hom
     naturality := fun _ _ _ ↦ rfl }⟩

/-- Composition with an etale arrow embeds its small pro-etale site into the ambient site.
Source: Bhatt--Scholze, Proposition 6.8.4(6), slice-site restriction
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseEtaleSiteInclusion {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    Y.ProEt ⥤ X.ProEt where
  obj V := Scheme.ProEt.mk (V.hom ≫ f)
  map {V W} a := MorphismProperty.Over.homMk a.left
    ((Category.assoc a.left W.hom f).symm.trans
      (congrArg (fun b : V.left ⟶ Y ↦ b ≫ f) a.w))

/-- The slice coefficient identification is the identity on continuous functions.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-lisse-lattice-etale-local). -/
noncomputable def lisseEtaleCoefficientIdentification (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E Y)).obj ⟶
    (lisseEtaleSiteInclusion f).op ⋙
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)).obj :=
  { app := fun _ ↦ 𝟙 _
    naturality := fun _ _ _ ↦ rfl }
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal --uses <name>` was run for
all six moved names. Each is mentioned only by the item among existing modules; the eight
transitive downstream modules are also listed below. No adapted existing module is needed.
Holders are those observed when writing this record.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal` | E3 | Six definitions are reexported from the new coefficient module; theorem signature unchanged. |
| `Sheaf.Paper.ContinuousConstructibleIntegralModel` | unclaimed | Same qualified constants and definitions through the public import; no edit. |
| `Sheaf.Paper.ContinuousConstructibleIntegralSingle` | unclaimed | Same qualified constants and definitions through the public import; no edit. |
| `Sheaf.Paper.ContinuousConstructibleIntegralStratum` | C4 | Same qualified constants and definitions through the public import; no edit. |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | unclaimed | Same qualified constants and definitions through the public import; no edit. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | Same qualified constants and definitions through the public import; no edit. |
| `TargetsCheck` | unclaimed | Same qualified constants and definitions through the public import; no edit. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Same qualified constants and definitions through the public import; no edit. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Same qualified constants and definitions through the public import; no edit. |
| `Sheaf.AlgebraicGeometry.LisseLatticeCoefficients` | E3 (new) | Uses the extracted coefficients; no existing user adapted. |
| `Sheaf.AlgebraicGeometry.LisseLatticeClassSheaf` | E3 (new) | Uses the extracted coefficients; no existing user adapted. |
| `Sheaf.AlgebraicGeometry.LisseLatticeSliceTransport` | E3 (new) | Uses the extracted coefficients; no existing user adapted. |
| `Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization` | E3 (new) | Uses the extracted coefficients; no existing user adapted. |
| `Sheaf.AlgebraicGeometry.LisseLatticePresentationTransport` | E3 (new) | Generic presentation interface; no existing user adapted. |

`Sheaf.AlgebraicGeometry.IntegralLatticeCoefficientTransport` is a new E3 module using only
the existing generic lattice-pair definitions in its statement. After the returned duplicate-helper
repair, its proof imports normalization to reuse finite local freeness transport; this proof-only
import also brings in the relocated coefficient definitions internally.

## Status

landed 20261016T070240-L-770593 2026-10-16 (merge of deliver/E3/Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal)
