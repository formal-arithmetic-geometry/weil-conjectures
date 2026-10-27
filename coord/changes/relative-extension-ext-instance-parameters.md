# AlgebraicGeometry.Etale.RelativeExtensionComparisonNormalization and companions

## Reason

Profiling showed that repeatedly synthesizing the expanded `HasExt` predicate for
etale sheaves made the module exceed the compile limit. Passing this already available
proposition as a typeclass parameter avoids repeated large instance terms. An actual
truncated header check dropped from roughly 33 seconds to 14 seconds, with kernel
checking below one second. A private cached `HasWeakSheafify` proof reduces repeated
sheafification search without changing any definition.

`HasExt` is already a theorem for these Grothendieck abelian sheaf categories, so this
introduces no mathematical restriction. Its proofs are propositionally irrelevant.
No target declaration changes, and the uniquely characterized data constructions keep
their bodies. Declarations with no Ext expression keep their original signatures.


The all-degree normalization is represented by a one-field Prop structure whose
`onCocycle` field is exactly the former universal equation. Its constructor and
projection give the equivalence in every degree, including zero and empty support.
The chosen comparison retains the same uniquely normalized characterization.
The enlargement restriction has its two Etale objects explicitly typed, and the
complex has its definitionally identical relative-complex arrow type. The enlargement
homology map uses the explicit `.hom` projection of the same additive map.

Repair of returned delivery `31cb6da8e2a` (reviewer C-31cb6): the mathematics passed,
but the reviewer correction was named `relative-extension-ext-instance-parameters.md`.
`tools/batch_land.py` requires reviewer corrections for this record to be named
`relative-extension-ext-instance-parameters.change.md`. This delivery includes the
record at `coord/changes/relative-extension-ext-instance-parameters.md` as usual.
The old/new excerpts below now give all fourteen changed public declarations
verbatim, including the full changed definitions and the enlargement square.
No launcher or landing tool is changed.

## Old

### `AlgebraicGeometry.Etale.RelativeExtensionRepresents`

```lean
def RelativeExtensionRepresents {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z)) G 1) : Prop:=
  ∃ (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ E)
    (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z))
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (f : P.1.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1}),
    (∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      @id (E.obj.obj V) (f.app V (P.1.vadd V g t)) =
        @id (E.obj.obj V) (f.app V t) + a.hom.app V g) ∧
    (∀ (V : T.Etaleᵒᵖ) (t : P.1.sheaf.obj.obj V),
      b.hom.app V (f.app V t) = (supportedIntegralUnit i).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩)) ∧
    @id (E.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
      (f.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2) = 0 ∧ β = hE.extClass
```

### `AlgebraicGeometry.Etale.relativeExtension_existsUnique`

```lean
theorem relativeExtension_existsUnique {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    ∃! β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z)) G 1, RelativeExtensionRepresents i P β
```

### `AlgebraicGeometry.Etale.relativeExtension`

```lean
def relativeExtension {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G 1:=
  Classical.choose (relativeExtension_existsUnique i P)
```

### `AlgebraicGeometry.Etale.RelativeExtensionComparisonNormalization`

```lean
def RelativeExtensionComparisonNormalization {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (e : ∀ q : ℕ, Ext.{u + 1}
      ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G q ≃+
        relativeCohomology T (Scheme.Etale.mk i.openComplement.ι) I q) : Prop:=
  ∀ (q : ℕ)
    (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z) ⟶
      I.cocomplex.X q) (hk : k ≫ I.cocomplex.d q (q + 1) = 0)
    (z : (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
      I.cocomplex).cycles (q : ℤ)),
    (relativeForgetComplex T (Scheme.Etale.mk i.openComplement.ι) I.cocomplex).f q
      ((relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        I.cocomplex).iCycles q z) =
      (HomologicalComplex.extendXIso
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex) ComplexShape.embeddingUpNat (rfl : (q : ℤ) = q)).inv
          (k.hom.app (op (Scheme.Etale.mk (𝟙 T)))
            ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
              (supportedIntegralOne T))) →
    (((CochainComplex.mappingCone (relativeSectionRestriction T
        (Scheme.Etale.mk i.openComplement.ι) I.cocomplex)).shiftFunctorObjXIso
        (-1) (q : ℤ) ((q : ℤ) + -1) rfl).hom ≫
      HomologicalComplex.homotopyCofiber.sndX
        (relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) I.cocomplex)
        ((q : ℤ) + -1))
      ((relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        I.cocomplex).iCycles q z) = 0 →
    e q (I.extMk k (q + 1) rfl hk) =
      (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        I.cocomplex).homologyπ q z
```

### `AlgebraicGeometry.Etale.relativeExtensionComparison_existsUnique`

```lean
theorem relativeExtensionComparison_existsUnique {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) :
    ∃! e : ∀ q : ℕ, Ext.{u + 1}
      ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G q ≃+
        relativeCohomology T (Scheme.Etale.mk i.openComplement.ι) I q,
      RelativeExtensionComparisonNormalization i G I e
```

### `AlgebraicGeometry.Etale.relativeExtensionComparison`

```lean
def relativeExtensionComparison {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (q : ℕ) : Ext.{u + 1}
      ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G q ≃+
        relativeCohomology T (Scheme.Etale.mk i.openComplement.ι) I q:=
  Classical.choose (relativeExtensionComparison_existsUnique i G I) q
```

### `AlgebraicGeometry.Etale.relative_extension_cohomology_normalization`

```lean
theorem relative_extension_cohomology_normalization {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    relativeExtensionComparison i G I 1 (relativeExtension i P) =
      -relativeTorsorEquiv T (Scheme.Etale.mk i.openComplement.ι) I (Quotient.mk _ P)
```

### `AlgebraicGeometry.Etale.relative_extension_coefficient`

```lean
theorem relative_extension_coefficient {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] {G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : G ⟶ G') (I : InjectiveResolution G) (J : InjectiveResolution G') (a : I.Hom J f)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (Q : Sheaf.Torsor G') (σ : P.1.sheaf.obj ⟶ Q.sheaf.obj)
    (hσ : ∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      σ.app V (P.1.vadd V g t) = Q.vadd V (f.hom.app V g) (σ.app V t)) :
    (relativeExtension i P).comp (Ext.mk₀ f) (add_zero 1) =
      relativeExtension i ⟨Q, σ.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2⟩ ∧
    homologyMap (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) a.hom) 1
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      relativeExtensionComparison i G' J 1
        (relativeExtension i ⟨Q, σ.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2⟩)
```

### `AlgebraicGeometry.Etale.relativeExtensionPullback`

```lean
def relativeExtensionPullback {T Z T' Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (h : T' ⟶ T) [Etale h] (w : Z' ⟶ Z) (sq : IsPullback w i' i h)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
    (β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z)) G 1) :
    Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i').obj (supportedIntegralConstant Z')) G' 1:=
  letI := relativeExtensionExchange_isIso i i' h w sq
  ((Ext.mk₀ (inv (relativeExtensionExchange i i' h w sq.toCommSq))).comp
    (β.mapExactFunctor (upperStar AddCommGrpCat.{u + 1} h)) (zero_add 1)).comp
      (Ext.mk₀ (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).homEquiv _ _).symm f))
      (add_zero 1)
```

### `AlgebraicGeometry.Etale.relative_extension_pullback`

```lean
theorem relative_extension_pullback {T Z T' Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (h : T' ⟶ T) [Etale h] (w : Z' ⟶ Z) (sq : IsPullback w i' i h)
    (hW : i'.openComplement = h ⁻¹ᵁ i.openComplement)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
    (I : InjectiveResolution G) (J : InjectiveResolution G')
    (a : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (ha : I.ι.f 0 ≫ a.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0))
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (Q : Sheaf.Torsor G')
    (b : P.1.sheaf.obj ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj)
    (hb : ∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      b.app V (P.1.vadd V g t) =
        Q.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj V.unop))
          (f.hom.app V g) (b.app V t)) :
    relativeExtensionPullback i i' h w sq f (relativeExtension i P) =
      relativeExtension i' (relativeExtensionPulledFrame i i' h hW P Q b) ∧
    homologyMap (relativeTransfer h i.openComplement I.cocomplex J.cocomplex a) 1
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      -relativeTorsorEquiv T' (Scheme.Etale.mk (h ⁻¹ᵁ i.openComplement).ι) J
        (Quotient.mk _ ⟨Q, Q.sheaf.obj.map (openSectionPullback h i.openComplement).op
          (b.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2)⟩)
```

### `AlgebraicGeometry.Etale.relativeExtensionEnlarge_square`

```lean
theorem relativeExtensionEnlarge_square {T Z Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    (𝟙 (relativeSections (Scheme.Etale.mk (𝟙 T)) I)) ≫
        relativeSectionRestriction T (Scheme.Etale.mk i'.openComplement.ι) I =
      relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) I ≫
        HomologicalComplex.extendMap
          (etaleSectionMap
            (MorphismProperty.Over.homMk (T.homOfLE hW) (by simp)) I)
          ComplexShape.embeddingUpNat
```

### `AlgebraicGeometry.Etale.relativeExtensionEnlargeComplex`

```lean
def relativeExtensionEnlargeComplex {T Z Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ):=
  relativeFiberMap (relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) I)
    (relativeSectionRestriction T (Scheme.Etale.mk i'.openComplement.ι) I) (𝟙 _)
    (HomologicalComplex.extendMap
      (etaleSectionMap (MorphismProperty.Over.homMk (T.homOfLE hW) (by simp)) I)
      ComplexShape.embeddingUpNat) (relativeExtensionEnlarge_square i i' hW I)
```

### `AlgebraicGeometry.Etale.relative_extension_enlarge`

```lean
theorem relative_extension_enlarge {T Z Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    (Ext.mk₀ (relativeExtensionSupportMap i i' hW)).comp
        (relativeExtension i P) (zero_add 1) =
      relativeExtension i' (relativeExtensionRestrictedFrame i i' hW P) ∧
    homologyMap (relativeExtensionEnlargeComplex i i' hW I.cocomplex) 1
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      relativeExtensionComparison i' G I 1
        (relativeExtension i' (relativeExtensionRestrictedFrame i i' hW P))
```

### `AlgebraicGeometry.Etale.relative_extension_forget`

```lean
theorem relative_extension_forget {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) (c : ResolutionSectionCanonicalComparison G I)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P.1)
    (hE : (ShortComplex.mk E.inclusion E.projection E.inclusion_projection).ShortExact) :
    (Ext.mk₀ (supportedIntegralUnit i)).comp (relativeExtension i P) (zero_add 1) =
      hE.extClass ∧
    relativeForgetH1 T i.openComplement G I c
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      Sheaf.Torsor.classH1 G (MorphismProperty.Over.mkIdTerminal @Etale T)
        (Quotient.mk _ P.1)
```

## New

### `AlgebraicGeometry.Etale.RelativeExtensionRepresents`

```lean
def RelativeExtensionRepresents {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i]
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z)) G 1) : Prop:=
  ∃ (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ E)
    (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z))
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (f : P.1.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1}),
    (∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      @id (E.obj.obj V) (f.app V (P.1.vadd V g t)) =
        @id (E.obj.obj V) (f.app V t) + a.hom.app V g) ∧
    (∀ (V : T.Etaleᵒᵖ) (t : P.1.sheaf.obj.obj V),
      b.hom.app V (f.app V t) = (supportedIntegralUnit i).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩)) ∧
    @id (E.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
      (f.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2) = 0 ∧ β = hE.extClass
```

### `AlgebraicGeometry.Etale.relativeExtension_existsUnique`

```lean
theorem relativeExtension_existsUnique {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    ∃! β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z)) G 1, RelativeExtensionRepresents i P β
```

### `AlgebraicGeometry.Etale.relativeExtension`

```lean
def relativeExtension {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i]
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G 1:=
  Classical.choose (relativeExtension_existsUnique i P)
```

### `AlgebraicGeometry.Etale.RelativeExtensionComparisonNormalization`

```lean
structure RelativeExtensionComparisonNormalization {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (e : ∀ q : ℕ, Ext.{u + 1}
      ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G q ≃+
        relativeCohomology T (Scheme.Etale.mk i.openComplement.ι) I q) : Propwhere
  onCocycle : ∀ (q : ℕ)
    (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z) ⟶
      I.cocomplex.X q) (hk : k ≫ I.cocomplex.d q (q + 1) = 0)
    (z : (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
      I.cocomplex).cycles (q : ℤ)),
    (relativeForgetComplex T (Scheme.Etale.mk i.openComplement.ι) I.cocomplex).f q
      ((relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        I.cocomplex).iCycles q z) =
      (HomologicalComplex.extendXIso
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex) ComplexShape.embeddingUpNat (rfl : (q : ℤ) = q)).inv
          (k.hom.app (op (Scheme.Etale.mk (𝟙 T)))
            ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
              (supportedIntegralOne T))) →
    (((CochainComplex.mappingCone (relativeSectionRestriction T
        (Scheme.Etale.mk i.openComplement.ι) I.cocomplex)).shiftFunctorObjXIso
        (-1) (q : ℤ) ((q : ℤ) + -1) rfl).hom ≫
      HomologicalComplex.homotopyCofiber.sndX
        (relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) I.cocomplex)
        ((q : ℤ) + -1))
      ((relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        I.cocomplex).iCycles q z) = 0 →
    e q (I.extMk k (q + 1) rfl hk) =
      (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        I.cocomplex).homologyπ q z
```

### `AlgebraicGeometry.Etale.relativeExtensionComparison_existsUnique`

```lean
theorem relativeExtensionComparison_existsUnique {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) :
    ∃! e : ∀ q : ℕ, Ext.{u + 1}
      ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G q ≃+
        relativeCohomology T (Scheme.Etale.mk i.openComplement.ι) I q,
      RelativeExtensionComparisonNormalization i G I e
```

### `AlgebraicGeometry.Etale.relativeExtensionComparison`

```lean
def relativeExtensionComparison {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (q : ℕ) : Ext.{u + 1}
      ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G q ≃+
        relativeCohomology T (Scheme.Etale.mk i.openComplement.ι) I q:=
  Classical.choose (relativeExtensionComparison_existsUnique i G I) q
```

### `AlgebraicGeometry.Etale.relative_extension_cohomology_normalization`

```lean
theorem relative_extension_cohomology_normalization {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    relativeExtensionComparison i G I 1 (relativeExtension i P) =
      -relativeTorsorEquiv T (Scheme.Etale.mk i.openComplement.ι) I (Quotient.mk _ P)
```

### `AlgebraicGeometry.Etale.relative_extension_coefficient`

```lean
theorem relative_extension_coefficient {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] {G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : G ⟶ G') (I : InjectiveResolution G) (J : InjectiveResolution G') (a : I.Hom J f)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (Q : Sheaf.Torsor G') (σ : P.1.sheaf.obj ⟶ Q.sheaf.obj)
    (hσ : ∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      σ.app V (P.1.vadd V g t) = Q.vadd V (f.hom.app V g) (σ.app V t)) :
    (relativeExtension i P).comp (Ext.mk₀ f) (add_zero 1) =
      relativeExtension i ⟨Q, σ.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2⟩ ∧
    homologyMap (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) a.hom) 1
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      relativeExtensionComparison i G' J 1
        (relativeExtension i ⟨Q, σ.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2⟩)
```

### `AlgebraicGeometry.Etale.relativeExtensionPullback`

```lean
def relativeExtensionPullback {T Z T' Z' : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (h : T' ⟶ T) [Etale h] (w : Z' ⟶ Z) (sq : IsPullback w i' i h)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
    (β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z)) G 1) :
    Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i').obj (supportedIntegralConstant Z')) G' 1:=
  letI := relativeExtensionExchange_isIso i i' h w sq
  ((Ext.mk₀ (inv (relativeExtensionExchange i i' h w sq.toCommSq))).comp
    (β.mapExactFunctor (upperStar AddCommGrpCat.{u + 1} h)) (zero_add 1)).comp
      (Ext.mk₀ (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).homEquiv _ _).symm f))
      (add_zero 1)
```

### `AlgebraicGeometry.Etale.relative_extension_pullback`

```lean
theorem relative_extension_pullback {T Z T' Z' : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (h : T' ⟶ T) [Etale h] (w : Z' ⟶ Z) (sq : IsPullback w i' i h)
    (hW : i'.openComplement = h ⁻¹ᵁ i.openComplement)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
    (I : InjectiveResolution G) (J : InjectiveResolution G')
    (a : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (ha : I.ι.f 0 ≫ a.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0))
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (Q : Sheaf.Torsor G')
    (b : P.1.sheaf.obj ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj)
    (hb : ∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      b.app V (P.1.vadd V g t) =
        Q.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj V.unop))
          (f.hom.app V g) (b.app V t)) :
    relativeExtensionPullback i i' h w sq f (relativeExtension i P) =
      relativeExtension i' (relativeExtensionPulledFrame i i' h hW P Q b) ∧
    homologyMap (relativeTransfer h i.openComplement I.cocomplex J.cocomplex a) 1
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      -relativeTorsorEquiv T' (Scheme.Etale.mk (h ⁻¹ᵁ i.openComplement).ι) J
        (Quotient.mk _ ⟨Q, Q.sheaf.obj.map (openSectionPullback h i.openComplement).op
          (b.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2)⟩)
```

### `AlgebraicGeometry.Etale.relativeExtensionEnlarge_square`

```lean
theorem relativeExtensionEnlarge_square {T Z Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    (𝟙 (relativeSections (Scheme.Etale.mk (𝟙 T)) I)) ≫
        relativeSectionRestriction T (Scheme.Etale.mk i'.openComplement.ι) I =
      relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) I ≫
        HomologicalComplex.extendMap
          (etaleSectionMap
            (show Scheme.Etale.mk i'.openComplement.ι ⟶ Scheme.Etale.mk i.openComplement.ι from
              MorphismProperty.Over.homMk (T.homOfLE hW) (by simp)) I)
          ComplexShape.embeddingUpNat
```

### `AlgebraicGeometry.Etale.relativeExtensionEnlargeComplex`

```lean
def relativeExtensionEnlargeComplex {T Z Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι) I ⟶
      relativeSectionComplex T (Scheme.Etale.mk i'.openComplement.ι) I:=
  relativeFiberMap (relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) I)
    (relativeSectionRestriction T (Scheme.Etale.mk i'.openComplement.ι) I) (𝟙 _)
    (HomologicalComplex.extendMap
      (etaleSectionMap
        (show Scheme.Etale.mk i'.openComplement.ι ⟶ Scheme.Etale.mk i.openComplement.ι from
          MorphismProperty.Over.homMk (T.homOfLE hW) (by simp)) I)
      ComplexShape.embeddingUpNat) (relativeExtensionEnlarge_square i i' hW I)
```

### `AlgebraicGeometry.Etale.relative_extension_enlarge`

```lean
theorem relative_extension_enlarge {T Z Z' : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (hW : i'.openComplement ≤ i.openComplement)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    (Ext.mk₀ (relativeExtensionSupportMap i i' hW)).comp
        (relativeExtension i P) (zero_add 1) =
      relativeExtension i' (relativeExtensionRestrictedFrame i i' hW P) ∧
    (homologyMap (relativeExtensionEnlargeComplex i i' hW I.cocomplex) 1).hom
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      relativeExtensionComparison i' G I 1
        (relativeExtension i' (relativeExtensionRestrictedFrame i i' hW P))
```

### `AlgebraicGeometry.Etale.relative_extension_forget`

```lean
theorem relative_extension_forget {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) (c : ResolutionSectionCanonicalComparison G I)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P.1)
    (hE : (ShortComplex.mk E.inclusion E.projection E.inclusion_projection).ShortExact) :
    (Ext.mk₀ (supportedIntegralUnit i)).comp (relativeExtension i P) (zero_add 1) =
      hE.extClass ∧
    relativeForgetH1 T i.openComplement G I c
        (relativeExtensionComparison i G I 1 (relativeExtension i P)) =
      Sheaf.Torsor.classH1 G (MorphismProperty.Over.mkIdTerminal @Etale T)
        (Quotient.mk _ P.1)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeExtensionCohomologyNormalization | M1 | Thread the available Ext instance through the definitions and proofs. |
| Sheaf.AlgebraicGeometry.CartierPairTensorAddition | unclaimed | Direct consumer; uses framed representation and normalized classes, with globally inferred HasExt. Does not use the changed normalization predicate. |
| Sheaf.Paper.RamifiedCartierSupportedPurity | unclaimed | Transitive consumer through CartierPairTensorAddition; no direct use of a changed declaration. |

The refreshed `tools/downstream.py` scan reports the two downstream modules above.
The direct consumer uses the framed representation and normalized classes; instance
proof irrelevance identifies the explicit HasExt parameter with the globally available
instance. Neither consumer uses `RelativeExtensionComparisonNormalization` directly.
Only the item itself uses that predicate. The DAG parent
`lem-pur-divisor-normalized-realization` remains attached and required; its module is
listed in rework as quarantined. This delivery does not withdraw or alter that parent.
Existing applications infer the added instances from the same global instances.
No forced adaptation of another group's file is needed.

## Status

landed 20261025T050832-L-3848476 2026-10-25 (merge of deliver/M1/Sheaf.AlgebraicGeometry.RelativeExtensionCohomologyNormalization)
